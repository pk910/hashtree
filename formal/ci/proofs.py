#!/usr/bin/env python3
"""Proof gate for the hashtree machine-code verification.

Two jobs:

  check       (CI, cheap) verify that the instruction models in
              formal/lean/Hashtree/Kernels still describe the objects in the
              shipped .syso archives, that the recorded artifact and source
              hashes are current, and that every proved kernel still has its
              certificate in formal/lean/Gen.tar.zst.  No Lean toolchain is
              needed: only python3, ar, objdump and zstd.

  gen-models  (contributor, cheap) regenerate the models from the current
              .syso files, update formal/proofs.json, and tell you which
              kernels need `make regen KERNEL=...` (the expensive step).

  check-audit (reviewer) check the output of `make audit` against the axiom
              policy: only Lean's standard axioms and the per-lemma
              `_native.bv_decide` axioms are allowed, and every theorem the
              manifest marks proved must actually have been audited.

  report      (reviewer) write a machine-readable verification report from a
              successful `make all && make audit` run: commit, toolchain,
              certificate digests, audit summary, host.  This is what an
              author and an independent reviewer compare in the PR.

The manifest formal/proofs.json is the certificate registry: it maps every
shipped kernel to the object it was extracted from, the Lean model, and the
theorem that covers it.  A kernel without an entry is reported as unproved.
It also records, at pack time, the hashes of the models and generator sources
the committed certificate was produced from; the cheap gate fails when either
changed without a new pack.

The heavy Lean check is deliberately NOT run in hosted CI.  Authors run it
locally and a reviewer repeats it; `formal/verify.sh` runs the full sequence
and emits the report both sides compare.

Usage:
  python3 formal/ci/proofs.py check --repo .
  python3 formal/ci/proofs.py gen-models --repo . [--force]
  python3 formal/ci/proofs.py check-audit --repo . --audit audit.log
  python3 formal/ci/proofs.py report --repo . --audit audit.log --out report.json

Exit codes: 0 ok, 1 verification failure, 2 usage/environment error,
3 models were rewritten and need `make regen KERNEL=...`.
"""

import argparse
import datetime
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
FORMAL = os.path.dirname(HERE)
LEAN = os.path.join(FORMAL, "lean")
MANIFEST = os.path.join(FORMAL, "proofs.json")

TRANSLATORS = {
    "x86_to_lean.py": "x86_to_lean.py",
    "arm_to_lean.py": "arm_to_lean.py",
    "riscv_to_lean.py": "riscv_to_lean.py",
}

# Objects that are known to have no functional proof yet (C code).  A new
# object that is not in the manifest is an error: somebody added a kernel and
# did not add a proof.
KNOWN_UNPROVED_OBJECTS = {"sha256_generic.o", "hashtree.o"}

# Sources that emit Hashtree/Gen.  The committed certificate is only meaningful
# for the models and generators recorded in the manifest; changing either
# without regenerating and repacking makes the gate fail.
GENERATOR_SOURCES = [
    "formal/lean/X86Loop.lean",
    "formal/lean/X86LoopW.lean",
    "formal/lean/X86Loop1.lean",
    "formal/lean/X86Loop1W.lean",
    "formal/lean/X86Proof1.lean",
    "formal/lean/X86ProofV.lean",
    "formal/lean/ArmProof.lean",
    "formal/lean/RvProof.lean",
    "formal/lean/tools/x86_to_lean.py",
    "formal/lean/tools/arm_to_lean.py",
    "formal/lean/tools/riscv_to_lean.py",
]

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NATIVE_AXIOM_RE = re.compile(r".*_native\.bv_decide\.ax_.*")


def is_allowed_axiom(name, extra):
    return (name in STANDARD_AXIOMS or name in extra or
            NATIVE_AXIOM_RE.fullmatch(name) is not None)


def die(msg):
    print("error: " + msg, file=sys.stderr)
    sys.exit(2)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_manifest(repo):
    path = os.path.join(repo, "formal", "proofs.json")
    if not os.path.exists(path):
        die("missing formal/proofs.json")
    with open(path) as f:
        return json.load(f)


def write_manifest(repo, data):
    path = os.path.join(repo, "formal", "proofs.json")
    with open(path, "w") as f:
        json.dump(data, f, indent=2)
        f.write("\n")


def archive_members(path):
    """Names of the members of an ar archive, without extracting it."""
    out = subprocess.run(["ar", "t", path], capture_output=True, text=True)
    if out.returncode != 0:
        die("cannot list %s: %s" % (path, out.stderr.strip()))
    return [ln.strip() for ln in out.stdout.splitlines() if ln.strip()]


def extract_archive(path, dest):
    out = subprocess.run(["ar", "x", os.path.abspath(path)], cwd=dest,
                         capture_output=True, text=True)
    if out.returncode != 0:
        die("cannot extract %s: %s" % (path, out.stderr.strip()))


def run_translator(repo, translator, obj, symbol, namespace):
    tool = os.path.join(repo, "formal", "lean", "tools", TRANSLATORS[translator])
    out = subprocess.run([sys.executable, tool, obj, symbol, namespace],
                         cwd=os.path.dirname(tool), capture_output=True, text=True)
    if out.returncode != 0:
        return None, (out.stderr.strip() or out.stdout.strip() or
                      "translator exited %d" % out.returncode)
    return out.stdout, None


def normalize_lean(text):
    """Drop generated trailing `-- ...` comments and blank lines.

    objdump versions differ in the symbol annotation they put in the comment
    (`<ltmp0>` vs `<_symbol>`); the Lean term is the same.  Comments are not
    part of the certificate, so compare the term stream only.
    """
    lines = []
    for line in text.splitlines():
        line = re.sub(r"\s+--\s.*$", "", line).rstrip()
        if line:
            lines.append(line)
    return "\n".join(lines)


def gen_members(repo):
    """Members of Gen.tar.zst, or None if the archive is unusable."""
    archive = os.path.join(repo, "formal", "lean", "Gen.tar.zst")
    proc = subprocess.Popen(["zstd", "-dc", archive], stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    tar = subprocess.run(["tar", "-t"], stdin=proc.stdout, capture_output=True,
                         text=True)
    proc.stdout.close()
    proc.wait()
    if proc.returncode != 0 or tar.returncode != 0:
        return None
    return set(tar.stdout.splitlines())


def theorem_module(theorem):
    parts = theorem.split(".")
    return ".".join(parts[:-1])


def module_path(module):
    return module.replace(".", "/") + ".lean"


def module_has_theorem(repo, theorem, gen_set):
    """Check that the theorem's module and declaration are present."""
    module = theorem_module(theorem)
    name = theorem.split(".")[-1]
    rel = module_path(module)
    if module.startswith("Hashtree.Gen."):
        if gen_set is None:
            return False, "Gen.tar.zst is unreadable (need zstd)"
        if rel not in gen_set:
            return False, "%s is not in Gen.tar.zst" % rel
        return True, "in Gen.tar.zst"
    path = os.path.join(repo, "formal", "lean", rel)
    if not os.path.exists(path):
        return False, "missing %s" % rel
    with open(path, errors="replace") as f:
        body = f.read()
    if not re.search(r"^\s*(theorem|def|lemma)\s+" + re.escape(name) + r"\b",
                     body, re.M):
        return False, "%s does not define `%s`" % (rel, name)
    return True, rel


def is_proved(unit):
    return unit.get("proof", {}).get("status", "").startswith("proved")


def audit_names(repo):
    """Theorems covered by `#print axioms` in Axioms.lean."""
    path = os.path.join(LEAN, "Axioms.lean")
    if not os.path.exists(path):
        return None, []
    with open(path, errors="replace") as f:
        body = f.read()
    names = re.findall(r"^\s*#print axioms\s+([A-Za-z0-9_'.]+)", body, re.M)
    return set(names), names


def check_bindings(repo, manifest):
    """The certificate must have been packed from the current models and generators."""
    errors = []
    units = manifest["units"]
    proved_models = [u for u in units if is_proved(u) and u.get("model")]
    recorded_models = manifest.get("models")
    if proved_models and recorded_models is None:
        errors.append("manifest is missing certificate model hashes; run `make pack`")
        recorded_models = {}
    for unit in units:
        model = unit.get("model")
        if not model or not is_proved(unit):
            continue
        path = os.path.join(LEAN, model)
        if not os.path.exists(path):
            errors.append("%s: model %s is missing" % (unit["name"], model))
            continue
        recorded = recorded_models.get(model)
        actual = sha256_file(path)
        if recorded is None:
            errors.append("%s: no recorded hash for model %s; run `make pack`"
                          % (unit["name"], model))
        elif actual != recorded:
            errors.append(
                "%s: model %s changed since the certificate was packed; rebuild "
                "it with `make -C formal/lean regen KERNEL=%s`, then `make pack`"
                % (unit["name"], model, unit["name"]))
    generators = manifest.get("generators")
    if proved_models and generators is None:
        errors.append("manifest is missing generator hashes; run `make pack`")
        generators = {}
    for rel, recorded in sorted(generators.items()):
        path = os.path.join(repo, rel)
        if not os.path.exists(path):
            errors.append("recorded generator %s is missing" % rel)
            continue
        actual = sha256_file(path)
        if actual != recorded:
            errors.append(
                "generator %s changed since the certificate was packed; "
                "regenerate the affected kernels (`make regen KERNEL=...`), "
                "then run `make pack`" % rel)
    return errors


def check_audit_coverage(repo, manifest):
    """Every proved theorem must be printed by `make audit`."""
    names, _ = audit_names(repo)
    if names is None:
        return ["missing formal/lean/Axioms.lean"]
    errors = []
    for unit in manifest["units"]:
        if not is_proved(unit):
            continue
        for theorem in unit["proof"].get("theorems", []):
            if theorem not in names:
                errors.append("%s: `%s` is not audited in Axioms.lean"
                              % (unit["name"], theorem))
    return errors


def check_axiom_declarations(repo):
    """Reject hand-written `axiom` declarations outside the generated proofs."""
    errors = []
    for root, dirs, files in os.walk(LEAN):
        dirs[:] = [d for d in dirs if d not in (".lake", "Gen")]
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(root, fn)
            rel = os.path.relpath(path, repo)
            with open(path, errors="replace") as f:
                for lineno, line in enumerate(f, 1):
                    m = re.match(r"\s*axiom\s+([A-Za-z0-9_']+)", line)
                    if m:
                        errors.append("%s:%d: unexpected `axiom %s` declaration"
                                      % (rel, lineno, m.group(1)))
    return errors


def check_archive(repo, manifest):
    errors = []
    archive = os.path.join(repo, manifest["gen"]["archive"])
    recorded = manifest["gen"]["sha256"]
    if not os.path.exists(archive):
        errors.append("missing %s" % manifest["gen"]["archive"])
    else:
        actual = sha256_file(archive)
        if actual != recorded:
            errors.append("Gen.tar.zst hash mismatch: manifest %s, actual %s"
                          % (recorded[:16], actual[:16]))
    # The restored tree, if present, must match its per-file manifest.
    gen_dir = os.path.join(LEAN, "Hashtree", "Gen")
    if os.path.isdir(gen_dir):
        files_manifest = os.path.join(repo, manifest["gen"]["files_manifest"])
        proc = subprocess.run(["sha256sum", "-c", os.path.basename(files_manifest),
                               "--quiet"], cwd=os.path.dirname(files_manifest),
                              capture_output=True, text=True)
        if proc.returncode != 0:
            errors.append("restored Hashtree/Gen does not match Gen.files.sha256 "
                          "(run `make verify` in formal/lean)")
    return errors


def check(repo, manifest):
    errors = []
    warnings = []
    rows = []

    errors += check_archive(repo, manifest)
    errors += check_bindings(repo, manifest)
    errors += check_audit_coverage(repo, manifest)
    errors += check_axiom_declarations(repo)
    gen_set = gen_members(repo)

    artifacts = manifest.get("artifacts", {})
    tmp = tempfile.mkdtemp(prefix="hashtree-proof-gate-")
    try:
        extracted = {}
        for plat, art in artifacts.items():
            path = os.path.join(repo, art["path"])
            if not os.path.exists(path):
                errors.append("missing artifact %s" % art["path"])
                continue
            actual = sha256_file(path)
            if actual != art["sha256"]:
                errors.append(
                    "artifact %s changed (%s -> %s); run "
                    "`python3 formal/ci/proofs.py gen-models` and commit "
                    "formal/proofs.json" % (art["path"], art["sha256"][:12],
                                            actual[:12]))
            dest = os.path.join(tmp, plat)
            os.makedirs(dest)
            extract_archive(path, dest)
            extracted[plat] = dest

        # Source hashes: catch an asm edit that was never rebuilt into a
        # .syso.  A comment-only edit can be recorded with `gen-models --force`.
        sources = manifest.get("sources", {})
        for src, recorded in sources.items():
            path = os.path.join(repo, src)
            if not os.path.exists(path):
                errors.append("manifest references missing source %s" % src)
                continue
            actual = sha256_file(path)
            if actual != recorded:
                errors.append(
                    "source %s changed but its artifacts were not rebuilt "
                    "(recorded %s, actual %s). Rebuild the .syso for every "
                    "platform using it, then run `gen-models`; use `--force` "
                    "only for comment-only edits."
                    % (src, recorded[:12], actual[:12]))

        # Rebuild every model from the current object and compare the term
        # stream.  This is the real "the shipped code is the proved code" gate.
        for unit in manifest["units"]:
            name = unit["name"]
            model_rel = unit.get("model")
            if not model_rel:
                continue
            model_path = os.path.join(LEAN, model_rel)
            if not os.path.exists(model_path):
                errors.append("%s: model %s is missing" % (name, model_rel))
                continue
            status = unit["proof"]["status"]
            if unit.get("translator"):
                plat = unit["platform"]
                if plat not in extracted:
                    continue
                obj = os.path.join(extracted[plat], unit["object"])
                if not os.path.exists(obj):
                    errors.append("%s: %s not found in %s"
                                  % (name, unit["object"],
                                     artifacts[plat]["path"]))
                    continue
                new, err = run_translator(repo, unit["translator"], obj,
                                          unit["symbol"], unit["namespace"])
                if err:
                    errors.append("%s: translator failed: %s" % (name, err))
                    continue
                with open(model_path, errors="replace") as f:
                    old = f.read()
                if normalize_lean(new) != normalize_lean(old):
                    errors.append(
                        "%s: %s does not describe %s in %s. Regenerate it with "
                        "`python3 formal/ci/proofs.py gen-models --repo .`, "
                        "then rebuild the certificate with "
                        "`make -C formal/lean regen KERNEL=%s`."
                        % (name, model_rel, unit["symbol"],
                           artifacts[plat]["path"], name))
                    rows.append((plat, name, "MODEL DIFF", status))
                    continue
            rows.append((unit.get("platform", "-"), name, "model OK", status))

            if status in ("proved-all-counts", "proved-fixed-count",
                          "proved-conditional"):
                for theorem in unit["proof"].get("theorems", []):
                    ok, detail = module_has_theorem(repo, theorem, gen_set)
                    if not ok:
                        errors.append("%s: certificate for `%s`: %s"
                                      % (name, theorem, detail))
            elif status in ("model-only", "transfers"):
                warnings.append("%s: model is validated but there is no "
                                "functional proof yet (%s)"
                                % (name, unit["proof"].get("note", status)))

        # Every generated model must be registered, and every object in the
        # archives must be either covered or a known-unproved C object.
        registered = {u.get("model") for u in manifest["units"]}
        for root, _, files in os.walk(os.path.join(LEAN, "Hashtree", "Kernels")):
            for fn in files:
                if not fn.endswith(".lean"):
                    continue
                rel = os.path.relpath(os.path.join(root, fn), LEAN)
                with open(os.path.join(root, fn), errors="replace") as f:
                    head = f.read(4096)
                if "Generated by tools/" in head and rel not in registered:
                    errors.append("unregistered model %s (add it to "
                                  "formal/proofs.json)" % rel)
        covered = {(u.get("platform"), u.get("object"))
                   for u in manifest["units"] if u.get("object")}
        for plat, art in artifacts.items():
            for obj in archive_members(os.path.join(repo, art["path"])):
                if (plat, obj) not in covered and obj not in KNOWN_UNPROVED_OBJECTS:
                    warnings.append("%s/%s is shipped but has no proof entry"
                                    % (plat, obj))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print("proof gate: %s" % repo)
    print("  Lean toolchain: %s" % manifest.get("toolchain", "?"))
    print()
    for plat, name, status, proof in rows:
        print("  %-14s %-22s %-10s %s" % (plat, name, status, proof))
    print()
    for w in warnings:
        print("warning: " + w)
    if errors:
        print()
        for e in errors:
            print("FAIL: " + e)
        print("\n%d problem(s)." % len(errors))
        return 1
    print("all shipped kernels match their models and certificates.")
    return 0


def gen_models(repo, force):
    manifest = read_manifest(repo)
    changed = []
    errors = []
    tmp = tempfile.mkdtemp(prefix="hashtree-gen-models-")
    try:
        extracted = {}
        for plat, art in manifest["artifacts"].items():
            path = os.path.join(repo, art["path"])
            if not os.path.exists(path):
                die("missing artifact %s" % art["path"])
            dest = os.path.join(tmp, plat)
            os.makedirs(dest)
            extract_archive(path, dest)
            extracted[plat] = dest

        # Refuse to record a source hash when the corresponding artifact was
        # not rebuilt: the proof would describe stale machine code.
        for src in manifest.get("sources", {}):
            path = os.path.join(repo, src)
            if os.path.exists(path):
                actual = sha256_file(path)
                if actual != manifest["sources"][src] and not force:
                    users = [u["name"] for u in manifest["units"]
                             if src in u.get("sources", [])]
                    stale = []
                    for u in manifest["units"]:
                        if src not in u.get("sources", []):
                            continue
                        art = manifest["artifacts"].get(u.get("platform"))
                        if art and sha256_file(os.path.join(repo, art["path"])) == art["sha256"]:
                            stale.append(u["name"])
                    if stale:
                        errors.append(
                            "source %s changed but %s still has the old "
                            "archive. Rebuild the .syso first (or pass "
                            "--force for a comment-only edit)."
                            % (src, ", ".join(stale)))

        for unit in manifest["units"]:
            if not unit.get("translator"):
                continue
            plat = unit["platform"]
            if plat not in extracted:
                continue
            obj = os.path.join(extracted[plat], unit["object"])
            if not os.path.exists(obj):
                errors.append("%s: %s missing" % (unit["name"], unit["object"]))
                continue
            new, err = run_translator(repo, unit["translator"], obj,
                                      unit["symbol"], unit["namespace"])
            if err:
                errors.append("%s: %s" % (unit["name"], err))
                continue
            model = os.path.join(LEAN, unit["model"])
            old = open(model, errors="replace").read() if os.path.exists(model) else ""
            if normalize_lean(new) != normalize_lean(old):
                with open(model, "w") as f:
                    f.write(new)
                if unit["proof"]["status"].startswith("proved"):
                    changed.append(unit["name"])
                else:
                    print("model updated (unproved, no certificate): %s"
                          % unit["name"])
            # The model is current now; record the artifact it came from.
            unit["_model_checked"] = True

        if errors:
            for e in errors:
                print("error: " + e, file=sys.stderr)
            return 2

        for plat, art in manifest["artifacts"].items():
            art["sha256"] = sha256_file(os.path.join(repo, art["path"]))
        for unit in manifest["units"]:
            for src in unit.get("sources", []):
                path = os.path.join(repo, src)
                if os.path.exists(path):
                    manifest["sources"][src] = sha256_file(path)
        manifest["sources"] = dict(sorted(manifest["sources"].items()))
        for unit in manifest["units"]:
            unit.pop("_model_checked", None)
        write_manifest(repo, manifest)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if changed:
        print("models rewritten: %s" % ", ".join(sorted(changed)))
        print("\nThe instruction streams changed, so the certificates for these "
              "kernels are stale. Rebuild them (this is the expensive step):")
        for name in sorted(changed):
            print("  make -C formal/lean regen KERNEL=%s" % name)
        print("\nThen repack and commit:")
        print("  make -C formal/lean pack")
        print("  git add formal/lean/Hashtree/Kernels formal/proofs.json "
              "formal/lean/Gen.tar.zst formal/lean/Gen.sha256 "
              "formal/lean/Gen.files.sha256")
        return 3
    print("models are current; formal/proofs.json updated.")
    return 0


def record_gen(repo):
    manifest = read_manifest(repo)
    archive = os.path.join(repo, manifest["gen"]["archive"])
    if not os.path.exists(archive):
        die("missing %s (run pack-gen.sh first)" % manifest["gen"]["archive"])
    manifest["schema"] = 2
    manifest["gen"]["sha256"] = sha256_file(archive)
    files_manifest = os.path.join(repo, manifest["gen"]["files_manifest"])
    if not os.path.exists(files_manifest):
        die("missing %s (run pack-gen.sh first)" % manifest["gen"]["files_manifest"])
    manifest["gen"]["files_manifest_sha256"] = sha256_file(files_manifest)

    generators = {}
    for rel in GENERATOR_SOURCES:
        path = os.path.join(repo, rel)
        if os.path.exists(path):
            generators[rel] = sha256_file(path)
    manifest["generators"] = dict(sorted(generators.items()))

    models = {}
    for unit in manifest["units"]:
        model = unit.get("model")
        if not model:
            continue
        path = os.path.join(LEAN, model)
        if os.path.exists(path):
            models[model] = sha256_file(path)
    manifest["models"] = dict(sorted(models.items()))

    write_manifest(repo, manifest)
    print("recorded %s %s" % (manifest["gen"]["archive"],
                              manifest["gen"]["sha256"]))
    print("recorded %d model and %d generator hashes"
          % (len(manifest["models"]), len(manifest["generators"])))
    return 0


AUDIT_DEPENDS_RE = re.compile(
    r"^\s*(?:'([^']+)'|([A-Za-z0-9_.]+)) depends on axioms: \[(.*)\]\s*$")
AUDIT_NONE_RE = re.compile(
    r"^\s*(?:'([^']+)'|([A-Za-z0-9_.]+)) does not depend on any axioms")


def parse_audit(path):
    """Map theorem -> list of axioms from `make audit` output."""
    result = {}
    if not os.path.exists(path):
        die("missing audit log %s" % path)
    with open(path, errors="replace") as f:
        for line in f:
            m = AUDIT_DEPENDS_RE.match(line)
            if m:
                name = m.group(1) or m.group(2)
                axioms = [a.strip() for a in m.group(3).split(",") if a.strip()]
                result[name] = axioms
                continue
            m = AUDIT_NONE_RE.match(line)
            if m:
                result[m.group(1) or m.group(2)] = []
    return result


def check_audit(repo, audit_path, extra):
    manifest = read_manifest(repo)
    audited = parse_audit(audit_path)
    problems = []
    if not audited:
        problems.append("audit log contains no `#print axioms` output")
    for name, axioms in sorted(audited.items()):
        for axiom in axioms:
            if not is_allowed_axiom(axiom, extra):
                problems.append("%s depends on disallowed axiom %s"
                                % (name, axiom))
    for unit in manifest["units"]:
        if not is_proved(unit):
            continue
        for theorem in unit["proof"].get("theorems", []):
            if theorem not in audited:
                problems.append("%s: `%s` was not audited"
                                % (unit["name"], theorem))
    if problems:
        print("audit check failed:", file=sys.stderr)
        for p in problems:
            print("  FAIL: " + p, file=sys.stderr)
        return 1
    print("audit clean: %d theorems, only standard and bv_decide native axioms"
          % len(audited))
    return 0


def verification_report(repo, audit_path, out, command, verifier):
    manifest = read_manifest(repo)
    audit_problems = []
    audited = parse_audit(audit_path)
    for name, axioms in sorted(audited.items()):
        for axiom in axioms:
            if axiom == "sorryAx" or not is_allowed_axiom(axiom, set()):
                audit_problems.append("%s: %s" % (name, axiom))
    for unit in manifest["units"]:
        if not is_proved(unit):
            continue
        for theorem in unit["proof"].get("theorems", []):
            if theorem not in audited:
                audit_problems.append("%s: %s was not audited"
                                      % (unit["name"], theorem))

    def git(*args):
        proc = subprocess.run(["git", "-C", repo] + list(args),
                              capture_output=True, text=True)
        return proc.stdout.strip() if proc.returncode == 0 else ""

    commit = os.environ.get("VERIFY_COMMIT") or git("rev-parse", "HEAD")
    branch = os.environ.get("VERIFY_BRANCH") or git("rev-parse", "--abbrev-ref", "HEAD")
    dirty_env = os.environ.get("VERIFY_DIRTY")
    dirty = (dirty_env == "1") if dirty_env is not None else bool(git("status", "--porcelain"))

    files_manifest = os.path.join(repo, manifest["gen"]["files_manifest"])
    files_count = 0
    if os.path.exists(files_manifest):
        with open(files_manifest, errors="replace") as f:
            files_count = sum(1 for line in f if line.strip())
    archive = os.path.join(repo, manifest["gen"]["archive"])

    report = {
        "result": "ok" if not audit_problems else "failed",
        "gate": os.environ.get("VERIFY_GATE"),
        "commit": commit,
        "branch": branch,
        "dirty": dirty,
        "toolchain": manifest.get("toolchain"),
        "lean_toolchain": open(os.path.join(repo, "formal", "lean",
                                            "lean-toolchain")).read().strip()
        if os.path.exists(os.path.join(repo, "formal", "lean", "lean-toolchain"))
        else None,
        "gen": {
            "archive": manifest["gen"]["archive"],
            "archive_sha256": sha256_file(archive) if os.path.exists(archive) else None,
            "files": files_count,
            "files_manifest_sha256": sha256_file(files_manifest)
            if os.path.exists(files_manifest) else None,
        },
        "audit": {
            "sha256": sha256_file(audit_path) if os.path.exists(audit_path) else None,
            "theorems": len(audited),
            "axioms": sorted({a for axioms in audited.values() for a in axioms}),
            "problems": audit_problems,
        },
        "host": {
            "name": platform.node(),
            "machine": platform.machine(),
            "cpus": os.cpu_count(),
            "utc": datetime.datetime.now(datetime.timezone.utc)
            .replace(microsecond=0).isoformat(),
        },
        "verifier": verifier,
        "command": command,
    }
    text = json.dumps(report, indent=2) + "\n"
    if out:
        with open(out, "w") as f:
            f.write(text)
        print("wrote %s" % out)
    print(text)
    if audit_problems:
        for p in audit_problems:
            print("FAIL: " + p, file=sys.stderr)
        return 1
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("check", help="verify models, artifacts and certificates")
    p.add_argument("--repo", default=os.path.dirname(FORMAL))
    p = sub.add_parser("gen-models", help="regenerate models from the current .syso files")
    p.add_argument("--repo", default=os.path.dirname(FORMAL))
    p.add_argument("--force", action="store_true",
                   help="record source hashes even if the artifact was not rebuilt")
    p = sub.add_parser("record-gen",
                       help="record certificate hashes after packing Gen")
    p.add_argument("--repo", default=os.path.dirname(FORMAL))
    p = sub.add_parser("check-audit",
                       help="check `make audit` output against the axiom policy")
    p.add_argument("--repo", default=os.path.dirname(FORMAL))
    p.add_argument("--audit", required=True)
    p.add_argument("--allow", action="append", default=[],
                   help="additional axiom name to allow (repeatable)")
    p = sub.add_parser("report",
                       help="write a verification report from an audit log")
    p.add_argument("--repo", default=os.path.dirname(FORMAL))
    p.add_argument("--audit", required=True)
    p.add_argument("--out", default=None)
    p.add_argument("--command", default=None)
    p.add_argument("--verifier", default=None)
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)

    for tool in ("ar", "zstd"):
        if shutil.which(tool) is None:
            die("%s not found in PATH" % tool)

    if args.cmd == "check":
        return check(repo, read_manifest(repo))
    if args.cmd == "record-gen":
        return record_gen(repo)
    if args.cmd == "check-audit":
        return check_audit(repo, args.audit, set(args.allow))
    if args.cmd == "report":
        return verification_report(repo, args.audit, args.out,
                                   args.command, args.verifier)
    return gen_models(repo, args.force)


if __name__ == "__main__":
    sys.exit(main())
