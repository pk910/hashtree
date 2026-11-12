import Hashtree.Asm.RiscvRun
import Hashtree.Kernels.Riscv.X1
import Hashtree.Kernels.Riscv.ZbbX1
import Hashtree.Kernels.Riscv.Crypto
import Hashtree.Kernels.Riscv.DispHash
import Hashtree.Kernels.Riscv.DispInitAndHash
import Hashtree.Kernels.Riscv.DispInit

/-! `rvcheck`: run every RV64 kernel model on random inputs for many counts and stack
alignments and compare with `Spec.node`; check the ABI (callee-saved registers, stack window,
writes only to the output), the ISA tag of every executed instruction, and count misaligned
accesses for unaligned buffers; run the dispatcher (`hashtree_hash` → `init_and_hash` →
`riscv_hwprobe` stub → kernel) for several probe answers.

Other modes (for the differential tests against qemu):
* `--dump <kernel> <count> <seed> <inOff> <outOff>`: print the output bytes (hex); `--dumpa`: the
  output buffer is inside the input buffer (at `outOff`);
* `--disp <probe hex | fail> <count> <seed> <inOff> <outOff>`: run `hashtree_hash` with that
  `riscv_hwprobe` answer, print the path and the output;
* `--insn`: read lines `op imm a b` (hex 64-bit operands) from stdin, print the model's result. -/

open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvRun

def progs : List Prog := [
  ⟨"hashtree_sha256_riscv_x1", Hashtree.Kernels.Riscv.X1.prog, Hashtree.Kernels.Riscv.X1.compressed,
    Hashtree.Kernels.Riscv.X1.got, Hashtree.Kernels.Riscv.X1.datarel, Hashtree.Kernels.Riscv.X1.rodata.toArray, 10⟩,
  ⟨"hashtree_sha256_riscv_zbb_x1", Hashtree.Kernels.Riscv.ZbbX1.prog, Hashtree.Kernels.Riscv.ZbbX1.compressed,
    Hashtree.Kernels.Riscv.ZbbX1.got, Hashtree.Kernels.Riscv.ZbbX1.datarel, Hashtree.Kernels.Riscv.ZbbX1.rodata.toArray, 13⟩,
  ⟨"hashtree_sha256_riscv_crypto", Hashtree.Kernels.Riscv.Crypto.prog, Hashtree.Kernels.Riscv.Crypto.compressed,
    Hashtree.Kernels.Riscv.Crypto.got, Hashtree.Kernels.Riscv.Crypto.datarel, Hashtree.Kernels.Riscv.Crypto.rodata.toArray, 16⟩,
  ⟨"hashtree_hash", Hashtree.Kernels.Riscv.DispHash.prog, Hashtree.Kernels.Riscv.DispHash.compressed,
    Hashtree.Kernels.Riscv.DispHash.got, Hashtree.Kernels.Riscv.DispHash.datarel, Hashtree.Kernels.Riscv.DispHash.rodata.toArray, 19⟩,
  ⟨"init_and_hash", Hashtree.Kernels.Riscv.DispInitAndHash.prog, Hashtree.Kernels.Riscv.DispInitAndHash.compressed,
    Hashtree.Kernels.Riscv.DispInitAndHash.got, Hashtree.Kernels.Riscv.DispInitAndHash.datarel,
    Hashtree.Kernels.Riscv.DispInitAndHash.rodata.toArray, 22⟩,
  ⟨"hashtree_init", Hashtree.Kernels.Riscv.DispInit.prog, Hashtree.Kernels.Riscv.DispInit.compressed,
    Hashtree.Kernels.Riscv.DispInit.got, Hashtree.Kernels.Riscv.DispInit.datarel, Hashtree.Kernels.Riscv.DispInit.rodata.toArray, 25⟩]

/-- The kernels with the extensions each needs (beyond RV64I + C). -/
def kernels : List (String × List Ext) := [
  ("hashtree_sha256_riscv_x1", []),
  ("hashtree_sha256_riscv_zbb_x1", [.zbb]),
  ("hashtree_sha256_riscv_crypto", [.zbkb, .zknh])]

def randInput (seed n : Nat) : Array Nat := Id.run do
  let mut x := seed * 6364136223846793005 + 1442695040888963407
  let mut a : Array Nat := #[]
  for _ in [0:n] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    a := a.push ((x >>> 33) % 256)
  return a

def fuel : Nat := 400000

structure Result where
  s : CS
  fm : FMap
  st : Stats
  path : List String
  m0 : Addr Int → Cell W32 Int

def runKernel (name : String) (allowed : List Ext) (probe : Probe) (count seed : Nat) (L : Layout) : Result :=
  let input := randInput seed (64 * count)
  let m0 := mem0 progs input L
  let (s, fm, st, path) := runChain progs allowed probe m0 fuel 8 name {} {} (entry count L)
  ⟨s, fm, st, path, m0⟩

def hex2 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (2 - d.length) '0' ++ d)

def hex64 (n : Nat) : String :=
  let d := Nat.toDigits 16 (n % 2 ^ 64)
  String.ofList (List.replicate (16 - d.length) '0' ++ d)

/-- Check one kernel run; returns the failure description, if any. -/
def check1 (name : String) (exts : List Ext) (count seed : Nat) (L : Layout) (alignedOnly : Bool) :
    Option String × Stats × Int :=
  let r := runKernel name ([.rv64i, .c] ++ exts) none count seed L
  let input := randInput seed (64 * count)
  let e0 := entry count L
  let out := outBytes (overlay r.m0 r.fm) r.s L (32 * count)
  let regsOk := calleeSaved.all (fun i => r.s.getG i == e0.getG i)
  let bad := badWrites r.fm r.s L count 80 false
  let problems : List String :=
    (if r.s.err.isSome then [s!"err={r.s.err}"] else []) ++
    (if !r.s.halted || r.s.tail.isSome then [s!"halted={r.s.halted} tail={r.s.tail}"] else []) ++
    (if out != some (expected input count) then ["output mismatch"] else []) ++
    (if !regsOk then ["callee-saved register changed"] else []) ++
    (if !bad.isEmpty then [s!"writes outside output/stack window: {bad.take 4}"] else []) ++
    (if !r.st.isaViol.isEmpty then [s!"ISA violations at {r.st.isaViol.take 4}"] else []) ++
    (if alignedOnly && r.st.mis.any (· ≠ 0) then [s!"misaligned accesses {r.st.mis}"] else [])
  (if problems.isEmpty then none
   else some s!"FAIL {name} count={count} in={L.inOff} out={L.outOff} sp0={L.sp0} alias={L.alias}: {problems} path={r.path}",
   r.st, stackDepth r.fm r.s L)

/-- The folded runner agrees with the plain model `Riscv.run` (final registers, output, error). -/
def selfTest (name : String) (count : Nat) : Bool :=
  match progs.find? (·.name = name) with
  | none => false
  | some p =>
    let L : Layout := { sp0 := 16 }
    let input := randInput 99 (64 * count)
    let m0 := mem0 progs input L
    let s1 := Riscv.run p.code (p.env progs) m0 (fun _ => false) fuel (entry count L)
    let r := runKernel name [.rv64i, .c, .zbb, .zbkb, .zknh] none count 99 L
    s1.err == r.s.err && s1.halted == r.s.halted && s1.gpr == r.s.gpr &&
      outBytes m0 s1 L (32 * count) == outBytes (overlay r.m0 r.fm) r.s L (32 * count)

/-! ## Dispatcher -/

def probeExts (probe : Probe) : List Ext :=
  match probe with
  | none => []
  | some v => (if v.testBit 4 then [.zbb] else []) ++ (if v.testBit 8 then [.zbkb] else []) ++
      (if v.testBit 13 then [.zknh] else [])

def expectedKernel (probe : Probe) : String :=
  match probe with
  | none => "hashtree_sha256_riscv_x1"
  | some v => if v &&& 0x2100 = 0x2100 then "hashtree_sha256_riscv_crypto"
      else if v.testBit 4 then "hashtree_sha256_riscv_zbb_x1" else "hashtree_sha256_riscv_x1"

def checkDisp (probe : Probe) (count : Nat) : IO Bool := do
  let L : Layout := { sp0 := 32, inOff := 3, outOff := 5 }
  let allowed := [.rv64i, .c] ++ probeExts probe
  let input := randInput 5 (64 * count)
  let m0 := mem0 progs input L
  -- first call: hashtree_hash → init_and_hash → hwprobe → kernel
  let (s, fm, st, path) := runChain progs allowed probe m0 fuel 8 "hashtree_hash" {} {} (entry count L)
  let e0 := entry count L
  let out := outBytes (overlay m0 fm) s L (32 * count)
  let ok1 := s.err.isNone && s.halted && s.tail.isNone && out == some (expected input count) &&
    calleeSaved.all (fun i => s.getG i == e0.getG i) && st.isaViol.isEmpty &&
    path.getLast? == some (expectedKernel probe) && (badWrites fm s L count 80 true).isEmpty
  -- second call: hash_ptr now points at the kernel
  let s2 : CS := { entry count L with mem := s.mem }
  let (s2, fm2, st2, path2) := runChain progs allowed probe m0 fuel 8 "hashtree_hash" fm {} s2
  let out2 := outBytes (overlay m0 fm2) s2 L (32 * count)
  let ok2 := s2.err.isNone && s2.halted && out2 == some (expected input count) && st2.isaViol.isEmpty &&
    path2 == ["hashtree_hash", expectedKernel probe]
  -- hashtree_init(NULL) then hashtree_hash
  let s3 : CS := (entry count L).setG 10 (.num 0 0)
  let (s3, fm3, _, path3) := runChain progs allowed probe m0 fuel 8 "hashtree_init" {} {} s3
  let s4 : CS := { entry count L with mem := s3.mem }
  let (s4, fm4, _, path4) := runChain progs allowed probe m0 fuel 8 "hashtree_hash" fm3 {} s4
  let out4 := outBytes (overlay m0 fm4) s4 L (32 * count)
  let ok3 := s3.err.isNone && s3.halted && s3.tail.isNone && s4.err.isNone && s4.halted &&
    out4 == some (expected input count) && path4 == ["hashtree_hash", expectedKernel probe]
  IO.println s!"dispatch probe={probe}: first {path} {if ok1 then "ok" else s!"FAIL err={s.err}"}; again {path2} {if ok2 then "ok" else s!"FAIL err={s2.err}"}; init {path3} then {path4} {if ok3 then "ok" else s!"FAIL err={s3.err} {s4.err}"}"
  return ok1 && ok2 && ok3

/-! ## Single instructions (differential test against qemu) -/

def parseHex (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0)) 0

def valOf (n : Nat) : Val W32 Int := .num (BitVec.ofNat 32 n) (BitVec.ofNat 32 (n / 2 ^ 32))

def insnOf (op : String) (imm : Nat) : Option Instr :=
  match op with
  | "sha256sum0" => some (.sha .sum0 7 5) | "sha256sum1" => some (.sha .sum1 7 5)
  | "sha256sig0" => some (.sha .sig0 7 5) | "sha256sig1" => some (.sha .sig1 7 5)
  | "roriw" => some (.wop .roriw 7 5 imm) | "slliw" => some (.wop .slliw 7 5 imm)
  | "srliw" => some (.wop .srliw 7 5 imm) | "sraiw" => some (.wop .sraiw 7 5 imm)
  | "rev8" => some (.rev8 7 5) | "srai" => some (.srai 7 5 imm) | "slli" => some (.slli 7 5 imm)
  | "addw" => some (.addw 7 5 6) | "add" => some (.add 7 5 6) | "and" => some (.bop .and 7 5 6)
  | "or" => some (.bop .or 7 5 6) | "xor" => some (.bop .xor 7 5 6)
  | "addi" => some (.addi 7 5 (if imm ≥ 2048 then (imm : Int) - 4096 else imm))
  | "andi" => some (.bopi .and 7 5 (if imm ≥ 2048 then (imm : Int) - 4096 else imm))
  | "lui" => some (.lui 7 imm)
  | _ => none

def insnTest : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut n := 0
  repeat
    let ln ← stdin.getLine
    if ln.isEmpty then break
    match (ln.trimAscii.toString.splitOn " ") with
    | [op, imm, a, b] =>
      let s0 : CS := ((entry 0 {}).setG 5 (valOf (parseHex a))).setG 6 (valOf (parseHex b))
      let env : Env := ⟨10, 11, 12, symsOf progs⟩
      let ex (i : Instr) (s : CS) : CS := exec env (mem0 progs #[] {}) (fun _ => false) i s
      -- memory forms: x5 points at a 16-byte buffer holding `a` (little endian) and zeros
      let sm : CS := (storeVal (storeVal s0 ⟨rIn, 0⟩ (valOf (parseHex a))) ⟨rIn, 8⟩ (valOf 0)).setG 5 (.ptr ⟨rIn, 0⟩)
      let o : Int := parseHex imm
      let res : Option CS := match op with
        | "lwu" => some (ex (.lwu 7 5 o) sm)
        | "swld" => some (ex (.ld 7 5 0) (ex (.sw 6 5 o) sm))
        | "sdld" => some (ex (.ld 7 5 0) (ex (.sd 6 5 o) sm))
        | _ => (insnOf op (parseHex imm)).map (ex · s0)
      match res with
      | some s =>
        match s.err, s.getG 7 with
        | none, .num lo hi => IO.println s!"{op} {imm} {a} {b} {hex64 (hi.toNat * 2 ^ 32 + lo.toNat)}"
        | e, _ => IO.println s!"{op} {imm} {a} {b} ERR {e}"
        n := n + 1
      | none => IO.println s!"unknown op {op}"
    | _ => pure ()
  IO.eprintln s!"{n} instructions"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--dump", k, c, seed, io, oo] | ["--dumpa", k, c, seed, io, oo] =>
    let count := c.toNat!
    let L : Layout := { inOff := io.toNat!, outOff := oo.toNat!, sp0 := 0, alias := args.head? = some "--dumpa" }
    let r := runKernel k [.rv64i, .c, .zbb, .zbkb, .zknh] none count seed.toNat! L
    match outBytes (overlay r.m0 r.fm) r.s L (32 * count) with
    | some bs => IO.println (String.join (bs.map hex2))
    | none => IO.println s!"ERROR {r.s.err}"
    return 0
  | ["--insn"] => insnTest
  | ["--disp", pv, c, seed, io, oo] =>
    let count := c.toNat!
    let probe : Probe := if pv = "fail" then none else some (parseHex pv)
    let L : Layout := { inOff := io.toNat!, outOff := oo.toNat!, sp0 := 0 }
    let input := randInput seed.toNat! (64 * count)
    let m0 := mem0 progs input L
    let allowed := [.rv64i, .c] ++ probeExts probe
    let (s, fm, st, path) := runChain progs allowed probe m0 fuel 8 "hashtree_hash" {} {} (entry count L)
    IO.println s!"path {path} err {s.err} isaViolations {st.isaViol.length}"
    match outBytes (overlay m0 fm) s L (32 * count) with
    | some bs => IO.println (String.join (bs.map hex2))
    | none => IO.println s!"ERROR {s.err}"
    return 0
  | _ =>
    let mut fails := 0
    -- the folded runner equals the plain model
    for (k, _) in kernels do
      for c in [0, 1, 2] do
        unless selfTest k c do
          IO.println s!"FAIL selfTest {k} {c}"; fails := fails + 1
    IO.println "selfTest (folded runner = Riscv.run) done"
    -- all kernels, counts 0..34, four stack alignments, aligned buffers
    for (k, exts) in kernels do
      let mut n := 0
      let mut maxSteps := 0
      let mut depth : Int := 0
      for count in [0:35] do
        for sp0 in [0, 16, 32, 48] do
          let (res, st, d) := check1 k exts count (count + 7) { sp0 := sp0 } true
          if let some msg := res then
            IO.println msg; fails := fails + 1
          n := n + 1
          maxSteps := max maxSteps st.steps
          depth := max depth d
      IO.println s!"{k}: {n} runs, max {maxSteps} steps, stack bytes written below sp: {depth}"
    -- sp only 8-byte aligned (not the LP64D ABI; Go's riscv64 stack): still no misaligned access
    for (k, exts) in kernels do
      for count in [0, 1, 2, 3] do
        for sp0 in [8, 24, 40, 56] do
          let (res, _, _) := check1 k exts count (count + 3) { sp0 := sp0 } true
          if let some msg := res then
            IO.println msg; fails := fails + 1
    IO.println "sp = 8 mod 16: 48 runs done"
    -- output inside the input buffer: in place (out = in) and lagging (out < in), any alignment
    for (k, exts) in kernels do
      for count in [1, 2, 3, 5, 8] do
        for (io, oo) in [(0, 0), (64, 0), (64, 32), (5, 5), (67, 1), (33, 2), (100, 64), (31, 30)] do
          let (res, _, _) := check1 k exts count (count + io) { inOff := io, outOff := oo, sp0 := 16, alias := true } false
          if let some msg := res then
            IO.println msg; fails := fails + 1
    IO.println "aliased output (out <= in): 120 runs done"
    -- unaligned buffers: correctness and misaligned accesses
    for (k, exts) in kernels do
      let mut lines : List String := []
      for io in [0:8] do
        for oo in [0:8] do
          let (res, st, _) := check1 k exts 2 (io * 8 + oo) { inOff := io, outOff := oo, sp0 := 16 } false
          if let some msg := res then
            IO.println msg; fails := fails + 1
          if io < 4 && oo < 2 || oo < 4 && io < 2 then
            lines := lines ++ [s!"in+{io} out+{oo}: misaligned in/out/stack/other = {st.mis} of {st.acc}"]
      IO.println s!"{k}, count 2, unaligned buffers (64 layouts):"
      for l in lines do IO.println s!"  {l}"
    -- dispatcher
    for probe in [none, some 0, some 0x10, some 0x2000, some 0x100, some 0x2100, some 0x2110, some 0x2010,
                  some 0x3fff8] do
      unless (← checkDisp probe 3) do fails := fails + 1
    IO.println s!"failures: {fails}"
    return (if fails = 0 then 0 else 1)
