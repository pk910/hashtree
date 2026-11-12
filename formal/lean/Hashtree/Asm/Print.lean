import Hashtree.Asm.Core

/-!
# Lean-source printers for symbolic states (proof generator; not part of any proof)
-/

namespace Hashtree.Asm

def Lin.toLean (l : Lin) : String := s!"(⟨{l.k}, {l.c}⟩ : Lin)"

def Key.toLean : Key → String
  | .n i => s!"(.n {i})"
  | .m r off => s!"(.m {r} {off.toLean})"

partial def E.toLean : E → String
  | .var k => s!"(.var {k.toLean})"
  | .const v => s!"(.const {v.toNat})"
  | .add a b => s!"(.add {a.toLean} {b.toLean})"
  | .xor a b => s!"(.xor {a.toLean} {b.toLean})"
  | .and a b => s!"(.and {a.toLean} {b.toLean})"
  | .or a b => s!"(.or {a.toLean} {b.toLean})"
  | .not a => s!"(.not {a.toLean})"
  | .shl a n => s!"(.shl {a.toLean} {n})"
  | .shr a n => s!"(.shr {a.toLean} {n})"
  | .sar a n => s!"(.sar {a.toLean} {n})"
  | .ror a n => s!"(.ror {a.toLean} {n})"
  | .tern i a b c => s!"(.tern {i} {a.toLean} {b.toLean} {c.toLean})"

def Addr.toLean (a : Addr Lin) : String := s!"(⟨{a.region}, {a.off.toLean}⟩ : Addr Lin)"

def Val.toLean : Val E Lin → String
  | .num lo hi => s!"(.num {lo.toLean} {hi.toLean})"
  | .ptr a => s!"(.ptr {a.toLean})"

def Cell.toLean : Cell E Lin → String
  | .dat x k => s!"(.dat {x.toLean} {k})"
  | .pb a k => s!"(.pb {a.toLean} {k})"

partial def Cond.toLean : Cond Lin → String
  | .eq a b => s!"(.eq {a.toLean} {b.toLean})"
  | .lt a b => s!"(.lt {a.toLean} {b.toLean})"
  | .le a b => s!"(.le {a.toLean} {b.toLean})"
  | .not c => s!"(.not {c.toLean})"
  | .tt => ".tt"

def listLean {β : Type} (f : β → String) (l : List β) : String :=
  "[" ++ ", ".intercalate (l.map f) ++ "]"

def optLean {β : Type} (f : β → String) : Option β → String
  | none => "none"
  | some x => s!"(some {f x})"

def State.toLean (s : State E Lin) : String :=
  "({
    gpr := " ++ listLean Val.toLean s.gpr ++
  ",\n    vr := " ++ listLean (listLean E.toLean) s.vr ++
  ",\n    flags := " ++ optLean (fun (p : Lin × Lin) => s!"({p.1.toLean}, {p.2.toLean})") s.flags ++
  ",\n    mem := " ++ listLean (fun (p : Addr Lin × Cell E Lin) => s!"({p.1.toLean}, {p.2.toLean})") s.mem ++
  s!",\n    pc := {s.pc}, halted := {s.halted}, tail := {optLean (fun (t : String) => s!"\"{t}\"") s.tail}" ++
  s!", err := {optLean (fun (t : String) => s!"\"{t}\"") s.err}" ++
  ",\n    assume := " ++ listLean (fun (p : Cond Lin × Bool) => s!"({p.1.toLean}, {p.2})") s.assume ++
  "
  } : State E Lin)"

end Hashtree.Asm
