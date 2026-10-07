import QICLean.Entropy.ConditionalMovement.UnitaryCovariance
open Lean Elab Command Meta

partial def collect (env : Environment) (n : Name) (acc : NameSet) : NameSet := Id.run do
  if acc.contains n then return acc
  let mut acc := acc.insert n
  match env.find? n with
  | none => return acc
  | some ci =>
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    for c in cs do
      if (`ConditionalMovement).isPrefixOf c then
        acc := collect env c acc
    return acc

elab "#closure" : command => do
  let env ← getEnv
  let s := collect env `ConditionalMovement.LocalMove.one_copy_move_cfc {}
  let mut all : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if (`ConditionalMovement).isPrefixOf n && !n.isInternal then all := all.push n
  let used := s.toList.map toString
  IO.FS.writeFile "closure_used.txt" (String.intercalate "\n" used)
  IO.FS.writeFile "closure_all.txt" (String.intercalate "\n" (all.toList.map toString))
#closure
