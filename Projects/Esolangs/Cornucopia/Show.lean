import Projects.Esolangs.Cornucopia.Defs

namespace Esolangs.Cornucopia

def Prog.HasModel (prog : Prog) : Prop :=
  ∃ fs, prog.Compatible fs

def Prog.HasUniqueModel (prog : Prog) : Prop :=
  ∃! fs, prog.Compatible fs

class ProgInfo (prog : Prog) : Type where
  name : String
  defNames : List String
  has_model : Bool
  has_unique_model : Bool
  h_defNames : prog.defs.keys.Perm # builtins.map Builtin.name ++ defNames
  h_wf' : prog.WF'
  h_has_model : prog.HasModel ↔ has_model
  h_has_unique_model : prog.HasUniqueModel ↔ has_unique_model

def Expr.show (e : Expr) (argNames : Array String) : String :=
  match e with
  | .arg i => argNames[i]!
  | .call t args =>
    t ++ if args.length = 0 then "" else
    "(" ++ ", ".intercalate (args.map (·.show argNames)) ++ ")"

def Def.show (d : Def) (name : String) : String :=
  let argNamesList := mkList d.arity λ i => String.ofList [.ofNat # 97 + i]
  let argNames := .mk argNamesList
  let argsStr := if d.arity = 0 then "" else
    "(" ++ ", ".intercalate argNamesList ++ ")"
  name ++ argsStr ++ " := " ++ d.expr.show argNames

def ProgInfo.showWF {prog : Prog} [info : ProgInfo prog] : String :=
  if !info.has_model then "no model"
  else if !info.has_unique_model then "multiple models"
  else "unique model"

def Prog.show (prog : Prog) [info : ProgInfo prog] : String :=
  let defs := "\n".intercalate # info.defNames.map # λ name =>
    "".intercalate (List.replicate 2 " ") ++ (prog.def name).show name
  "".intercalate ["program ", info.name, " -- ", info.showWF, "\n", defs]