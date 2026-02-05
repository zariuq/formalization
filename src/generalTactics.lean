import Lean

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

/- Method for reading a string until the nth empty line 
   Also removes the first line
-/
def NEWLINE : Char := Char.ofNat 10

def untilNthEmptyLine_core : Option Nat → List String → String
  | _, [] => ""
  | some num, "" :: rest => if num = 0 then "" else
      "\n" ++ untilNthEmptyLine_core (some (num - 1)) rest
  | none, line :: rest =>
      line ++ "\n" ++ untilNthEmptyLine_core none rest
  | some num, line :: rest => if num = 0 then "" else
      line ++ "\n" ++ untilNthEmptyLine_core (some num) rest

def untilNthEmptyLine (onum : Option Nat) (s : String) : String :=
  untilNthEmptyLine_core onum <| (s.splitOn "\n").drop 1

/- Tactics for print-debugging
    `trace_goal_core (some n) iden` will print a line with `iden`, 
      followed by the first `n` goals
    `trace_goal_core none iden` will print a line with `iden`, 
      followed by all goals
-/
def trace_goal_core (o : Option Nat) (iden : String) : TacticM Unit := do
  logInfo m!"\n-- {iden} --"
  let goals ← getGoals
  let goals :=
    match o with
    | some n => goals.take n
    | none => goals
  withMainContext do
    for g in goals do
      let t ← g.getType
      let t ← instantiateMVars t
      logInfo m!"{t}"

def trace_goal (iden : String) : TacticM Unit :=
  trace_goal_core (some 1) iden
def trace_goals (num : Nat) (iden : String) : TacticM Unit :=
  trace_goal_core (some num) iden
def trace_all_goals (iden : String) : TacticM Unit :=
  trace_goal_core none iden

/- Counts how many goals there currently are -/
def count_goals : TacticM Nat := do
  return (← getGoals).length

/- Takes a list of names, introduces new variables by those names,
   and then returns a list of the names and corresponding expr's
   paired together. 
   REQUIRES: goal is a Pi type of at least n args, where n is
    the length of the input list   
-/
def repeat_assume_pair : List Name → TacticM (List (Name × Expr))
| [] => pure []
| nm :: nms => do
    let mvarId ← getMainGoal
    let (fvarId, newGoal) ← mvarId.intro nm
    replaceMainGoal [newGoal]
    let rest ← repeat_assume_pair nms
    return (nm, Expr.fvar fvarId) :: rest


/- Takes a list of names, introduces new variables by those names,
   and then returns unit. 
   REQUIRES: goal is a Pi type of at least n args, where n is
    the length of the input list   
-/
def repeat_assume (names : List Name) : TacticM Unit := do
  let _ ← repeat_assume_pair names
  pure ()

/- Takes a list N=[nm_0,nm_1,...,nm_{|N|-1}] of names, and
   1. does |N| introductions to get e_0,e_1,...,e_{|N|-1},
   2. does tactic T
   3. does `induction e_i with nm_i` for each i,
   4. returns unit.

   REQUIRES: goal is a Pi type of at least |N| args, each of which can
   have induction applied. Also T must work after the introductions
   Will only attach nm_i to the first induction arg of e_i.

   EXAMPLE: If goal is of the form
      ⊢ ∀ (x_0,...,x_n : X) (y : Y), Q
   then doing 
      repeat_assume_then_induct `[ assume y ] [`φ0,...,`φn]
    will have the same effect as
      assume x0 ... xn,
      assume y,
      induction x0 with φ0,
      ...
      induction xn with φn,
    So the assumption of y is outside the induction. If it's not
    important to assume y before inducting, then the repeat_assume_induct
    tactic can be used, followed by assume y.
-/
def repeat_assume_then_induct (T : TacticM Unit) (N : List Name) : TacticM Unit := do
  let _ ← repeat_assume_pair N
  T

def repeat_assume_induct (N : List Name) : TacticM Unit :=
  repeat_assume_then_induct (pure ()) N

/-
  Assumes premises with each name from N, and then "applies" the
  operation named F to each premise.
-/
def repeat_assume_replace (fName : Name) (N : List Name) : TacticM Unit := do
  for nm in N do
    withMainContext do
      let mvarId ← getMainGoal
      let localDecl ← getLocalDeclFromUserName nm
      let arg := localDecl.toExpr
      let newVal ← Meta.mkAppM fName #[arg]
      let (_, newGoal) ← mvarId.note nm newVal
      let newGoal ← newGoal.clear localDecl.fvarId
      replaceMainGoal [newGoal]


/-
  gen_nameList takes a "base name" nm and will generate n
  unique names: nm0, nm1, ...
  More user-readable way of generating fresh names
-/
def varFormat (baseName : Name) (i : Nat) : Name :=
  Name.mkSimple (toString baseName ++ toString i)
def gen_nameList (baseName : Name) (n : Nat) : List Name :=
  (List.range n).map (varFormat baseName)
