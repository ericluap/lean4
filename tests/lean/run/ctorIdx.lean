inductive Enum where | a1 | a2 | a3 | a4 | a5
deriving DecidableEq

/--
info: @[reducible] def Enum.toCtorIdx : Enum → Nat :=
fun x => Enum.casesOn x 0 1 2 3 4
-/
#guard_msgs in
#print Enum.toCtorIdx

inductive NonRec where | a1 (u : Unit) | a2 (i : Int) | a3 (n : Nat) (f : Fin n) | a4 (s : String) (b : Bool) | a5

/--
info: @[reducible] def NonRec.toCtorIdx : NonRec → Nat :=
fun x => NonRec.casesOn x (fun u => 0) (fun i => 1) (fun n f => 2) (fun s b => 3) 4
-/
#guard_msgs in
#print NonRec.toCtorIdx


inductive Nested (α : Type) where
  | a1 (x : α)
  | a2 (y : Nested α)
  | a3 (z : List (Nested α))

/--
info: @[reducible] def Nested.toCtorIdx : (α : Type) → Nested α → Nat :=
fun α x => x.casesOn (fun x => 0) (fun y => 1) fun z => 2
-/
#guard_msgs in
#print Nested.toCtorIdx

mutual
inductive A (m : Nat) : Nat → Type
  | self : A m n → A m (n+m)
  | other : B m n → A m (n+m)
  | empty : A m 0
inductive B (m : Nat) : Nat → Type
  | self : B m n → B m (n+m)
  | other : A m n → B m (n+m)
  | empty : B m 0
end

/--
info: @[reducible] def A.toCtorIdx : (m a : Nat) → A m a → Nat :=
fun m a x => x.casesOn (fun {n} a => 0) (fun {n} a => 1) 2
-/
#guard_msgs in
#print A.toCtorIdx
