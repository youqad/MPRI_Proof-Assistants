(* Universe hierarchy *)

Check Type.

Set Printing Universes.

Check Type.

Universes i j k.
Constraint i < j.

Check Type@{i} : Type@{j}.

Fail Check Type@{j} : Type@{i}.
Fail Check Type@{j} : Type@{j}.

Check Type@{i} -> Type@{i}.

(** Type eliminations *)

Section TypeElim.
  Variable b : bool.

  Check (match b return Type with
         | true => nat
         | false => bool
         end).

  Check (match b return Prop with
         | true => True
         | false => False
         end).

  Check (match b return (nat : Set) with
         | true => 0
         | false => 1
         end).

End TypeElim.

(** Prop eliminations *)
Section PropElim.
  Variable P : Prop.
  Variable b : or P P.

  Fail Check (match b return Type with
              | or_introl _ => nat
              | or_intror _ => bool
              end).

  Fail Check (match b return Prop with
         | or_introl _ => P
         | or_intror _ => P
         end).

  Fail Check (match b return (nat : Set) with
         | or_introl _ => 0
         | or_intror _ => 1
         end).

  Check (match b return P with
         | or_introl p => p
         | or_intror p => p
         end).

End PropElim.

Section PropSingleton.
  Variable b : (True : Prop).

  Check (match b return Type with
              | I => nat
              end).

  Check (match b return Prop with
         | I => False
         end).

  Check (match b return (nat : Set) with
         | I => 0
         end).

  Check (match b return True with
         | I => I
         end).

End PropSingleton.

Section PropSingletonEq.
  Variables (A : Type) (x y : A).
  Variable b : (@eq A x y : Prop).

  Check (match b return Type with
              | eq_refl => nat
              end).

  Variable (P : A -> Type).

  Check (match b in eq _ y return P y -> P x with
         | eq_refl => fun x : P x => x
         end).

End PropSingletonEq.
