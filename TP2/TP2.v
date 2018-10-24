Inductive bool : Type := true : bool | false : bool.

Definition negb (b:bool) := match b with
    | true => false
    | false => true
    end.

Eval compute in (negb true).

Definition andb (b: bool) (b': bool) := match (b, b') with
    | (true, true) => true
    |  _ => false
    end.

Eval compute in (andb true false).

Eval compute in (fun x => negb (andb false x)).
(*    = λ _ : bool ⇒ true
     : bool ⟶ bool 

Pattern-matching directly branches into the 
second branch without looking at x. *)


Eval compute in (fun x => negb (andb x false)).
(*   = λ x : bool ⇒
       match match x with
             | true | _ ⇒ false
             end with
       | true ⇒ false
       | false ⇒ true
       end
     : bool ⟶ bool 

x is the first argument, and it is unknown: Coq doesn't 
know which branch of the negb pattern-matching it is 
supposed to pick.
*)

Lemma andb_comm : forall b_1 b_2, andb b_1 b_2 = andb b_2 b_1. 
Proof.
    intros; destruct b_1; destruct b_2; now simpl.
Qed.

Print and.
(* Inductive and (A B : Prop) : Prop ≜  conj : A ⟶ B ⟶ A ∧ B *)

Print or.
(* Inductive or (A B : Prop) : Prop ≜
    or_introl : A ⟶ A ∨ B | or_intror : B ⟶ A ∨ B *)

Print ex.
(* Inductive ex (A : Type) (P : A ⟶ Prop) : Prop ≜
    ex_intro : ∀ x : A, P x ⟶ ∃ y, P y *)

Set Implicit Arguments.

Inductive list {A: Type} := 
    | nil 
    | cons (_: A) (_: list).

(* 
    Inductive prod (A B : Type) : Type := pair : A -> B -> prod A B. 
    Inductive unit : Type := tt : unit.
    Inductive nat : Type := O : nat | S : nat -> nat.     
*)

Fixpoint prodn (A: Type) (n: nat) : Type := match n with
    | 0 => unit
    | S n => prod A (prodn A n)
end.

Eval compute in prodn nat 3.

Fixpoint length {A: Type} (l: @list A) : nat := match l with
    | nil => 0
    | cons _ l' => S (length l')
end.

Fixpoint embed {A: Type} (l: list) : prodn A (length l) := match l with
    | nil => tt
    | cons a l' => (a, embed l')
end.

Inductive nat := O | S (_ :nat).

Fixpoint add (n m: nat) : nat := match m with
    | O => n
    | S m' => S (add n m')
end.

Fixpoint mul (n m: nat) : nat := match m with
    | O => O
    | S m' => add n (mul n m')
end.

Definition D (n: nat) : Prop := match n with
    | O => True
    | S m => False
end.

Definition nat_imp := forall Q:Prop, Q -> (Q -> Q) -> Q.

Definition zero_imp : nat_imp := fun Q x f => x.

Definition succ_imp (n: nat_imp) : nat_imp  :=  fun Q x f => f (n Q x f).

Definition add_imp (n m: nat_imp) : nat_imp := fun Q x f => n Q (m Q x f) f.







