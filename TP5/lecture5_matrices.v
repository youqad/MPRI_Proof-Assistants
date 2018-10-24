(* Second example : 2 x 2 Matrices *)
Set Implicit Arguments.

Require Import List.
Require Import Arith Ring Div2 Recdef.
Require Import Omega.
Require Import ZArith.

(** Definitional classes.   
   
   Bas Spitters, Eelis van der Weegen: 
   Type Classes for Mathematics in Type Theory.

   Idea: one class per symbol.
  *)

Class MonoidOp A := monop : A -> A -> A.
Class MonoidUnit A := monunit : A.

(** Definitional classes are transparent definitions, 
   not records. *)

Print MonoidUnit.
Print monunit.

Infix "*" := monop.
Notation eps := monunit.

(** Definitional classes for properties *)
Class Associative {A} (f : A -> A -> A) :=
  assoc : forall x y z, f x (f y z) = f (f x y) z.

Class LeftUnit {A} (f : A -> A -> A) u :=
  leftu : forall x, f u x = x.

Class RightUnit {A} (f : A -> A -> A) u :=
  rightu : forall x, f x u = x.

Class Monoid {A} (dot : MonoidOp A) 
      (unit : MonoidUnit A) := 
  { dot_assoc :> Associative monop;
    one_left :> LeftUnit monop monunit;
    one_right :> RightUnit monop monunit }.
  




























(** Redoing the power development 
   in that representation: *)

Generalizable Variables A.

Section Power.

  (** Generalization of the remaining arguments 
     (now refered to by overloaded notations) *)

  Context `{Monoid A}.
  Inspect 5.

  Fixpoint power (a : A) (n : nat) :=
    match n with
      | 0%nat => eps
      | S p => a * (power a p)
    end.

  Lemma power_of_unit : forall n, power eps n = eps.
  Proof. 
    induction n as [|p Hp];simpl;
      [|rewrite Hp;simpl;rewrite one_left];trivial. 
  Qed.

  Lemma power_square x n : power (x * x) n = 
                           power x (2 * n). 
  Proof. induction n; simpl. auto.
         rewrite <- plus_n_O. rewrite IHn. 
         assert (n + S n = 1 + 2 * n) by omega.
         rewrite H0. simpl. now rewrite <- dot_assoc.
  Qed.

  Function binary_power_mult (acc x : A) (n : nat)
    {measure (fun i=>i) n} : A (* acc * (power x n) *) :=
    match n with
      | 0%nat => acc
      | S n' => if Even.even_odd_dec n
        then binary_power_mult acc (x * x) (div2 n)
        else binary_power_mult
          (acc * x) (x * x) (div2 n)
    end.
  Proof.
    intros;apply lt_div2; auto with arith.
    intros;apply lt_div2; auto with arith.
  Defined.

  Definition binary_power (x : A) (n : nat) :=
    binary_power_mult eps x n.

  Lemma even_div2 n : 
    (Even.even n -> 2 * div2 n = n)%nat
    /\ (Even.odd n -> 2 * div2 n = n - 1)%nat.
  Proof.
    assert (oddH:=Div2.odd_double).
    assert(evenH:=Div2.even_double).
    split; intros.
    specialize (evenH _ H0). rewrite evenH at 2. unfold double; omega.
    specialize (oddH _ H0). rewrite oddH at 2. unfold double; omega.
  Qed.

  Lemma minus_n_0 n : (n - 0 = n)%nat.
  Proof. now rewrite minus_n_O. Qed.

  Lemma binary_spec x n : 
    power x n = binary_power x n.
  Proof.
    (* Left as an exercise. 
       Hint: tail recursive functions need a generalized induction hypothesis.
       Function provides a tactic [functional induction (f n)] for every [Function f]...
     *)
    admit.
  Qed.

End Power.






























(* Let's build the square 2 x 2 matrix
   monoid on any ring *)

Section matrices.
 Variables (A:Type)
           (zero one : A) 
           (plus mult minus : A -> A -> A)
           (sym : A -> A).
 Notation "0" := zero.  Notation "1" := one.
 Notation "x + y" := (plus x y).  
 Notation "x * y " := (mult x y).

 Variable rt : ring_theory zero one plus mult
   minus sym (@eq A).
 Add Ring Aring : rt.




















 Structure M2 : Type := {c00 : A;  c01 : A;
                         c10 : A;  c11 : A}.

 Definition Id2 : M2 := Build_M2 1 0 0 1.

 Definition M2_mult (m m':M2) : M2 :=
   Build_M2 (c00 m * c00 m' + c01 m * c10 m')
   (c00 m * c01 m' + c01 m * c11 m')
   (c10 m * c00 m' + c11 m * c10 m')
   (c10 m *  c01 m' +  c11 m * c11 m').

















  Lemma M2_eq_intros :
    forall m m':M2, c00 m = c00 m' ->
      c01 m = c01 m' ->
      c10 m = c10 m' ->
      c11 m = c11 m' -> m = m'.
  Proof.
    destruct m;destruct m';simpl.
    intros H H1 H2 H3;rewrite H ,H1, H2, H3;trivial.
  Qed.
  
  Definition M2_Monoid : Monoid  M2_mult Id2. 
  Proof. split;
    destruct x; try destruct y; try destruct z; 
      simpl; apply M2_eq_intros; simpl; ring.
  Defined.

End matrices.


























(** Matrices of integers: *)

Instance: MonoidOp (M2 Z) := M2_mult Z.add Z.mul.
Instance: MonoidUnit (M2 Z) := Id2 Z.zero Z.one.

Instance M2Z : Monoid _ _ := M2_Monoid Zth.

Print Instances Monoid.





















(** Tests *)
Open Scope Z_scope.
Unset Printing All.
Compute power (Build_M2 1 1 1 0) 40.

Fixpoint fib (n : nat) :=
  match n with
    | 0%nat | 1%nat => 1
    | S (S n as n') => fib n' + fib n
  end.

Definition fib_mat := Build_M2 1 1 1 0.

Definition fibonacci (n:nat) :=
  c00 (power fib_mat n).

(* Time Compute fibonacci 3000. *)

Definition not_faster_fibonacci (n:nat) :=
  c00 (binary_power fib_mat n).

(* Time Compute fib 33. *)
(* Time Compute fibonacci 3000. *)
(* Time Compute not_faster_fibonacci 3000. *)
(* Time Compute fibonacci 6000. *)

Fixpoint fibonaccis (n : nat) :=
  match n with
    | 0%nat => nil
    | S n => fibonaccis n ++ (fibonacci n :: nil)
  end.

Time Compute fibonaccis 10.

(* Exercise: prove it indeed builds the fibonacci sequence! *)

(* Useful to not unfold blindly as there is a nested case analysis *)
Definition fib0 : fib 0 = 1 := eq_refl.
Definition fib1 : fib 1 = 1 := eq_refl.
Definition fibSSn n : fib (S (S n)) = fib (S n) + fib n := eq_refl.
Hint Rewrite fib0 fib1 fibSSn : fib.

Lemma fibonacci_correct n : fibonacci n = fib n.
Proof.
  (* Left as an exercise. 
     - Define the matrix addition monoid and show that:
     [forall m m' : M2 Z, m * m' + m' = (m + 1) * m']
     - Show that [forall m m' : M2 Z, (c00 m + c00 m')%Z = c00 (m + m')].
     - The proof follows by well-founded induction on [n], using these two lemmas
     and the monoid laws on matrices.
 *)
  admit.
Qed.

Print Assumptions fibonacci_correct. (* Should be closed under the global context! *)