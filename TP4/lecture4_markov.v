Require Import Arith.

Axiom todo : forall {A}, A.

(* Tactics needed:
   [intros], [destruct], [induction], [exists], [apply],
   [rewrite], [assumption], [contradiction] *)

(* The proof of easy_implication consists in breaking the pair of data
   stored in hypothesis {n : nat | P n = true} and to
   instantaeoulsy rebuild a new pair, with the same components,
   in a different 'container', which lands in sort Prop. *)
Lemma easy_implication (P : nat -> bool) :
{n : nat | P n = true} -> exists n, P n = true.
Proof.
  intros [n Pn]. exists n. assumption.
Qed.

(* However the same operation does not work in the opposite
  direction, because of restricted elimination rules. *)
Lemma harder_implication (P : nat -> bool) :
  (exists n, P n = true) -> {n : nat | P n = true}.
Proof.
  intros H. Fail destruct H.
Abort.

Section Markov.

(* This is what we call a boolean predicate on natural numbers. A
    witness for P is an (x : nat) for which P x = true. *)

Variable (P : nat -> bool).

(* We should not formalize the existence of a witness for P as:
   Variable (x : nat).
   Hypothesis Px : P x = true.

   This is indeed a stronger statement than the exP hypothesis
   that we use below, since it readily breaks the pair which seemed
   difficult to break in script harder above... *)

Hypothesis exP : exists n, P n = true.

(* The purpose of this exercise is to show that it is still possible
   to forge a proof term which takes benefit from exP in order to
   build an instance of the Type-sorted pair, without hitting
   the restricted elimination barrier.*)

(* The computational content of a statement asserting the
   existence of an (x : nat) such that P x = true is a search
   algorithm which terminates with outputting a natural number
   for which P x = true.*)

(* The harder statement states that from a 'non computational'
   proof (in sort Prop), possibly using a computational axiom,
   we can deduce a computational proof  (a search algorithm) that
   eventually terminates and produces a concrete and correct
   natural number. This algorithm will be the naive search
   trying natural numbers one after the other starting from 0
   and exP the justification that it terminates. We need
   to turn exP into a data we can compute on by recursion. *)

(* The structure of a proof term of the proposition
   (acc_nat i) measures the distance from i to a witness for P.
   By distance we mean the distance between i and a greater or equal
   number at which P holds. *)

(* Note that this a simplified version of the instance of the
   Acc accessiblity predicate that could also be used for
   the purpose of this proof. *)

(* Note that in the AccNatS constructor, we see how
   values of the parameters can be modified in the arguments of
   constructors, while being imposed in their conclusion:
   we use an (acc_nat (S i)) to build a term in (acc_nat i). *)

Inductive acc_nat (i : nat) : Prop :=
  |AccNat0 : P i = true -> acc_nat i
  |AccNatS : acc_nat (S i) -> acc_nat i.

Show acc_nat_rect.

(* The following lemma describes formally the informal intuition
   described above.  *)
(* uses plus_Snm_nSm *)
Lemma acc_nat_plus :  forall x n : nat, P (x + n) = true -> acc_nat n.
Proof.
  intro.
  induction x. simpl; try now constructor.
  intros. rewrite (plus_Snm_nSm x n) in H.
  apply AccNatS. now apply IHx.
Qed.

(* In particular we can use exP to show that acc_nat holds at
   0, since we carefully put the acc_nat predicate in Prop. *)
(* uses plus_0_r *)
Lemma acc_nat0 : acc_nat 0.
Proof.
  inversion exP.
  apply acc_nat_plus with (x:= x).
  now rewrite plus_0_r.
Qed.


(* Now the main step of the proof : if acc_nat holds for an (n : nat),
   we can compute a value for which P holds. We compute
   by induction on the proof of (acc_nat n). *)
Lemma find_ex : forall n : nat, acc_nat n -> {m | P m = true}.
Proof.
(* fix 2. *)
Show Proof.
(* we could be tempted to cheat using the seamingly correct
   correct:

   exact find_ex.
   Qed.

   but Coq complains because the proof term we just built is
   a non-terminating recursive function, of the form:
      fix f n := f n
   which cannot be accepted without risking consistency troubles... *)
   intros.
   induction H with acc_nat_ind.
Qed.

(* We are done: *)
Theorem Markov : {m | P m = true}.
Proof.
  apply todo.
Qed.

End Markov.

(* Here is the complete statement we prouved, as available outside
   of the section. *)
Check Markov.
