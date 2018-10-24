Require Import Arith Extraction.
(** A word on extraction *)

Example nth :
  forall A (l : list A), {n : nat | n < length l} -> A.
Proof.
  intros A l n.
  induction l as [|l' Hl'].
  destruct n as [n Hn].
  - simpl in Hn.
    apply False_rect.
    red in Hn.
    Unset Printing Notations. Print le.
    inversion Hn.
    Set Printing Notations.
  - destruct n as [n Hn].
    destruct n as [|n'].
    + (* 0 *)
      exact l'.
    + (* S n' *)
      apply IHHl'.
      exists n'.
      simpl in Hn.
      apply lt_S_n. apply Hn.
Defined.

Extraction nth.
