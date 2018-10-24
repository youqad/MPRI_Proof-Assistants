Require Import Omega.

Inductive even : nat -> Prop := 
    | even0 : even 0
    | evenS n : even n -> even (S (S n)).

(* Produced by Coq: even_ind *)

Lemma even_is_double : forall n, even n -> exists m, n = m+m.
Proof.
    induction 1.
    now exists 0.
    destruct IHeven. exists (S x). omega.
Qed.

Lemma half : forall n, even n -> {m | n=m+m}.
Proof.
    fix 1.
    intro.
    destruct n; intro.
    now exists 0.
    destruct n.
    exfalso. inversion H.
    pose proof (half n).
    destruct H.