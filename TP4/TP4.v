Print True.
(* Inductive ⊤ : Prop ≜  I : ⊤ *)
Print unit.
(* Inductive unit : Set ≜  tt : unit *)

About unit_rect.
(*  Dependent Scheme
    unit_rect : ∀ P : unit ⟶ Type, P tt ⟶ ∀ u : unit, P u *)
About True_rect.
(*  Non-dependent Scheme
    True_rect : ∀ P : Type, P ⟶ ⊤ ⟶ P *)


Definition True_rect_dep (P: True -> Type) : P I -> forall u : True, P u := 
fun (pi : P I) (u: True) => 
    match u with
    | I => pi
    end.

Definition True_rect_dep2 : forall (P: True -> Type), P I -> forall u : True, P u.
Proof.
    intros; now destruct u.
Qed.


Lemma easy_implic (P : nat -> bool) :
{n : nat | P n = true} -> exists n, P n = true.
Proof.
    intro; destruct H; now exists x.
Qed.


Lemma hard_implic (P : nat -> bool) :
(exists n, P n = true) -> {n : nat | P n = true}.
Proof.
    intro.
    Fail destruct H.
Abort.
