(************************)
(** * A decision procedure for intuitionistic propositional tautologies  **)
(************************)

(** *** Proof Assistants - Younesse Kaddar *)

Require Import List Arith Lia Notations.
Open Scope list_scope.
Import ListNotations.
Require Import Program.


Hint Extern 8 (_ = _ :> nat) => lia.
Hint Extern 8 (_ <= _) => lia.
Hint Extern 8 (_ < _) => lia.
Hint Extern 8 (_ <> _ :> nat) => lia.
Hint Extern 8 (~ (_ <= _)) => lia.
Hint Extern 8 (~ (_ < _)) => lia.
Hint Extern 12 => exfalso; lia.

(** * 2.2 Building the tactic **)
(***********************)

(** ** 1. Write a tactic [tauto1] that searches for a derivation (where propositions are expressed using Coq's standard connectives). 
    The tactic shall leave a trace of all rules applied (axiom rules may be omitted). 
    It is also recommended to print the search depth in order to figure out how the tactic backtracks. **)
(***********************)

(** Here is [tauto1]: *)

Lemma tauto_test :
  forall A B C : Prop, (A -> B) -> C.
Proof.
    do 4 intro.
    cut A; 
    [ intro HA; apply H in HA; clear H | clear H ].
Admitted.

Lemma tauto_test2 :
  forall A B C : Prop, A \/ B -> C.
Proof.
    intros.
    destruct H as [H1 | H2].
Admitted.


Ltac tauto1_aux n := 
    match goal with
        | _ : ?A    |- ?A => idtac "[Depth: " n "] Axiom on " A; assumption
        | _ : False |- ?A => idtac "[Depth: " n "] ⊥-E on " A; contradiction
        |   |- True => idtac "[Depth: " n "] ⊤-I on ⊤"; constructor
        |   |- ?A -> ?B => idtac "[Depth: " n "] ⇒-I on " A " ⇒ " B; intro; tauto1_aux (S n)
        | H : ?A -> ?B  |- ?C => let HA := fresh in
            idtac "[Depth: " n "] ⇒-E on " C;
            cut A; 
            [ intro HA; apply H in HA | ];
            clear H; tauto1_aux (S n)
        |   |- ?A /\ ?B => idtac "[Depth: " n "] ∧-I on " A " ∧ " B; split; [tauto1_aux (S n) | tauto1_aux (S n)]
        | H : ?A /\ ?B  |- _ => idtac "[Depth: " n "] ∧-E on " A " ∧ " B; destruct H as [H1 H2]; tauto1_aux (S n)
        |   |- ?A \/ ?B => idtac "[Depth: " n "] ∨-I₁ on " A " ∨ " B; left; tauto1_aux (S n)
        |   |- ?A \/ ?B => idtac "[Depth: " n "] ∨-I₂ on " A " ∨ " B; right; tauto1_aux (S n)
        | H : ?A \/ ?B  |- _ => idtac "[Depth: " n "] ∨-E on " A " ∨ " B; destruct H; tauto1_aux (S n)
        | _ => idtac "[Depth: " n "] Backtrack"; fail
    end.

Ltac tauto1 := tauto1_aux 0.


Section Examples1.
    Variables A B C D : Prop.

    Lemma tauto_ex2 : (A -> B) -> True.
    Proof.
        tauto1.
    Qed.

End Examples1.



Ltac tauto2_aux n := 
    match goal with
        | _ : ?A    |- ?A => idtac "[Depth: " n "] Axiom on " A; assumption
        | _ : False |- ?A => idtac "[Depth: " n "] ⊥-E on " A; contradiction
        |   |- True => idtac "[Depth: " n "] ⊤-I on ⊤"; constructor
        |   |- ?A -> ?B => idtac "[Depth: " n "] ⇒-I on " A " ⇒ " B; intro; tauto2_aux (S n); fail 1
        | H : ?A -> ?B  |- ?C => let HA := fresh in
            idtac "[Depth: " n "] ⇒-E on " C;
            cut A; 
            [ intro HA; apply H in HA | ];
            clear H; tauto2_aux (S n)
        |   |- ?A /\ ?B => idtac "[Depth: " n "] ∧-I on " A " ∧ " B; split; (tauto2_aux (S n) + fail 1)
        | H : ?A /\ ?B  |- _ => idtac "[Depth: " n "] ∧-E on " A " ∧ " B; destruct H as [H1 H2]; tauto2_aux (S n); fail 1
        |   |- ?A \/ ?B => idtac "[Depth: " n "] ∨-I₁ on " A " ∨ " B; left; tauto2_aux (S n)
        |   |- ?A \/ ?B => idtac "[Depth: " n "] ∨-I₂ on " A " ∨ " B; right; tauto2_aux (S n)
        | H : ?A \/ ?B  |- _ => idtac "[Depth: " n "] ∨-E on " A " ∨ " B; destruct H; (tauto2_aux (S n) + fail 1)
        | _ => idtac "[Depth: " n "] Backtrack"; fail
end.

Ltac tauto2 := tauto2_aux 0.


Section Examples2.
    Variables A B C D : Prop.

    Lemma tauto_ex3 : ((((A /\ A) /\ A) /\ A) /\ A) \/ True.
    Proof.
        tauto2.
    Qed.
End Examples2.

(* Type of variables *)
Variable Var : Set.
Parameter Var_eq_dec: forall (x y: Var), {x = y}+{x <> y}. (* Decidable equality *)

Inductive form : Set :=
  | form_var : Var -> form
  | form_true : form
  | form_false : form
  | form_and : form -> form -> form
  | form_or : form -> form -> form
  | form_implies : form -> form -> form.

Hint Constructors form.
Notation "A ∧ B" := (form_and A B) (at level 30, right associativity).
Notation "A ∨ B" := (form_or A B) (at level 35, right associativity).
Notation "A → B" := (form_implies A B) (at level 49, right associativity, B at level 50).
Notation "⊤" := (form_true) (at level 5).
Notation "⊥" := (form_false) (at level 5).

Definition form_of_var := fun (x: Var) => form_var x.
Coercion form_of_var : Var >-> form.


Definition seq := list form * form.

Notation "Δ ⊢ A" := (Δ, A) (at level 65).
Notation "∅ ⊢ A" := (nil ⊢ A) (at level 10).

Check (nil ⊢ ⊤).


Fact form_eq_dec : forall A B : form, {A = B} + {A <> B}.
Proof with apply Var_eq_dec.
    decide equality...
Qed.

Definition form_in_dec : forall (A: form) (Δ : list form), {In A Δ} + {~ In A Δ}.
    apply (in_dec form_eq_dec).
Defined.

Definition is_leaf (s : seq) : bool := 
    match s with
        | _ ⊢ ⊤ => true
        | Δ ⊢ A =>  if form_in_dec ⊥ Δ then true
                    else if form_in_dec A Δ then true
                    else false
    end.

Definition subgoals := list (list seq).

Fixpoint pick_hyp_aux (l l': list form) : list (form * list form) := 
    match l' with 
        | nil => nil
        | h :: t => (h, l ++ t) :: (pick_hyp_aux (l ++ [ h ]) t)
    end.

Definition pick_hyp (s: seq) : list (form * list form) := 
    match s with Δ ⊢ _ => pick_hyp_aux nil Δ end.

Variables x y z t : Var.

Eval compute in (pick_hyp ([ x ∧ y ; y ∨ ⊤ ; x → ⊥ ] ⊢ ⊤)).

Definition apply_elim_rules (C : form) (hyps : form * list form) := 
    match hyps with 
        |  (* ⇒-E *)    A → B ⊢ Δ    => [B :: Δ ⊢ C; Δ ⊢ A]
        |  (* ∧-E *)    A ∧ B ⊢ Δ    => [A :: B :: Δ ⊢ C]
        |  (* ∨-E *)    A ∨ B ⊢ Δ    => [A :: Δ ⊢ C; B :: Δ ⊢ C]
        | _                          => []
    end.

Definition step (s : seq) : subgoals := let '(Δ ⊢ C) := s in
    let intro_rules := 
        match C with 
            |  (* ⇒-I *)        A → B           => [[A :: Δ ⊢ B]]
            |  (* ∧-I *)        A ∧ B           => [[Δ ⊢ A; Δ ⊢ B]]
            |  (* ∨-I₁ ∨-I₂ *)  A ∨ B           => [[Δ ⊢ A]; [Δ ⊢ B]]
            | _                                 => []
        end 
    in intro_rules ++ map (apply_elim_rules C) (pick_hyp s).

Eval compute in (step ([x ∨ y] ⊢ z → t)).



Fixpoint tauto (max_depth: nat) (s: seq) : bool :=
    match max_depth with
        | 0     => false
        | S n   => if is_leaf s 
                    then true 
                    else existsb (forallb (tauto n)) (step s)
    end.