(************************)
(** * A decision procedure for intuitionistic propositional tautologies  **)
(************************)

(** *** Proof Assistants - Younesse Kaddar *)

Require Import Arith Notations List Lia Program Omega.
Open Scope list_scope.
Import ListNotations.
Set Implicit Arguments.

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

Inductive seq : Set :=
    vdash : list form -> form -> seq.

Infix "⊢" := vdash (at level 65).
Notation "∅ ⊢ A" := (nil ⊢ A) (at level 10).


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

Definition apply_elim_rules (C : form) (Γ : form * list form) : list seq := 
    match Γ with 
        |  (* ⇒-E *)    (A → B, Δ)    => [Δ ++ [B] ⊢ C; Δ ⊢ A]
        |  (* ∧-E *)    (A ∧ B, Δ)    => [Δ ++ [A; B] ⊢ C]
        |  (* ∨-E *)    (A ∨ B, Δ)    => [Δ ++ [A] ⊢ C; Δ ++ [B] ⊢ C]
        | _                          => []
    end.

Definition step (s : seq) : subgoals := let '(Δ ⊢ C) := s in
    let intro_rules := 
        match C with 
            |  (* ⇒-I *)        A → B           => [[Δ ++ [A] ⊢ B]]
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

Fixpoint size_form (φ : form) : nat := 
    match φ with
        | form_var _ | ⊤ | ⊥ => 0
        | A ∧ B | A ∨ B | A → B => S (size_form A + size_form B)
    end.

Tactic Notation "int" tactic(t) := t; intuition.
Tactic Notation "aut" tactic(t) := t; auto.
Tactic Notation "sint" tactic(t) := t; simpl; intuition.
Tactic Notation "saut" tactic(t) := t; simpl; auto.


Open Scope nat_scope.

(* Print fold_left. *)

Definition sum (l : list nat) := fold_right Nat.add 0 l.

Fact sum_fst : forall l a, sum (a :: l) = a + sum l.
Proof.
    int induction l.
Qed.

Fact sum_app : forall l l', sum (l ++ l') = sum l + sum l'.
Proof.
    int induction l. 
    rewrite <- app_comm_cons; repeat rewrite sum_fst.
    int rewrite IHl.
Qed.

Hint Resolve map_app sum_app sum_fst.


Definition size (s: seq) : nat := let '(Δ ⊢ A) := s in 
    sum (map size_form Δ) + size_form A.

Fact Forall_app: forall A (P:A -> Prop) l l', Forall P l /\ Forall P l' <-> Forall P (l ++ l').
Proof.
    split.
    -   intros; induction l; int destruct H.
        rewrite <- app_comm_cons; constructor; int inversion H.
    -   intro; split; rewrite Forall_forall in * |- *; intros; int apply H.
Qed.

Definition prepend {A: Type} (a: A) '(b, l) : A * list A := (b, a :: l).

Lemma pick_hyp_prepend : forall φ l l', pick_hyp_aux (φ::l) l' = map (prepend φ) (pick_hyp_aux l l').
Proof.
    intros; revert φ l; sint induction l'.
    now rewrite IHl'.
Qed.

Ltac constructors_Forall := repeat (repeat apply Forall_nil; repeat apply Forall_cons; simpl).
Ltac sum_map_app := repeat (rewrite map_app + rewrite sum_app).
Ltac Forall_sum_map := constructors_Forall; saut sum_map_app.

Lemma Forall_concat_prepend : forall l C n φ, 
    Forall (fun s' : seq => size s' < n) (concat (map (apply_elim_rules C) l))
    -> 
    Forall (fun s' : seq => size s' < size_form φ + n)
        (concat (map (fun Γ => (apply_elim_rules C) (prepend φ Γ)) l)).
Proof.
    intros; revert φ; sint induction l.  
    rewrite <- Forall_app; split.
    -   destruct a as (ψ, Δ); simpl.
        simpl in H; apply <- Forall_app in H; destruct H as [? _].
        destruct ψ; Forall_sum_map; 
        repeat match goal with 
            | H : Forall _ _  |- _ => inversion H; clear H
        end; unfold size in * |-.
        all: repeat (rewrite map_app in * |- + rewrite sum_app in * |-). 
        all: aut simpl in * |-.
    -   apply IHl; simpl in * |-; apply <- Forall_app in H; now destruct H as [_ ?].
Qed.


Theorem size_decreasing : forall s, Forall (fun s' => size s' < size s) (concat (step s)).
Proof.
    destruct s; induction l; unfold step;
    rewrite concat_app; repeat (apply Forall_app; saut split).
    1-3: destruct f; try destruct a; Forall_sum_map.
    simpl in IHl. rewrite pick_hyp_prepend. rewrite map_map.
    rewrite concat_app in IHl; apply <- Forall_app in IHl; destruct IHl as [_ ?].
    rewrite <- plus_assoc; now apply Forall_concat_prepend.
Qed.

