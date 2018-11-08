Axiom admitted : forall {A}, A.
Ltac todo := apply admitted. 
Definition ty := Type.
Inductive paths {A : Type} (a : A) : A -> ty :=
  | idpath : paths a a.

Infix "=" := paths.
Infix "=" := paths : type_scope.
Arguments idpath [A a]. 

Hint Resolve idpath.

(* Program a boolean test of equality eq_nat : nat -> nat -> bool *)
Fixpoint eq_nat (n m : nat) : bool := 
    match n, m with 
    | 0, 0 => true
    | S n', S m' => eq_nat n' m'
    | _, _ => false
end.

Lemma ap {A B} (f : A -> B) (x y : A) 
  : x = y -> f x = f y.
Proof.
  intro; destruct X; apply idpath.
Qed.
                                        

(* Prove the following lemma. There is a (small) trick. *)
Lemma eq_nat_eq (n m : nat) : 
  eq_nat n m = true -> n = m.
Proof.
  revert m; induction n; intros; destruct m.
  1-2: try reflexivity; simpl in *; inversion X.
  all: inversion X. apply ap; now apply IHn.
Qed.




Section HowToExplainLogicalLaws.

Variable T : Type.

(* A type which depends on T *)
Variable P : T -> Type.

(* f is an inhabitant of a dependent product type *)
Variable f : forall x : T, P x.

(* Dependent sums in Coq *)
(* In order to forge new inhabitants: *)
Check existT.

(* In order to project the pair on its first component: *)
Check projT1.

(* In order to project the pair on its second component: *)
Check projT2.

(* Let us have a try: *)

(* (sigT B) is denoted {x : A & B x} *)
Definition sig_witness {T} {P : T -> Type} (t : T)  (ht : P t) 
: {x : T & P x} := existT _ t ht.

About sig_witness.

(* The type of disjoint sums *)
Inductive disjoint_sum (A B : Type) : Type :=
  |in_left : A -> disjoint_sum A B
  |in_right : B -> disjoint_sum A B.

Inductive Empty : Set :=.

Inductive Unit : Set := tt : Unit.

Lemma Empty_elim (R : Type) : Empty -> R.
Proof. intros x. case x. Qed.

Definition Not (T : Type) := T -> Empty.

(* Now we can start our definitions *)
Definition prop (T : Type) := forall x y : T, x = y.

Definition set (T : Type) := forall x y : T, prop (x = y).

Lemma unit_prop : prop unit. 
Proof. unfold prop. destruct x, y. apply idpath. Defined.

Definition empty_prop : prop Empty.
Proof. unfold prop. destruct x, y. Defined.

End HowToExplainLogicalLaws.

Section RulesForEquality.

Variables A : Type.

(* We dispose of Martin-Lof's proposal for equality: *)

Check (@paths A).

Check (@idpath A).

Check (@paths_ind A).

(* Let us prove the 'vacuum cleaner power chord' principle *)
Definition Sing (a : A) := {x : A & a = x}.

Lemma sig_eq_fst {P : A -> Type} (a b : A) (p : P a) (q : P b) : existT _ a p = existT _ b q -> a = b.
  intro. apply (ap (@projT1 A P)) in X; now simpl in *|-.  
Qed.

Lemma sig_eq_prf {P : A -> Type} (a b : A) 
  (p : P a) (q : P b) (H : a = b) :
  paths_rect A a (fun b _ => P b) p b H = q -> 
existT _ a p = existT _ b q.
Proof.
  intros. Print paths_rect.
  destruct H. simpl in *.
  now destruct X.
Defined.
  
Lemma sig_eq_snd {P : A -> Type} (a b : A) 
  (p : P a) (q : P b) 
  (eq : existT _ a p = existT _ b q) :
         paths_rect A a (fun b _ => P b) p b 
                    (sig_eq_fst a b p q eq)
         = q.
Proof.
  pose proof eq as eq'.
  pose proof eq as eq''.
  apply (ap (@projT1 A P)) in eq'.
  apply (ap (@projT2 A P)) in eq''.

Defined.
(* Let us check that (a, eq_refl) is in *)
Variable a : A.
Check (existT _ a idpath : Sing a).

Definition sing_elt (x : A) (p : a = x) : 
  Sing a := existT _ x p.


Remark vacuum_cleaner_power_chord : 
  forall z : Sing a, z = sing_elt a idpath.
Proof.
  todo.
Qed.

(** The singleton has essentially one inhabitant (up-to equality) *)
Lemma Sing_prop : prop (Sing a).
Proof.
  todo.
Qed.

End RulesForEquality.

(** Now we're gonna show that booleans are discrete, i.e., they have decidable equality, hence they form a (h)set. *)

Section ConstructiveMathematics.

Definition decidable (T : Type) := disjoint_sum T (Not T).

Definition discrete (T : Type) := forall x y : T, decidable (x = y).

Proposition discrete_Empty : discrete Empty.
Proof.
  todo.
Qed.

Proposition discrete_Unit : discrete Unit.
Proof.
  todo.
Qed.

(* N2 is bool *)

(* Boolean negation *)

Definition eqb (b1 b2 : bool) : bool := 
  match b1, b2 with
    |true, true | false, false => true
    |_, _ => false
  end.

Lemma eq_eqbP (b1 b2 : bool) : b1 = b2 -> eqb b1 b2 = true.
Proof. case b1; case b2; simpl; trivial; intros H; inversion H. Qed.

Lemma eqb_eqP (b1 b2 : bool) : eqb b1 b2 = true ->  b1 = b2.
Proof. case b1; case b2; simpl; trivial; intros H; inversion H. Qed.

Proposition discrete_bool : discrete bool.
Proof.
  todo.
Qed.

Scheme paths_elim := Minimality for paths Sort Type.
About paths_elim.

(* What is the discriminate tactic doing? *)
Definition bool_discriminate (T : Type) : true = false -> T.
intros h.
apply Empty_elim.
pose (C := (fun (b : bool) => if b then Unit else Empty) : bool -> Type).
About paths_elim.
exact (paths_elim _ true C tt false h).
Qed.
(* The previous proof can be adapted to any equality between two terms
   presenting distinct head constructors. *)

(** Show that bool is _not_ propositional: it contains distinct objects up-to equality *)
Lemma not_prop_bool : Not (prop bool).
Proof.
  todo.
Qed.

(* All these proofs are in fact instances of the same pattern *)
Section DiscreteFromBoolEq.

Variable T : Type.

Variable eqT : T -> T -> bool.

Hypothesis eq_eqTP : forall t1 t2 : T, t1 = t2 -> eqT t1 t2 = true.

Hypothesis eqT_eqP : forall t1 t2 : T, eqT t1 t2 = true ->  t1 = t2.

Proposition discrete_bool_eq : discrete T.
Proof.
  todo.
Qed.

End DiscreteFromBoolEq.

Lemma eq_eq_natP (n1 n2 : nat) : n1 = n2 -> eq_nat n1 n2 = true.
Proof.
  todo.
Qed.

Lemma eq_nat_eqP (n1 n2 : nat) : eq_nat n1 n2 = true ->  n1 = n2.
Proof.
  todo.
Qed.

Proposition discrete_nat : discrete nat.
Proof.
  todo. (* using discrete_bool_eq *)
Qed.

End ConstructiveMathematics.


(** Some laws of groupoids *)
Section GroupoidProps.

Definition mapOnPaths {A B : Type} {x y : A} (f : A -> B) : 
  x = y -> f x = f y.
Proof.
  todo.
Defined.

(* These two terms are convertible *)
Remark mapOnPaths1 {A B : Type} (f : A -> B) (x : A) : 
  mapOnPaths f (@idpath A x) = idpath.
Proof.
  todo.
Qed.

Context {A : Type}.

Definition comp {a b : A} (p : a = b) {c : A} (q : b = c) : a = c.
Proof.
  todo.
Defined.

Remark comp1p {a b : A} (p : a = b) : comp idpath p = p.
Proof.
  todo. 
Defined.

Remark compp1 {a b : A} (p : a = b) : comp p idpath = p.
Proof.
  todo.
Defined.

Lemma comp_simpl {a b} (r : a = b) {c : A} (p q : b = c) :
  comp r p = comp r q ->  p = q.
Proof. 
  todo.
Defined.

End GroupoidProps.

(** Hedberg's theorem states that any discrete type (i.e. with decidable equality)
  is an homotopy set. Let's prove it. *)
Section Hedberg.

Variable A : Type.

Lemma lemma1 (f : forall x y : A, x = y -> x = y) (x y : A) (p : x = y) :
  f _ _ p = comp (f _ _ idpath) p.
Proof.
  todo.
Qed.

(** We define when [f] has a contractible image. *)
Definition contr_im {C : Type} (f : C -> C) :=  forall x y : C, f x = f y.

(** If [C] is decidable, then there exists a constant automorphism 
   on [C]. *)
Lemma lemma2 (C : Type) (h : decidable C) : {f : C -> C & contr_im f}.
Proof. 
  todo.
Qed.

Theorem Hedberg : discrete A -> set A.
Proof.
intros hdiscr a b p q.
assert (h : forall (x y : A), {f : x = y -> x = y & contr_im f}).
  todo.
pose (g x y := projT1 (h x y)).
assert (hgpq : g _ _ p = g _ _ q).
  todo.
assert (e : comp (g a a idpath) p = comp (g a a idpath) q).
  todo.
todo.
Qed.

End Hedberg.

Section Equivalence.

Section EquivDef.

(** The fiber of f over b are all points in the domain of f whose image has a path to b. *)
Definition fiber {A B : Type} (f : A -> B) (b : B) := {x : A & f x = b}.

(** A contractible type is inhabited and propositional (all elements are equal to the 
 contraction element *)
Record is_contr (T : Type) := IsContr {
  contr_elt : T;
  contr_eltE : prop T}.

(* f is an equivalence if the fiber is contractible (all points x over b and proofs 
  of [f x = b] are equal).  *)
Definition is_equiv {A B : Type} (f : A -> B) := 
  forall b : B, is_contr (fiber f b).

Definition is_equiv_inverse {A B : Type} (f : A -> B) (H : is_equiv f) : B -> A.
  todo.
Defined.

Definition equiv (A B : Type) := {f : A -> B & is_equiv f}.

Lemma id_is_equiv (A : Type) : is_equiv (fun x : A => x).
Proof.
  todo.
Qed.

Definition is_section {A B : Type} (f : A -> B) (g : B -> A) :=
  forall b : B, f (g b) = b.

(** Show than an equiv induces an inverse that is a section *)
Lemma equiv_section (A B : Type) (f : A -> B) :
   is_equiv f -> {g : B -> A & is_section f g}.
Proof.
  todo. 
Qed.

(** Show than any type equality implies an equivalence *)
Definition univalence_fun {A B : Type} (p : A = B) : equiv A B.
Proof.
  todo. 
Defined.

Definition univalence (A B : Type) := is_equiv (@univalence_fun A B).

Definition is_retract {A B : Type} (f : A -> B) (g : B -> A) :=
  forall x, g (f x) = x.


(** Show that a section/retraction pair + a side condition suffice to build an equivalence.
  You can look at the HoTT book for inspiration.
 *)
Section CoherentToEquiv.

Context {A B : Type}.

Variables  (f : A -> B) (g : B -> A).

Hypothesis hsection : is_section g f.

Hypothesis hretract : is_retract g f.

Hypothesis hcoherent : forall x, hretract (f x) = mapOnPaths f (hsection x).

Lemma coherent_is_equiv : is_equiv f.
Proof.
intros b.
assert (alt_contr : {a : fiber f b & forall x, x = a}).
  todo.
case alt_contr as [a ha].
apply IsContr.
- exact a.
- todo. 
Qed.

End CoherentToEquiv.


