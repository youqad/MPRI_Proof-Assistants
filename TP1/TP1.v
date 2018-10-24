Parameter A B C: Prop.

Definition imp_id0 (A : Prop) : A -> A := fun x => x.
Definition imp_trans0 (A B C : Prop) : (A -> B) -> (B -> C) -> (A -> C) := 
    fun h1 h2 a => h2 (h1 a). 
Definition disj_comm (A B : Prop) : (A \/ B) -> (B \/ A) := 
    fun a_or_b => (or_ind (fun a => or_intror a) (fun b => or_introl b) a_or_b).


Lemma AimpA : A -> A.
Proof. 
    intro; assumption.
Qed.


Lemma imp_trans : (A->B) -> (B->C) -> A -> C.
Proof.
    intros; apply H in H1; now apply H0 in H1.
Qed.


Lemma and_comm : A /\ B -> B /\ A.
Proof.
    intro; 
    destruct H; split; assumption.
Qed.

Lemma AnotnotA : forall A: Prop, A -> ~~A.
Proof.
    intros; intro; contradiction.
Qed. 

Lemma assoc_tauto : (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
    intro; 
    repeat destruct H.
    now left.
    now right.
Qed.

Lemma Aequiv : A <-> A.
Proof.
    unfold iff; split; now intro.
Qed.

Print AimpA.
Print imp_trans.


Definition excluded_middle := forall P:Prop, P \/ ~P.

Lemma EM_iff : excluded_middle <-> (forall P:Prop, ~~P -> P).
Proof.
    unfold excluded_middle; split; intros.
    destruct (H P). assumption. contradiction.
    apply H.
    intro.
    assert (~ P /\ ~~ P).
    - split; intro; apply H0.
      + now left.
      + now right.
    - destruct H1; contradiction.
Qed. 

Lemma classical_implication : excluded_middle <-> (forall P Q:Prop, (P -> Q) <-> ~P \/ Q).
Proof.
    unfold excluded_middle; split; intros.
    - split; intros.
      assert (P \/ ~ P). apply H.
      destruct H1; try (right; now apply H0 in H1);
      try (left; easy).
      destruct H0; try contradiction; try easy.
    - assert (~ P \/ P). now apply (H P P).
      now apply disj_comm.
Qed.

Lemma not_exists : forall X (P: X -> Prop), (~ (exists p, P p)) <-> forall p, ~ P p.
Proof.
    intros.
    split; intros; intro.
    apply H; now exists p.
    destruct H0; now apply H in H0.
Qed.


Parameter Person : Set.
Parameter Drinks : Person -> Prop.
Axiom non_empty_room : Person.
Axiom EM : excluded_middle.


Theorem Drinker_paradox : exists p: Person, (Drinks p -> forall q, Drinks q).
Proof.
    assert ((forall q, Drinks q) \/ (~(forall q, Drinks q))) by apply EM.
    destruct H.
    - exists non_empty_room; now intro.
    - assert (exists p, ~ Drinks p).
      pose proof EM as EM.
      pose proof EM_iff as EM_iff.
      assert (forall P : Prop, ~ ~ P -> P) as not_not_elim. now apply -> EM_iff.
      clear EM_iff.
      assert (~ (forall q : Person, ~ ~ Drinks q)).
      + intro. 
        apply H; intro.
        assert (~ ~ Drinks q) by apply H0.
        now apply not_not_elim in H1.
      + assert (~ ~ (exists q : Person, ~ Drinks q)).
        intro. apply H0. now apply -> not_exists.
        now apply not_not_elim.
      + destruct H0; exists x; now intro.
Qed.


      










    
