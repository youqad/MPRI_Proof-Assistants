Require Import List Arith Omega Program.

Program Definition imposs (H : 0 = 1) : False := !.

Program Definition exists_nonzero : { x : nat | x > 0 } := 1.
(* 
Obligation Tactic := idtac. 

or:

Next Obligation.
    auto.
Defined.
**)


Program Definition exists_lt_zero : { x : nat | x < 0 } := 0. Admit Obligations.

Program Definition head {A} (l: {l: list A | l <> nil}) : A := 
    match l with
    | nil => !
    | (cons h t) => h
    end.

Eval cbv beta zeta delta [head] in head.
Extraction head.

Program Fixpoint euclid (x : nat) 
    (y : nat | 0 < y) { wf lt x } : { (q, r) : nat * nat | x = q * y + r } 
    := 
    if lt_dec x y then (0, x)
    else let 'pair q r := euclid (x - y) y in
    ((S q), r).
Next Obligation.
    omega.
Defined.

Next Obligation.
    destruct euclid as [[q' r'] H']. simpl in *.
    injection Heq_anonymous. intros <- <-. omega.
Defined.

Extraction Inline proj1_sig projT2 projT1.
Recursive Extraction euclid.



Inductive type := 
  | cst | arrow : type -> type -> type.
Inductive term := 
  | var : nat -> term
  | lam : type -> term -> term
  | app : term -> term -> term.
Definition ctx := list type.


Inductive typing : ctx -> term -> type -> Prop :=
| Var : forall (G : ctx) (x : nat) (A : type), 
    List.nth_error G x = Some A -> 
    typing G (var x) A

| Abs : forall (G : ctx) (t : term) (A B : type),
    typing (A :: G) t B ->
    typing G (lam A t) (arrow A B)

| App : forall (G : ctx) (t u : term) (A B : type),
    typing G t (arrow A B) ->
    typing G u A ->
    typing G (app t u) B.


Lemma invert_var Γ x T (H : typing Γ (var x) T) : 
    List.nth_error Γ x = Some T.
Proof.  
    now inversion H.
    (* or: 
    remember (var x) as t.
    induction H as [G x' A Hnth|G t A B HB|G t u A B HAB HA]; 
    try injection Heqt; try discriminate.
    intro.
    *)
Qed.

Implicit Types A B : Set.

Inductive vect (A : Set) : nat -> Set :=
| vnil : vect A 0
| vcons (a : A) (n : nat) : vect A n -> vect A (S n).

Example v3 : vect bool 3 :=
 vcons _ true 2 (vcons _ true 1 (vcons _ false 0 (vnil _))).

Arguments vnil {A}. Arguments vcons {A} a {n} v.

Example v3' : vect bool 3 :=
 vcons true (vcons true (vcons false vnil)).

Fixpoint vmap {A B} {n} (f : A -> B) (v : vect A n) : vect B n
:= match v in vect _ k (* binds *) return vect B k with
   | vnil => vnil
   | vcons a v' => vcons (f a) (vmap f v')
   end.

Definition vhead {A} {n} (v : vect A (S n)) : A :=
match v in vect _ k
    return match k with 0 => unit | S k => A end with
    | vnil => tt
    | vcons a v' => a
end.

Definition vtail {A} {n} (v : vect A (S n))
  : vect A n := 
  match v in vect _ k
    return match k with 0 => unit | S k => vect A k end with
    | vnil => tt
    | vcons a v' => v'
end.

Definition vtail' {A} {n} (v : vect A (S n)) : vect A n.
Proof. (* using tactics *)
  now inversion v.
Defined.

Extraction vtail.
Extraction vtail'.


Definition ilist A n := {l : list A | length l = n}.

Record Iso (A B : Type) :=
  { iso_lr : A -> B; iso_rl : B -> A;
    iso_lr_rl : forall x, iso_lr (iso_rl x) = x;
    iso_rl_lr : forall x, iso_rl (iso_lr x) = x }.

Program Fixpoint vect_ilist {A n} (v : vect A n) : ilist A n := 
    match v with
    | vnil => nil
    | vcons a v' => a :: (vect_ilist v')
    end.

Fixpoint ilist_vect {A} (l : list A) : vect A (length l) := 
    match l with
    | nil => vnil
    | a :: v' => vcons a (ilist_vect v')
    end.

Program Definition vect_ilist_iso {A} (n : nat) :
    Iso (vect A n) (@ilist A n) :=
    {| iso_lr := fun x => vect_ilist x ;
        iso_rl := fun x => ilist_vect x |}.
Next Obligation.
    destruct x; auto.
Defined.

(* Solve Obligations with . *)


   
