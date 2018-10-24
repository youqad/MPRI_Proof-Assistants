Require Import List Arith Omega.
Require Import FunctionalExtensionality.
Require Import Program.

Inductive tree (A : Type) := 
| leaf (data : A)
| node (l : tree A) (r : tree A).

Arguments leaf {A} data.
Arguments node {A} l r.

Fixpoint relabel {A} (t : tree A) (acc : nat) : tree nat * nat :=
  match t with
    | leaf x => (leaf acc, S acc)
    | node l r => 
      let 'pair l' acc' := relabel l acc in
      let 'pair r' acc'' := relabel r acc' in
        (node l' r', acc'')
  end.

(** Instead of folding the state through explicitly,
  we can use a monadic interface that does it
  implicitly.
 *)


Class Monad (m : Type -> Type) :=
  { ret : forall {A}, A -> m A ;
    bind : forall {A B}, m A -> (A -> m B) -> m B ;

    bind_return_l {A B} (x : A) (f : A -> m B) : 
      bind (ret x) f = f x;

    bind_return_r {A} (x : m A) : bind x ret = x;

    bind_assoc {A B C} (x : m A) 
               (f : A -> m B) (g : B -> m C) :
      bind x (fun a => bind (f a) g) = 
      bind (bind x f) g
 }.

Delimit Scope monad_scope with monad.

Notation " x <- m ;; f " := (bind m (fun x => f)) (at level 100, m at next level, right associativity) : monad_scope.
Notation " m ;; f " := (_ <- m%monad ;; f%monad)%monad (at level 100, right associativity) : monad_scope.

Local Open Scope monad_scope.

(** First a simple monad: the option *)

Program Instance option_monad : Monad option :=
  { ret A x := Some x ;
    bind A B m f := 
      match m return option B with
        | None => None
        | Some x => f x
      end }.
(* Exercise: prove the laws *)
Admit Obligations.

(** Typical usage: *)

Fixpoint nth_opt {A} (l : list A) (n : nat) : option A := 
  match l with
    | nil => None
    | cons a l' =>
      match n with
        | 0 => Some a
        | S n' => nth_opt l' n'
      end
  end.

(** Check if elements at indices [m] and [n] of [l] 
  are equal, propagating out-of-bounds errors. *)

Definition foo (l : list nat) (n m : nat) : option bool := 
  x <- nth_opt l n;;
  y <- nth_opt l m;;
  ret (beq_nat x y).

(** State forms a monad. *)

Definition stateM (S : Type) (A : Type) := 
  S -> (A * S).

Program Instance state_monad S : Monad (stateM S) :=
  { ret A x := _ (* : S -> A * S *);
    bind A B := fun (m : stateM S A) 
                    (f : A -> stateM S B) => 
                  _ (* : S -> B * S *) }.

(* The proofs require extensionality of functions: 
  (forall x, f x = g x) -> f = g.
  Use [extensionality x] to apply it to a goal 
of the form [f = g].

Next Obligation.
Proof. Qed. *)

Admit Obligations.

(* The state monad has associated operations 
  to manipulate the (otherwise hidden) state *)  
Definition get {S} : stateM S S := fun s => (s, s).
Definition put {S} (x : S) : stateM S S := 
  fun s => (x, x).

(* The run function compute the result of the 
  monadic computation on a given initial state. *)

Definition runS {A S} (s : stateM S A) (init : S) : A * S := s init.

Bind Scope monad_scope with stateM.

Fixpoint relabelM {A} (t : tree A) : stateM nat (tree nat).
(* Exercise: Rewrite [relabel] using the monadic
   operations. *)
clear relabelM; admit.
Qed.

(** Should be exactly the same as relabel: *)


(** Optionally, show that getting the elements of 
  a labeled tree with n leaves starting from 0
  from left-to-right gives the sequence of numbers
  0..n.
 *)

Fixpoint elements {A} (t : tree A) : list A.
clear; admit.
Qed.

Lemma label_elements {A} (t : tree A) : 
  forall acc, 
    let (t', acc') := relabel t acc in
    let x := elements t' in
    (acc' = acc + length x) /\
    (forall n, n < length x -> 
               (nth n x 0 = acc + n)).
Proof. admit. Qed.

(** What conclusions do you draw on proving 
  monadic code? *)
