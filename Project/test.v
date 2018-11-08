Definition eq_sym (A : Type) (x y z : A) (p: x = y) : y = z -> x = z :=
    match p in _ = u return (u = z -> x = z) with
        | eq_refl => (fun q => q)
    end.

Require Import List.

Fixpoint iter {T : Type} (n : nat) (f : T -> T) (x0 : T) {struct n} : T := 
    match n with 
    | 0   => x0
    | S m => f (iter m f x0)
    end.

Fixpoint rcons {A : Type} (x : A) (xs : list A) {struct xs} : list A := 
    match xs with 
    | nil      => x :: nil 
    | y :: ys  => y :: rcons x ys 
    end.


Fixpoint take {A : Type} (n : nat) (l : list A) : list A := 
    match n with 
    | 0   => nil
    | S m => match l with 
            | nil => nil 
            | x :: xs => x :: (take m xs)
            end
    end.

Fixpoint drop {A : Type} (n : nat) (l : list A) {struct n}: list A := 
    match n with 
    | 0   => l
    | S m => match l with 
            | nil => nil 
            | x :: xs => (drop m xs)
            end
end.

Fixpoint take_drop {A: Type} (n: nat) (l: list A) : (take n l) ++ (drop n l) = l := 
    match n with 
        | 0 => eq_refl
        | S m => (match l with 
                    | nil => eq_refl 
                    | x::l' => f_equal (fun l' => cons x l') (take_drop m l')
        end)
    end.

Fixpoint rot {A : Type} (n: nat) (l: list A) : list A := 
    iter n (fun l' => (drop 1 l) ++ (take 1 l)) l.

Fixpoint cycle {A : Type} (n: nat) (l: list A) : list A := 
    iter n (fun l' =>  (drop (length l - 1) l) ++ (take (length l - 1) l)) l.

Lemma cycle_add : forall {A: Type} (l: list A) n m, cycle m (cycle n l) = cycle (n+m) l.
Admitted.

Parameter A : Set.
Parameter eqA : A -> A -> bool.
Inductive regexp : Set :=
    | empty : regexp
    | epsilon : regexp
    | test : (A -> bool) -> regexp
    | compose : regexp -> regexp -> regexp
    | or : regexp -> regexp -> regexp
    | star : regexp -> regexp.

Definition word := list A.

Definition recognizer_A (a: A) := test (eqA a).

Fixpoint recognizer_word (w: word) := 
    match w with 
    | nil => empty
    | h::t => compose (recognizer_A h) (recognizer_word t)
    end.

Fixpoint matches_empty_word (r: regexp) : bool := 
    match r with
        | empty => false
        | epsilon => true
        | test P => false
        | compose r_1 r_2 => (matches_empty_word r_1) && (matches_empty_word r_2) 
        | or r_1 r_2 => (matches_empty_word r_1) || (matches_empty_word r_2) 
        | star _ => true
    end.


(* Fixpoint matches (r : regexp) (w : word) (k : word -> bool) : bool :=
    match r, w with
    | empty, s => false
    | epsilon, s => k s
    | test f, c :: s => if f c then k s else false
    | test f, nil => false
    | compose r r', s => matches r s (fun s' => matches r' s' k)
    | or r r', s => matches r s k || matches r' s k
    | star r, s => matches r s (fun s' => matches (star r) s' k) || k s
end. *)


Parameter matches : regexp -> word -> (word -> bool) -> bool.

Parameter matches_bool : word -> regexp -> bool.


Inductive matches_Prop : word -> regexp -> Prop := 
    | mepsilon : matches_Prop nil epsilon
    | mtest : forall P a, (P a = true) -> matches_Prop (a::nil) (test P)
    | mcompose : forall w_1 w_2 r_1 r_2, matches_Prop w_1 r_1 -> matches_Prop w_2 r_2 -> matches_Prop (w_1 ++ w_2) (compose r_1 r_2)
    | mor : forall w r_1 r_2, matches_Prop w r_1 \/ matches_Prop w r_2 -> matches_Prop w (or r_1 r_2)
    | mstar : forall w_1 w_2 r, matches_Prop w_1 r -> matches_Prop w_2 (star r) -> matches_Prop (w_1 ++ w_2) (star r). 

Lemma correctness : forall r w, matches_bool r w = true -> matches_Prop r w.
Admitted.

Lemma completeness : forall r w, matches_Prop r w -> matches_bool r w = true.
Admitted.

