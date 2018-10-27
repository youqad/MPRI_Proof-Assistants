Inductive form : Set :=
  | form_var : nat -> form
  | form_true : form
  | form_false : form
  | form_and : form -> form -> form
  | form_or : form -> form -> form
  | form_implies : form -> form -> form.

  (* Notation "∼ x" := (form_var x) (at level 2). *)


Ltac destruct_sumbool := 
match goal with
    | H: sumbool _ _ |- _ => destruct H
end.

Definition form_in_dec : forall (A: form) (Δ : list form), {In A Δ} + {~ In A Δ}.
    induction Δ. 
        now right.
        simpl; pose proof form_eq_dec a A.
        do 2 destruct_sumbool;
        match goal with
            | _: In _ _ |- _ => left
            | _: _ = _ |- _ => left
            | |- _ => right
        end; try solve [now left | now right | intuition].
Defined.

(* Notation "x ⊢ A" := (((cons x nil), A) : seq) (at level 2).
Notation "x , y , .. , z ⊢ A" := (((cons x (cons y .. (cons z nil) ..)), A) : seq) (at level 2). *)

(* Definition seq := (list form) * form. 
Notation "Δ ⊢ A" := ((Δ, A) : seq).
Notation " ⊢ A" := ((nil, A) : seq).
*)

(* Inductive seq : Set :=
    vdash : list form -> form -> seq.

Infix "⊢" := vdash (at level 65).
Notation "∅ ⊢ A" := (nil ⊢ A) (at level 10). *)
