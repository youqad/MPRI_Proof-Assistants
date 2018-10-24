Require Import List (* lemmas on the list datatype *).
Require Import Recdef (* loading the Function toolbox *).
Require Import Lia. (* the lia decision procedure *)
Definition slen (p : list nat * list nat) :=
  let '(x, y) := p in
  length x + length y.

Function merge (p : list nat * list nat) { measure slen p } : list nat :=
  match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | ((x1 :: l1') as l1, (x2 :: l2') as l2) =>
    if Nat.leb x1 x2 then x1 :: merge (l1', l2)
    else x2 :: merge (l1, l2')
  end.

Proof.
  intros. simpl. lia.
  intros. simpl. lia.
Defined.
