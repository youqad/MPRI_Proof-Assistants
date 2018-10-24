Require Import ZArith Omega.

Record monoid := mkMonoid { 
    carrier: Type;
    unit: carrier;
    op: carrier -> carrier -> carrier;
    left_unit: forall x, op x unit = x;
    right_unit: forall x, op unit x = x;
    assoc_op : forall x y z, op (op x y) z = op x (op y z);
}.

Program Definition nat_plus : monoid := {|
    carrier := nat;
    unit := 0;
    op := (fun x y => x+y);
    left_unit := _;
    right_unit := _;
    assoc_op := _;
|}.

Next Obligation.
    omega.
Qed.


Program Definition nat_times : monoid := {|
    carrier := nat;
    unit := 1;
    op := (fun x y => x*y);
    left_unit := _;
    right_unit := _;
    assoc_op := _;
|}.

Next Obligation.
    omega.
Qed.


(* Fixpoint expon {m: monoid} (a: carrier m) (n: nat) :=
    match n with
    | 0 => unit m.
    | S m => op m *)

Definition bool_to_nat (b: bool) : nat := if b then 1 else 0.

Definition nat_to_bool n := match n with 
    | 0 => false
    | _ => true
    end.



