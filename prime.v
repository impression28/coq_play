Require Import Coq.Arith.PeanoNat.
Require Import Coq.omega.Omega.

Definition prime (p : nat) :=
forall n m : nat, n*m = p -> (n = 1 <-> m <> 1).
Example one_not_prime: ~ prime 1.
Proof.
unfold prime. intros H. assert (1 * 1 = 1). reflexivity. apply H in H0.
unfold iff in H0. assert (1 = 1 -> 1 <> 1). apply H0. apply H1; reflexivity.
Qed.
