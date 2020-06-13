Require Import Coq.Arith.PeanoNat.
Require Import Coq.omega.Omega.

Definition prime (p : nat) :=
forall n m : nat, n*m = p -> (n = 1 <-> m <> 1).

Example one_not_prime: ~ prime 1.
Proof.
unfold prime. intros H. assert (1 * 1 = 1). reflexivity. apply H in H0.
destruct H0 as [P Q]. apply P; reflexivity.
Qed.

Example two_is_prime: prime 2.
Proof.
unfold prime; intros; split; intros.
- rewrite H0 in H. simpl in H. Search (_ + 0).
rewrite <- plus_n_O in H. rewrite H. Search (_ <> _).
apply Nat.neq_succ_diag_l.
- destruct n. simpl. discriminate H. destruct m.
Search (_ * 0). rewrite <- mult_n_O in H. discriminate H.
simpl in H. Search (_ * S _). rewrite Nat.mul_succ_r in H. Search (S _ = S _).
apply Nat.succ_inj in H. apply -> Nat.succ_inj_wd_neg in H0.
destruct m. exfalso. apply H0; reflexivity. rewrite Nat.mul_succ_r in H.
simpl in H. apply Nat.succ_inj in H. apply eq_S. destruct n. reflexivity. exfalso.
Search (_ + S _). rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H.
discriminate H.
Qed.