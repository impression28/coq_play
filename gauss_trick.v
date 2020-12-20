Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Require Import List.
Import ListNotations.

Fixpoint vec_sum (l1 l2 : list nat) :=
  match l1, l2 with
  | h1 :: t1, h2 :: t2 => (h1 + h2) :: (vec_sum t1 t2)
  | nil, h2 :: t2 => h2 :: t2
  | h1 :: t1, nil => h1 :: t1
  | nil, nil => nil
  end.

Lemma sum_of_vec_sum : forall l1 l2,
 list_sum (vec_sum l1 l2) = list_sum l1 + (list_sum l2).
induction l1 as [|h t IH]; intros.
  - destruct l2; reflexivity.
  - destruct l2.
    + simpl. lia.
    + simpl. rewrite IH. lia.
Qed.

Lemma list_sum_rev : forall l,
  list_sum l = list_sum (rev l).
Proof.
  induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite list_sum_app. rewrite IH.
  rewrite Nat.add_comm. simpl. rewrite <- plus_n_O.
  reflexivity.
Qed.

Example gauss_trick_ex :
  vec_sum (rev (seq 0 3)) (seq 0 3) = repeat (pred 3) 3.
Proof. simpl. reflexivity. Qed.

Lemma repeat_sum : forall n m,
  list_sum (repeat n m) = m*n.
Proof.
  induction m as [|m' IHm'].
  - reflexivity.
  - simpl. rewrite IHm'. reflexivity.
Qed.

Fixpoint dec_seq n :=
  match n with
  | O => nil
  | S n' => n' :: dec_seq n'
  end.

Lemma seq_push : forall m n,
  seq (S n) m = map S (seq n m).
Proof.
  induction m as [|m' IHm'].
  - reflexivity.
  - intros. simpl. rewrite <- IHm'. reflexivity.
Qed.

Lemma seq_first : forall n,
  [0] ++ seq 1 n = seq 0 (S n).
Proof. reflexivity. Qed.

Lemma seq_last: forall n,
  seq 0 n ++ [n] = seq 0 (S n).
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite seq_push.
  replace ([S n']) with (map S [n']) by reflexivity.
  rewrite <- map_app. rewrite IHn'. rewrite <- seq_push.
  reflexivity.
Qed.

Lemma rev_seq_dec_seq : forall n,
  rev (seq 0 n) = dec_seq n.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
  rewrite <- IHn'. simpl. Search (rev (_ ++ _)).
  replace ([0]) with (rev [0]) by reflexivity.
  rewrite <- rev_app_distr. rewrite <- rev_unit. rewrite seq_last.
  reflexivity.
Qed.

Lemma dec_seq_length : forall n,
  length (dec_seq n) = n.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma vec_sum_map_S : forall l1 l2,
  length l1 = length l2 ->
  vec_sum (map S l1) l2 = map S (vec_sum l1 l2).
Proof.
  induction l1 as [|h t IH]; intros.
  - simpl in H. symmetry in H.
  apply length_zero_iff_nil in H. rewrite H. reflexivity.
  - destruct l2 as [|h' t']. discriminate H. simpl. rewrite IH.
  reflexivity. simpl in H. lia.
Qed.

Lemma map_repeat : forall (f : nat->nat) n m,
  map f (repeat n m) = repeat (f n) m.
Proof.
  induction m as [|m' IHm'].
  - reflexivity.
  - simpl. rewrite IHm'. reflexivity.
Qed.

Lemma vec_sum_seq_dec_seq : forall n,
  vec_sum (seq 0 n) (dec_seq n) = repeat (pred n) n.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite seq_push. rewrite vec_sum_map_S.
  rewrite IHn'. rewrite map_repeat. Search (Nat.pred (S _)).
  destruct n'. reflexivity. rewrite Nat.pred_succ. reflexivity.
  rewrite seq_length. rewrite dec_seq_length. reflexivity.
Qed.


Lemma gauss_trick : forall n,
  vec_sum (seq 0 n) (rev (seq 0 n)) = repeat (pred n) n.
Proof.
  intros. rewrite rev_seq_dec_seq. rewrite vec_sum_seq_dec_seq.
  reflexivity.
Qed.

Theorem sum_consecutive : forall n,
  2*(list_sum (List.seq 0 n)) = n*(pred n).
Proof.
  intros. simpl. rewrite <- plus_n_O. replace
  (list_sum (seq 0 n) + list_sum (seq 0 n)) with
  (list_sum (seq 0 n) + list_sum (rev (seq 0 n))).
  - rewrite <- sum_of_vec_sum. rewrite gauss_trick.
  rewrite repeat_sum. reflexivity.
  - rewrite <- list_sum_rev. reflexivity.
Qed.