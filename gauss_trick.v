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
Admitted.

Lemma list_sum_rev : forall l,
  list_sum l = list_sum (rev l).
Admitted.

Example gauss_trick_ex :
  vec_sum (rev (seq 0 3)) (seq 0 3) = repeat (pred 3) 3.
Proof. simpl. reflexivity. Qed.

Lemma gauss_trick : forall n,
  vec_sum (rev (seq 0 n)) (seq 0 n) = repeat (pred n) n.
Admitted.

Lemma repeat_sum : forall n m,
  list_sum (repeat n m) = m*n.
Admitted.

Theorem sum_consecutive : forall n,
  2*(list_sum (List.seq 0 n)) = n*(pred n).
Proof.
  intros. simpl. rewrite <- plus_n_O. replace
  (list_sum (seq 0 n) + list_sum (seq 0 n)) with
  (list_sum (rev (seq 0 n)) + list_sum (seq 0 n)).
  - rewrite <- sum_of_vec_sum. rewrite gauss_trick.
  rewrite repeat_sum. reflexivity.
  - rewrite <- list_sum_rev. reflexivity.
Qed.