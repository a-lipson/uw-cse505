(*

  _   _    ___    __  __   _____  __        __   ___    ____    _  __    ____
 | | | |  / _ \  |  \/  | | ____| \ \      / /  / _ \  |  _ \  | |/ /   |___ \
 | |_| | | | | | | |\/| | |  _|    \ \ /\ / /  | | | | | |_) | | ' /      __) |
 |  _  | | |_| | | |  | | | |___    \ V  V /   | |_| | |  _ <  | . \     / __/
 |_| |_|  \___/  |_|  |_| |_____|    \_/\_/     \___/  |_| \_\ |_|\_\   |_____|


Howdy folks! In this homework assignment we'll explore more Rocq programming
and proving and get some practice with lists, trees, and propositions.

There are 21 problems worth a total of 150 points.

*)


Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

(*
 * Step through this file with VSCode (or another IDE for Rocq), and complete
 * the problems. Search for "PROBLEM" to be sure you find them all---not all
 * problems correspond to Rocq code!
 *
 * Throughout, we include the approximate lines of code (LOC) or number of
 * tactics for each of our solutions to these problems.  These are rough
 * guidelines to help you figure out if you are getting off track.
 *
 * There is no penalty for writing a shorter or longer solution! However, if
 * you find yourself writing a much longer solution, you might save yourself
 * some time by taking a step back and seeing if you can find a simpler way.
 *
 *)

(* --- More arithmetic --- *)

(* This module creates a namespace where we can travel back in time to
 * Homework 1. Later in this homework we will be using the Rocq standard library
 * version of nat, so we hide our own definitions in this namespace so we can
 * close it later.
 *)
Module Homework1_TimeTravel. (* get in the DeLorean *)
Set Implicit Arguments.

(*
 * Here are some definitions again from Homework 1.
 *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => S (add m1 n2)
  end.

(*
 * PROBLEM 1 [0 points, ~4 tactics]
 *
 * You'll need this, which you proved in Homework 1. Feel free to copy/paste
 * your solution.
 *)
Lemma add_n_S :
  forall n1 n2,
    add n1 (S n2) = S (add n1 n2).
Proof.
  induction n1.
  - reflexivity.
  - intro n2. simpl. f_equal. apply IHn1.
Qed.


(* We can define multiplication recursively as repeated addition. *)

Fixpoint mult (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => O
  | S m1 => add n2 (mult m1 n2)
  end.

(*
 * PROBLEM 2 [8 points, ~35 tactics]
 *
 * Prove that multiplication is commutative, as stated by the lemma below.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Don't use more than one induction inside a single proof.  Instead,
 * figure out lemmas that might be useful, and then prove those separately
 * (by induction, probably). See the style guide for more information.
 *
 * Hint: It might be useful to review all the lemmas about `add` in
  Homework 1.
 * Feel free to copy them over if you need to use them. You might need to
 * state and prove some analogous lemmas about `mult`.
 *
 * Hint: In order to prove your helpers about `mult`, you might need 1 or 2
 * additional facts about `add`.  Try to keep these simple, based on facts
 * you know from math, and prove them by induction.
 *)

Lemma add_n_0: 
  forall n,
    add n O = n. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma add_assoc : 
  forall n1 n2 n3,
  add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
  intros.
  induction n1.
  - reflexivity.
  - simpl. f_equal. apply IHn1.
Qed.

Lemma add_comm : 
  forall n1 n2, 
    add n1 n2 = add n2 n1.
Proof.
  intros.
  induction n1; simpl;
  [ rewrite add_n_0 | rewrite IHn1; rewrite add_n_S ]; 
  reflexivity.
  (* 
    - rewrite add_n_0. reflexivity.
    - rewrite IHn1. rewrite add_n_S. reflexivity.   
  *)
Qed.

Lemma mult_n_0 : 
  forall n, 
    mult n O = O.
Proof.
  induction n.
  - reflexivity.
  - simpl. assumption. 
Qed.

Lemma mult_n_S :
  forall n1 n2,
    mult n1 (S n2) = add n1 (mult n1 n2).
Proof.
 induction n1; simpl.
  - reflexivity.
  - intro n2. f_equal. 
    rewrite IHn1.
    rewrite add_assoc.
    rewrite add_assoc.
    f_equal.
    rewrite <- add_comm.
    reflexivity.
Qed.

Lemma mult_comm :
  forall n1 n2,
    mult n1 n2 = mult n2 n1.
Proof.
  intros.
  induction n1; simpl.
  - rewrite mult_n_0. reflexivity.
  - rewrite mult_n_S. f_equal. assumption.
Qed.

(* ~45 tactics *)

(*
 * PROBLEM 3 [10 points, ~25 tactics]
 *
 * State and prove that the `mult` function is associative.
 *
 * Hint: You'll probably need ~2 more lemmas about mult and/or add.
 *)

Lemma mult_distr: 
  forall n1 n2 n3,
    mult (add n1 n2) n3 = add (mult n1 n3) (mult n2 n3).
Proof.
  intros. 
  induction n1.
  - reflexivity.
  - simpl. rewrite IHn1. rewrite add_assoc. reflexivity. 
Qed.


Lemma mult_assoc: 
  forall n1 n2 n3, 
    mult (mult n1 n2) n3 = mult n1 (mult n2 n3). 
Proof.
  intros.
  induction n1.
  - reflexivity.
  - simpl. 
    rewrite mult_distr.   
    rewrite IHn1. reflexivity.  
Qed.

(* Here's the definition of `le` from lecture (and the standard library). *)
Inductive le (n : nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m, le n m -> le n (S m).

(*
 * PROBLEM 4 [10 points, ~9 tactics]
 *
 * State and prove the following:
 * If a <= b then a + c <= b + c
 *
 * Hint: Proceed by induction.
 *)
Lemma le_mono: 
  forall a b c, 
    le a b -> le (add a c) (add b c).
Proof.
  intros.
  induction H.
  - constructor.
  - simpl. constructor. assumption.
Qed.   

End Homework1_TimeTravel. (* return to the present *)

(*
 * Now that you've seen how nat, add, and mult are defined under the hood,
 * from now on we'll use the versions in Rocq's standard library. These come
 * with nice notations like `1 + 3 * 4`, and with lots of free lemmas.
 *
 * There are also some useful tactics for working with arithmetic.
 *
 * Here are some automated proofs that the Rocq standard library versions
 * of add and mult are commutative. (These lemmas are also in the standard
 * library, but we prove them from scratch just to demonstrate the tactics.)
 *)

Lemma add_comm_again :
  forall a b, a + b = b + a.
Proof.
  intros.
  lia.
Qed.

Lemma mult_comm_again :
  forall a b, a * b = b * a.
Proof.
  intros.
  ring.
Qed.

(*
 * PROBLEM 5 [4 points, ~5 tactics]
 *
 * Prove this simple fact about and.
 *
 * Hint: Review tactics that are useful for taking apart hypotheses.
 *
 * Hint: Review tactics that are useful for decomposing goals.
 *
 * Hint: Our solution uses little automation. If you feel like it, you can solve
 * it with ~1 tactic as well, using automation.
 *)
Lemma and_comm :
  forall (A B : Prop),
    A /\ B ->
    B /\ A.
Proof.
  split; apply H.
Qed.  
    

(*
 * PROBLEM 6 [4 points, ~7 tactics]
 *
 * Prove this simple fact about or.
 *
 * Hint: Review tactics that are useful for taking apart hypotheses.
 *
 * Hint: Review tactics that are useful for decomposing goals.
 *
 * Hint: Our solution uses little automation. If you feel like it, you can solve
 * it with ~1 tactic as well, using automation.
 *)
Lemma or_comm :
  forall (A B : Prop),
    A \/ B ->
    B \/ A.
Proof.
  (* tauto. *)
  intros A B H.
  destruct H.
  - right. apply H. 
  - left. apply H.
Qed.

(* Here is an inductive definition of evenness for natural numbers. *)
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).

(*
 * There are two constructors that can prove even. 0 is even. And a number of
 * the form S (S n) is even if n is even.
 *)

(*
 * PROBLEM 7 [9 points, ~3 sentences]
 *
 * Write a comment answering the following questions.
 *
 * (a) If n is a nat in Rocq, how many constructors of the type nat (O or S) is
 *     it built with? How many of those are S constructors and how many are O?
 *
 * (b) If n is a nat in Rocq, and pf is a proof of even n, how many constructors
 *     of the proposition even is pf built with? How many are even_O and how
 *     many are even_SS?
 *
 * (c) If n is a nat in Rocq, and n is odd, explain intuitively why your answer
 *     to part (b) implies that there is no proof of "even n".
 *
 * Hint: Your answer to part (a) should be three quantities: how many
 * constructors total, how many are O, and how many are S? Each quantity should
 * be expressed in terms of n. For example, one (wrong) answer would be "There
 * are n / 3 + 7 constructors total, n / 3 are O, and 7 are S."
 *
 * Hint: Your answer to part (b) should be of a similar "shape" to part (a):
 * three quantities expressed in terms of n.
 *)
(*
 * TODO: complete this part!
 * (a) For a nat n, there are n+1 constructors total, 1 is O and n are S.
 * (b) For a proof of even n, there are ?? constructors total, ?? are even_O and ?? are even_SS. 
 * (c) n will have an odd number of S constructors?
 *)

(* Here is a function that returns twice its argument. *)
Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S m => S (S (double m))
  end.

(*
 * PROBLEM 8 [4 points, ~5 tactics]
 *
 * Prove that double always returns an even number.
 *
 * Hint: Proceed by induction.
 *)
Lemma double_even :
  forall n,
    even (double n).
Proof.
  induction n.
  - constructor. 
  - simpl. constructor. assumption.
Qed.

(*
 * PROBLEM 9 [4 points, ~2 sentences]
 *
 * Consider the following lemma, which says that every even number is the output
 * of double on some input.
 *
 * Attempt to prove this lemma by induction on n. No need to turn in your
 * partial proof.
 *
 * Explain in a comment where you get stuck.
 *)
Lemma even_double :
  forall n,
    even n ->
    exists k,
      n = double k.
Proof.
  intro n.
  induction n.
  - exists 0. reflexivity.
  - exists (S n). simpl.
Abort.
(* Becuase we can't be sure that n is even, we can't get anywhere in the proof.*)
(* We get stuck proving a false proposition or can't progress no matter how much we try to change things.*)
  
(* 
 * TODO: explain how we got stuck here!
 *)


(*
 * PROBLEM 10 [5 points, ~9 tactics]
 *
 * Now prove the lemma by induction on the derivation of even n.
 *)
Lemma even_double :
  forall n,
    even n ->
    exists k,
      n = double k.
Proof.
intros.
induction H.
- exists 0. reflexivity.
- destruct IHeven.
  exists (S x). 
  simpl. 
  rewrite H0. 
  reflexivity.
Qed. 
(*
 * PROBLEM 11 [5 points, ~6 tactics]
 *
 * Prove that the sum of two even numbers is even.
 *
 * Hint: What should you induct on?
 *)
Lemma plus_even :
  forall x y,
    even x ->
    even y ->
    even (x + y).
Proof.
  intros.
  induction H.
  - apply H0.
  - constructor. assumption.
Qed.  

(*
 * PROBLEM 12 [5 points, ~4 tactics]
 *
 * Prove that 3 is not even.
 *
 * Hint: No need for induction. "Call Rocq's bluff".
 *)
Lemma three_not_even :
  even 3 -> False.
Proof.
  intro n.
  inversion n. 
  inversion H0.
Qed.
  
Module Data_Structures.
Set Implicit Arguments.

(* --- List practice --- *)

(* Here are some definitions copied from the Rocq standard library. *)
Inductive list (A : Type) : Type :=
| nil
| cons (hd : A) (tl : list A).

Arguments nil {A}.
Infix "::" := cons.
Notation "[ ]" := nil.
Notation "[ x1 ; .. ; xN ]" := (cons x1 (.. (cons xN nil) ..)).

Fixpoint length {A} (ls : list A) : nat :=
  match ls with
  | nil => 0
  | _ :: ls' => 1 + length ls'
  end.

Fixpoint app {A} (ls1 ls2 : list A) : list A :=
  match ls1 with
  | nil => ls2
  | x :: ls1' => x :: app ls1' ls2
  end.
Infix "++" := app.

Fixpoint rev {A} (ls : list A) : list A :=
  match ls with
  | nil => nil
  | x :: ls' => rev ls' ++ [x]
  end.

(*
 * PROBLEM 13 [12 points, ~15 tactics]
 *
 * Prove the following theorem about the length of a reversed list.
 *
 * Hint: Proceed by induction on l.
 *
 * Hint: You'll need a helper lemma!
 *)
Lemma length_app: 
  forall A (l: list A) t,
    length (l ++ [t]) = S (length l).
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. 
    rewrite IHl. 
    reflexivity.
Qed. 

Lemma length_rev :
  forall A (l : list A),
    length (rev l) = length l.
Proof.
intros.
induction l.
- reflexivity.
- simpl. 
  rewrite length_app. 
  rewrite IHl. 
  reflexivity.
Qed. 

(*
 * Here is a function that adds up all the elements of a list of nats.
 *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

(*
 * And here are two functions that computes the same result with tail recursion.
 *)
Fixpoint sum_list_tr (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => sum_list_tr xs (x + acc)
  end.

Definition sum_list_tailrec (l : list nat) : nat :=
  sum_list_tr l 0.

(*
 * PROBLEM 14 [5 points, ~1 sentences]
 *
 * Consider the following theorem about the two ways of summing a list. You will
 * be asked to prove it in the next problem. For now, make a proof attempt that
 * proceeds directly by induction on `l`, without any nested inductions or
 * extra lemmas. At some point, you should get stuck.
 *
 * Write a sentence or two explaining why your proof attempt fails. Focus on the
 * induction hypothesis and whether it gives you enough information to complete
 * the proof.
 *
 * There is no need to turn in your proof attempt. Just turn in your
 * explanation.
 *
 * Hint: The base case should be provable.
 *
 * Hint: You might be able to make slightly more progress if you use the
 * `unfold` tactic to see inside the definition of `sum_list_tailrec`.
 *)
Theorem sum_list_tailrec_ok : forall l,
  sum_list_tailrec l = sum_list l.
Proof.
  induction l.
  - reflexivity.
  - unfold sum_list_tailrec. 
    simpl. 
Abort.
(* 
 * We need a way of eliminating the accumulator that we get from 
 * unfolding the tail recursive form of sum list.
 * Otherwise, we have no way of working with the accumulator inside 
   of the tail recursive sum list. 
 *)

(*
 * PROBLEM 15 [8 points, ~15 tactics]
 *
 * Now fix your broken proof by backing up and stating and proving a more
 * general helper lemma. Then use your helper lemma to finish the proof.
 *
 * Hint: Since `sum_list_tailrec` is defined in terms of the recursive function
 * `sum_list_tr`, it makes sense for your lemma to be about `sum_list_tr`.
 *
 * Hint: Your lemma should be proved by induction.
 *
 * Hint: Your fixed proof of `sum_list_tailrec_ok` should *not* use induction.
 *)

Lemma sum_acc_tr : 
  forall l acc, 
    sum_list_tr l acc = sum_list l + acc.
Proof.
  induction l.
  - auto.
  - intro acc. 
    simpl. 
    rewrite IHl. 
    lia.  
Qed.

Theorem sum_list_tailrec_ok : forall l,
  sum_list_tailrec l = sum_list l.
Proof.
  intro l.
  destruct l.
  - reflexivity.
  - unfold sum_list_tailrec. 
    rewrite sum_acc_tr. 
    lia.
Qed. 


(* --- Binary Tree practice --- *)

Inductive tree (A : Type) : Type :=
| Leaf
| Node : tree A -> A -> tree A -> tree A.
Arguments Leaf {A}.

Fixpoint reverse {A} (t : tree A) : tree A :=
  match t with
  | Leaf => Leaf
  | Node l d r => Node (reverse r) d (reverse l)
  end.

(*
 * PROBLEM 16 [5 points, ~5 LOC]
 *
 * Define a function that adds up all the elements of a tree of nats.
 *)
Fixpoint sum_tree (t : tree nat) : nat :=
  match t with
  | Leaf => 0
  | Node l d r => d + sum_tree l + sum_tree r
  end.

(*
 * PROBLEM 17 [5 points, ~5 tactics]
 *
 * Prove that `reverse` has no effect on the sum of the elements in a tree.
 *)
Lemma sum_tree_reverse :
  forall t,
    sum_tree (reverse t) = sum_tree t.
Proof.
  induction t.
  - reflexivity.
  - simpl. lia.
Qed.  

(*
 * PROBLEM 18 [12 points, ~20 tactics]
 *
 * Prove the following similar lemma about `sum_list` and `rev`.
 *
 * Hint: Proceed by induction on l.
 *
 * Hint: You'll need a helper lemma about sum_list.
 *)
Lemma sum_acc: 
  forall l acc, 
    sum_list (l ++ [acc]) = acc + sum_list l.
Proof.
  induction l; simpl.
  - lia.
  - intros acc. 
    rewrite IHl. 
    lia.
Qed.

Lemma sum_list_rev :
  forall l,
    sum_list (rev l) = sum_list l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
   rewrite sum_acc. 
   rewrite <- IHl.
   reflexivity.
Qed.


End Data_Structures.

(*
 * CHALLENGE 19 [10 points, ~20 tactics]
 *
 * Give an alternative characterization of evenness as follows.
 *
 * Note: This problem could be harder than some others! We recommend trying
 * the other problems first.
 *)
Print even.
(* need lemma since lia won't work *)
(* TODO: i think we should be able to make lia work on something? *)
Lemma add_identity : 
  forall x, 
    x + 0 = x.
Proof.
  auto.
Qed.

(* TODO: inline this lemma if it can be solved with auto? *)
Lemma add_assoc : 
  forall x, 
    S (x + S x) = S (S (x + x)).
Proof.
  auto.
Qed.

Lemma even_iff_exists_half :
  forall n,
    even n <-> exists k, n = 2 * k.
 Proof.
  split.
  - intros. induction H.
    + exists 0. reflexivity.
    + destruct IHeven. 
      exists (S x). lia.
  - intros. 
    destruct H. revert n H.
    + induction x; intros; rewrite H.
      * constructor.
      * simpl.
        rewrite add_identity.
        rewrite add_assoc.
        apply even_SS.
        apply IHx.
        lia.
Qed.

(*
 * CHALLENGE 20 [20 points, ~8 tactics]
 *
 * In class we saw a proof that Peirce's law implies the law of excluded middle.
 * Now prove the reverse direction.
 *
 * Hint: This way should be easier than the proof from lecture.
 *
 * Note: This problem could be harder than some others! We recommend trying
 * the other problems first.
 *
 *)
Lemma lem_implies_peirce :
  (forall P : Prop, P \/ ~P) -> forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
intros LEM P Q Peirce.
  destruct (LEM P) as [HP | HnotP].
  - exact HP.
  - apply Peirce.
    intro HP.
    contradiction.
Qed.



(* TODO: Your feedback here! *)
(*
 * 1. The homework took us about 8 hours.
 *
 * 2. We loved the realization that oftentimes only reflexivity is needed for base cases.
 *    This made our inductive proofs a lot of fun since we only had to focus on the inductive case.
 *
 * 3. The challenge problems have provided quite the challenge... 
 *    Also, early on, when prvoing one of the addition theorems, we couldn't trivially use
*     associativity and commutativity - so we proved a really dumb lemma called "swap lemma"
*     that took us like 3 days to take out. 
 *)  


(*
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this
 * homework assignment.
 *)
