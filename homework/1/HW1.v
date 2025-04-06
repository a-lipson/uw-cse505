(*

    _   _    ___    __  __   _____  __        __   ___    ____    _  __    _
   | | | |  / _ \  |  \/  | | ____| \ \      / /  / _ \  |  _ \  | |/ /   / |
   | |_| | | | | | | |\/| | |  _|    \ \ /\ / /  | | | | | |_) | | ' /    | |
   |  _  | | |_| | | |  | | | |___    \ V  V /   | |_| | |  _ <  | . \    | |
   |_| |_|  \___/  |_|  |_| |_____|    \_/\_/     \___/  |_| \_\ |_|\_\   |_|


*)


(*
 * This homework assignment is a tutorial introduction to Rocq.
 *
 * Set up Rocq as described in README.md. Then step through this file with
 * VSCode (or another IDE for Rocq), and complete the problems. Search for
 * "PROBLEM" to be sure you find them all---not all problems correspond to Rocq
 * code!
 *
 * Throughout, we include the approximate lines of code (LOC) or number of
 * tactics for each of our solutions to these problems.  These are rough
 * guidelines to help you figure out if you are getting off track.
 *
 * There is no penalty for writing a shorter or longer solution! However, if
 * you find yourself writing a much longer solution, you might save yourself
 * some time by taking a step back and seeing if you can find a simpler way.
 *
 * Every problem on this homework is designed to be conceptually
 * straightforward; the hard part is just getting up to speed on Rocq.
 *
 * There are 9 problems worth a total of 50 points.
 *
 * See the bottom of README.md for quite a bit more information, including some
 * advice on how to do this homework, how this homework will be graded, and a
 * list of tactics used in our solution.
 *)

(* --- Setting up Rocq --- *)

(*
 * PROBLEM 1 [0 points, ~1 LOC]
 * Set up Rocq as described in README.md
 *
 * Once Rocq is installed according to directions, you should be able to step
 * through this entire file in your IDE.
 *
 * We will always have a non-problem PROBLEM 1, because Gradescope makes the
 * autograder results "Problem 1" :)
 *
 * You've heard of computer scientists counting from zero, but have you heard of
 * them counting from two?!
   most ridiculous indeed!
 *)

(* infer type arguments *)
Set Implicit Arguments.

(* --- Boolean practice --- *)

(* Here are some definitions about booleans from lecture.  *)

Inductive bool : Type :=
| true : bool
| false : bool.

Definition notb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.


(*
 * PROBLEM 2 [4 points, ~5 LOC]
 * Write a function called `orb` that implements boolean disjunction.
 *
 * Hint: Kinda like `andb`, but different.
 *)
Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with 
  | true => true
  | false => b2
  end.


(*
 * Remember that `Compute` just runs programs.
 * We can use it for simple testing.
 *)
Compute orb true true.   (* should be true. *)
Compute orb true false.  (* should be true. *)
Compute orb false true.  (* should be true. *)
Compute orb false false. (* should be false. *)


(*
 * PROBLEM 3 [4 points, ~15 tactics]
 * Prove the following theorem, that `orb` is commutative.
 *
 * Hint: Kinda like `andb_comm` from lecture.
 * Hint: You may need fewer tactics if you use semicolon chains.
 *)
Lemma orb_comm :
  forall b1 b2,
    orb b1 b2 = orb b2 b1.
Proof.
  (* concise example as in the lecture notes *)
  destruct b1, b2; auto.
Qed.

(* when we were first going over this in class, 
   it reminded me of the FOL proofs we wrote in PHIL 120. *)
Lemma orb_comm' :
  forall b1 b2,
    orb b1 b2 = orb b2 b1.
Proof.
  (* let x, y be arbitary booleans *)
  intro x. 
  intro y.
  (* consider cases for x. according to bool type def, 
  these are either either true or false *)
  destruct x. 
  - (* assume x true, and consider cases for y *)
    destruct y. 
    + reflexivity. (* assume y true; both sides are equal orb true true *)
    + simpl. (* assume y false, and evaluate orb function *)
      reflexivity. 
  - destruct y. (* assume x false, and consider cases for y *)
    + simpl. (* assume y true, and evaluate orb function *)
      reflexivity. 
    + reflexivity. (* assume y false; both sides are equal orb false false *)
  (* we have now exhausted all possible cases, 
     where commutativity holds in each case for two arbitatry booleans, 
     therefore communitivity holds in general for all pairs of booleans. *)
Qed.

Lemma orb_comm'' :
  forall b1 b2,
    orb b1 b2 = orb b2 b1.
Proof.
(* playing with a different proof style. 
   i imagine that the | separator apply to cases might work 
   where we only have two or three cases, 
   but would be excessive otherwise. *)
  destruct b1.
  - destruct b2; [reflexivity | simpl; reflexivity].
  - destruct b2; [simpl; reflexivity | reflexivity].
Qed.



(*
 * PROBLEM 4 [4 points, ~7 tactics]
 * Prove the following theorem about `notb`, `orb`, and `andb`.
 *
 * Hint: You may need fewer tactics if you use semicolon chains.
 * Hint: All these proofs start to look the same after a while...
 *)
Lemma notb_andb_is_orb_notb :
  forall b1 b2,
    notb (andb b1 b2) = orb (notb b1) (notb b2).
Proof.
  destruct b1, b2; auto.
Qed.

Lemma notb_andb_is_orb_notb' :
  forall b1 b2,
    notb (andb b1 b2) = orb (notb b1) (notb b2).
Proof.
  (* can be ever so slightly more explicit if necessary *)
  destruct b1, b2; simpl; reflexivity.
Qed.

(* --- Natural numbers practice --- *)

(*
 * Here are some more definitions from lecture,
 * this time about natural numbers.
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
 * PROBLEM 5 [4 points, ~4 tactics]
 * Prove the following theorem about add.
 *
 * Hint: Do you think you'll need induction? Hmm...
 *)
Lemma add_S_n :
  forall n1 n2,
    add (S n1) n2 = S (add n1 n2).
Proof.
  auto. (* oh, that's nice of it! no induction needed? *)
Qed.

Lemma add_S_n' :
  forall n1 n2,
    add (S n1) n2 = S (add n1 n2).
Proof.
  (* don't even need to intro n1? *)
  induction n1; simpl; reflexivity.
  (* simplification can be applied to both the base and inductive cases 
     because we are given this equality by how our add if defined,
     i.e. pattern matching on the first argument *)
Qed.

(*
 * PROBLEM 6 [8 points, ~1 sentences]
 * Consider the following theorem, superficially similar to the previous one.
 *
 * The problem below asks you to prove it, but before that, describe here
 * whether you expect it to be less difficult than, more difficult than,
 * or about the same difficulty as the previous theorem.
 *
 * Please explain your answer in 1 to 2 sentences, using your mental model
 * for what kinds of things different tactics are good at.
 *
 * Hint: If you don't know, it's okay to try to prove it (the next problem
 *       below), and then come back and explain the outcome.
 *)

(* hypothesis: 
   i think that this proof will be more difficult because 
   we are not given the equality directly by our definition of add; 
   i.e., we are not pattern matching on the second argument, which 
   in this case, has the S constructor on it. *)
Lemma add_n_S :
  forall n1 n2,
    add n1 (S n2) = S (add n1 n2).
Proof.
Abort.
  (* YOUR EXPLANATION HERE (no need to prove it yet!) *)
(* explanation: 
   here, we need to perform induction because our true statement 
   (the one above the Coq proof line) will come from the inductive hypothesis 
   instead of directly from the definition of add. 
   we are able to turn our statement into a form addressable by the IH
   given that simplification employs the definition of our add function 
   to move any S constructor in the first argument to the outside, applying 
   instead to the result of the add function. *)


(*
 * PROBLEM 7 [8 points, ~8 tactics]
 * Now go ahead and prove the theorem from the previous problem
 * (restated below).
 *
 * Hint: You may need fewer tactics than we did if you use semicolon chains.
 *
 * Hint: Do you think you'll need induction? Hmm...
 *)
Lemma add_n_S :
  forall n1 n2,
    add n1 (S n2) = S (add n1 n2).
Proof.
  (* intro n1.  *)
  induction n1.
  - simpl. reflexivity. 
  - simpl. intro n2. 
    rewrite IHn1. 
    reflexivity.
Qed.

(* using lemmas from lecture for next problem *)
Lemma add_n_O :
  forall n,
    add n O = n.
Proof.
  induction n; auto.
  simpl; f_equal.
  assumption.
Qed.

(*
 * PROBLEM 8 [15 points, ~20 tactics]
 * Prove the following theorem about add.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Don't forget to reuse previously proved Lemmas by using
 *       the `rewrite` tactic.
 *
 * Hint: It's okay to copy-paste lemmas we proved in lecture if you need them.
 *)
Lemma add_comm :
  forall n1 n2,
    add n1 n2 = add n2 n1.
Proof.
  induction n1.
  - intro n2. simpl.
    rewrite add_n_O. 
    reflexivity.
  - intro n2. simpl.
    rewrite IHn1.
    rewrite add_n_S. 
    reflexivity.
Qed.

(*
 * PROBLEM 9 [3 points, ~3 sentences]
 *
 * Please take a moment to let us know how the homework went for you by
 * answering the following three questions:
 *    1. How long did the homework take you?
 *    2. Which parts were most interesting or helpful for you?
 *    3. Which parts were especially frustrating, confusing, or tedious?
 *       What should we do better next time?
 *
 * It's fine if your answers are short if you don't have much to say!
 *)

(* 
 * 1. i think the homework took around an hour or so.
 * 
 * 2. i think the software setup was interesting because, for me, 
 * it involved setting up vim for a new language, and getting to 
 * marvel at the "coqtail" plungin's interactive mode; who needs
 * a graphical environment anyway, right? In any case, this was not 
 * quite the most helpful part, i think seeing the extent to which 
 * we can just write just, auto, or some other super-brief chain of 
 * tactics to complete a proof, versus when we need to do some actual
 * thinking, as in the case of induction, to complete our proofs. 
 * So, that was both interesting and helpful in terms of practicing using 
 * different techniques to achieve the same thing.
 * 
 * 3. i do not think any part of this homework was frustrating or tedious.
 * i think that the number of tactics suggestions were perhaps a bit confusing 
 * considering that we could use but a single tactic to complete the proof where 
 * the suggestions indicated that four might be necessary. Perhaps the brevy will 
 * detract from points? However, recalling that the point of this homework was 
 * to make sure the software is working, which, indeed, it is! 
 * 
 * [end sensible + gradable content, begin semi-random nonsense]
 * but not quite at maximum efficiency, for i have yet to memorize all the bindings... 
 * also, i considered using the Proof General for Emacs, 
 * (after all, as they say, the best editor is neither emacs nor vim alone, 
 * but emacs with vim motions) 
 * Yet, the human mind was only meant to comprehend a single font style and size 
 * at once, while hunched over in chair staring at a glass panel with millions 
 * of tiny lights flashing 240 times per second to render a terminal, of course.
 * So, not only is the ability to visually distinguish content by scale in org mode 
 * an inconceivable invention, but so too is that of the SKI combinator calculus!
 * i very much enjoy skiing, but SKIing is most intimidating... 
 * Perhaps we should work to understanding merely the Y in the λ calculus first.
 *)


(*
 * This is the end of Homework 1.  It's never too early to get started on
 * Homework 2!
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this
 * homework.
 *)
