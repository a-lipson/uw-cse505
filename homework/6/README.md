# Homework 6

## Setup

This homework has the same setup as previous homework assignments. As you did
for previous assignments, please ensure that the Rocq compiler `coqc` is in one
of the directories included in your `$PATH` environment variable.

You can build the homework using `make`:
```
make
```

Building the homework should take just a few seconds.

You can also run our autograder locally by running `make grade`. It will tell
you if you changed of the starter code you weren't supposed to, and if you have
any `admit`s left to solve.

If you are using Windows powershell and the scoop package manager, the Makefile
should still work if you do
```
scoop install zip busybox
```
The busybox dependency adds several Unix utilities used by the scripts.

## Doing the Homework

The `Makefile` is good for checking the entire file, but when you are working on
solving a problem, you should use VSCode (or another editor with interactive Rocq
support) to work interactively. Don't be constantly switching to the terminal to
run `make` every time you take one step in the proof.


## Submitting Homeworks

Upload `HW5.v` to the 505 Gradescope linked from the course website.

Please make sure to upload to the correct assignment and add your partner(s) on
the Gradescope submission page!

We have set up Gradescope to run an autograder to check that your submission
compiles, and that it does not contain `admit`s. However, **points are assigned
manually** by course staff, so please ignore the points that come from the
autograder. The purpose of the autograder is only to help you know whether your
code is going to work on our machines. Also, consider this fair warning that the
autograder does not check everything about the homework. For example, if the
homework asks you write a comment, or to *state* and prove a theorem, those will
not be checked by the autograder.

Remember, you can run `make grade` to run the autograder on your machine without
having to upload to Gradescope, if you just want to see how you are doing so
far.


## How you will be assessed

We will award points according to the breakdown in the `.v` file for problems
that you solve. If you make a good faith attempt to solve a problem, we will
award partial credit. There may be small deductions for violations of the
style guide linked from the course website.


## Tactic Hints

Below is a list of tactics we used in our solution. We provide this list **for
guidance only**. You might not need to use all these tactics in your solutions,
and it's also fine if you use tactics not listed here. We hope this list might
help you in case you get stuck or if you want to learn more about the zoo of
available tactics :)

In our solutions we used the following tactics:
  - [apply](https://docs.google.com/document/d/17YpDAbrUMukAuaaID8o4iQh8H_YJxChTzmH_y3yw1Kk/edit?tab=t.0#bookmark=id.6hj9bgx79d4q)
  - [congruence](https://docs.google.com/document/d/17YpDAbrUMukAuaaID8o4iQh8H_YJxChTzmH_y3yw1Kk/edit?tab=t.0#bookmark=kix.whozx6ybsumx)
  - eauto
  - [f_equal](https://docs.google.com/document/d/17YpDAbrUMukAuaaID8o4iQh8H_YJxChTzmH_y3yw1Kk/edit?tab=t.0#bookmark=kix.u5onr74tkc21)
  - [induction](https://docs.google.com/document/d/17YpDAbrUMukAuaaID8o4iQh8H_YJxChTzmH_y3yw1Kk/edit?tab=t.0#bookmark=id.vdd8yhofsq41)
  - [intros](https://docs.google.com/document/d/17YpDAbrUMukAuaaID8o4iQh8H_YJxChTzmH_y3yw1Kk/edit?tab=t.0#bookmark=id.ctlk62idrwvx)
  - invc
  - revert
