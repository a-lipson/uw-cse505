# Homework 1

## Setup

Follow the 505 Software Setup Instructions from the course website to install
Rocq and VSCode.

Please ensure that the Rocq compiler `coqc` is in one of the directories included
in your `$PATH` environment variable.

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

Upload `HW1.v` to the course Gradescope. You can find the course Gradescope
(and an add code if you need it) on the course website.

Please make sure to upload to the correct assignment!

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

The purpose of this homework is to ensure you have Rocq installed and can
interactively edit proofs in VSCode. For this homework, we will grade each
problem solely based on whether you attempted it (in good faith), not whether
you were able to solve it or not. So, if you attempt all the problems, you will
receive the full 50 points this week. Besides making sure you have things
installed, this also gives the staff an opportunity to provide you with feedback
about proof style.

Future homeworks will be graded slightly more strictly than this, where for full
points, you will actually have to solve the problems, and violations of the
style guide will incur some (small) penalty. See the course website for the
style guide and the grading rubric for future homeworks.


## Tactic Hints

Below is a list of tactics we used in our solution. We provide this list **for
guidance only**. You might not need to use all these tactics in your solutions,
and it's also fine if you use tactics not listed here. We hope this list might
help you in case you get stuck or if you want to learn more about the zoo of
available tactics :)

In our solutions we used the following tactics:
  - [destruct](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.31h1z5e3u3wt)
  - [induction](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.vdd8yhofsq41)
  - [intros](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.ctlk62idrwvx)
  - [reflexivity](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.w7wn2c8h0zwt)
  - [rewrite](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.hge0chk9zpao)
  - [simpl](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.tglpvbqrvega)
