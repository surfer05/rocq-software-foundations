# Software Foundations — Personal Solutions (Self-Study)

This repository contains **my own** Coq/Rocq proof scripts and notes while working through exercises from **Software Foundations, Volume 1: Logical Foundations**.

These are **not official solutions**, not endorsed by the authors, and may be incomplete, inelegant, or simply wrong in places.

## What this is

- A scratchpad / archive of *my* attempts at the exercises
- Extra lemmas, alternative proofs, and small experiments I found helpful


## What this is not

- Not an “answer key”
- Not guaranteed-correct solutions
- Not something to use for coursework / graded assignments


## Book reference

- Software Foundations (Logical Foundations):  
  https://softwarefoundations.cis.upenn.edu/lf-current/

- Example chapter link (Basics):  
  https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html

Note: the text sometimes says **Coq** and sometimes **Rocq** (the project is in a transition period).

## Repo layout (example)

- `Basics.v`, `Lists.v`, `Poly.v`, ...: my working files for each chapter
- `Makefile`, `_CoqProject`: build configuration (if present)

## Build / check

If you have a Makefile already:

```bash
make
```

Clean build artifacts:

```bash
make clean
```

If your repo uses `_CoqProject`, you can typically regenerate a makefile like this:

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

## Conventions (mine)

- I try to keep proofs readable over clever.
- When something gets messy, I add helper lemmas rather than piling on tactics.


## About sharing

These are exercise solutions. If you’re using Software Foundations for a class or self-study, consider keeping solutions **private** to avoid spoiling the learning process for others.

## License

My contributions in this repo are mine.

The upstream **Software Foundations** materials (text and accompanying files) have their own licensing terms—please refer to the official site for details.



