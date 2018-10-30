/-
You need to understand the following
elements of automated predicate logic 
for Exam 2

Suppose P and Q are arbitrary propositions 
(i.e., P Q : Prop) and T and V are arbitrary
types (i.e., T V : Type). 

Know the following forms, how to prove them, 
how to use proofs of them, and how to do these 
things in Lean. 

To know how to prove them and how to use proofs
of them, you need an intuitive understanding of
the introduction and elimination rules for each
form, and how to use them in Lean.

* true : Prop
* false : Prop
* =                    -- equality
* P ∧ Q : Prop
* (∀ p : P, Q) : Prop  -- Q can involve p
* T → V : Type         -- function type)
* P → Q : Prop         -- implication)
* ¬ P : Prop
* P ↔ Q : Prop
* P ∨ Q : Prop
* (∃ p : P, Q) : Prop  -- Q can involve p
* T → Prop             -- a property of Ts
* T → V → Prop         -- a T-V binary relation

Knowing this material, you are also expected to be
able to combine these reasoning rules to prove more 
interesting propositions. In general, such a proof
first applies elimination rules to obtain additional 
useful elements from given assumptions, and then uses 
introduction  rules to combine the elements obtained 
into proofs of desired conclusions. 

You should have an intuitive understanding of the
meaning of each form and how to use each form in 
logical reasoning. In particular, understand (1)
the introduction rules for each -- how to construct
proofs in these forms -- and (2) the elimination
rules for each form -- how to use proofs in these 
forms to obtain additional facts to be used in 
constructing proofs of other propositions.

For extra credit, be able to work in Lean with
(1) propositions and proofs involving combinations 
of quantifiers, such as (∀ x : X, ∃ y : Y, Z) and
(∃ x : X, ∀ y : Y, Z), and with (2) negations of 
quantified propositions, such as ¬ (∃ p : P, Q) 
and ¬ (∀ p : P, Q).

The test will be structured to help you to know and
to show how far you've gotten and where you still 
have some work to do. 

Here are exercises for each form.
-/

/- ***************************************** -/
/- ***************** true ****************** -/
/- ***************************************** -/

/- 
(1)

Use "example" in Lean to prove that there
is a proof of true.  Be sure that after the :=
you can provide a proof using both an expression
and a tactic script.
-/

example : true := true.intro


example : true :=
    begin
    apply true.intro,
    end

/- ***************************************** -/
/- ***************** false ***************** -/
/- ***************************************** -/

/-
(2)
Use "def" in Lean to define a function, fq, 
that proves that if P and Q are propositions 
and if Q is true then false → ¬ Q.
-/

def fq (P : Prop) (Q : Prop) (pfq : Q) : false → ¬ Q :=
    begin
    assume f,
    assume q,
    show false,
    from false.elim f,
    end

/-
(3)
Use "example" in Lean to prove that if 0 = 1
then 0 ≠ 1.
-/

example : (0 = 1) → (0 ≠ 1) :=
    λ h : (0 = 1), 
        nat.no_confusion h

/-
(4) Use "example" to prove that for any two
natural numbers, a and b if a = b then if 
b ≠ a then a ≠ b.
-/

example (a : ℕ) (b : ℕ) : a = b → b ≠ a → a ≠ b :=
    begin
    assume ab nba nab,
    show false,
    from
        begin
            have ba := eq.symm ab,
            exact false.elim (nba ba),
        end,
    end

example (a : ℕ) (b : ℕ) : a = b → b ≠ a → a ≠ b :=
    λ ab nba nab, false.elim (nba (eq.symm ab))


/- ***************************************** -/
/- ***************** and ******************* -/
/- ***************************************** -/

/-
(5) 

Use "example" to prove that if P, Q, and R 
are propositions, P → Q → R → (P ∧ Q) ∧ R
-/

example (P Q R : Prop): P → Q → R → (P ∧ Q) ∧ R :=
    λ P Q R, and.intro (and.intro P Q) R
/-
(6) 

Use "example" to prove that if P, Q, and R 
are propositions, (P ∧ Q) ∧ R → P ∧ R.
-/

example (P Q R : Prop): (P ∧ Q) ∧ R → P ∧ R :=
    begin
        assume pqr,
        have pq : P ∧ Q := pqr.1,
        have p : P := pq.1,
        have r : R := pqr.2,
        exact and.intro p r,
    end

example (P Q R : Prop): (P ∧ Q) ∧ R → P ∧ R :=
    λ pqr, and.intro ((pqr.left).left) pqr.2

/- ***************************************** -/
/- *************** functions *************** -/
/- ***************************************** -/

/-
(7) Use example to prove that if S and T 
are arbitrary types and if there is a value, 
t : T, then S → T. Remember that a proof of 
S → T has to be a function that if given any 
value of type S returns some value of type T.

Present this proof as a Python-style function
definition, isFun, then using a tactic script. 
The Π you can read and treast as ∀, for now.
-/

example (S T : Type) (t : T) : S → T :=
    λ s, t

example (S T : Type) (t : T) : S → T :=
    begin
    assume s,
    exact t,
    end

/-
(8) use def to define comp to be a function 
that takes as its argments, the types S, T, 
and R, along with a function of type S → T 
and a function of type T → R and that returns 
a function of type S → R. It should take S,
T, and R implicitly and st and tr explicitly.
-/

def comp (S T R : Type) : (S → T) → (T → R) → (S → R) :=
    λ st tr s, tr (st s)

/-
(9) Define square to be a function that
takes a natural number and returns its
square, and inc to be a function that
takes a nat, n, and returns n + 1. Now
use def and comp to define incSquare to
be a function that takes a nat, n, as an
argument and that returns one more than
n^2. Use #reduce to check that the value
of (incSquare 5) is 26. 
-/

def square : ℕ → ℕ :=
    λ n, n*n

def inc : ℕ → ℕ :=
    λ n, n + 1

def incSquare : ℕ → ℕ := sorry

/-
(10)

Consider the function, sum4, below. What
is the type of (sum4 3 7)? What function is
(sum4 3 7)? Answer the second question 
with a lambda abstraction.
-/

--(sum4 3 7) likely has type ℕ → ℕ → ℕ
--this might be it, no clue why it would be called
--sum4
def sum4 : ℕ → ℕ → ℕ :=
    λ n m, n + m 

/- ***************************************** -/
/- ************** implication ************** -/
/- ***************************************** -/

/-
(11)

Use several "examples" to prove (1) false → false, 
(2) false → true, (3) ¬ (true → false).
-/

example : false → false :=
    λ f, false.elim f

example : false → true :=
    λ f, false.elim f

example : ¬ (true → false) :=
    begin
        assume TtoF,
        exact false.elim (TtoF true.intro),
    end

/-
(12)

Use example to prove that for any two 
propositions, P, Q, if P ∧ Q is true
then if ¬ (P ∨ Q) is true, then you 
can derive a proof of false.
-/

example (P Q : Prop) : (P ∧ Q) → ¬ (P ∨ Q) → false :=
    begin
        assume pq nporq,
        cases pq with p q,
        exact nporq (or.intro_left Q p),
    end

/- ***************************************** -/
/- *************** forall (∀) ************** -/
/- ***************************************** -/

/-
(13) 

Use example to prove that for all proposition,
P, Q, and R, if P → Q → R then P → R.
-/

example : ∀(P Q R : Prop), (P → Q → R) → (P → R) :=
    λ P Q R,
        λ pqr p,
            pqr p sorry -- error here as I do not how to get q here by this def
--if this is not the right function, and this is

/-
(14)

Prove that for any type, T, for any a : T, 
and for any property, (P : T → Prop), if 
(∀ t : T, P t), then P a.
-/

example : ∀(T : Type), ∀ (a : T), ∀(P : T → Prop), (∀ t : T, P t) → P a :=
    begin
        intros,
        exact a_1 a,
    end


/- ***************************************** -/
/- *************** negation **************** -/
/- ***************************************** -/

/-
(15) 

Show that for any propositions, P and Q, 
¬ ((P ∧ Q) ∧ ((P ∧ Q) → (¬ Q ∧ P)).
-/

example : ∀(P Q : Prop), ¬ ((P ∧ Q) ∧ ((P ∧ Q) → (¬ Q ∧ P))) :=
    begin
        intros,
        assume pf,
        show false,
        from
            begin
            cases pf with left right,
            have nqandp := right left,
            exact nqandp.1 left.2,
            end,
    end
/-
(16)

Prove that for any propositions, P and R, 
if P → R  and ¬ P → R, then R. You might 
need to use the law of the excluded middle.
-/
open classical

example : ∀(P R : Prop), (P → R) → (¬P → R) → R :=
    begin
        intros,
        cases em P with p np,
        --p
        show R,
        from a p,
        --np
        show R,
        from a_1 np, 
    end

/- ***************************************** -/
/- ************* bi-implication ************ -/
/- ***************************************** -/

/-
(17)

Prove that for any propositions P and Q, 
(P -> Q) ∧ (Q → P) → (P ↔ Q).
-/
example : ∀(P Q : Prop), (P -> Q) ∧ (Q → P) → (P ↔ Q) := 
    begin
        assume P Q pf,
        cases pf with left right pf,
        exact iff.intro left right,
    end
/-
(18)

Prove that for propositions P and Q,
((P ↔ Q) ∧ P) → Q.
-/

example : ∀(P Q : Prop), ((P ↔ Q) ∧ P) → Q :=
    begin
        assume p q pf,
        cases pf with left right,
        exact (iff.elim_left left) right,
    end

/- ***************************************** -/
/- ************** disjunction ************** -/
/- ***************************************** -/

/-
(19)

Prove that if you eat donuts or if you eat
candy you will get cavities. The proposition
you prove should build in the assumptions 
that if you eat donuts you will get cavities
and if you eat candy you will get cavities. 
We start the proof for you. You complete it.
Start your proof like this:

example : ∀ donut candy cavity : Prop, ...
-/

example : ∀ donut candy cavity : Prop, ((donut → cavity) ∧ (candy → cavity)) → (donut ∨ candy) → cavity :=
    begin
        intros,
        cases a with left right,
        cases a_1 with donut candy,
        exact left donut,
        exact right candy,
    end

/-
(20)

Prove that if P and Q are any propositions, and
if you have a proof of ¬(P ∨ Q) then you can
construct a proof of ¬ P.
-/

example : ∀ (P Q : Prop), ¬(P ∨ Q) → ¬ P :=
    begin
        intros,
        assume p,
        exact a (or.intro_left Q p),
    end

/-
(21)

Show, without using em explicitly, that if
for any proposition, P, P ∨ ¬ P, then for any
proposition, Q, ¬ ¬ Q → Q. The proposition to 
prove is (∀ P : Prop, P ∨ ¬ P) → (∀ Q, ¬¬ Q → Q).
Remember that a proof of (∀ P, S) can be applied
to a value of type P to get a value of type S.
-/

example : (∀ P : Prop, P ∨ ¬ P) → (∀ Q, ¬¬ Q → Q) :=
    begin
        intros,
        cases a Q with q nq,
        --Q
        assumption,
        --nQ
        show Q,
        from false.elim (a_1 nq),
    end

/- ***************************************** -/
/- **************** predicates ************* -/
/- ***************************************** -/


/-
(22)

Define notZero(n) to be a predicate on
natural numbers that is true when 0 ≠ n
(and false otherwise). Then prove two facts 
using "example." First, ¬ (notZero 0). When
doing this proof, remember what (notZero 0)
means, and remember what negation means.
Second, prove (notZero 1).
-/

def notZero : ℕ → Prop := 
    λ n, n ≠ 0

#check notZero 2
#reduce notZero 5

example : notZero 1 :=
    begin
    unfold notZero,
    assume eq,
    show false,
    from nat.no_confusion eq,
    end

example : ¬ (notZero 0) :=
    begin
    unfold notZero,
    assume neq,
    show false,
    from neq (eq.refl 0),
    end

/-
(23)

Define eqString(s, t) to be a predicate on
values of type string, that is true when
s = t (and not true otherwise). Then prove: 
eqString "Hello Lean" ("Hello " ++ "Lean")
-/

def eqString : string → string → Prop :=
    λ s t,
        string.length s = string.length t
    sorry --how does this work

/- ***************************************** -/
/- **************** exists ***************** -/
/- ***************************************** -/

/-
(24) 

Prove that ∃ n : ℕ, n = 13. 
-/

example :  ∃ n : ℕ, n = 13 :=
    begin
        apply exists.intro 13,
        apply eq.refl 13,
    end
    
/-
(25)

Prove ∀ s : string, ∃ n, n = string.length s.
-/
example : ∀(s : string), ∃ n, n = string.length s :=
    begin
        assume str,
        apply exists.intro 5,
        sorry
    end



/-
(26)

Prove exists m : ℕ, exists n: ℕ, m * n = 100.
Remember that you can apply exists.intro to a
witness, leaving the proof to be constructed
interactively.
-/

example : ∀(m : ℕ), exists n: ℕ, m * n = 100 :=
    begin
        intros,
        apply exists.intro 10,
        sorry
    end

/-
(27)

Prove that if P and S are properties of 
natural numbers, and if (∃ n : ℕ, P n ∧ S n), 
then (∃ n : ℕ, P n ∨ S n). 
-/

example : (∃ n : ℕ, P n ∧ S n), (∃ n : ℕ, P n ∨ S n)


