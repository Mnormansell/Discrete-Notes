/-
This in-class exercise requires solutions to two problems
-/

/-
PROBLEM #1. 

In Lean, define pf1 to be a proof of the proposition
that, "for any proposition, Q, ¬ (Q ∧ ¬ Q). We write
this as ∀ Q : Prop, ¬ (Q ∧ ¬ Q). In English it says,
it's not possible for any proposition to be both true
and false. 

There are at least three forms a solution can take.

#1. You can prove the proposition by declaring
pf1 to be a proof (value) of the proposition/type
as written, then use a lambda expression to give
the actual proof term. Here we give you the first
line of the lambda, which you can read as either
(A) "a function that takes a proposition Q as an
argument and that returns ...", or as (B) "assume
Q is some proposition and then return ..." You 
have to fill in the _. You know of course that 
it could be another lambda expression.

theorem pf1 : ∀ Q : Prop, ¬ (Q ∧ ¬ Q)  :=
    λ (Q : Prop),
        _

#2: You can use an equivalent tactic script. It 
will start like this:

theorem pf1' : ∀ Q : Prop, ¬ (Q ∧ ¬ Q)  :=
assume Q : Prop,
...

You have to fill in the rest in place of the
elipsis.

#3: You can prove the theorem by writing an
ordinary function. It'd start like this:

theorem pf1'' (Q : Prop) (pfQnQ : Q ∧ ¬ Q) : false :=
_

Again you have to replace the _ with "code"
that constructs the required proof.

For extra credit, give the answer in all three
forms.

Here are some extra hints.

Hint #1: Remember that, assuming that A is any
proposition (such as Q ∧ ¬ Q), ¬ A simply means 
(A → false). So what does ¬ (Q ∧ ¬ Q) mean? That
is the proposition you need to prove, and its 
form will tell you a lot about what for a proof
has to have.

Hint #2: Hover your mouse cursor over the underscores
in the preceding code. That will tell you exactly 
what proof you need to fill in in place of the _.

Hint #3: (Q ∧ ¬ Q) → false is an implication. 
Remember what a proof of an implication looks like. 
Use a corresponding expression in place of the _.
Yes, we're repeating the same hint as before but
using other words.

Hint #4: Remember the elimination rules for ∧. If
you assume you have a proof of (Q ∧ ¬ Q) what two
smaller proofs can you derive from it?

Hint #5: Remember again: ¬ Q  means (Q → false).
If you have a proof of Q → false, then you have
a function that, if it is given an assumed proof
of Q, reduces it to a proof of false. Look for a
way to get this function and then to apply it to
a proof of Q!
-/

/- SOLUTION #1 -/

theorem pf1 : ∀ Q : Prop, ¬ (Q ∧ ¬ Q)  :=
    λ (Q : Prop) (q : (Q ∧ ¬ Q)),
        q.2 q.1

/- SOLUTION #2 -/

theorem pf1' : ∀ Q : Prop, ¬ (Q ∧ ¬ Q)  :=
    begin
        assume Q : Prop,
        assume q : (Q ∧ ¬ Q),
        show false,
        from q.2 q.1
    end

/- SOLUTION #3 -/

theorem pf1'' (Q : Prop) (pfQnQ : Q ∧ ¬ Q) : false :=
    begin
        have pfQ := and.elim_left pfQnQ,
        have pfnQ := and.elim_right pfQnQ,
        exact pfnQ pfQ
    end
/-
PROBLEM #2.

Produce a proof, pf2, of the proposition, that 
for any propositions, P and Q, (P ∧ Q) ∧ (P ∧ ¬ Q) 
→ false. (You could of course also write this as
¬ ((P ∧ Q) ∧ (P ∧ ¬ Q)). You can use the partial 
solutions we gave for the last problem as models. 
Start by assuming (P Q : Prop) rather than just
Q : Prop. Hint: Remember the and elimination rules.
Look for ways to extract from the assumed proof
the other proofs that you'll need to combine in
some way to construct a proof of false. You may
provide your answer in any of the three forms we
discussed. For extra credit, provide it in all
three forms.
-/

/- #1 -/

theorem pf2 : 
    ∀ P Q : Prop, (P ∧ Q) ∧ (P ∧ ¬ Q) → false :=
        λ (P Q : Prop),
            λ (p : (P ∧ Q) ∧ (P ∧ ¬ Q)),
                (p.2).2 (p.1).2
/- #2 -/

theorem pf2' : 
    ∀ P Q : Prop, (P ∧ Q) ∧ (P ∧ ¬ Q) → false :=
        begin
            assume P Q : Prop,
            assume p : (P ∧ Q) ∧ (P ∧ ¬ Q),
            show false,
            from (p.2).2 (p.1).2
        end 

/- #3 -/

theorem pf1''' (P Q : Prop) (pf : (P ∧ Q) ∧ (P ∧ ¬ Q)) : false :=
    begin
    have pfL := and.elim_left pf,
    have pfR := and.elim_right pf,
    have pfQ := and.elim_right pfL,
    have pfnQ := and.elim_right pfR,
    exact pfnQ pfQ
    end
