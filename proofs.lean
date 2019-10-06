/- ****************** -/
/- *** PREDICATES *** -/
/- ****************** -/

/-
Define a function called isOdd that
takes an argument, n : ℕ, and returns a 
proposition that asserts that n is odd.
The function will thus be a predicate on 
values of type ℕ. Hint: a number is odd
if it's one more than an even number.
-/

def isOdd (n :ℕ) : Prop :=
  ∃ m : nat, 2 * m + 1 = n

/-
To test your predicate, use "example"
to write and prove isOdd(15).
-/

example : isOdd 15 :=
begin
unfold isOdd,
apply exists.intro 7,
apply rfl,
end

/-
Define isSmall : ℕ → Prop, to be a
predicate that is true exactly when the
argument, n, is such that n = 0 ∨ n = 1
∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5. (Don't
try to rewrite this proposition as an 
inequality; just use it as is.) 
-/

def isSmall (n :ℕ) : Prop := n = 0 ∨ n = 1
∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5

/-
Define a predicate, isBoth(n:ℕ) that 
is true exacly when n satisfies both the
isOdd and isSmall predicates. Use isOdd 
and isSmall in your answer.
-/

def isBoth (n : ℕ) : Prop := isOdd n ∧ isSmall n


/- ******************* -/
/- *** DISJUNCTIONS ***-/
/- ******************* -/

/-
Jane walks to school or she carries 
her lunch. In either case, she uses
a bag. If she walks, she uses a bag for
her books. If she carries her lunch, she
uses a bag to carry her food. So if she
walks, she uses a bag, and if she carries
her lunch, she uses a bag. From the fact
that she walks or carries her lunch, and
from the added facts that in either case 
she uses a bag, we can conclude that she 
uses a bag.

Using Walks, Carries, and Bag as names
of propositions, write a Lean example 
that asserts the following proposition; 
then prove it. 

If Walks, Carries, and Bag are 
propositions, then if (Walks ∨ Carries) 
is true, and then if (Walks implies Bag)
is true, and then if (Carries implies Bag)
is true, then Bag is true.
-/

example : ∀ (Walks Carries Bag : Prop), ((Walks ∨ Carries) ∧ (Walks → Bag)
∧ (Carries → Bag)) → Bag :=
begin
    assume W C B f,
    have f1 := f.1,
    cases f1 with w c,
    exact f.2.1 w,
    exact f.2.2 c,
end


/-
Prove the following proposition.
-/

example : 
    ∀ (P Q R : Prop), 
    (P ∧ Q) → (Q ∨ R) → (P ∨ R) :=
begin
    assume P Q R paq qar,
    exact or.inl paq.1,
end


/- ********************* -/
/- *** EXISTENTIALS  *** -/
/- ********************* -/

/-
Referring to the isBoth predicate you
defined in question #1, state and prove 
the proposition that there *exists* a 
number, n, that satisfies isBoth. Remember 
that you can use the unfold tactic to 
expand the name of a predicate in a goal.
Use "example" to state the proposition.
-/


lemma pf3isOdd : isOdd 3 :=
begin
unfold isOdd,
apply exists.intro 1,
apply rfl,
end

lemma pf3isSmall : isSmall 3 :=
begin
unfold isSmall,
apply or.intro_right,
apply or.intro_right,
apply or.intro_right,
apply or.intro_left,
apply rfl,
end

example : ∃ n : ℕ, isBoth n :=
begin
unfold isBoth,
apply exists.intro 3,
have pfOdd := pf3isOdd,
have pfSmall := pf3isSmall,
exact and.intro pfOdd pfSmall,
end


/-
Suppose that Heavy and Round are
predicates on values of any type, T.
Prove the proposition that if every 
t : T is Heavy (satisfies the Heavy 
predicate) and if there exists some 
t : T that is Round (satisfies the
Round predicate) then there exists 
some t : T is both Heavy and Round
(satisfies the conjunction of the
two properties). 
-/

example : 
∀ T : Type, ∀ (Heavy Round : T → Prop),
(∀ t, Heavy t) → (∃ t, Round t) →
(∃ t, Heavy t ∧ Round t) :=
begin
    assume T h r aht ert,
    apply exists.elim ert,
    assume x rt,
    apply exists.intro x,
    exact and.intro (aht x) rt,
end