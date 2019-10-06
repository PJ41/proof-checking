
def proper_subset : 
  ∀ { α : Type }, 
    set α → set α → Prop :=
  λ α x y, forall (e : α), 
    (e ∈ x → e ∈ y) ∧ (∃ f, f ∈ y ∧ f ∉ x) 

example : 
  ∀ a b c : ℕ, a = b → b = c → a = c  
:=
begin
intros a b c,
assume ab bc,
rewrite ab,
rw bc, -- shorthand
-- and rw does rfl for us
end

example : 
  ∀ a b c : ℕ, a = b → b = c → a = c  
:=
begin
intros a b c,
assume ab bc,
rewrite ←bc,
rw ←ab, 
end

example : ∀ n : ℕ, true :=
begin
assume n,
cases n,  -- whoa, that's cool
trivial,
trivial,
end

example : ∀ P Q : Prop, P ∨ Q → true :=
begin
intros P Q,
assume h,
cases h, -- whoa, now I get it!
trivial,
trivial
end

example : 4 = 5 → 0 = 1 :=
begin
assume four_equals_five,
cases four_equals_five, --whoa!
end

example : 
proper_subset  
  { 1, 3 } 
  { n | ∃ m, n = 2 * m + 1 } 
:=
begin
unfold proper_subset,
intro o,
split,
assume h,

cases h,
apply exists.intro 1,
assumption,

cases h,
apply exists.intro 0,
assumption,

cases h,
apply exists.intro 5,

split,
apply exists.intro 2,
exact rfl,


intro h,
cases h,
cases h,
cases h,
cases h,
cases h,
end

lemma quiz : proper_subset { 1, 2 } { n : nat | true } :=
begin
unfold proper_subset,
assume n,
split,
assume f,
trivial,
apply exists.intro 5,
split,
trivial,
assume fn12,
cases fn12,
cases fn12,
cases fn12,
cases fn12,
cases fn12,
end