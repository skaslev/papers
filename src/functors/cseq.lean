import ..type

-- Cardinal sequence aka "polynomial functor"
-- `cseq x` is a sequence of `x` with length some cardinal number
def cseq (X : Type*) := Σ A : Type*, A → X

namespace cseq
variable {X : Type*}

-- Cardinal sequences can be coerced both to type and a function.
-- For example we can write the polynomial functor as
--
--   def poly (c : cseq Type*) (X : Type*) :=
--   Σ i : c, c i → X
--
-- instead of the more explicit version without coercions
--
--   def poly (c : cseq Type*) (X : Type*) :=
--   Σ i : c.1, c.2 i → X
instance : has_coe_to_fun (cseq X) :=
{ F := λ c, c.1 → X, coe := λ c, c.2 }

instance : has_coe_to_sort (cseq X) :=
{ S := Type*, coe := λ c, c.1 }

@[reducible, simp]
def mem (p : X) (c : cseq X) := ∃ i : c, c i = p

instance : has_mem X (cseq X) :=
⟨mem⟩

def empty : cseq X := ⟨0, pempty.rec _⟩
def single {X} (x : X) : cseq X := ⟨1, λ _, x⟩

instance : inhabited (cseq X) :=
⟨empty⟩

def is_empty (c : cseq X) := ∀ p : X, ¬p ∈ c
def is_complete  (c : cseq X) := ∀ p : X,  p ∈ c

def empty_is_empty : is_empty (@empty X) :=
λ p ⟨i, _⟩, i.rec _

def map {X Y} (f : X → Y) (x : cseq X) : cseq Y :=
⟨x.1, f ∘ x.2⟩

instance : functor cseq :=
{ map := @map }

instance : is_lawful_functor cseq :=
{ id_map := λ X c, by simp [functor.map, map],
  comp_map := λ A B C g h c, by simp [functor.map, map] }

def pure {X} (x : X) : cseq X :=
⟨unit, λ i, x⟩

def seq {A B : Type*} (f : cseq (A → B)) (x : cseq A) : cseq B :=
⟨f.1 × x.1, λ i, (f i.1) (x i.2)⟩

def join {X} (c : cseq (cseq X)) : cseq X :=
⟨Σ a, (c a).1, λ i, c i.1 i.2⟩

def bind {A B} (x : cseq A) (f : A → cseq B) : cseq B :=
join $ f <$> x

instance : has_pure cseq :=
⟨@pure⟩

instance : has_seq cseq :=
⟨@seq⟩

instance : has_bind cseq :=
⟨@bind⟩

instance : applicative cseq :=
{ pure := @pure,
  seq := @seq }

instance : monad cseq :=
{ pure := @pure,
  bind := @bind }

-- Surprising monad laws hold only up to isomorphism
-- https://youtu.be/RDuNIP4icKI?t=13192

-- local infixl  >>= :55 := bind

-- def pure_bind {A B} (x : A) (f : A → cseq B) : pure x >>= f = f x :=
-- begin
--   dsimp [pure, bind, functor.map, map, join],
--   sorry
-- end

-- def bind_assoc {A B C} (x : cseq A) (f : A → cseq B) (g : B → cseq C) : x >>= f >>= g = x >>= λ x, f x >>= g :=
-- begin
--   dsimp [pure, bind, functor.map, map, join],
--   sorry
-- end
end cseq
