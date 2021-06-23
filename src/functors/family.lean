import data.iso

-- Family of `X`s
-- `fam x` is a collection of `x` with length some cardinal number
def fam (X : Type*) := Σ A : Type*, A → X

namespace fam
variable {X : Type*}

-- Families can be coerced both to type and a function.
-- For example we can write the polynomial functor as
--
--   def poly (c : fam Type*) (X : Type*) :=
--   Σ i : c, c i → X
--
-- instead of the more explicit version without coercions
--
--   def poly (c : fam Type*) (X : Type*) :=
--   Σ i : c.1, c.2 i → X
instance : has_coe_to_fun (fam X) :=
{ F := λ c, c.1 → X, coe := λ c, c.2 }

instance : has_coe_to_sort (fam X) :=
{ S := Type*, coe := λ c, c.1 }

def of {A X} (f : A → X) : fam X :=
⟨A, f⟩

-- "Car Salesman: *slaps `fam.of`* this bad boy can fit a whole `f : Type* → Type*` in it."
def of_iso {f : Type* → Type*} {A} : f A ≃ of f A :=
iso.id_iso

def fam_iso {c : fam Type*} {A} : c A ≃ of c A :=
iso.id_iso

@[reducible, simp]
def mem (p : X) (c : fam X) := ∃ i : c, c i = p

instance : has_mem X (fam X) :=
⟨mem⟩

def empty : fam X := ⟨0, pempty.rec _⟩
def single {X} (x : X) : fam X := ⟨1, λ _, x⟩

instance : inhabited (fam X) :=
⟨empty⟩

def is_empty (c : fam X) := ∀ p : X, ¬p ∈ c
def is_complete (c : fam X) := ∀ p : X, p ∈ c

def empty_is_empty : is_empty (@empty X) :=
λ p ⟨i, _⟩, i.rec _

def add {A} (x : fam A) (y : fam A) : fam A :=
⟨x ⊕ y, λ i, sum.rec x y i⟩

def map {X Y} (f : X → Y) (x : fam X) : fam Y :=
⟨x.1, f ∘ x.2⟩

instance : functor fam :=
{ map := @map }

instance : is_lawful_functor fam :=
{ id_map := λ X c, by simp [functor.map, map],
  comp_map := λ A B C g h c, by simp [functor.map, map] }

def pure {X} (x : X) : fam X :=
⟨unit, λ i, x⟩

def seq {A B : Type*} (f : fam (A → B)) (x : fam A) : fam B :=
⟨f.1 × x.1, λ i, (f i.1) (x i.2)⟩

def join {X} (c : fam (fam X)) : fam X :=
⟨Σ a, (c a).1, λ i, c i.1 i.2⟩

def bind {A B} (x : fam A) (f : A → fam B) : fam B :=
join $ f <$> x

instance : has_pure fam :=
⟨@pure⟩

instance : has_seq fam :=
⟨@seq⟩

instance : has_bind fam :=
⟨@bind⟩

instance : applicative fam :=
{ pure := @pure,
  seq := @seq }

instance : monad fam :=
{ pure := @pure,
  bind := @bind }

-- Surprisingly monad laws hold only up to isomorphism
-- https://youtu.be/RDuNIP4icKI?t=13192

-- local infixl  >>= :55 := bind

-- def pure_bind {A B} (x : A) (f : A → fam B) : pure x >>= f = f x :=
-- begin
--   dsimp [pure, bind, functor.map, map, join],
--   sorry
-- end

-- def bind_assoc {A B C} (x : fam A) (f : A → fam B) (g : B → fam C) : x >>= f >>= g = x >>= λ x, f x >>= g :=
-- begin
--   dsimp [pure, bind, functor.map, map, join],
--   sorry
-- end
end fam
