import data.iso
import functors.family

-- Polynomial functor
def poly (c : fam Type*) (X : Type*) :=
Σ i : c, c i → X

-- Polynomial functor given by the fibers of `f`
-- as in "Polynomial Functors and Polynomial Monads"
-- https://arxiv.org/pdf/0906.4931.pdf
def poly' {A B} (f : B → A) :=
poly (fam.fibers f)

namespace poly
def map {c X Y} (f : X → Y) (p : poly c X) : poly c Y :=
⟨p.1, f ∘ p.2⟩

instance {c} : functor (poly c) :=
{ map := @map c }

instance {c} : is_lawful_functor (poly c) :=
{ id_map := by intros; simp [functor.map, map],
  comp_map := by intros; simp [functor.map, map] }

def has_poly {F : Type* → Type*} (c : fam Type*) (A) :=
F A ≃ poly c A

def has_poly' {F : Type* → Type*} {B C} (c : B → C) (A) :=
F A ≃ poly' c A

def has_poly'' {F : Type* → Type*} {C} (s : Π A, F A → C) (A) :=
F A ≃ poly' (s A) A

end poly
