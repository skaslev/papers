import data.iso
import functors.family

-- Polynomial functor
-- poly(c) = Σ i:c, x^c(i)
def poly (c : fam Type*) (X : Type*) :=
Σ i : c, c i → X

-- qpf(c,r) = Σ i:c, x^c(i) / r(i)
def qpf (c : fam Type*) (r : Π i A, rel (c i → A)) (A : Type*) :=
Σ i : c, quot (r i A)

-- poly(c) ↪ qpf(c, ordered)
def poly.lift_qpf {c A} (x : poly c A) : qpf c (λ _ _, eq) A :=
⟨x.1, quot.mk _ x.2⟩

namespace poly
-- Polynomial functor given by the fibers of `f`
-- as in "Polynomial Functors and Polynomial Monads"
-- https://arxiv.org/pdf/0906.4931.pdf
def from_fiber {B A} (f : B → A) :=
poly ⟨A, fiber f⟩

def from_fiber' {A} (f : fam A) :=
poly ⟨A, fiber f⟩

def map {c X Y} (f : X → Y) (p : poly c X) : poly c Y :=
⟨p.1, f ∘ p.2⟩

instance {c} : functor (poly c) :=
{ map := @map c }

instance {c} : is_lawful_functor (poly c) :=
{ id_map := by intros; simp [functor.map, map],
  comp_map := by intros; simp [functor.map, map] }

def has_poly {F : Type* → Type*} (c : fam Type*) (A) :=
F A ≃ poly c A

def has_poly_fiber {F : Type* → Type*} {B C} (c : B → C) (A) :=
F A ≃ from_fiber c A

end poly
