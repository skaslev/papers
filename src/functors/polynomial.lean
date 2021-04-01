import ..data.cseq
import ..type

-- Polynomial functor
def poly (c : cseq Type*) (X : Type*) :=
Σ i : c, c i → X

namespace poly
def map {c X Y} (f : X → Y) (p : poly c X) : poly c Y :=
⟨p.1, f ∘ p.2⟩

instance {c} : functor (poly c) :=
{ map := @map c }

instance {c} : is_lawful_functor (poly c) :=
{ id_map := by intros; simp [map],
  comp_map := by intros; simp [map] }
end poly