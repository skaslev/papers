import ..type

-- Cardinal sequence
-- `cseq x` is a sequence of `x` with length some cardinal number
@[reducible, simp]
def cseq (X : Type*) := Σ I : Type*, I → X

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
def is_full  (c : cseq X) := ∀ p : X,  p ∈ c

def empty_is_empty : is_empty (@empty X) :=
λ p ⟨i, _⟩, i.rec _
end cseq
