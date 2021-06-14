import functors.cseq
import isos.nat

open cseq

@[reducible, simp]
def statement (M : Type*) := M → Type*

def proof {M} (c : statement M) := Π m, c m

@[reducible, simp]
def statements (M) := cseq (statement M)

def proofs {M} (c : statements M) := Π i, proof (c i)

def theorems (M) := Σ c : statements M, proofs c

def theory (M) := theorems M → theorems M

def is_complete {M} (c : theorems M) := c.1.is_complete

section examples
def ex₁ : theorems ℕ :=
⟨single $ λ n : ℕ, Σ' m : ℕ, n + 1 = m,
 λ _ n, ⟨n+1, rfl⟩⟩

def ex₂ : theorems Type :=
⟨single $ λ T, (T ≃ ℕ) → (T ⊕ 1 ≃ T),
 λ _ T f, iso.add_left f ⋆ iso.add_comm ⋆ nat.def_iso⁻¹ ⋆ f⁻¹⟩
end examples
