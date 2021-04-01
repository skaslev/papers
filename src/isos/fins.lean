import .list

namespace fins
-- 0⁰ = 1
def one_iso : fin 0 → fin 0 ≃ 1 :=
⟨λ x, (),
 λ x, fin.elim0,
 λ x, funext (λ y, fin.elim0 (x y)),
 λ x, by induction x; refl⟩

-- 0ⁿ⁺¹ = 0
def zero_iso {n} : fin (n + 1) → fin 0 ≃ 0 :=
⟨λ x, by have z : fin 0 := x 0; exact fin.elim0 z,
 λ x, pempty.rec _ x,
 λ x, funext (λ y, fin.elim0 (x y)),
 λ x, pempty.rec _ x⟩

-- Σ k:ℕ, nᵏ = 1/(1-n)
def list_iso {n} : (Σ k, fin k → fin n) ≃ list (fin n) :=
list.geom_iso⁻¹

def cf (n k : ℕ) := n^k

-- Σ k:ℕ, nᵏ = Σ k:ℕ, cₖ 1ᵏ
-- cₖ = {1, n, n², n³, n⁴, ...}
def ogf_iso {n} : (Σ k, fin k → fin n) ≃ ogf (cf n) 1 :=
iso.sigma_subst (λ k, iso.mul_one_right ⋆ iso.mul fin.pow_iso fseq.one_iso₂⁻¹)
end fins
