import category.kan
import functors.family

def fam.lan_iso {A} : fam A ≃ lan id (const 1) A :=
iso.sigma_subst (λ x, iso.mul_one_right)

def one.ran_iso {A} : 1 ≃ ran id (const 1) A :=
(iso.pi_one⁻¹ ⋆ iso.pi_sigma_curry⁻¹ : 1 ≃ Π B:Type*, (A → B) → 1)
