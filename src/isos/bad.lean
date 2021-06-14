import isos.list

namespace bad₁
-- c = a + bc  ⇒  c - bc = a  ⇒  c(1-b) = a  ⇒  c = a/(1-b)
-- yet `linear` is false because that would imply `1 ≃ 0`
-- 1 = 0 + 1×1 ⇒ 1 = 0 × list(1) = 0, _|_
variable linear : Π {A B C : Type}, (C ≃ A ⊕ B × C) → (C ≃ A × list B)

def wat : 1 ≃ 0 :=
linear id.linear ⋆ iso.mul_zero_left⁻¹
end bad₁

namespace bad₂
-- this is also false since it implies `1 ≃ ℕ`
-- 1 = 0 + 1×1 ⇒ 1 = 0 + 1×list(1) = ℕ, _|_
variable linear : Π {A B C : Type}, (C ≃ A ⊕ B × C) → (C ≃ A ⊕ B × list B)

def wat {A} : A ≃ ℕ :=
linear id.linear ⋆ iso.add_zero_left⁻¹ ⋆ iso.mul_one_left⁻¹ ⋆ list.nat_iso
end bad₂
