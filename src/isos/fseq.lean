import data.iso
import data.fseq
import isos.fin

namespace fseq
-- x⁰ = 1
def one_iso {A} : fseq 0 A ≃ 1 :=
⟨λ x, (),
 λ x, fin.elim0,
 λ x, by funext y; exact fin.elim0 y,
 λ x, by induction x; refl⟩

-- 1ⁿ = 1
def one_iso₂ {n} : fseq n 1 ≃ 1 :=
⟨λ x, (),
 λ x n, (),
 λ x, by funext; apply isprop_one,
 λ x, by apply isprop_one⟩

-- x¹ = x
def id_iso {A} : fseq 1 A ≃ A :=
⟨λ x, x 0,
 λ x _, x,
 λ x,
 begin
  funext y,
  induction y with y yh,
  induction y with y ih,
  { refl },
  { exact false.elim (nat.not_lt_zero y (nat.lt_of_succ_lt_succ yh)) }
 end,
 λ x, rfl⟩

-- xᵐ xⁿ = xᵐ⁺ⁿ
def mul_iso (m n A) : fseq m A × fseq n A ≃ fseq (m + n) A :=
iso.mul_func₁ ⋆ iso.func_left fin.add_iso

-- x xⁿ = xⁿ⁺¹
def cons_iso {n A} : A × fseq n A ≃ fseq (n+1) A :=
iso.mul_left id_iso⁻¹ ⋆ eq.mp (by rw nat.add_comm) (mul_iso 1 n A)

def fseq_repr {n A} [has_repr A] : fseq n A → string :=
nat.rec_on n
  (λ x, "")
  (λ n ih x,
    let y := fseq.cons_iso.g x in
    repr y.1 ++ ite (n=0) "" (", " ++ ih y.2))

instance {n A} [has_repr A] : has_repr (fseq n A) :=
{repr := λ x, "{" ++ fseq_repr x ++ "}"}
end fseq
