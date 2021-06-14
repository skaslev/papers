import data.iso

namespace fin
@[simp]
def mk.eta {n} (i : fin n) {h} : fin.mk i.val h = i :=
by induction i; refl

def zero_iso : fin 0 ≃ 0 :=
⟨λ x, fin.elim0 x, λ x, pempty.rec _ x,
 λ x, fin.elim0 x, λ x, pempty.rec _ x⟩

def one_iso : fin 1 ≃ 1 :=
⟨λ x, (),
 λ x, 0,
 λ x, by induction x with x h; simp [lt_one h]; congr,
 λ x, by induction x; refl⟩

def foo {a b x : ℕ} (h : x < a) : x < a + b :=
begin
  induction b,
  { exact h },
  { apply nat.lt_trans b_ih,
    apply nat.lt_succ_of_le,
    exact nat.less_than_or_equal.refl }
end

def bar {a b x : ℕ} (g : x < a + b) (h : ¬x < a) : x - a < b :=
begin
  have i := nat.eq_or_lt_of_not_lt h,
  induction i,
  { rw i,
    rw i at g,
    rw nat.sub_self,
    have j : a + 0 < a + b := by exact g,
    exact nat.lt_of_add_lt_add_left j },
  { have j : a + (x - a) < a + b :=
    begin
      rw ←nat.add_sub_assoc (nat.le_of_lt i),
      rw nat.add_comm,
      rw nat.add_sub_cancel,
      exact g
    end,
    exact nat.lt_of_add_lt_add_left j }
end

def add_iso {a b} : fin a ⊕ fin b ≃ fin (a + b) :=
⟨λ x, sum.rec (λ y, ⟨y.1, foo y.2⟩) (λ y, ⟨a + y.1, nat.add_lt_add_left y.2 a⟩) x,
 λ x, dite (x.1 < a) (λ h, sum.inl ⟨x.1, h⟩) (λ h, sum.inr ⟨x.1 - a, bar x.2 h⟩),
 begin
   intros,
   induction x,
   { induction x with x xh, exact dif_pos xh },
   { induction x with x xh,
     have h : ¬ a + x < a :=
     begin
       intros h,
       induction x with x xih,
       { exact nat.lt_irrefl a h },
       { have g : a < a + (nat.succ x) := nat.lt_add_of_pos_right (nat.pos_of_ne_zero (nat.succ_ne_zero x)),
         exact nat.lt_le_antisymm h (nat.le_of_lt g) }
     end,
     simp [dif_neg h, nat.add_sub_cancel_left a x] }
 end,
 begin
   intros,
   induction x with x xh,
   by_cases x < a,
   { rw dif_pos h },
   { rw dif_neg h,
     have i := nat.eq_or_lt_of_not_lt h,
     induction i,
     { simp [i, nat.sub_self a] },
     { simp [nat.add_sub_of_le (nat.le_of_lt i)] }}
 end⟩

def add_one_iso {n} : 1 ⊕ fin n ≃ fin (n+1) :=
iso.add_comm ⋆ iso.add_right one_iso.inv ⋆ add_iso

def two_iso : fin 2 ≃ 1 ⊕ 1 :=
add_iso⁻¹ ⋆ iso.add one_iso one_iso

def mul_iso {n m} : fin n × fin m ≃ fin (n * m) :=
sorry

def pow_iso {n k} : fin k → fin n ≃ fin (n^k) :=
sorry
end fin
