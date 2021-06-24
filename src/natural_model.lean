-- This is based on the talk "Polynomial Functors and Natural Models of Type Theory"
-- by Steve Awodey on the Polynomial Functor Workshop
-- https://youtu.be/RDuNIP4icKI?list=PLhgq-BqyZ7i7R-fGcAmNyWmJBQg1wzex-&t=10765

import functors.family

open fam

-- Type' is a pointed type
def Type' := Σ A : Type*, A
def p (x : Type') : Type* := x.1
def P (X : Type*) : Type* := Σ I : Type*, fiber p I → X

def fiber_p_A_iso_A {A} : fiber p A ≃ A :=
⟨λ x, eq.mpr (eq.symm x.2) x.1.2,
 λ x, ⟨⟨A, x⟩, rfl⟩,
 λ ⟨⟨B, x⟩, eq.refl A⟩, rfl,
 λ x, rfl⟩

def P_iso_fam {X} : P X ≃ fam X :=
iso.sigma_subst (λ i, iso.func_left fiber_p_A_iso_A)

def pie (c : fam Type*) : Type* := Π i, c i
def sig (c : fam Type*) : Type* := Σ i, c i

def lam (c : fam Type') : Type' := ⟨(pie ∘ map p) c, λ i, (c i).2⟩

-- https://youtu.be/RDuNIP4icKI?t=12445
def p_pie_pullback : p ∘ lam = pie ∘ map p := rfl

def Q := sig $ of sig
def q (x : Q) : fam Type* := x.1
def pair (x : Q) : Type' := ⟨(sig ∘ q) x, x.2⟩

-- https://youtu.be/RDuNIP4icKI?t=12866
def p_sig_pullback : p ∘ pair = sig ∘ q := rfl

def s (X : Type*) : Prop := nonempty X
def i (X : Prop) : Type* := inhabited X

-- https://youtu.be/RDuNIP4icKI?t=13639
def trunc : Type* → Type* := i ∘ s
def s_i_eq_id : s ∘ i = id :=
begin
  funext p,
  apply propext,
  cases classical.em p with x x,
  { have y : nonempty (inhabited p) := ⟨⟨x⟩⟩,
    exact iff.intro (const x) (const y) },
  cases classical.em (nonempty (inhabited p)) with y y,
  { induction y,
    induction y,
    contradiction },
  { apply iff.intro _ _,
    repeat { contradiction } }
end

def all (c : fam Prop) : Prop := ∀ i, c i
def exi (c : fam Prop) : Prop := ∃ i, c i

-- https://youtu.be/RDuNIP4icKI?t=13681
def all_as_pie : all = s ∘ pie ∘ map i :=
begin
  funext c,
  apply propext _,
  apply iff.intro (λ x, _) (λ x, _),
  { exact nonempty.intro (λ y, inhabited.mk (x y)) },
  { induction x,
    intro y,
    have z : inhabited (c y) := x y,
    induction z,
    exact z }
end

-- https://youtu.be/RDuNIP4icKI?t=13681
def exi_as_sig : exi = s ∘ sig ∘ map i :=
begin
  funext c,
  apply propext _,
  apply iff.intro (λ x, _) (λ x, _),
  { exact nonempty.intro ⟨classical.some x, inhabited.mk (classical.some_spec x)⟩ },
  { induction x,
    induction x with y z,
    induction z,
    exact ⟨y, z⟩ }
end
