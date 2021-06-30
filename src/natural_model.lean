-- This is based on the talk "Polynomial Functors and Natural Models of Type Theory"
-- by Steve Awodey on the Polynomial Functor Workshop
-- https://youtu.be/RDuNIP4icKI?list=PLhgq-BqyZ7i7R-fGcAmNyWmJBQg1wzex-&t=10765

import functors.family

open fam

abbreviation U := Type*
abbreviation Ω := Prop
abbreviation P := fam

-- U' is a pointed type
def U' := Σ A : U, A
def p (x : U') : U := x.1

def fiber_p_A_iso_A {A} : fiber p A ≃ A :=
⟨λ ⟨⟨A, x⟩, rfl⟩, x,
 λ x, ⟨⟨A, x⟩, rfl⟩,
 λ ⟨⟨A, x⟩, rfl⟩, rfl,
 λ x, rfl⟩

-- The `P` functor from the talk. We prove it's equivalent the one we use below.
def P' (A : U) : U := Σ I : U, fiber p I → A
def P'_iso_P {A} : P' A ≃ P A :=
iso.sigma_subst (λ I, iso.func_left fiber_p_A_iso_A)

def pie (c : P U) : U := Π i, c i
def sig (c : P U) : U := Σ i, c i

def lam (c : P U') : U' := ⟨pie (map p c), λ i, (c i).2⟩

-- https://youtu.be/RDuNIP4icKI?t=12445
def p_pie_pullback : p ∘ lam = pie ∘ map p := rfl

namespace alt
def R := Σ c : P U, pie c
def r (x : R) : P U := x.1
def lam (x : R) : U' := ⟨pie (r x), x.2⟩
def p_pie_pullback : p ∘ lam = pie ∘ r := rfl
end alt

def Q := Σ c : P U, sig c
example : Q = sig (of sig) := rfl
def q (x : Q) : P U := x.1
def pair (x : Q) : U' := ⟨sig (q x), x.2⟩

-- https://youtu.be/RDuNIP4icKI?t=12866
def p_sig_pullback : p ∘ pair = sig ∘ q := rfl

def s (A : U) : Ω := nonempty A
def i (A : Ω) : U := inhabited A

-- https://youtu.be/RDuNIP4icKI?t=13639
def trunc : U → U := i ∘ s
def s_i_eq_id : s ∘ i = id :=
funext $ λ p, propext
⟨λ ⟨⟨x⟩⟩, x,
 λ x, ⟨⟨x⟩⟩⟩

def all (c : P Ω) : Ω := ∀ i, c i
def exi (c : P Ω) : Ω := ∃ i, c i

-- https://youtu.be/RDuNIP4icKI?t=13681
def all_as_pie : all = s ∘ pie ∘ map i :=
funext $ λ c, propext
⟨λ x, ⟨λ y, ⟨x y⟩⟩,
 λ ⟨x⟩ y, let ⟨z⟩ := x y in z⟩

-- https://youtu.be/RDuNIP4icKI?t=13681
def exi_as_sig : exi = s ∘ sig ∘ map i :=
funext $ λ c, propext
⟨λ ⟨x, y⟩, ⟨⟨x, ⟨y⟩⟩⟩,
 λ ⟨⟨x, ⟨y⟩⟩⟩, ⟨x, y⟩⟩
