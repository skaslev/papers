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

-- https://youtu.be/RDuNIP4icKI?t=12445
def lam' (c : P U') : U' := ⟨pie (map p c), λ i, (c i).2⟩
def p_pie_pullback' : p ∘ lam' = pie ∘ map p := rfl

-- Alternative pullback of `p` and `pie`
def R := Σ c : P U, pie c
def lam (x : R) : U' := ⟨pie x.1, x.2⟩
def p_pie_pullback : p ∘ lam = pie ∘ sigma.fst := rfl

-- https://youtu.be/RDuNIP4icKI?t=12866
def Q := Σ c : P U, sig c
def pair (x : Q) : U' := ⟨sig x.1, x.2⟩
def p_sig_pullback : p ∘ pair = sig ∘ sigma.fst := rfl

example : R = sig (of pie) := rfl
example : Q = sig (of sig) := rfl

def R_iso_P_U' : R ≃ P U' :=
⟨λ x, ⟨x.1, λ i, ⟨x.1 i, x.2 i⟩⟩,
 λ x, ⟨⟨x, λ i, (x i).1⟩, λ i, (x i).2⟩,
 λ ⟨⟨A, B⟩, x⟩, rfl,
 λ ⟨A, x⟩, congr_arg _ $ funext $ λ i, sigma.eq rfl rfl⟩

def Q_iso_expl : Q ≃ Σ (A : U) (B : A → U) (a : A), B a :=
⟨λ ⟨⟨A, B⟩, ⟨a, b⟩⟩, ⟨A, B, a, b⟩,
 λ ⟨A, B, a, b⟩, ⟨⟨A, B⟩, ⟨a, b⟩⟩,
 λ ⟨⟨A, B⟩, ⟨a, b⟩⟩, rfl,
 λ ⟨A, B, a, b⟩, rfl⟩

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
