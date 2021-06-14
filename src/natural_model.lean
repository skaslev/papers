-- This is based on the talk "Polynomial Functors and Natural Models of Type Theory" 
-- by Steve Awodey on the Polynomial Functor Workshop
-- https://youtu.be/RDuNIP4icKI?list=PLhgq-BqyZ7i7R-fGcAmNyWmJBQg1wzex-&t=10765

import .data.iso
import .functors.cseq

-- Type' is a pointed type
def Type' := Σ A : Type*, A
def p (x : Type') : Type* := x.1
def P (X : Type*) : Type* := Σ I : Type*, fiber p I → X

def fiber_p_A_iso_A {A} : fiber p A ≃ A :=
⟨λ x, eq.mpr (eq.symm x.2) x.1.2,
 λ x, ⟨⟨A, x⟩, rfl⟩,
 λ ⟨⟨B, x⟩, eq.refl A⟩, rfl,
 λ x, rfl⟩

def P_iso_cseq {X} : P X ≃ cseq X :=
iso.sigma_subst (λ i, iso.func_left fiber_p_A_iso_A)

def pie (c : cseq Type*) : Type* := Π i, c i
def sig (c : cseq Type*) : Type* := Σ i, c i

def lam (c : cseq Type') : Type' := ⟨(pie ∘ functor.map p) c, λ i, (c i).2⟩
-- https://youtu.be/RDuNIP4icKI?t=12445
def p_pie_pullback : p ∘ lam = pie ∘ functor.map p := rfl

def Q := Σ c, sig c
def q (x : Q) : cseq Type* := x.1
def pair (x : Q) : Type' := ⟨(sig ∘ q) x, x.2⟩
-- https://youtu.be/RDuNIP4icKI?t=12866
def p_sig_pullback : p ∘ pair = sig ∘ q := rfl
