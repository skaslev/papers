def iter {A} (g : A → A) : ℕ → A → A
| 0 := id
| (n+1) := iter n ∘ g

def diter {B : Type → Type 1} {C : Type → Type} (g : Π {A}, B (C A) → B A) : Π (n : ℕ) {A}, B (iter C n A) → B A
| 0 A := id
| (n+1) A := g ∘ diter n

def delta (k n : ℕ) := ite (n = k) 1 0

def partial_sum (f : ℕ → ℕ) : ℕ → ℕ
| 0 := f 0
| (n+1) := partial_sum n + f (n+1)

def take {A} : ℕ → (ℕ → A) → list A
| 0 c := []
| (n+1) c := take n c ++ [c n]

def const {A B} (a : A) (b : B) := a

attribute [simp] function.comp

def {u} id_def {A : Sort u} : id = λ x:A, x :=
funext (λ _, rfl)

namespace function
def add {A B C D} (f : A → B) (g : C → D) (x : A ⊕ C) : B ⊕ D :=
sum.rec (sum.inl ∘ f) (sum.inr ∘ g) x

def mul {A B C D} (f : A → B) (g : C → D) (x : A × C) : B × D :=
(f x.1, g x.2)

def dimap {A B C D} (f : A → B) (g : C → D) (x : B → C) : A → D :=
g ∘ x ∘ f
end function
