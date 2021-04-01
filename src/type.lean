def ℕ₁ := Σ' n:ℕ, n > 0

def rel (A) := A → A → Prop

inductive {u} pempty : Sort u

@[instance]
def {u} sort_has_zero : has_zero (Sort u) :=
{zero := pempty}

instance : has_repr pempty :=
{repr := λ _, "∅"}

@[instance]
def {u} sort_has_one : has_one (Sort u) :=
{one := punit}

def fiber {A B : Type*} (f : A → B) (y : B) := Σ' x, f(x) = y

def iscontr (A : Type*) := ∃ x : A, ∀ y : A, x = y
def isprop (A : Type*) := ∀ x y : A, x = y

def isprop_unit : isprop unit
| () () := rfl

def isprop_one : isprop 1
| () () := rfl

@[simp] lemma sigma.mk.eta {A} {B : A → Type*} : Π {p : Σ A, B A}, sigma.mk p.1 p.2 = p
| ⟨a, b⟩ := rfl
