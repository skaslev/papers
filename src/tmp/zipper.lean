import data.iso
import category.comonad

def U := Type
def UU := Type → Type

axiom deriv : UU → UU

-- The generating function of `zipper f` is T(x) = x f'(x)
def zipper (f : UU) (A) := A × deriv f A

-- The logarithmic derivative of f(x) is g(x) such that f'(x) = f(x) g(x)
-- that is g(x) = (ln f(x))' = f'(x)/f(x)
def logderiv (f : UU) := Σ g : UU, Π A, iso (deriv f A) (f A × g A)

-- Given f(x) and it's logarithmic derivative g(x) we can construct alternative zipper
def logderiv_zipper (f : UU) (g : logderiv f) (A) := A × f A × g.1 A

-- .. that is isomorphic to the usual one
def logderiv_zipper_iso (f : UU) (g : logderiv f) (A) : iso (zipper f A) (logderiv_zipper f g A) :=
iso.id_iso.mul (g.2 A)

namespace zipper
variables {f : UU} [functor (deriv f)]

def map {A B} (g : A → B) (x : zipper f A) : zipper f B :=
(g x.1, g <$> x.2)

instance : functor (zipper f) :=
{ map := @map _ _ }

def extract {A} (z : zipper f A) : A := z.1
-- def dup {A} (z : zipper f A) : zipper f (zipper f A) :=
end zipper
