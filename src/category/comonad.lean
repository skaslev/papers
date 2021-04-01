class comonad (m : Type → Type) extends functor m :=
(extract : Π {A}, m A → A)
(dup : Π {A}, m A → m (m A))
(map_extract_over_dup : Π {A} {x : m A}, extract <$> dup x = x)

namespace comonad
def cobind {m A B} [comonad m] (x: m A) (f : m A -> B) : m B := f <$> dup x
notation x `=>>` g := cobind x g
end comonad

def bind {m A B} [monad m] (x : m A) (f : A -> m B) : m B := monad.join $ f <$> x
