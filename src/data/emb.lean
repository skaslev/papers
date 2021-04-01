structure {u v} emb (A : Sort u) (B : Sort v) :=
(f : A → B) (g : B → A) (gf : Π x, g (f x) = x)

notation a ` ≲ ` b := emb a b
