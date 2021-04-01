class {u v} cofunctor (f : Type u → Type v) : Type (max (u+1) v) :=
(comap : Π {A B : Type u}, (A → B) → f B → f A)

infixr ` <€> `:100 := cofunctor.comap

class {u v} is_lawful_cofunctor (f : Type u → Type v) [cofunctor f] : Prop :=
(id_comap     : Π {A : Type u} (x : f A), id <€> x = x)
(comp_comap   : Π {A B C : Type u} (g : A → B) (h : B → C) (x : f C), (h ∘ g) <€> x = g <€> h <€> x)
