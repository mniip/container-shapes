import Mathlib.Control.Fold

def Shape (f : Type u → Type u) : Type u := f PUnit

def shape {f : Type u → Type u} [Functor f] : f α → Shape f
  := Functor.mapConst PUnit.unit

@[simp] theorem shape.preserved_by_map [Functor f] [LawfulFunctor f]
  {h : α → β} {xs : f α}
  : shape (h <$> xs) = shape xs
  := by
    unfold shape
    rw [map_const, map_const]
    simp only [Function.comp_apply, Functor.map_map, Function.const_apply]

@[simp] theorem shape.preserved_by_map_const [Functor f] [LawfulFunctor f]
  {x : β} {xs : f α}
  : shape (Functor.mapConst x xs) = shape xs
  := by
    unfold shape
    rw [map_const, map_const, map_const]
    simp only [Function.comp_apply, Functor.map_map, Function.const_apply]

@[simp] theorem shape.preserves_length
  [Traversable f] [LawfulTraversable f] {xs : f α}
  : Traversable.length (shape xs) = Traversable.length xs
  := by
    unfold shape Traversable.length
    rw [map_const]
    simp only [Function.comp_apply, Traversable.foldl_map]

@[simp] theorem Shape.shape_shape [Functor f] [LawfulFunctor f] {s : Shape f}
  : shape s = s
  := by
    unfold shape
    rw [map_const, Function.comp_apply]
    suffices Function.const _ _ = id by rw [this, id_map]
    funext _
    apply PUnit.subsingleton
