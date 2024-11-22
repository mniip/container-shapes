import Container.Bazaar
import Container.Shape

def Shaped (t : Type u → Type u) [Functor t] (s : Shape t) (α : Type u) : Type u
  := { xs : t α // shape xs = s }

instance [Functor t] [LawfulFunctor t] : Functor (Shaped t s) where
  map f
    | ⟨xs, p⟩ => ⟨f <$> xs, by rw [shape.preserved_by_map, p]⟩
  mapConst x
    | ⟨xs, p⟩ =>
      ⟨Functor.mapConst x xs, by rw [shape.preserved_by_map_const, p]⟩

@[simp] theorem Shaped.map_def [Functor t] [LawfulFunctor t]
  {f : α → β} {xs : t α} {p : shape xs = s}
  : Functor.map (f:=Shaped t s) f ⟨xs, p⟩
    = ⟨f <$> xs, by rw [shape.preserved_by_map, p]⟩
  := by rfl

@[simp] theorem Shaped.mapConst_def [Functor t] [LawfulFunctor t]
  {x : β} {xs : t α} {p : shape xs = s}
  : Functor.mapConst (f:=Shaped t s) x ⟨xs, p⟩
    = ⟨Functor.mapConst x xs, by rw [shape.preserved_by_map_const, p]⟩
  := by rfl

instance [Functor f] [LawfulFunctor f] : LawfulFunctor (Shaped f s) where
  map_const := by
    intro _ _
    funext _ ⟨_, _⟩
    dsimp only [Shaped.mapConst_def, Function.comp_apply, Shaped.map_def]
    congr
    rw [map_const]
    rfl
  id_map := by
    intro _ ⟨_, _⟩
    simp only [Shaped.map_def, id_map]
  comp_map := by
    intro _ _ _ _ _ ⟨_, _⟩
    simp only [Shaped.map_def, Functor.map_map]
    rfl

local instance [Subsingleton α] : Subsingleton (Mathlib.Vector α n) where
  allEq := by
    intro xs ys
    induction n with
    | zero => apply Subsingleton.allEq
    | succ _ IH =>
      suffices xs.head ::ᵥ xs.tail = ys.head ::ᵥ ys.tail
        by simp at this; assumption
      apply congrArg₂
      . apply Subsingleton.allEq
      . apply IH

def shape.repopulate [Traversable t] [LawfulTraversable t]
  (xs : List α) (p : List.length xs = Traversable.length s)
  : Shaped t s α
  :=
    ⟨ (traverse Bazaar.sell s).continuation
      ⟨xs, by rw [p, Bazaar.traverse_length]⟩
    , by
      show (shape <$> traverse Bazaar.sell s).continuation _ = _
      unfold shape
      rw [map_const, Function.comp_apply]
      rw [Bazaar.injEq_continuation (Bazaar.map_continuation_traverse _ _).symm]
      unfold Bazaar.map_continuation
      dsimp only [Function.comp_apply]
      conv_rhs =>
        rw [← LawfulTraversable.id_traverse s, Bazaar.traverse_universal]
      congr
      apply Subsingleton.allEq
    ⟩

@[simp] theorem shape.repopulate_id
  [Traversable t] [LawfulTraversable t] {xs : t α} p
  : shape xs = s → (shape.repopulate (s:=s) (Traversable.toList xs) p).1 = xs
  := by
    intro p
    unfold repopulate
    dsimp only
    rw [Bazaar.injEq_continuation (by rw [← p])]
    unfold shape
    rw [Bazaar.injEq_continuation (by rw [map_const, Function.comp_apply])]
    rw [Bazaar.continuation_parametric]
    conv_rhs =>
      rw [← LawfulTraversable.id_traverse xs, Bazaar.traverse_universal]
    congr
    rw [Mathlib.Vector.id_traverse]
    apply Mathlib.Vector.eq
    rw [← Bazaar.traverse_toList]
    simp only [Mathlib.Vector.length_cast_toList, Mathlib.Vector.toList_mk]

instance [Traversable t] [LawfulTraversable t] : Traversable (Shaped t s) where
  traverse f
    | ⟨xs, p⟩ => Mathlib.Vector.traverse f ⟨Traversable.toList xs, rfl⟩
      <&> λ⟨ys, q⟩ => shape.repopulate ys $ by
        rw [q, ← p, shape.preserves_length, Traversable.length_toList]

@[simp] theorem Shaped.traverse_square
  [Traversable t] [LawfulTraversable t] [Applicative F] [LawfulApplicative F]
  {xs : Shaped t s α} {f : α → F β}
  : Subtype.val <$> traverse f xs = traverse f xs.1
  := by
    obtain ⟨xs, q⟩ := xs
    simp only [traverse, Functor.mapRev]
    have p
      : (Traversable.toList xs).length
        = (traverse (Bazaar.sell (β:=β)) xs).length
      := by rw [← Bazaar.traverse_length, Traversable.length_toList]
    have e
      : ⟨Traversable.toList xs, rfl⟩ = p ▸ (traverse Bazaar.sell xs).elements
      := by
        apply Mathlib.Vector.eq
        simp only [Mathlib.Vector.toList_mk, Mathlib.Vector.length_cast_toList]
        rw [← Bazaar.traverse_toList]
    rw [e, Mathlib.Vector.length_cast_traverse]
    simp only [functor_norm]
    rw [Bazaar.traverse_universal (f:=f) (xs:=xs)]
    congr
    funext ⟨_, _⟩
    show (traverse Bazaar.sell s).continuation _ = _
    rw [Bazaar.injEq_continuation (by rw [← q])]
    unfold shape
    rw [Bazaar.injEq_continuation (by rw [map_const, Function.comp_apply])]
    rw [Bazaar.continuation_parametric]
    congr
    apply Mathlib.Vector.eq
    simp only [Mathlib.Vector.length_cast_toList, Mathlib.Vector.toList_mk]
    show Mathlib.Vector.toList _ = _ -- ???
    simp only [Mathlib.Vector.length_cast_toList, Mathlib.Vector.toList_mk]
