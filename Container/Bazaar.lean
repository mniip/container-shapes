import Mathlib.Algebra.PUnitInstances.Algebra
import Mathlib.Control.Fold
import Mathlib.Control.Functor
import Mathlib.Data.Vector.Basic

open Mathlib (Vector)

structure Bazaar (α β τ : Type u) : Type u where
  length : ℕ
  elements : Vector α length
  continuation : Vector β length → τ

def Bazaar.ext
  {xs : Vector α n} {ys : Vector α m} {k : Vector β n → τ} {c : Vector β m → τ}
  : (length : n = m)
    → (elements : length ▸ xs = ys)
    → (continuation : ∀x, k x = c (length ▸ x))
    → Bazaar.mk n xs k = Bazaar.mk m ys c
  | rfl, rfl, e => by
    dsimp only at e
    congr
    funext
    apply e

instance : Functor (Bazaar α β) where
  map f | ⟨l, xs, k⟩ => ⟨l, xs, f ∘ k⟩
  mapConst x | ⟨l, xs, _⟩ => ⟨l, xs, Function.const _ x⟩

@[simp] theorem Bazaar.map_def
  : f <$> Bazaar.mk l xs k = ⟨l, xs, f ∘ k⟩
  := rfl

@[simp] theorem Bazaar.mapConst_def
  : Functor.mapConst x (Bazaar.mk l xs k) = ⟨l, xs, Function.const _ x⟩
  := rfl

instance : LawfulFunctor (Bazaar α β) where
  map_const := by
    intros
    funext _ ⟨_, _, _⟩
    simp only
      [ Bazaar.mapConst_def
      , Function.comp_apply
      , Bazaar.map_def
      , Function.const_comp
      ]
  id_map := by intros; rfl
  comp_map := by intros; rfl

def Mathlib.Vector.unappend n m (v : Vector α (n + m)) : Vector α n × Vector α m
  :=
    ( @Nat.min_add_right n m ▸ take n v
    , @Nat.add_sub_cancel_left n m ▸ drop n v
    )

@[simp] theorem Mathlib.Vector.length_cast_toList {p : n = m} {v : Vector α n}
  : (p ▸ v).toList = v.toList
  := match p with | rfl => rfl

@[simp] theorem Mathlib.Vector.unappend_append
  : unappend _ _ (append xs ys) = ⟨xs, ys⟩
  := by
    unfold unappend
    obtain ⟨xs, rfl⟩ := xs
    obtain ⟨ys, _⟩ := ys
    congr
    . apply Vector.eq
      simp only
        [ length_cast_toList
        , toList_take
        , toList_append
        , toList_mk
        , List.take_left
        ]
    . apply Vector.eq
      simp only
        [ length_cast_toList
        , toList_drop
        , toList_append
        , toList_mk
        , List.drop_left
        ]

@[simp] theorem Mathlib.Vector.map_unappend_1
  : map f (unappend n m v).1 = (unappend n m (map f v)).1
  := by
    unfold unappend
    apply Vector.eq
    simp only [toList_map, length_cast_toList, toList_take, List.map_take]

@[simp] theorem Mathlib.Vector.map_unappend_2
  : map f (unappend n m v).2 = (unappend n m (map f v)).2
  := by
    unfold unappend
    apply Vector.eq
    simp only [toList_map, length_cast_toList, toList_drop, List.map_drop]

@[simp] theorem Mathlib.Vector.append_unappend
  : append (unappend n m v).1 (unappend n m v).2 = v
  := by
    unfold unappend
    apply Vector.eq
    simp only
      [ toList_append
      , length_cast_toList
      , toList_take
      , toList_drop
      , List.take_append_drop
      ]

theorem Mathlib.Vector.append_ind {motive : Vector α (m + n) → Prop}
  (p : ∀xs ys, motive (Vector.append xs ys)) v
  : motive v
  := by
    rw [← append_unappend (v:=v)]
    apply p

instance : Applicative (Bazaar α β) where
  pure x := ⟨0, Vector.nil, λ_ => x⟩
  seq | ⟨n, xs, k⟩, f => match f () with
    | ⟨m, ys, c⟩ =>
      ⟨ n + m
      , Vector.append xs ys
      , λv => match v.unappend n m with | (as, bs) => k as (c bs)
      ⟩

@[simp] theorem Bazaar.pure_def
  : pure x = Bazaar.mk (α:=α) (β:=β) 0 Vector.nil λ_ => x
  := rfl

@[simp] theorem Bazaar.seq_def {xs : Vector α n} {k : Vector β n → τ → σ}
  : Seq.seq ⟨n, xs, k⟩ (λ_ => ⟨m, ys, c⟩) = Bazaar.mk
    (n + m)
    (Vector.append xs ys)
    λv => match v.unappend with | (as, bs) => k as (c bs)
  := rfl

instance : LawfulApplicative (Bazaar α β) where
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq := by
    intro _ _ _ ⟨_, _, _⟩
    dsimp only [Bazaar.pure_def, Bazaar.seq_def, Bazaar.map_def]
    apply Bazaar.ext
    case length => simp only [zero_add]
    case elements =>
      apply Vector.eq
      simp only
        [ Vector.length_cast_toList
        , Vector.toList_append
        , Vector.toList_empty
        , List.nil_append
        ]
    case continuation =>
      intro _
      congr
  map_pure _ _ := rfl
  seq_pure := by
    intro _ _ ⟨_, _, _⟩ x
    simp only
      [ Bazaar.pure_def
      , Bazaar.seq_def
      , Nat.add_zero
      , Vector.append_nil
      , Bazaar.map_def
      ]
    congr
    funext v
    congr
    symm
    calc
      v = (Vector.unappend _ _ (Vector.append v Vector.nil)).1
        := by rw [Vector.unappend_append]
      _ = _ := by rw [Vector.append_nil]
  seq_assoc := by
    intro _ _ _ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩
    simp only [Bazaar.seq_def, Bazaar.map_def, Function.comp_apply]
    apply Bazaar.ext
    case length => rw [Nat.add_assoc]
    case elements =>
      apply Vector.eq
      simp only
        [ Vector.length_cast_toList
        , Vector.toList_append
        , List.append_assoc
        ]
    case continuation =>
      intro v
      induction v using Vector.append_ind with | _ xs v =>
      induction v using Vector.append_ind with | _ ys zs =>
      simp only [Vector.unappend_append]
      suffices Nat.add_assoc _ _ _ ▸ Vector.append xs (Vector.append ys zs)
        = Vector.append (Vector.append xs ys) zs
        by simp only [this, Vector.unappend_append]
      apply Vector.eq
      simp only
        [ Vector.length_cast_toList
        , Vector.toList_append
        , List.append_assoc
        ]

def Bazaar.sell (x : α) : Bazaar α β β :=
  { length := 1
  , elements := x ::ᵥ Vector.nil
  , continuation := Vector.head
  }

def Bazaar.length_parametric.emptied {α β : Type u}
  : ApplicativeTransformation
    (Bazaar α β)
    (Functor.Comp (Bazaar α PEmpty) (Functor.Const PUnit))
  :=
    { app := λ_ ⟨l, e, _⟩ => Functor.Comp.mk
        ⟨l, e, λ_ => Functor.Const.mk PUnit.unit⟩
    , preserves_pure' := λ _ => rfl
    , preserves_seq' := λ_ _ => rfl
    }

theorem Bazaar.length_parametric {α β₁ β₂ : Type u}
  [Traversable t] [LawfulTraversable t] (xs : t α)
  : (traverse (sell (β:=β₁)) xs).length = (traverse (sell (β:=β₂)) xs).length
  := by
    have p
      : ∀β τ (b : Bazaar α β τ),
        b.length = (length_parametric.emptied b).run.length
      := λ_ _ _ => rfl
    have q
      : ∀(β : Type u), length_parametric.emptied.app β ∘ sell (α:=α)
        = Functor.Comp.mk
          ∘ Functor.map (Function.const PEmpty $ Functor.Const.mk PUnit.unit)
          ∘ sell
      := λ_ => rfl
    rw
      [ p β₁
      , LawfulTraversable.naturality length_parametric.emptied sell xs
      , p β₂
      , LawfulTraversable.naturality length_parametric.emptied sell xs
      , q β₁
      , LawfulTraversable.comp_traverse
      , q β₂
      , LawfulTraversable.comp_traverse
      ]
    rfl

theorem Bazaar.elements_parametric
  [Traversable t] [LawfulTraversable t] (xs : t α)
  : (traverse (sell (β:=β₁)) xs).elements
    = Bazaar.length_parametric xs ▸ (traverse (sell (β:=β₂)) xs).elements
  := by admit -- use emptied

def Bazaar.traverse_length.folded
  : ApplicativeTransformation
    (Bazaar α β)
    (Functor.Const (Monoid.Foldl (ULift ℕ)))
  :=
    { app := λ_ b => Functor.Const.mk
      $ Monoid.Foldl.mk λl => ULift.up (l.down + b.length)
    , preserves_pure' := by
        intro _ _
        simp only [pure_def, add_zero]
        rfl
    , preserves_seq' := by
        intro _ _ ⟨_, _, _⟩ ⟨_, _, _⟩
        show _ = Functor.Const.mk
          (Monoid.Foldl.mk λl => ULift.up (l.down + _ + _))
        simp only [seq_def]
        congr
        funext
        rw [Nat.add_assoc]
    }

theorem Bazaar.traverse_length [Traversable t] [LawfulTraversable t] (xs : t α)
  : Traversable.length xs = (traverse (sell (β:=β)) xs).length
  := by
    rw [length_parametric (β₁:=β) (β₂:=PUnit)]
    unfold Traversable.length Traversable.foldl Traversable.foldMap
    admit -- use folded

def Bazaar.traverse_toList.listed
  : ApplicativeTransformation
    (Bazaar α β)
    (Functor.Const (Monoid.Foldl (List α)))
  :=
    { app := λ_ b => Functor.Const.mk
      $ Monoid.Foldl.mk λl => b.elements.toList.reverse ++ l
    , preserves_pure' := by
        intro _ _
        simp only
          [ pure_def
          , Vector.toList_empty
          , List.reverse_nil
          , List.nil_append
          ]
        rfl
    , preserves_seq' := by
        intro _ _ ⟨_, _, _⟩ ⟨_, _, _⟩
        show _ = Functor.Const.mk (Monoid.Foldl.mk λl => _)
        show _ = Functor.Const.mk (Monoid.Foldl.mk λl => _ ++ (_ ++ l))
        simp only
          [ seq_def
          , Vector.toList_append
          , List.reverse_append
          , List.append_assoc
          ]
    }

theorem Bazaar.traverse_toList [Traversable t] [LawfulTraversable t] (xs : t α)
  : Traversable.toList xs = (traverse (sell (β:=β)) xs).elements.toList
  := by
    rw [elements_parametric (β₁:=β) (β₂:=PUnit)]
    unfold Traversable.toList Traversable.foldl Traversable.foldMap
    admit -- use listed
