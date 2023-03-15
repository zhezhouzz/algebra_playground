From stdpp Require Import stringmap mapset.
(* Equality *)
(* id function *)

Class Arrows (O: Type): Type := arrow: O → O → Type.
Set Warnings "-unsupported-attributes". (* FIXME: remove when minimal Coq version is enough *)

#[global]
Typeclasses Transparent Arrows. (* Ideally this should be removed *)

Set Warnings "+unsupported-attributes".
Infix "⟶" := arrow (at level 90, right associativity).
Class CatId O `{Arrows O} := cat_id: ∀ x, x ⟶ x.
Class CatComp O `{Arrows O} := comp: ∀ x y z, (y ⟶ z) → (x ⟶ y) → (x ⟶ z).
(* Class CatId O `{Arrows O} := cat_id: forall x, x ⟶ x. *)
(* Class CatComp O `{Arrows O} := comp: forall a b c, (b ⟶ c) -> (a ⟶ b) -> (a ⟶ c). *)
Infix "⋅" := (comp _ _ _) (at level 40, left associativity).
Definition dom O `{Arrows O} {a b} (arr: a ⟶ b) := a.
Definition codom O `{Arrows O} {a b} (arr: a ⟶ b) := b.

Arguments cat_id {O arrow cat_id x} : rename.
Arguments comp {O arrow comp} _ _ _ _ _ : rename.


Class Setoid A {Ae : Equiv A} : Prop := setoid_eq :> Equivalence (@equiv A Ae).

Class Cat (O: Type) `{!Arrows O} `{forall a b, Equiv (a ⟶ b)} `{!CatId O} `{!CatComp O} : Prop :=
  {
    arrow_eq :> forall a b, Setoid (a ⟶ b);
    comp_proper :> forall x y z, Proper ((=) ==> (=) ==> (=)) (comp x y z);
    comp_assoc: forall (a b c d: O) (f: a ⟶ b) (g: b ⟶ c) (k: c ⟶ d), k ⋅ (g ⋅ f) = (k ⋅ g) ⋅ f;
    id_l: forall (a b: O) (f: a ⟶ b), (comp a b b) cat_id f = f;
    id_r: forall (a b: O) (f: a ⟶ b), (comp a a b) f cat_id = f;
  }.

Section setoid_morphisms.
  Context {A B} {Ae : Equiv A} {Be : Equiv B} (f : A → B).

  Class Setoid_Morphism :=
    { setoidmor_a : Setoid A
    ; setoidmor_b : Setoid B
    ; sm_proper :> Proper ((=) ==> (=)) f }.

End setoid_morphisms.

Section initial_.
Context `{Cat A}.
Class InitialArrows (a: A): Type := initial_arrow: forall b, a ⟶ b.
Class Initial (a: A) `{InitialArrows a}: Prop :=
  initial_arrow_unique: forall (b: A) (f: a ⟶ b), f = initial_arrow b.
End initial_.

Section setoid_morphisms.
Context `{Cat C} `{Cat D} (M: C → D).
Class Fmap : Type := fmap: forall {x1 x2: C}, (x1 ⟶ x2) -> (M x1 ⟶ M x2).

Class Functor `(Fmap): Prop := {
    functor_from: Cat C;
    functor_to: Cat D;
    functor_morphism :> ∀ a b: C, Setoid_Morphism (@fmap _ a b);
    preserves_id: `(fmap (cat_id: a ⟶ a) = cat_id);
    preserves_comp `(f: y ⟶ z) `(g: x ⟶ y): fmap (f ⋅ g) = fmap f ⋅ fmap g }.
End setoid_morphisms.

Notation "F ⟹ G" := (forall x, F x ⟶ G x) (at level 90, right associativity).

Section natural_transformation.

  Context `{Cat C} `{Cat D} `{!Functor (F: C -> D) Fa} `{!Functor (G: C -> D) Ga}.

  Class NaturalTransformation (η: F ⟹ G): Prop := {
      naturaltrans_from: Functor F Fa;
      naturaltrans_to: Functor G Ga;
      natrual: forall `(f: x ⟶ y), η y ⋅ (fmap F f) = (fmap G f) ⋅ η x
    }.

End natural_transformation.

Section adjunction.

  Context `{Cat C} `{Cat D} `{!Functor (F: C -> D) Fa} `{!Functor (G: D -> C) Ga}.

  Class ϕAdjunction (ϕ: forall `(F c ⟶ d), (c ⟶ G d)): Prop := {
      adjunction_left_functor: Functor F Fa;
      adjunction_right_functor: Functor G Ga;
      ϕnatural_left `(f: F c ⟶ d) `(k: d ⟶ d'): ϕ (k ⋅ f) = fmap G k ⋅ ϕ f;
      ϕnatural_right `(f: F c ⟶ d) `(h: c' ⟶ c): ϕ (f ⋅ fmap F h) = ϕ f ⋅ h
    }.

End adjunction.
