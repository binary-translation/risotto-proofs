{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.TCG using (LabelTCG)
open import TransformRAW using (RAW-Restricted)


module Proof.Elimination.RAW.Behavior
  (dst : Execution LabelTCG) (dst-ok : RAW-Restricted dst) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; Irreflexive; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_])
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.TCG as TCG
open import Arch.TCG.Detour
open import TransformRAW
open import Helpers

open RAW-Restricted

open import Proof.Elimination.RAW.Execution dst dst-ok as RAW-Ex
open import Proof.Elimination.RAW.WellFormed dst dst-ok as RAW-Wf
import Proof.Framework LabelTCG dst dst-wf as Ψ
import Proof.Elimination.Framework dst dst-wf as Δ

open Ex.Execution
open Ex.WellFormed

open Ψ.Definitions ev[⇐]
open Δ.Definitions δ
open RAW-Ex.Extra


src-behavior : behavior src ⇔₂ behavior dst
src-behavior = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : behavior src ⊆₂' behavior dst
  ⊆-proof loc val (x , x∈src , x-w , x-val , x-loc , ¬∃z) =
    let ¬elim-x = elim-¬w x-w
    in
    ( ev[⇒] x∈src
    , events[⇒] x∈src
    , W[⇒] ¬elim-x x∈src x-w
    , val[⇒] ¬elim-x x∈src x-val
    , loc[⇒] ¬elim-x x∈src x-loc , ¬∃z'
    )
    where
    ¬∃z' : ¬ (∃[ z ] co dst (ev[⇒] x∈src) z)
    ¬∃z' (z , co[xz]) =
      let z∈dst = coʳ∈ex dst-wf co[xz]
      in ¬∃z (ev[⇐] z∈dst , co[⇐$] x∈src (events[⇐] z∈dst) co[xz])

  ⊇-proof : behavior dst ⊆₂' behavior src
  ⊇-proof loc val (x , x∈dst , x-w , x-val , x-loc , ¬∃z) = 
    ( ev[⇐] x∈dst
    , events[⇐] x∈dst
    , W[⇐] x∈dst x-w
    , val[⇐] x∈dst x-val
    , loc[⇐] x∈dst x-loc
    , ¬∃z'
    )
    where
    ¬∃z' : ¬ (∃[ z ] co src (ev[⇐] x∈dst) z)
    ¬∃z' (z , co[xz]) =
      let x∈src = events[⇐] x∈dst
          z∈src = coʳ∈src co[xz]
          ¬x-elim = elim-¬w (W[⇐] x∈dst x-w)
          ¬z-elim = elim-¬w (×₂-applyʳ (co-w×w src-wf) co[xz])
      in ¬∃z (ev[⇒] z∈src , co[⇒] ¬x-elim ¬z-elim x∈src z∈src co[xz])
