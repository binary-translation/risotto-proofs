{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.TCG using (LabelTCG)
open import TransformFWAW using (FWAW-Restricted)


module Proof.Elimination.FWAW.Behavior
  (dst : Execution LabelTCG) (dst-ok : FWAW-Restricted dst) where

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
-- Local imports: General
open import Helpers
-- Local imports: Architecture Specifications
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.TCG as TCG
open import Arch.TCG.Detour
-- Local imports: Theorem Specification
open import TransformFWAW
-- Local imports: Proof Components
open import Proof.Elimination.FWAW.Execution dst dst-ok as FWAW-Ex
open import Proof.Elimination.FWAW.WellFormed dst dst-ok as FWAW-Wf
import Proof.Framework LabelTCG dst dst-wf as Ψ
import Proof.Elimination.Framework dst dst-wf as Δ


open FWAW-Restricted
open Ex.Execution
open Ex.WellFormed
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
open Δ.Definitions δ
open FWAW-Ex.Extra


src-behavior : behavior src ⇔₂ behavior dst
src-behavior = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : behavior src ⊆₂' behavior dst
  ⊆-proof loc val (x , x∈src , x-w , x-val , x-loc , ¬∃z) =
    let ¬x-elim = λ{refl → ⊥-elim (¬∃z (src-pres₂-ev , co-ep refl src-pres₂-def))}
    in
    ( ev[⇒] x∈src
    , events[⇒] x∈src
    , W[⇒] ¬x-elim x∈src x-w
    , val[⇒] ¬x-elim x∈src x-val
    , loc[⇒] ¬x-elim x∈src x-loc
    , ¬∃z'
    )
    where
    ¬∃z' : ¬ (∃[ z ] co dst (ev[⇒] x∈src) z)
    ¬∃z' (z , co[xz]) =
      let z∈src = events[⇐] (coʳ∈ex dst-wf co[xz])
      in ¬∃z (_ , co[⇐$] x∈src z∈src co[xz])

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
    ¬∃z' (z , co[xz]) with ev-eq-dec z src-elim-ev
    ... | yes refl =
      let ¬x-elimᵗ = λ{refl → disjoint-w/skip _ (x-w , elim-ev-skip dst-ok)}
          ¬x-elimˢ = ¬x-elimᵗ ∘ ev[$⇒]eq x∈dst (elim∈ex dst-ok)
          co[xp] = coʳ-e⇒p co[xz]
      in ¬∃z (_ , co[⇒] ¬x-elimˢ ¬pres₂-elim (events[⇐] x∈dst) pres₂∈src co[xp])
    ... | no ¬z-elim =
      let ¬x-elimᵗ = λ{refl → disjoint-w/skip _ (x-w , elim-ev-skip dst-ok)}
          ¬x-elimˢ = ¬x-elimᵗ ∘ ev[$⇒]eq x∈dst (elim∈ex dst-ok)
          z∈src = coʳ∈src co[xz]
      in ¬∃z (_ , co[⇒] ¬x-elimˢ ¬z-elim (events[⇐] x∈dst) z∈src co[xz])
