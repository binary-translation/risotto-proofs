{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.TCG using (LabelTCG)
open import TransformRAW using (RAW-Restricted)


module Proof.Elimination.RAW.Mapping (dst : Execution LabelTCG) (dst-ok : RAW-Restricted dst) where

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


events-preserved : ∀ {x : Event LabelTCG} → x ≢ elim-ev dst-ok → x ∈ events dst → x ∈ events src
events-preserved {event-init _ _ _}   ¬x-elim x∈dst = events[⇐] x∈dst
events-preserved x@{event-skip uid _} ¬x-elim x∈dst with ℕ-dec uid (elim-uid dst-ok)
... | yes refl    = ⊥-elim (¬x-elim (unique-ids dst-wf uid (has-uid-skip , x∈dst) (elim-has-uid dst-ok , elim∈ex dst-ok)))
... | no uid≢elim = _ , x∈dst , lemma
  where
  -- Unsure why this lemma is needed, as we're above already splitting on
  -- > ℕ-dec uid (elim-uid dst-ok)
  -- But without this lemma, it doesn't type-check
  lemma : x ≡ ev[⇐] x∈dst
  lemma with ℕ-dec uid (elim-uid dst-ok)
  ... | yes refl = ⊥-elim (uid≢elim refl)
  ... | no _     = refl
events-preserved {event _ _ _}      ¬x-elim x∈dst = events[⇐] x∈dst


src-elim-ev-def : src-elim-ev ≡ event (elim-uid dst-ok) (elim-tid dst-ok) (lab-r tmov (elim-loc dst-ok) (elim-val dst-ok))
src-elim-ev-def with elim-ev-skip dst-ok
-- this is strange, but necessary as it matches over the cases in `ev[⇐]`
src-elim-ev-def | ev-skip with ℕ-dec (elim-uid dst-ok) (elim-uid dst-ok)
src-elim-ev-def | ev-skip | yes refl = refl
src-elim-ev-def | ev-skip | no uid≢uid = ⊥-elim (uid≢uid refl)


src-mapping : RAWMapping src dst-ok
src-mapping =
  record
    { src-elim-ev      = src-elim-ev
    ; src-elim-ev-def  = src-elim-ev-def
    ; src-elim-ev∈src  = elim∈src
    ; events-preserved = events-preserved
    }
