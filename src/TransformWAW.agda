{-# OPTIONS --safe #-}

-- Write-after-Write transformation
module TransformWAW where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong; cong₂) renaming (sym to ≡-sym)
open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim; ⊥)
open import Data.Product using (_×_; _,_; ∃-syntax; map₂; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Tri)
-- Local imports: Relations
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.TCG as TCG

open import Helpers


open Execution

--
-- WAW: X = v'; X = v  ↦  X = v
--      ^
--      |
--     This Write becomes a Skip
--


record WAW-Restricted (ex : Execution LabelTCG) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsTCGConsistent ex

    -- | The skip event that overwrites the eliminated read.
    elim-ev      : Event LabelTCG
    elim-ev-skip : elim-ev ∈ EvSkip
    
    preserved-ev     : Event LabelTCG
    -- non-init relaxed write
    preserved-ev-wₙᵣ : preserved-ev ∈ EvWₙₜ tmov

    transform-pair : po-imm ex elim-ev preserved-ev

open WAW-Restricted

-- relaxed write
preserved-ev-wᵣ : {ex : Execution LabelTCG} → (ex-ok : WAW-Restricted ex) → EvWₜ tmov (preserved-ev ex-ok)
preserved-ev-wᵣ ex-ok = wₙₜ⇒wₜ (preserved-ev-wₙᵣ ex-ok)

preserved-ev-w : {ex : Execution LabelTCG} → (ex-ok : WAW-Restricted ex) → EvW (preserved-ev ex-ok)
preserved-ev-w ex-ok = wₙₜ⇒w (preserved-ev-wₙᵣ ex-ok)

elim-uid : {ex : Execution LabelTCG} → WAW-Restricted ex → UniqueId
elim-uid = ev-uid ∘ elim-ev

elim-has-uid : {ex : Execution LabelTCG} → (ex-ok : WAW-Restricted ex) → HasUid (elim-uid ex-ok) (elim-ev ex-ok)
elim-has-uid ex-ok = ev-has-uid _

elim-tid : {ex : Execution LabelTCG} → WAW-Restricted ex → ThreadId
elim-tid = skip-tid ∘ elim-ev-skip

elim-loc : {ex : Execution LabelTCG} → WAW-Restricted ex → Location
elim-loc = w-loc ∘ preserved-ev-w

elim-val : {ex : Execution LabelTCG} → WAW-Restricted ex → Value
elim-val = w-val ∘ preserved-ev-w

preserved∈ex : {ex : Execution LabelTCG} → (ex-ok : WAW-Restricted ex)
  → preserved-ev ex-ok ∈ events ex
preserved∈ex ex-ok = piʳ∈ex (wf ex-ok) (transform-pair ex-ok)

elim∈ex : {ex : Execution LabelTCG} → (ex-ok : WAW-Restricted ex)
  → elim-ev ex-ok ∈ events ex
elim∈ex ex-ok = piˡ∈ex (wf ex-ok) (transform-pair ex-ok)

preserved-has-loc : {ex : Execution LabelTCG} → (ex-ok : WAW-Restricted ex) → HasLoc (elim-loc ex-ok) (preserved-ev ex-ok)
preserved-has-loc ex-ok with preserved-ev-w ex-ok
... | ev-w is-w = has-loc-w is-w refl

preserved-has-val : {ex : Execution LabelTCG} → (ex-ok : WAW-Restricted ex) → HasVal (elim-val ex-ok) (preserved-ev ex-ok)
preserved-has-val ex-ok with preserved-ev-w ex-ok
... | ev-w is-w = has-val-w is-w refl


-- | Relates the source and target executions.
--
-- If the source has the additional write event, then - by WellFormedness - it is part of the execution.
record WAWMapping (src : Execution LabelTCG) {dst : Execution LabelTCG} (dst-res : WAW-Restricted dst) : Set where
  field
    src-elim-ev     : Event LabelTCG
    src-elim-ev-def : src-elim-ev ≡ event (elim-uid dst-res) (elim-tid dst-res) (lab-w tmov (elim-loc dst-res) (elim-val dst-res))
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelTCG} → x ≢ elim-ev dst-res → x ∈ events dst → x ∈ events src
