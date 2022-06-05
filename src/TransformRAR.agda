{-# OPTIONS --safe #-}

-- Read-after-read transformation
module TransformRAR where

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
-- RAR: a = X; b = X  ->  a = X; b = a
--             ^
--             |
--            This Read becomes a Skip
--

record RAR-Restricted (ex : Execution LabelTCG) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsTCGConsistent ex

    -- | The skip event that overwrites the eliminated read.
    elim-ev      : Event LabelTCG
    elim-ev-skip : elim-ev ∈ EvSkip
    
    preserved-ev   : Event LabelTCG
    preserved-ev-r : preserved-ev ∈ EvRₜ tmov

    transform-pair : po-imm ex preserved-ev elim-ev

open RAR-Restricted
  

elim-uid : {ex : Execution LabelTCG} → RAR-Restricted ex → UniqueId
elim-uid = ev-uid ∘ elim-ev

elim-has-uid : {ex : Execution LabelTCG} → (ex-ok : RAR-Restricted ex) → HasUid (elim-uid ex-ok) (elim-ev ex-ok)
elim-has-uid ex-ok = ev-has-uid _

elim-tid : {ex : Execution LabelTCG} → RAR-Restricted ex → ThreadId
elim-tid = skip-tid ∘ elim-ev-skip

elim-loc : {ex : Execution LabelTCG} → RAR-Restricted ex → Location
elim-loc = r-loc ∘ rₜ⇒r ∘ preserved-ev-r

elim-val : {ex : Execution LabelTCG} → RAR-Restricted ex → Value
elim-val = r-val ∘ rₜ⇒r ∘ preserved-ev-r

preserved∈ex : {ex : Execution LabelTCG} → (ex-ok : RAR-Restricted ex) → preserved-ev ex-ok ∈ events ex
preserved∈ex ex-ok = piˡ∈ex (wf ex-ok) (transform-pair ex-ok)

elim∈ex : {ex : Execution LabelTCG} → (ex-ok : RAR-Restricted ex) → elim-ev ex-ok ∈ events ex
elim∈ex ex-ok = piʳ∈ex (wf ex-ok) (transform-pair ex-ok)

preserved-has-loc : {ex : Execution LabelTCG} → (ex-ok : RAR-Restricted ex) → HasLoc (elim-loc ex-ok) (preserved-ev ex-ok)
preserved-has-loc ex-ok with preserved-ev-r ex-ok
... | ev-r is-r refl = has-loc-r is-r refl

preserved-has-val : {ex : Execution LabelTCG} → (ex-ok : RAR-Restricted ex) → HasVal (elim-val ex-ok) (preserved-ev ex-ok)
preserved-has-val ex-ok with preserved-ev-r ex-ok
... | ev-r is-r refl = has-val-r is-r refl


-- | Relates the source and target executions.
--
-- If the source has the additional read event, then - by WellFormedness - it is part of the execution.
record RARMapping (src : Execution LabelTCG) {dst : Execution LabelTCG} (dst-res : RAR-Restricted dst) : Set where
  field
    src-elim-ev     : Event LabelTCG
    src-elim-ev-def : src-elim-ev ≡ event (elim-uid dst-res) (elim-tid dst-res) (lab-r tmov (elim-loc dst-res) (elim-val dst-res))
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelTCG} → x ≢ elim-ev dst-res → x ∈ events dst → x ∈ events src
