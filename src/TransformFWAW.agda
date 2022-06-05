{-# OPTIONS --safe #-}

-- Fence-Write-after-Write transformation
module TransformFWAW where

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
-- Library imports: Relations
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.TCG as TCG


open Execution


--
-- FWAW: X = v'; F; X = v  ↦  F; X = v
--       ^
--       |
--      This Write becomes a Skip
--


data FWAWEvent : Event LabelTCG → Set where
  raw-init : {uid : UniqueId} {loc : Location} {val : Value} → FWAWEvent (event-init uid loc val)
  raw-skip : {uid : UniqueId} {tid : ThreadId} → FWAWEvent (event-skip uid tid)
  raw-r    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → FWAWEvent (event uid tid (lab-r tag loc val))
  raw-w    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → FWAWEvent (event uid tid (lab-w tag loc val))
  raw-f-sc : {uid : UniqueId} {tid : ThreadId} → FWAWEvent (event uid tid (lab-f SC))
  raw-f-rm : {uid : UniqueId} {tid : ThreadId} → FWAWEvent (event uid tid (lab-f RM))
  raw-f-ww : {uid : UniqueId} {tid : ThreadId} → FWAWEvent (event uid tid (lab-f WW))


record FWAW-Restricted (ex : Execution LabelTCG) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsTCGConsistent ex

    events-bound : events ex ⊆₁ FWAWEvent
    
    -- | The skip event that overwrites the eliminated read.
    elim-ev      : Event LabelTCG
    elim-ev-skip : elim-ev ∈ EvSkip

    -- preserved event 1
    pres₁-ev  : Event LabelTCG
    pres₁-f   : EvF pres₁-ev

    -- preserved event 2
    pres₂-ev  : Event LabelTCG
    -- non-init relaxed write
    pres₂-wₙᵣ : EvWₙₜ tmov pres₂-ev

    pi[ep₁]ᵗ  : po-imm ex elim-ev pres₁-ev
    pi[p₁p₂]ᵗ : po-imm ex pres₁-ev pres₂-ev

    -- Note that we -- specifically -- assume the execution was obtained by /mapping from x86/.
    -- That is, every read operation is directly /followed by/ a F_RM fence.
    po-r-rm : {x : Event LabelTCG} → x ∈ events ex → EvRᵣ x → ∃[ y ] (EvF₌ RM y × po-imm ex x y)
    -- Every write operation is directly /preceded by/ a F_WW fence.
    po-w-ww : {y : Event LabelTCG} → y ∈ events ex → EvWₙₜ tmov y → ∃[ x ] (EvF₌ WW x × po-imm ex x y)

open FWAW-Restricted

pres₂-wᵣ : {ex : Execution LabelTCG} → (ex-ok : FWAW-Restricted ex) → EvWᵣ (pres₂-ev ex-ok)
pres₂-wᵣ = wₙₜ⇒wₜ ∘ pres₂-wₙᵣ

pres₂-w : {ex : Execution LabelTCG} → (ex-ok : FWAW-Restricted ex) → EvW (pres₂-ev ex-ok)
pres₂-w = wₜ⇒w ∘ pres₂-wᵣ

elim-uid : {ex : Execution LabelTCG} → FWAW-Restricted ex → UniqueId
elim-uid = ev-uid ∘ elim-ev

elim-has-uid : {ex : Execution LabelTCG} → (ex-ok : FWAW-Restricted ex) → HasUid (elim-uid ex-ok) (elim-ev ex-ok)
elim-has-uid ex-ok = ev-has-uid _

elim-tid : {ex : Execution LabelTCG} → FWAW-Restricted ex → ThreadId
elim-tid = skip-tid ∘ elim-ev-skip

elim-loc : {ex : Execution LabelTCG} → FWAW-Restricted ex → Location
elim-loc = w-loc ∘ pres₂-w

elim-val : {ex : Execution LabelTCG} → FWAW-Restricted ex → Value
elim-val = w-val ∘ pres₂-w


pres₁∈ex : {ex : Execution LabelTCG} → (ex-ok : FWAW-Restricted ex) → pres₁-ev ex-ok ∈ events ex
pres₁∈ex ex-ok = piʳ∈ex (wf ex-ok) (pi[ep₁]ᵗ ex-ok)

pres₂∈ex : {ex : Execution LabelTCG} → (ex-ok : FWAW-Restricted ex) → pres₂-ev ex-ok ∈ events ex
pres₂∈ex ex-ok = piʳ∈ex (wf ex-ok) (pi[p₁p₂]ᵗ ex-ok)

elim∈ex : {ex : Execution LabelTCG} → (ex-ok : FWAW-Restricted ex) → elim-ev ex-ok ∈ events ex
elim∈ex ex-ok = piˡ∈ex (wf ex-ok) (pi[ep₁]ᵗ ex-ok)


pres₂-has-loc : {ex : Execution LabelTCG} → (ex-ok : FWAW-Restricted ex) → HasLoc (elim-loc ex-ok) (pres₂-ev ex-ok)
pres₂-has-loc ex-ok with pres₂-w ex-ok
... | ev-w is-w = has-loc-w is-w refl

pres₂-has-val : {ex : Execution LabelTCG} → (ex-ok : FWAW-Restricted ex) → HasVal (elim-val ex-ok) (pres₂-ev ex-ok)
pres₂-has-val ex-ok with pres₂-w ex-ok
... | ev-w is-w = has-val-w is-w refl

po[ep₂]ᵗ : {ex : Execution LabelTCG} → (ex-ok : FWAW-Restricted ex) → po ex (elim-ev ex-ok) (pres₂-ev ex-ok)
po[ep₂]ᵗ ex-ok = po-trans (wf ex-ok) (proj₁ (pi[ep₁]ᵗ ex-ok)) (proj₁ (pi[p₁p₂]ᵗ ex-ok))


-- | Relates the source and target executions.
--
-- If the source has the additional write event, then - by WellFormedness - it is part of the execution.
record FWAWMapping (src : Execution LabelTCG) {dst : Execution LabelTCG} (dst-res : FWAW-Restricted dst) : Set where
  field
    src-elim-ev     : Event LabelTCG
    src-elim-ev-def : src-elim-ev ≡ event (elim-uid dst-res) (elim-tid dst-res) (lab-w tmov (elim-loc dst-res) (elim-val dst-res))
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelTCG} → x ≢ elim-ev dst-res → x ∈ events dst → x ∈ events src
