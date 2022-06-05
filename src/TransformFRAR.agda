{-# OPTIONS --safe #-}

-- Fence-Read-after-Read transformation
module TransformFRAR where

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
-- FRAR: a = X; F; b = X  ->  a = X; F; b = a
--                 ^
--                 |
--                This Read becomes a Skip
--


data FRAREvent : Event LabelTCG → Set where
  raw-init : {uid : UniqueId} {loc : Location} {val : Value} → FRAREvent (event-init uid loc val)
  raw-skip : {uid : UniqueId} {tid : ThreadId} → FRAREvent (event-skip uid tid)
  raw-r    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → FRAREvent (event uid tid (lab-r tag loc val))
  raw-w    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → FRAREvent (event uid tid (lab-w tag loc val))
  raw-f-sc : {uid : UniqueId} {tid : ThreadId} → FRAREvent (event uid tid (lab-f SC))
  raw-f-rm : {uid : UniqueId} {tid : ThreadId} → FRAREvent (event uid tid (lab-f RM))
  raw-f-ww : {uid : UniqueId} {tid : ThreadId} → FRAREvent (event uid tid (lab-f WW))


record FRAR-Restricted (ex : Execution LabelTCG) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsTCGConsistent ex

    events-bound : events ex ⊆₁ FRAREvent
    
    pres₁-ev  : Event LabelTCG
    pres₁-rₜ  : EvRₜ tmov pres₁-ev
    
    pres₂-ev : Event LabelTCG
    pres₂-f  : EvF pres₂-ev

    -- | The skip event that overwrites the eliminated read.
    elim-ev      : Event LabelTCG
    elim-ev-skip : EvSkip elim-ev

    pair₁-pi : po-imm ex pres₁-ev pres₂-ev
    pair₂-pi : po-imm ex pres₂-ev elim-ev

    -- Note that we -- specifically -- assume the execution was obtained by /mapping from x86/.
    -- That is, every read operation is directly followed by a F_RM fence.
    po-r-rm : {x : Event LabelTCG} → x ∈ events ex → EvRᵣ x → ∃[ y ] (EvF₌ RM y × po-imm ex x y)

open FRAR-Restricted


pres₁-r : {ex : Execution LabelTCG} → (ex-ok : FRAR-Restricted ex) → EvR (pres₁-ev ex-ok)
pres₁-r = rₜ⇒r ∘ pres₁-rₜ

elim-uid : {ex : Execution LabelTCG} → FRAR-Restricted ex → UniqueId
elim-uid = ev-uid ∘ elim-ev

elim-has-uid : {ex : Execution LabelTCG} → (ex-ok : FRAR-Restricted ex) → HasUid (elim-uid ex-ok) (elim-ev ex-ok)
elim-has-uid ex-ok = ev-has-uid _

elim-tid : {ex : Execution LabelTCG} → FRAR-Restricted ex → ThreadId
elim-tid = skip-tid ∘ elim-ev-skip

elim-loc : {ex : Execution LabelTCG} → FRAR-Restricted ex → Location
elim-loc = r-loc ∘ pres₁-r

elim-val : {ex : Execution LabelTCG} → FRAR-Restricted ex → Value
elim-val = r-val ∘ pres₁-r

pres₁∈ex : {ex : Execution LabelTCG} → (ex-ok : FRAR-Restricted ex) → pres₁-ev ex-ok ∈ events ex
pres₁∈ex ex-ok = piˡ∈ex (wf ex-ok) (pair₁-pi ex-ok)

pres₂∈ex : {ex : Execution LabelTCG} → (ex-ok : FRAR-Restricted ex) → pres₂-ev ex-ok ∈ events ex
pres₂∈ex ex-ok = piˡ∈ex (wf ex-ok) (pair₂-pi ex-ok)

elim∈ex : {ex : Execution LabelTCG} → (ex-ok : FRAR-Restricted ex) → elim-ev ex-ok ∈ events ex
elim∈ex ex-ok = piʳ∈ex (wf ex-ok) (pair₂-pi ex-ok)

pres₁-has-loc : {ex : Execution LabelTCG} → (ex-ok : FRAR-Restricted ex) → HasLoc (elim-loc ex-ok) (pres₁-ev ex-ok)
pres₁-has-loc ex-ok with pres₁-r ex-ok
... | ev-r is-r = has-loc-r is-r refl

pres₁-has-val : {ex : Execution LabelTCG} → (ex-ok : FRAR-Restricted ex) → HasVal (elim-val ex-ok) (pres₁-ev ex-ok)
pres₁-has-val ex-ok with pres₁-r ex-ok
... | ev-r is-r = has-val-r is-r refl


-- | Relates the source and target executions.
--
-- If the source has the additional read event, then - by WellFormedness - it is part of the execution.
record FRARMapping (src : Execution LabelTCG) {dst : Execution LabelTCG} (dst-ok : FRAR-Restricted dst) : Set where
  field
    src-elim-ev     : Event LabelTCG
    src-elim-ev-def : src-elim-ev ≡ event (elim-uid dst-ok) (elim-tid dst-ok) (lab-r tmov (elim-loc dst-ok) (elim-val dst-ok))
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelTCG} → x ≢ elim-ev dst-ok → x ∈ events dst → x ∈ events src
