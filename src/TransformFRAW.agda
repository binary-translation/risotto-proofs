{-# OPTIONS --safe #-}

-- Read-after-write transformation
module TransformFRAW where

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
-- FRAW: X = v; F; a = X  ->  X = v; F; a = v
--                 ^
--                 |
--                This Read becomes a Skip
--


-- | We assume the TCG program is obtained through mapping a x86 program.
--
-- This means that /not/ all fences can be present in the execution. If all
-- fences were present, this mapping is /incorrect/ in general.
data FRAWEvent : Event LabelTCG → Set where
  raw-init : {uid : UniqueId} {loc : Location} {val : Value} → FRAWEvent (event-init uid loc val)
  raw-skip : {uid : UniqueId} {tid : ThreadId} → FRAWEvent (event-skip uid tid)
  raw-r : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → FRAWEvent (event uid tid (lab-r tag loc val))
  raw-w : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → FRAWEvent (event uid tid (lab-w tag loc val))
  raw-f-sc : {uid : UniqueId} {tid : ThreadId} → FRAWEvent (event uid tid (lab-f SC))
  raw-f-rm : {uid : UniqueId} {tid : ThreadId} → FRAWEvent (event uid tid (lab-f RM))
  raw-f-ww : {uid : UniqueId} {tid : ThreadId} → FRAWEvent (event uid tid (lab-f WW))


record FRAW-Restricted (ex : Execution LabelTCG) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsTCGConsistent ex

    events-bound : events ex ⊆₁ FRAWEvent

    pres₁-ev  : Event LabelTCG
    pres₁-wₙᵣ : EvWₙₜ tmov pres₁-ev
    
    pres₂-ev : Event LabelTCG
    pres₂-f  : EvF pres₂-ev

    -- | The skip event that overwrites the eliminated read.
    elim-ev   : Event LabelTCG
    elim-skip : EvSkip elim-ev

    pi[p₁p₂]ᵗ : po-imm ex pres₁-ev pres₂-ev
    pi[p₂e]ᵗ  : po-imm ex pres₂-ev elim-ev

    -- We /specifically/ assume the execution was obtained by /mapping from x86/.
    -- That is, every read operation is directly /followed by/ a F_RM fence.
    po-r-rmʳ : {x : Event LabelTCG} → x ∈ events ex → EvRᵣ x → ∃[ y ] (EvF₌ RM y × po-imm ex x y)
    po-r-rmˡ : {y : Event LabelTCG} → y ∈ events ex → EvF₌ RM y → ∃[ x ] (EvRᵣ x × po-imm ex x y)
    -- Every write operation is directly /preceded by/ a F_WW fence.
    po-w-wwˡ : {y : Event LabelTCG} → y ∈ events ex → EvWₙₜ tmov y → ∃[ x ] (EvF₌ WW x × po-imm ex x y)
    po-w-wwʳ : {x : Event LabelTCG} → x ∈ events ex → EvF₌ WW x → ∃[ y ] (EvWₙₜ tmov y × po-imm ex x y)


open FRAW-Restricted

pres₁-w : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → EvW (pres₁-ev ex-ok)
pres₁-w = wₙₜ⇒w ∘ pres₁-wₙᵣ

pres₁-wᵣ : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → EvWᵣ (pres₁-ev ex-ok)
pres₁-wᵣ = wₙₜ⇒wₜ ∘ pres₁-wₙᵣ

pres₁∈ex : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → pres₁-ev ex-ok ∈ events ex
pres₁∈ex ex-ok = piˡ∈ex (wf ex-ok) (pi[p₁p₂]ᵗ ex-ok)

pres₂∈ex : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → pres₂-ev ex-ok ∈ events ex
pres₂∈ex ex-ok = piʳ∈ex (wf ex-ok) (pi[p₁p₂]ᵗ ex-ok)

elim∈ex : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → elim-ev ex-ok ∈ events ex
elim∈ex ex-ok = piʳ∈ex (wf ex-ok) (pi[p₂e]ᵗ ex-ok)

pres₂-mode : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → ∃[ mode ] (EvF₌ mode (pres₂-ev ex-ok))
pres₂-mode ex-ok with pres₂-ev ex-ok | pres₂-f ex-ok
... | event _ _ (lab-f mode) | ev-f is-f = mode , ev-f₌

elim-uid : {ex : Execution LabelTCG} → FRAW-Restricted ex → UniqueId
elim-uid = ev-uid ∘ elim-ev

elim-has-uid : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → HasUid (elim-uid ex-ok) (elim-ev ex-ok)
elim-has-uid _ = ev-has-uid _

elim-tid : {ex : Execution LabelTCG} → FRAW-Restricted ex → ThreadId
elim-tid = skip-tid ∘ elim-skip

elim-loc : {ex : Execution LabelTCG} → FRAW-Restricted ex → Location
elim-loc = w-loc ∘ pres₁-w

elim-val : {ex : Execution LabelTCG} → FRAW-Restricted ex → Value
elim-val = w-val ∘ pres₁-w

pres₁-has-loc : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → HasLoc (elim-loc ex-ok) (pres₁-ev ex-ok)
pres₁-has-loc ex-ok with pres₁-w ex-ok
... | ev-w is-w = has-loc-w is-w refl

pres₁-has-val : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → HasVal (elim-val ex-ok) (pres₁-ev ex-ok)
pres₁-has-val ex-ok with pres₁-w ex-ok
... | ev-w is-w = has-val-w is-w refl


-- | Relates the source and target executions.
--
-- If the source has the additional write event, then - by WellFormedness - it is part of the execution.
record FRAWMapping (src : Execution LabelTCG) {dst : Execution LabelTCG} (dst-res : FRAW-Restricted dst) : Set where
  field
    src-elim-ev     : Event LabelTCG
    src-elim-ev-def : src-elim-ev ≡ event (elim-uid dst-res) (elim-tid dst-res) (lab-r tmov (elim-loc dst-res) (elim-val dst-res))
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelTCG} → x ≢ elim-ev dst-res → x ∈ events dst → x ∈ events src
