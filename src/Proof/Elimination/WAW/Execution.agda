{-# OPTIONS --safe #-}


open import Arch.General.Execution using (Execution)
open import Arch.TCG using (LabelTCG)
open import TransformWAW using (WAW-Restricted)


module Proof.Elimination.WAW.Execution
  (dst : Execution LabelTCG) (dst-ok : WAW-Restricted dst) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_])
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.TCG as TCG
open import Arch.TCG.Detour
-- Local imports: Other
open import Helpers
-- Local imports: Theorem Specification
open import TransformWAW
-- Local imports: Proof Components
import Proof.Framework LabelTCG dst (WAW-Restricted.wf dst-ok) as Ψ
import Proof.Elimination.Framework dst (WAW-Restricted.wf dst-ok) as Δ


open Ex.Execution
open Ex.WellFormed
open WAW-Restricted

dst-wf = wf dst-ok


--
-- The transformation:
--
-- WAW: X = v'; X = v  ↦  X = v
--      ^
--      |
--     This Write becomes a Skip
--


-- File structure
-- * General Proof Framework
-- * Elimination Proof Framework
-- * Execution
-- * Extra


-- # General Definitions

-- | It is identical between the source and target, because it is preserved.
-- src-preserved-ev : Event LabelTCG
-- src-preserved-ev = preserved-ev dst-ok


-- # Backward Mapping of Execution

ev[⇐] : {x : Event LabelTCG} → (x∈dst : x ∈ events dst) → Event LabelTCG
ev[⇐] x@{event-init _ _ _} x∈dst = x
ev[⇐] {event-skip uid tid} x∈dst with ℕ-dec uid (elim-uid dst-ok)
... | yes refl     = event uid tid (lab-w tmov (elim-loc dst-ok) (elim-val dst-ok))
... | no  uid≢elim = event-skip uid tid
ev[⇐] x@{event _ _ _} x∈dst = x
  
elim-wₙₜ : EvWₙₜ tmov (ev[⇐] (elim∈ex dst-ok))
elim-wₙₜ with inspect (elim-ev-skip dst-ok)
elim-wₙₜ | ev-skip with≡ refl with ℕ-dec (elim-uid dst-ok) (elim-uid dst-ok)
elim-wₙₜ | ev-skip with≡ refl | yes refl      = ev-w is-w refl
elim-wₙₜ | ev-skip with≡ refl | no ¬elim-elim = ⊥-elim (¬elim-elim refl)


-- # Framework

open Ψ.Definitions ev[⇐]
open Δ.Types ev[⇐] (elim-ev dst-ok)

src-po : Rel (Event LabelTCG) ℓzero
src-po = src-rel (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

-- Note that `co` is an order, and thus transitive. The order between other `co`-related events remains preserved.
--
-- We add additional edges, though:
-- * co[py] → co[ey]
-- * co[xp] → co[xe] if x ≢ e
data SrcCo (x y : Event LabelTCG) : Set where
  co-dst : src-rel (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) x y → SrcCo x y
  -- co[py] → co[ey]
  co-newˡ : {y-dst : Event LabelTCG}
    → (dst-co[py] : co dst (preserved-ev dst-ok) y-dst)
    → x ≡ ev[⇐] (elim∈ex dst-ok)
    → y ≡ ev[⇐] (coʳ∈ex dst-wf dst-co[py])
    → SrcCo x y
  -- co[xp] → co[xe]
  co-newʳ : {x-dst : Event LabelTCG}
    → (dst-co[xp] : co dst x-dst (preserved-ev dst-ok))
    → x ≡ ev[⇐] (coˡ∈ex dst-wf dst-co[xp])
    → y ≡ ev[⇐] (elim∈ex dst-ok)
    → SrcCo x y
  co-ep :
      x ≡ ev[⇐] (elim∈ex dst-ok)
    → y ≡ ev[⇐] (preserved∈ex dst-ok)
    → SrcCo x y

src-rf : Rel (Event LabelTCG) ℓzero
-- There is no need to re-attach the source read of a preserved write to it's preceding eliminated write
-- as we're picking the execution. An eliminated write is never read from.
src-rf = src-rel (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

elim-rwₙₜ : EvRWₙₜ tmov (ev[⇐] (elim∈ex dst-ok))
elim-rwₙₜ = wₙₜ⇒rwₙₜ elim-wₙₜ

uid[⇐] : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
uid[⇐]       x∈dst has-uid-init = has-uid-init
uid[⇐] {uid} x∈dst has-uid-skip with ℕ-dec uid (elim-uid dst-ok)
uid[⇐]       x∈dst has-uid-skip | yes refl = has-uid
uid[⇐]       x∈dst has-uid-skip | no  _    = has-uid-skip
uid[⇐]       x∈dst has-uid = has-uid

uid[$⇒] : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _} x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip uid _} x∈dst _ with ℕ-dec uid (elim-uid dst-ok)
uid[$⇒] {_}                    x∈dst has-uid      | yes refl = has-uid-skip
uid[$⇒] {_}                    x∈dst has-uid-skip | no  _    = has-uid-skip
uid[$⇒] {_} {event _ _ _}      x∈dst has-uid = has-uid


tid[⇐] : {tid : ThreadId} → Pred[⇐]² (HasTid tid)
tid[⇐] {_} {event-skip uid _} x∈dst has-tid-skip with ℕ-dec uid (elim-uid dst-ok)
tid[⇐] {_}                    x∈dst has-tid-skip | yes refl = has-tid
tid[⇐] {_}                    x∈dst has-tid-skip | no  _    = has-tid-skip
tid[⇐] {_}                    x∈dst has-tid = has-tid

tid[$⇒] : {tid : ThreadId} → Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip uid _} x∈dst _ with ℕ-dec uid (elim-uid dst-ok)
tid[$⇒] {_}                    x∈dst has-tid      | yes refl    = has-tid-skip
tid[$⇒] {_}                    x∈dst has-tid-skip | no tid≢elim = has-tid-skip
tid[$⇒] {_} {event _ _ _}      x∈dst has-tid = has-tid


loc[⇐] : {loc : Location} → Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init          = has-loc-init
loc[⇐] x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[⇐] x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl

val[⇐] : {val : Value} → Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init          = has-val-init
val[⇐] x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[⇐] x∈dst (has-val-w is-w refl) = has-val-w is-w refl


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init

Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _} x∈dst ev-init = ev-init
Init[$⇒] {event-skip uid _} x∈dst _ with ℕ-dec uid (elim-uid dst-ok)
Init[$⇒]                    x∈dst () | yes refl


ψ : Ψ.GeneralFramework
ψ =
  record
    { ev[⇐]    = ev[⇐]
    ; uid[⇐]   = uid[⇐]
    ; uid[$⇒]  = uid[$⇒]
    ; tid[⇐]   = tid[⇐]
    ; tid[$⇒]  = tid[$⇒]
    ; Init[⇐]  = Init[⇐]
    ; Init[$⇒] = Init[$⇒]
    }


-- # Elimination-specific Framework

open Ψ.WellFormed ψ

Wₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] x∈dst (ev-init refl)   = ev-init refl
Wₜ[⇐] x∈dst (ev-w is-w refl) = ev-w is-w refl

Rₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] x∈dst (ev-r is-r refl) = ev-r is-r refl


F₌[⇐] : {m : F-mode} → Pred[⇐] (EvF₌ m) (EvF₌ m)
F₌[⇐] x∈dst ev-f₌ = ev-f₌

F₌[$⇒] : {m : F-mode} → Pred[$⇒] (EvF₌ m) (EvF₌ m)
F₌[$⇒] {_} {event-skip uid _} x∈dst _ with ℕ-dec uid (elim-uid dst-ok)
F₌[$⇒] {_} {event-skip _   _} x∈dst () | yes refl
F₌[$⇒] {_} {event _ _ _}      x∈dst ev-f₌ = ev-f₌


-- Conditionally preserved properties

loc[$⇒] : {loc : Location} → CPred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _} ¬elim-x x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-skip uid _} ¬elim-x x∈dst _ with ℕ-dec uid (elim-uid dst-ok)
loc[$⇒] {_} {event-skip _ _}   ¬elim-x x∈dst (has-loc-w is-w refl) | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid dst-ok , elim∈ex dst-ok)))
loc[$⇒] {_} {event _ _ _}      ¬elim-x x∈dst x-loc = x-loc

val[$⇒] : {val : Value} → CPred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _} ¬elim-x x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-skip uid _} ¬elim-x x∈dst _ with ℕ-dec uid (elim-uid dst-ok)
val[$⇒] {_} {event-skip _ _}   ¬elim-x x∈dst (has-val-w is-w refl) | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid dst-ok , elim∈ex dst-ok)))
val[$⇒] {_} {event _ _ _}      ¬elim-x x∈dst x-val = x-val

Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-skip uid _} x∈dst _           with ℕ-dec uid (elim-uid dst-ok)
Rₜ[$⇒] {_} {event-skip _ _}   x∈dst (ev-r () _) | yes refl
Rₜ[$⇒] {_} {event _ _ _}      x∈dst (ev-r is-r refl) = ev-r is-r refl

Wₐ[$⇒] : Pred[$⇒]² (EvWₜ trmw)
Wₐ[$⇒] {event-init _ _ _} x∈dst (ev-init ())
Wₐ[$⇒] {event-skip uid _} x∈dst q with ℕ-dec uid (elim-uid dst-ok)
Wₐ[$⇒] {event-skip _ _}   x∈dst (ev-w is-w ()) | yes refl
Wₐ[$⇒] {event _ _ _}      x∈dst (ev-w is-w refl) = ev-w is-w refl

Wᵣ[$⇒] : CPred[$⇒]² (EvWₜ tmov)
Wᵣ[$⇒] {event-init _ _ _} ¬x-elim x∈dst (ev-init refl) = ev-init refl
Wᵣ[$⇒] {event-skip uid _} ¬x-elim x∈dst _ with ℕ-dec uid (elim-uid dst-ok)
Wᵣ[$⇒] {event-skip _ _}   ¬x-elim x∈dst _ | yes refl =
  ⊥-elim (¬x-elim (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid dst-ok , elim∈ex dst-ok)))
Wᵣ[$⇒] {event _ _ _} ¬x-elim x∈dst (ev-w is-w refl) = ev-w is-w refl


co[$⇒] : CRel[$⇒] SrcCo (co dst)
co[$⇒] ¬x-elim ¬y-elim x∈dst y∈dst (co-dst dst-co[xy]) =
  rel[$⇒] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) x∈dst y∈dst dst-co[xy]
co[$⇒] ¬x-elim ¬y-elim x∈dst y∈dst (co-newˡ dst-co[py] p _) = ⊥-elim (¬x-elim (ev[$⇒]eq x∈dst (elim∈ex dst-ok) p))
co[$⇒] ¬x-elim ¬y-elim x∈dst y∈dst (co-newʳ dst-co[xp] _ q) = ⊥-elim (¬y-elim (ev[$⇒]eq y∈dst (elim∈ex dst-ok) q))
co[$⇒] ¬x-elim ¬y-elim x∈dst y∈dst (co-ep p _) = ⊥-elim (¬x-elim (ev[$⇒]eq x∈dst (elim∈ex dst-ok) p))

co[⇐] : Rel[⇐] SrcCo (co dst)
co[⇐] x∈dst y∈dst = co-dst ∘ rel[⇐] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) x∈dst y∈dst


rf[$⇒] : Rel[$⇒] src-rf (rf dst)
rf[$⇒] = rel[$⇒] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

rf[⇐] : Rel[⇐] src-rf (rf dst)
rf[⇐] = rel[⇐] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

δ : Δ.EliminationFramework
δ =
  record
    { ψ        = ψ
    ; elim-ev  = elim-ev dst-ok
    ; elim∈ex  = elim∈ex dst-ok
    ; src-co   = SrcCo
    ; src-rf   = src-rf
    ; elim-r/w = elim-rwₙₜ
    ; loc[⇐]   = loc[⇐]
    ; val[⇐]   = val[⇐]
    ; Wₜ[⇐]    = Wₜ[⇐]
    ; Rₜ[⇐]    = Rₜ[⇐]
    ; F₌[⇐]    = F₌[⇐]
    ; F₌[$⇒]   = F₌[$⇒]
    ; Wₐ[$⇒]   = Wₐ[$⇒]
    ; Rₐ[$⇒]   = Rₜ[$⇒]
    ; rf[⇐]    = rf[⇐]
    ; co[⇐]    = co[⇐]
    ; Wᵣ[$⇒]   = Wᵣ[$⇒]
    ; Rᵣ[$⇒]   = λ _ → Rₜ[$⇒]
    ; loc[$⇒]  = loc[$⇒]
    ; val[$⇒]  = val[$⇒]
    ; rf[$⇒]   = λ _ _ → rf[$⇒]
    ; co[$⇒]   = co[$⇒]
    }


open Δ.Definitions δ


-- # Extra Helpers

module Extra where
  
  src-preserved-ev : Event LabelTCG
  src-preserved-ev = ev[⇐] (preserved∈ex dst-ok)

  preserved∈src : src-preserved-ev ∈ events src
  preserved∈src = events[⇐] (preserved∈ex dst-ok)

  src-preserved-wᵣ : EvWₜ tmov src-preserved-ev
  src-preserved-wᵣ = Wₜ[⇐] (preserved∈ex dst-ok) (preserved-ev-wᵣ dst-ok)
  
  src-preserved-w : EvW src-preserved-ev
  src-preserved-w = W[⇐] (preserved∈ex dst-ok) (preserved-ev-w dst-ok)

  elim∈src : src-elim-ev ∈ events src
  elim∈src = events[⇐] (elim∈ex dst-ok)

  src-elim-w : EvW src-elim-ev
  src-elim-w with elim-ev-skip dst-ok
  ... | ev-skip with ℕ-dec (elim-uid dst-ok) (elim-uid dst-ok)
  ... | yes refl = ev-w is-w
  ... | no uid≢uid = ⊥-elim (uid≢uid refl)
  
  src-rfˡ-w : {x y : Event LabelTCG} → src-rf x y → EvW x
  src-rfˡ-w (x-dst , y-dst , rf[xy] , refl , refl) =
    W[⇐] (rfˡ∈ex dst-wf rf[xy]) (×₂-applyˡ (rf-w×r dst-wf) rf[xy])

  src-rfʳ-r : {x y : Event LabelTCG} → src-rf x y → EvR y
  src-rfʳ-r (x-dst , y-dst , rf[xy] , refl , refl) =
    R[⇐] (rfʳ∈ex dst-wf rf[xy]) (×₂-applyʳ (rf-w×r dst-wf) rf[xy])

  src-coˡ-w : {x y : Event LabelTCG} → SrcCo x y → EvW x
  src-coˡ-w (co-dst (_ , _ , co[xy] , refl , refl)) =
    W[⇐] (coˡ∈ex dst-wf co[xy]) (×₂-applyˡ (co-w×w dst-wf) co[xy])
  src-coˡ-w (co-newˡ co[py] refl refl) = wₙₜ⇒w elim-wₙₜ
  src-coˡ-w (co-newʳ co[xp] refl refl) =
    W[⇐] (coˡ∈ex dst-wf co[xp]) (×₂-applyˡ (co-w×w dst-wf) co[xp])
  src-coˡ-w (co-ep refl refl) = wₙₜ⇒w elim-wₙₜ

  src-coʳ-w : {x y : Event LabelTCG} → SrcCo x y → EvW y
  src-coʳ-w (co-dst (_ , _ , co[xy] , refl , refl)) =
    W[⇐] (coʳ∈ex dst-wf co[xy]) (×₂-applyʳ (co-w×w dst-wf) co[xy])
  src-coʳ-w (co-newˡ co[py] refl refl) =
    W[⇐] (coʳ∈ex dst-wf co[py]) (×₂-applyʳ (co-w×w dst-wf) co[py])
  src-coʳ-w (co-newʳ co[xp] refl refl) = wₙₜ⇒w elim-wₙₜ
  src-coʳ-w (co-ep refl refl) = src-preserved-w


  -- # Eliminated / Preserved Event Definitions

  src-preserved-def : src-preserved-ev ≡ preserved-ev dst-ok
  src-preserved-def with preserved-ev-w dst-ok
  ... | ev-w is-w = refl

  src-elim-has-uid : HasUid (elim-uid dst-ok) src-elim-ev
  src-elim-has-uid = uid[⇐] (elim∈ex dst-ok) (elim-has-uid dst-ok)

  src-transform-pair : po-imm src src-elim-ev src-preserved-ev
  src-transform-pair = pi[⇐$] elim∈src preserved∈src (transform-pair dst-ok)

  src-elim-has-loc : HasLoc (elim-loc dst-ok) src-elim-ev
  src-elim-has-loc with elim-ev-skip dst-ok
  src-elim-has-loc | ev-skip with ℕ-dec (elim-uid dst-ok) (elim-uid dst-ok)
  src-elim-has-loc | ev-skip | yes refl = has-loc-w is-w refl
  src-elim-has-loc | ev-skip | no ¬elim-elim = ⊥-elim (¬elim-elim refl)

  src-elim-has-val : HasVal (elim-val dst-ok) src-elim-ev
  src-elim-has-val with elim-ev-skip dst-ok
  src-elim-has-val | ev-skip with ℕ-dec (elim-uid dst-ok) (elim-uid dst-ok)
  src-elim-has-val | ev-skip | yes refl = has-val-w is-w refl
  src-elim-has-val | ev-skip | no ¬elim-elim = ⊥-elim (¬elim-elim refl)

  src-preserved-has-loc : HasLoc (elim-loc dst-ok) src-preserved-ev
  src-preserved-has-loc = loc[⇐] (preserved∈ex dst-ok) (preserved-has-loc dst-ok)
  
  src-preserved-has-val : HasVal (elim-val dst-ok) src-preserved-ev
  src-preserved-has-val = val[⇐] (preserved∈ex dst-ok) (preserved-has-val dst-ok)

  pe-sloc : SameLoc src-preserved-ev src-elim-ev
  pe-sloc = same-loc src-preserved-has-loc src-elim-has-loc

  pe-sval : SameVal src-preserved-ev src-elim-ev
  pe-sval = same-val src-preserved-has-val src-elim-has-val

  p≢e : src-preserved-ev ≢ src-elim-ev
  p≢e τ with ev[$⇒]eq (preserved∈ex dst-ok) (elim∈ex dst-ok) τ
  ... | refl = po-irreflexive dst-wf refl (proj₁ (transform-pair dst-ok))


  -- # Relation properties

  rfˡ∈src : rf src ˡ∈src
  rfˡ∈src = relˡ∈src (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

  rfʳ∈src : rf src ʳ∈src
  rfʳ∈src = relʳ∈src (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)
  
  udr-rf∈src : udr[ rf src ]∈src
  udr-rf∈src = lr→udr (rf src) rfˡ∈src rfʳ∈src


  coˡ∈src : co src ˡ∈src
  coˡ∈src (co-dst co[xy]) = relˡ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) co[xy]
  coˡ∈src (co-newˡ co[py] refl refl) = elim∈src
  coˡ∈src (co-newʳ co[xp] refl refl) = events[⇐] (coˡ∈ex dst-wf co[xp])
  coˡ∈src (co-ep refl refl) = elim∈src

  coʳ∈src : co src ʳ∈src
  coʳ∈src (co-dst co[xy]) = relʳ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) co[xy]
  coʳ∈src (co-newˡ co[py] refl refl) = events[⇐] (coʳ∈ex dst-wf co[py])
  coʳ∈src (co-newʳ co[xp] refl refl) = elim∈src
  coʳ∈src (co-ep refl refl) = preserved∈src

  udr-co∈src : udr[ co src ]∈src
  udr-co∈src = lr→udr (co src) coˡ∈src coʳ∈src


  coˡ-e⇒p : {y : Event LabelTCG} → y ≢ src-preserved-ev → co src src-elim-ev y → co src src-preserved-ev y
  coˡ-e⇒p ¬y-pres (co-newˡ co[py] refl refl) = co-dst (_ , _ , co[py] , refl , refl)
  -- impossible cases
  coˡ-e⇒p ¬y-pres (co-dst (_ , _ , co[ey] , τ , refl))
    with ev[$⇒]eq (elim∈ex dst-ok) (coˡ∈ex dst-wf co[ey]) τ
  ... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyˡ (co-w×w dst-wf) co[ey] , elim-ev-skip dst-ok))
  coˡ-e⇒p ¬y-pres (co-newʳ co[xp] τ refl)
    with ev[$⇒]eq (elim∈ex dst-ok) (coˡ∈ex dst-wf co[xp]) τ
  ... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyˡ (co-w×w dst-wf) co[xp] , elim-ev-skip dst-ok))
  coˡ-e⇒p ¬y-pres (co-ep refl refl) = ⊥-elim (¬y-pres refl)


  coʳ-e⇒p : {x : Event LabelTCG} → co src x src-elim-ev → co src x src-preserved-ev
  coʳ-e⇒p (co-dst (_ , _ , co[xe] , refl , τ))
    with ev[$⇒]eq (elim∈ex dst-ok) (coʳ∈ex dst-wf co[xe]) τ
  ... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyʳ (co-w×w dst-wf) co[xe] , elim-ev-skip dst-ok))
  coʳ-e⇒p (co-newˡ co[pe] refl τ)
    with ev[$⇒]eq (elim∈ex dst-ok) (coʳ∈ex dst-wf co[pe]) τ
  ... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyʳ (co-w×w dst-wf) co[pe] , elim-ev-skip dst-ok))
  coʳ-e⇒p (co-newʳ dst-co[xp] refl refl) = co-dst (_ , _ , dst-co[xp] , refl , refl)
  coʳ-e⇒p (co-ep refl τ) = ⊥-elim (p≢e (≡-sym τ))


  frʳ-e⇒p : ∀ {x : Event LabelTCG} → fr src x src-elim-ev → fr src x src-preserved-ev
  frʳ-e⇒p (rf⁻¹[xz] ⨾[ _ ]⨾ co[ze]) = rf⁻¹[xz] ⨾[ _ ]⨾ coʳ-e⇒p co[ze]
