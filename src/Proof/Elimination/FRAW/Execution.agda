{-# OPTIONS --safe #-}


open import Arch.General.Execution using (Execution)
open import Arch.TCG using (LabelTCG)
open import TransformFRAW using (FRAW-Restricted)


module Proof.Elimination.FRAW.Execution
  (dst : Execution LabelTCG) (dst-ok : FRAW-Restricted dst) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip)
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
open import TransformFRAW
-- Local imports: Proof Components
import Proof.Framework LabelTCG dst (FRAW-Restricted.wf dst-ok) as Ψ
import Proof.Elimination.Framework dst (FRAW-Restricted.wf dst-ok) as Δ


open Ex.Execution
open Ex.WellFormed
open FRAW-Restricted

dst-wf = wf dst-ok


--
-- The transformation:
--
-- X = a; F; b = X  ->  X = a; F; b = a
--


-- # General Definitions

-- | It is identical between the source and target, because it is preserved.
src-pres₁-ev : Event LabelTCG
src-pres₁-ev = pres₁-ev dst-ok

-- | It is identical between the source and target, because it is preserved.
src-pres₂-ev : Event LabelTCG
src-pres₂-ev = pres₂-ev dst-ok


-- # Backward Mapping of Execution

ev[⇐] : {x : Event LabelTCG} → (x∈dst : x ∈ events dst) → Event LabelTCG
ev[⇐] x@{event-init _ _ _} x∈dst = x
-- Note that the target execution only /has a single skip/, which is obtained from the elimination.
ev[⇐] {event-skip uid tid} x∈dst with ℕ-dec uid (elim-uid dst-ok)
... | yes refl     = event uid tid (lab-r tmov (elim-loc dst-ok) (elim-val dst-ok))
... | no  uid≢elim = event-skip uid tid
ev[⇐] x@{event _ _ _} x∈dst = x

elim-rₜ : EvRₜ tmov (ev[⇐] (elim∈ex dst-ok))
elim-rₜ with inspect (elim-skip dst-ok)
elim-rₜ | ev-skip with≡ refl with ℕ-dec (elim-uid dst-ok) (elim-uid dst-ok)
elim-rₜ | ev-skip with≡ refl | yes refl      = ev-r is-r refl
elim-rₜ | ev-skip with≡ refl | no ¬elim-elim = ⊥-elim (¬elim-elim refl)


-- # General Framework

open Ψ.Definitions ev[⇐]
open Δ.Types ev[⇐] (elim-ev dst-ok)


src-po : Rel (Event LabelTCG) ℓzero
src-po = src-rel (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

src-co : Rel (Event LabelTCG) ℓzero
src-co = src-rel (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

-- W × R
data SrcRf (x y : Event LabelTCG) : Set where
  rf-dst : src-rel (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf) x y → SrcRf x y
  -- the eliminated event reads from the preserved event
  rf-new : x ≡ src-pres₁-ev → y ≡ ev[⇐] (elim∈ex dst-ok) → SrcRf x y

elim-rwₙₜ : EvRWₙₜ tmov (ev[⇐] (elim∈ex dst-ok))
elim-rwₙₜ = rₜ⇒rwₙₜ elim-rₜ

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
loc[$⇒] {_} {event-skip _ _}   ¬elim-x x∈dst (has-loc-r is-r refl) | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid dst-ok , elim∈ex dst-ok)))
loc[$⇒] {_} {event _ _ _}      ¬elim-x x∈dst x-loc = x-loc

val[$⇒] : {val : Value} → CPred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _} ¬elim-x x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-skip uid _} ¬elim-x x∈dst _ with ℕ-dec uid (elim-uid dst-ok)
val[$⇒] {_} {event-skip _ _}   ¬elim-x x∈dst (has-val-r is-r refl) | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid dst-ok , elim∈ex dst-ok)))
val[$⇒] {_} {event _ _ _}      ¬elim-x x∈dst x-val = x-val

Wₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _} x∈dst (ev-init refl) = ev-init refl
Wₜ[$⇒] {_} {event-skip uid _} x∈dst _           with ℕ-dec uid (elim-uid dst-ok)
Wₜ[$⇒] {_} {event-skip _ _}   x∈dst (ev-w () _) | yes refl
Wₜ[$⇒] {_} {event _ _ _}      x∈dst (ev-w is-w refl) = ev-w is-w refl

Rₐ[$⇒] : Pred[$⇒]² (EvRₜ trmw)
Rₐ[$⇒] {event-skip uid _} x∈dst q with ℕ-dec uid (elim-uid dst-ok)
Rₐ[$⇒] {event-skip _ _}   x∈dst (ev-r is-r ()) | yes refl
Rₐ[$⇒] {event _ _ _}      x∈dst (ev-r is-r refl) = ev-r is-r refl

Rᵣ[$⇒] : CPred[$⇒]² (EvRₜ tmov)
Rᵣ[$⇒] {event-skip uid _} ¬elim-x x∈dst _ with ℕ-dec uid (elim-uid dst-ok)
Rᵣ[$⇒] {event-skip _ _}   ¬elim-x x∈dst q | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid dst-ok , elim∈ex dst-ok)))
Rᵣ[$⇒] {event _ _ _}      ¬elim-x x∈dst (ev-r is-r refl) = ev-r is-r refl


co[$⇒] : Rel[$⇒] src-co (co dst)
co[$⇒] = rel[$⇒] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

co[⇐] : Rel[⇐] src-co (co dst)
co[⇐] = rel[⇐] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)


rf[$⇒] : CRel[$⇒] SrcRf (rf dst)
rf[$⇒] _ _ x∈dst y∈dst (rf-dst dst-rf[xy]) =
  rel[$⇒] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf) x∈dst y∈dst dst-rf[xy]
rf[$⇒] ¬x-elim ¬y-elim x∈dst y∈dst (rf-new p q) =
  ⊥-elim (¬y-elim (ev[$⇒]eq y∈dst (elim∈ex dst-ok) q))

rf[⇐] : Rel[⇐] SrcRf (rf dst)
rf[⇐] x∈dst y∈dst = rf-dst ∘ (rel[⇐] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf) x∈dst y∈dst)

δ : Δ.EliminationFramework
δ =
  record
    { ψ        = ψ
    ; elim-ev  = elim-ev dst-ok
    ; elim∈ex  = elim∈ex dst-ok
    ; src-co   = src-co
    ; src-rf   = SrcRf
    ; elim-r/w = elim-rwₙₜ
    ; loc[⇐]   = loc[⇐]
    ; val[⇐]   = val[⇐]
    ; Wₜ[⇐]    = Wₜ[⇐]
    ; Rₜ[⇐]    = Rₜ[⇐]
    ; F₌[⇐]    = F₌[⇐]
    ; F₌[$⇒]   = F₌[$⇒]
    ; Wₐ[$⇒]   = Wₜ[$⇒]
    ; Rₐ[$⇒]   = Rₐ[$⇒]
    ; rf[⇐]    = rf[⇐]
    ; co[⇐]    = co[⇐]
    ; Wᵣ[$⇒]   = λ _ → Wₜ[$⇒]
    ; Rᵣ[$⇒]   = Rᵣ[$⇒]
    ; loc[$⇒]  = loc[$⇒]
    ; val[$⇒]  = val[$⇒]
    ; rf[$⇒]   = rf[$⇒]
    ; co[$⇒]   = λ _ _ → co[$⇒]
    }


open Δ.Definitions δ


-- # Extra Helpers

module Extra where

  elim-¬w : {x : Event LabelTCG} → EvW x → x ≢ src-elim-ev
  elim-¬w x-w refl = disjoint-r/w _ (rₜ⇒r elim-rₜ , x-w)
  
  src-rfˡ-w : {x y : Event LabelTCG} → SrcRf x y → EvW x
  src-rfˡ-w (rf-dst (_ , _ , dst-rf[xy] , refl , refl)) =
    W[⇐] (rfˡ∈ex dst-wf dst-rf[xy]) (×₂-applyˡ (rf-w×r dst-wf) dst-rf[xy])
  src-rfˡ-w (rf-new refl refl) = pres₁-w dst-ok

  src-rfʳ-r : {x y : Event LabelTCG} → SrcRf x y → EvR y
  src-rfʳ-r (rf-dst (_ , _ , dst-rf[xy] , refl , refl)) =
    R[⇐] (rfʳ∈ex dst-wf dst-rf[xy]) (×₂-applyʳ (rf-w×r dst-wf) dst-rf[xy])
  src-rfʳ-r (rf-new refl refl) = rₜ⇒r elim-rₜ

  src-coˡ-w : {x y : Event LabelTCG} → co src x y → EvW x
  src-coˡ-w (x-dst , y-dst , dst-co[xy] , refl , refl) =
    W[⇐] (coˡ∈ex dst-wf dst-co[xy]) (×₂-applyˡ (co-w×w dst-wf) dst-co[xy])

  src-coʳ-w : {x y : Event LabelTCG} → co src x y → EvW y
  src-coʳ-w (x-dst , y-dst , dst-co[xy] , refl , refl) =
    W[⇐] (coʳ∈ex dst-wf dst-co[xy]) (×₂-applyʳ (co-w×w dst-wf) dst-co[xy])


  -- |
  --
  -- Any fence between a Write and a Read can only be a SC fence.
  -- By the x86 mapping, WW fences only occur /before/ writes, and RM fences
  -- only occur /after/ reads. (See `FRAW-Restricted`) 
  pres₂-f₌ : {ex : Execution LabelTCG} → (ex-ok : FRAW-Restricted ex) → EvF₌ SC (pres₂-ev ex-ok)
  pres₂-f₌ ex-ok with pres₂-mode ex-ok
  ... | SC  , ev-f₌ = ev-f₌
  -- impossible cases
  ... | RM  , ev-f₌ =
    let (x , x-rᵣ , pi[xp₂]) = po-r-rmˡ ex-ok (pres₂∈ex ex-ok) ev-f₌
        p₁≡x = po-immˡ (wf ex-ok) (pi[p₁p₂]ᵗ ex-ok) pi[xp₂]
    in ⊥-elim (disjoint-r/w _ (rₜ⇒r x-rᵣ , subst EvW p₁≡x (pres₁-w ex-ok)))
  ... | WW  , ev-f₌ =
    let (y , y-wₙᵣ , pi[p₂y]) = po-w-wwʳ ex-ok (pres₂∈ex ex-ok) ev-f₌
        e≡y = po-immʳ (wf ex-ok) (λ()) (pi[p₂e]ᵗ ex-ok) pi[p₂y]
    in ⊥-elim (disjoint-w/skip _ (wₙₜ⇒w y-wₙᵣ , subst EvSkip e≡y (elim-skip ex-ok)))
  ... | RR  , ev-f₌ = absurd (⊆₁-apply (events-bound ex-ok) (pres₂∈ex ex-ok)) (λ())
  ... | RW  , ev-f₌ = absurd (⊆₁-apply (events-bound ex-ok) (pres₂∈ex ex-ok)) (λ())
  ... | WR  , ev-f₌ = absurd (⊆₁-apply (events-bound ex-ok) (pres₂∈ex ex-ok)) (λ())
  ... | WM  , ev-f₌ = absurd (⊆₁-apply (events-bound ex-ok) (pres₂∈ex ex-ok)) (λ())
  ... | MR  , ev-f₌ = absurd (⊆₁-apply (events-bound ex-ok) (pres₂∈ex ex-ok)) (λ())
  ... | MW  , ev-f₌ = absurd (⊆₁-apply (events-bound ex-ok) (pres₂∈ex ex-ok)) (λ())
  ... | MM  , ev-f₌ = absurd (⊆₁-apply (events-bound ex-ok) (pres₂∈ex ex-ok)) (λ())
  ... | ACQ , ev-f₌ = absurd (⊆₁-apply (events-bound ex-ok) (pres₂∈ex ex-ok)) (λ())
  ... | REL , ev-f₌ = absurd (⊆₁-apply (events-bound ex-ok) (pres₂∈ex ex-ok)) (λ())


  -- #
  
  src-pres₁-def : src-pres₁-ev ≡ ev[⇐] (pres₁∈ex dst-ok)
  src-pres₁-def with pres₁-w dst-ok
  ... | ev-w is-w = refl
  
  src-pres₂-def : src-pres₂-ev ≡ ev[⇐] (pres₂∈ex dst-ok)
  src-pres₂-def with pres₂-f dst-ok
  ... | ev-f is-f = refl

  elim∈src : src-elim-ev ∈ events src
  elim∈src = events[⇐] (elim∈ex dst-ok)

  pres₁∈src : src-pres₁-ev ∈ events src
  pres₁∈src = subst (events src) (≡-sym src-pres₁-def) (events[⇐] (pres₁∈ex dst-ok))
  
  pres₂∈src : src-pres₂-ev ∈ events src
  pres₂∈src = subst (events src) (≡-sym src-pres₂-def) (events[⇐] (pres₂∈ex dst-ok))

  pi[p₁p₂]ˢ : po-imm src src-pres₁-ev src-pres₂-ev
  pi[p₁p₂]ˢ =
    subst-rel (po-imm src)
      (≡-sym src-pres₁-def)
      (≡-sym src-pres₂-def)
      (pi[⇐$]
        (events[⇐] (pres₁∈ex dst-ok))
        (events[⇐] (pres₂∈ex dst-ok))
        (pi[p₁p₂]ᵗ dst-ok)
      )
      
  pi[p₂e]ˢ : po-imm src src-pres₂-ev src-elim-ev
  pi[p₂e]ˢ =
    subst-rel (po-imm src)
      (≡-sym src-pres₂-def)
      refl
      (pi[⇐$]
        (events[⇐] (pres₂∈ex dst-ok))
        (events[⇐] (elim∈ex dst-ok))
        (pi[p₂e]ᵗ dst-ok)
      )

  po[p₁e]ᵗ : po dst (pres₁-ev dst-ok) (elim-ev dst-ok)
  po[p₁e]ᵗ = po-trans dst-wf (proj₁ (pi[p₁p₂]ᵗ dst-ok)) (proj₁ (pi[p₂e]ᵗ dst-ok))
      
  po[p₁e]ˢ : po src src-pres₁-ev src-elim-ev
  po[p₁e]ˢ =
    subst-rel (po src)
      (≡-sym src-pres₁-def)
      refl
      (po[⇐$]
        (events[⇐] (pres₁∈ex dst-ok))
        (events[⇐] (elim∈ex dst-ok))
        po[p₁e]ᵗ
      )

  src-elim-has-loc : HasLoc (elim-loc dst-ok) src-elim-ev
  src-elim-has-loc with inspect (elim-skip dst-ok)
  src-elim-has-loc | ev-skip with≡ refl with ℕ-dec (elim-uid dst-ok) (elim-uid dst-ok)
  src-elim-has-loc | ev-skip with≡ refl | yes refl = has-loc-r is-r refl
  src-elim-has-loc | ev-skip with≡ refl | no ¬elim-elim = ⊥-elim (¬elim-elim refl)

  src-elim-has-val : HasVal (elim-val dst-ok) src-elim-ev
  src-elim-has-val with inspect (elim-skip dst-ok)
  src-elim-has-val | ev-skip with≡ refl with ℕ-dec (elim-uid dst-ok) (elim-uid dst-ok)
  src-elim-has-val | ev-skip with≡ refl | yes refl = has-val-r is-r refl
  src-elim-has-val | ev-skip with≡ refl | no ¬elim-elim = ⊥-elim (¬elim-elim refl)
  
  p₁e-sloc : SameLoc src-pres₁-ev src-elim-ev
  p₁e-sloc = same-loc (pres₁-has-loc dst-ok) src-elim-has-loc
  
  pe-sval : SameVal src-pres₁-ev src-elim-ev
  pe-sval = same-val (pres₁-has-val dst-ok) src-elim-has-val


  -- # Relation properties

  rfˡ∈src : rf src ˡ∈src
  rfˡ∈src (rf-dst src-rf[xy]) = relˡ∈src (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf) src-rf[xy]
  rfˡ∈src (rf-new refl refl)  = pres₁∈src

  rfʳ∈src : rf src ʳ∈src
  rfʳ∈src (rf-dst (_ , _ , dst-rf[xy] , refl , refl)) =
    events[⇐] (rfʳ∈ex dst-wf dst-rf[xy])
  rfʳ∈src (rf-new refl refl) = events[⇐] (elim∈ex dst-ok)

  udr-rf∈src : udr[ rf src ]∈src
  udr-rf∈src = lr→udr (rf src) rfˡ∈src rfʳ∈src


  coˡ∈src : co src ˡ∈src
  coˡ∈src = relˡ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

  coʳ∈src : co src ʳ∈src
  coʳ∈src = relʳ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

  udr-co∈src : udr[ co src ]∈src
  udr-co∈src = lr→udr (co src) coˡ∈src coʳ∈src    
