{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.Armv8 using (LabelArmv8)
open import MapTCGtoArmv8NonAtomic using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8NonAtomic.Execution (dst : Execution LabelArmv8) (dst-wf : WellFormed dst) (dst-ok : Armv8-TCGRestricted dst) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Rel)
open import Relation.Binary using (IsStrictTotalOrder; Tri; tri<; tri≈; tri>)
open import Relation.Binary using () renaming (IsStrictTotalOrder to STO)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.TCG as TCG
open import Arch.Armv8 as Armv8
open import MapTCGtoArmv8NonAtomic
import Proof.Framework LabelTCG dst dst-wf as Ψ
import Proof.Mapping.Framework LabelTCG dst dst-wf as Δ

open import Helpers


open Ex.Execution
open Ex.WellFormed
open IsArmv8Consistent
open Armv8-TCGRestricted
open Armv8Execution


dst-consistent = Armv8-TCGRestricted.consistent dst-ok

dst-a8 = a8 dst-consistent


-- # Backward Mapping of Relations

-- The mapping:
--
-- Rᵣ         ↦  Rᵣ
-- Wᵣ         ↦  Wᵣ
-- Rₗ;rmw;Wₗ  ↦  F_FULL;Rₗ;lxsx;Wₗ;F_FULL  || successful RMW
-- Rₗ         ↦  F_FULL;Rₗ;F_FULL          || failed RMW
--
-- F_RR       ↦  F_LD
-- F_RW       ↦  F_LD
-- F_RM       ↦  F_LD
--
-- F_WW       ↦  F_ST
--
-- F_WR       ↦  F_FULL
-- F_WM       ↦  F_FULL
-- F_MR       ↦  F_FULL
-- F_MW       ↦  F_FULL
-- F_MM       ↦  F_FULL
-- F_SC       ↦  F_FULL

ev[⇐] : {x : Event LabelArmv8} → (x∈dst : x ∈ events dst) → Event LabelTCG
ev[⇐] {event-init uid loc val}          x∈dst = event-init uid loc val
ev[⇐] {event-skip uid tid}              x∈dst with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
... | inj₁ (inj₁ _) = event-skip uid tid
... | inj₁ (inj₂ _) = event uid tid (lab-f ACQ)
... | inj₂ _        = event uid tid (lab-f REL)
ev[⇐] {event uid tid (lab-r t loc val)} x∈dst = event uid tid (lab-r t loc val)
ev[⇐] {event uid tid (lab-w t loc val)} x∈dst = event uid tid (lab-w t loc val)
ev[⇐] x@{event uid tid (lab-f F-full)}    x∈dst with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
... | inj₁ opt = event uid tid (lab-f (lemma opt))
  where
  -- This saves a pattern match in the uid/tid translations
  lemma : OptPred₆ (org-f-wr dst-ok) (org-f-wm dst-ok) (org-f-mr dst-ok) (org-f-mw dst-ok) (org-f-mm dst-ok) (org-f-sc dst-ok) x
    → TCG.F-mode
  lemma (opt₁ _) = WR
  lemma (opt₂ _) = WM
  lemma (opt₃ _) = MR
  lemma (opt₄ _) = MW
  lemma (opt₅ _) = MM
  lemma (opt₆ _) = SC
... | inj₂ _ = event-skip uid tid -- pre/post cases
ev[⇐] {event uid tid (lab-f F-ld)}      x∈dst = event uid tid (lab-f lemma)
  where
  -- This saves a pattern match in the uid/tid translations
  lemma : TCG.F-mode
  lemma with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  ... | inj₁ (inj₁ _) = RR
  ... | inj₁ (inj₂ _) = RW
  ... | inj₂ _        = RM
ev[⇐] {event uid tid (lab-f F-st)}      x∈dst = event uid tid (lab-f WW)
-- absent events
ev[⇐] {event _ _ (lab-a _ _ _)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event _ _ (lab-q _ _)}   x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event _ _ (lab-l _ _ _)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event _ _ lab-isb}       x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


-- # Proof framework

open Ψ.Definitions ev[⇐]

uid[⇐] : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
uid[⇐] {_}                            x∈dst has-uid-init = has-uid-init
uid[⇐] {_}                            x∈dst has-uid-skip with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
uid[⇐] {_}                            x∈dst has-uid-skip | inj₁ (inj₁ _) = has-uid-skip
uid[⇐] {_}                            x∈dst has-uid-skip | inj₁ (inj₂ _) = has-uid
uid[⇐] {_}                            x∈dst has-uid-skip | inj₂ _        = has-uid
uid[⇐] {_} {event _ _ (lab-r _ _ _)}  x∈dst has-uid = has-uid
uid[⇐] {_} {event _ _ (lab-w _ _ _)}  x∈dst has-uid = has-uid
uid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-uid with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
uid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-uid | inj₁ _ = has-uid
uid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-uid | inj₂ _ = has-uid-skip
uid[⇐] {_} {event _ _ (lab-f F-ld)}   x∈dst has-uid = has-uid
uid[⇐] {_} {event _ _ (lab-f F-st)}   x∈dst has-uid = has-uid
-- impossible cases
uid[⇐] {_} {event _ _ (lab-a _ _ _)} x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event _ _ (lab-q _ _)}   x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event _ _ (lab-l _ _ _)} x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event _ _ lab-isb}       x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


uid[$⇒] : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}         x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
uid[$⇒] {_} {event-skip _ _}           x∈dst has-uid-skip | inj₁ (inj₁ _) = has-uid-skip
uid[$⇒] {_} {event-skip _ _}           x∈dst has-uid      | inj₁ (inj₂ _) = has-uid-skip
uid[$⇒] {_} {event-skip _ _}           x∈dst has-uid      | inj₂ _        = has-uid-skip
uid[$⇒] {_} {event _ _ (lab-r _ _ _)}  x∈dst has-uid = has-uid
uid[$⇒] {_} {event _ _ (lab-w _ _ _)}  x∈dst has-uid = has-uid
uid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
uid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst has-uid      | inj₁ _ = has-uid
uid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst has-uid-skip | inj₂ _ = has-uid
uid[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst has-uid = has-uid
uid[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst has-uid = has-uid
-- impossible cases
uid[$⇒] {_} {event _ _ (lab-a _ _ _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event _ _ (lab-q _ _)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event _ _ (lab-l _ _ _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event _ _ lab-isb}       x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


tid[⇐] : {tid : ThreadId} → Pred[⇐]² (HasTid tid)
tid[⇐]                                x∈dst has-tid-skip with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
tid[⇐]                                x∈dst has-tid-skip | inj₁ (inj₁ _) = has-tid-skip
tid[⇐]                                x∈dst has-tid-skip | inj₁ (inj₂ _) = has-tid
tid[⇐]                                x∈dst has-tid-skip | inj₂ _        = has-tid
tid[⇐] {_} {event _ _ (lab-r _ _ _)}  x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ (lab-w _ _ _)}  x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-tid with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
tid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-tid | inj₁ _ = has-tid
tid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-tid | inj₂ _ = has-tid-skip
tid[⇐] {_} {event _ _ (lab-f F-ld)}   x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ (lab-f F-st)}   x∈dst has-tid = has-tid
-- impossible cases
tid[⇐] {_} {event _ _ (lab-a _ _ _)} x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event _ _ (lab-q _ _)}   x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event _ _ (lab-l _ _ _)} x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event _ _ lab-isb}       x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


tid[$⇒] : {tid : ThreadId} → Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
tid[$⇒] {_} {event-skip _ _}           x∈dst has-tid-skip | inj₁ (inj₁ _) = has-tid-skip
tid[$⇒] {_} {event-skip _ _}           x∈dst has-tid      | inj₁ (inj₂ _) = has-tid-skip
tid[$⇒] {_} {event-skip _ _}           x∈dst has-tid      | inj₂ _        = has-tid-skip
tid[$⇒] {_} {event _ _ (lab-r _ _ _)}  x∈dst has-tid = has-tid
tid[$⇒] {_} {event _ _ (lab-w _ _ _)}  x∈dst has-tid = has-tid
tid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
tid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst has-tid      | inj₁ _ = has-tid
tid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst has-tid-skip | inj₂ _ = has-tid
tid[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst has-tid = has-tid
tid[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst has-tid = has-tid
-- impossible cases
tid[$⇒] {_} {event _ _ (lab-a _ _ _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event _ _ (lab-q _ _)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event _ _ (lab-l _ _ _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event _ _ lab-isb}       x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


loc[⇐] : {loc : Location} → Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init          = has-loc-init
loc[⇐] x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[⇐] x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl
-- impossible cases
loc[⇐] x∈dst (has-loc-r is-a refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] x∈dst (has-loc-r is-q refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] x∈dst (has-loc-w is-l refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


loc[$⇒] : {loc : Location} → Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}        x∈dst has-loc-init          = has-loc-init
loc[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl
-- impossible cases
loc[$⇒] {_} {event-skip _ _}           x∈dst x-loc with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
loc[$⇒] {_} {event-skip _ _}           x∈dst x-loc | inj₁ (inj₂ _) = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))
loc[$⇒] {_} {event-skip _ _}           x∈dst x-loc | inj₂ _        = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))
loc[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _     with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
loc[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst x-loc | inj₁ _ = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))
loc[$⇒] {_} {event _ _ (lab-a _ _ _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-q _ _)}    x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-l _ _ _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ lab-isb}        x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst x-loc = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))
loc[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst x-loc = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))


val[⇐] : {val : Value} → Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init          = has-val-init
val[⇐] x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[⇐] x∈dst (has-val-w is-w refl) = has-val-w is-w refl
-- impossible cases
val[⇐] x∈dst (has-val-r is-a refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] x∈dst (has-val-r is-q refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] x∈dst (has-val-w is-l refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


val[$⇒] : {val : Value} → Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}        x∈dst has-val-init          = has-val-init
val[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-val-w is-w refl) = has-val-w is-w refl
-- impossible cases
val[$⇒] {_} {event-skip _ _}           x∈dst x-val with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
val[$⇒] {_} {event-skip _ _}           x∈dst x-val | inj₁ (inj₂ _) = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))
val[$⇒] {_} {event-skip _ _}           x∈dst x-val | inj₂ _        = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))
val[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _     with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
val[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst x-val | inj₁ _ = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))
val[$⇒] {_} {event _ _ (lab-a _ _ _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-q _ _)}    x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-l _ _ _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ lab-isb}        x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst x-val = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))
val[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst x-val = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init


Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _}         x∈dst ev-init = ev-init
-- impossible cases
Init[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
Init[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
Init[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
Init[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
Init[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ _
Init[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
Init[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Wₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] x∈dst (ev-init refl)   = ev-init refl
Wₜ[⇐] x∈dst (ev-w is-w refl) = ev-w is-w refl
Wₜ[⇐] x∈dst (ev-w is-l refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Wₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}        x∈dst (ev-init refl)   = ev-init refl
Wₜ[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (ev-w is-w refl) = ev-w is-w refl
-- impossible cases
Wₜ[$⇒] {_} {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
Wₜ[$⇒] {_} {event-skip _ _}           x∈dst (ev-w () refl) | inj₁ (inj₂ _)
Wₜ[$⇒] {_} {event-skip _ _}           x∈dst (ev-w () _)    | inj₂ _
Wₜ[$⇒] {_} {event _ _ (lab-r _ _ _)}  x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
Wₜ[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst (ev-w () _) | inj₁ _
Wₜ[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Rₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] x∈dst (ev-r is-r refl) = ev-r is-r refl
-- impossible cases
Rₜ[⇐] x∈dst (ev-r is-a refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[⇐] x∈dst (ev-r is-q refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event _ _ (lab-r _ _ _)}  x∈dst (ev-r is-r refl) = ev-r is-r refl
-- impossible cases
Rₜ[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
Rₜ[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst (ev-r () _) | inj₁ _
Rₜ[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst ()          | inj₂ _
Rₜ[$⇒] {_} {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
Rₜ[$⇒] {_} {event-skip _ _}           x∈dst (ev-r () refl) | inj₁ (inj₂ _)
Rₜ[$⇒] {_} {event-skip _ _}           x∈dst (ev-r () _)    | inj₂ _
Rₜ[$⇒] {_} {event _ _ (lab-w _ _ _)}  x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-l _ _ _ )} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

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

δ : Δ.MappingFramework
δ =
  record
    { ψ       = ψ
    ; loc[⇐]  = loc[⇐]
    ; loc[$⇒] = loc[$⇒]
    ; val[⇐]  = val[⇐]
    ; val[$⇒] = val[$⇒]
    ; Wₜ[⇐]   = Wₜ[⇐]
    ; Wₜ[$⇒]  = Wₜ[$⇒]
    ; Rₜ[⇐]   = Rₜ[⇐]
    ; Rₜ[$⇒]  = Rₜ[$⇒]
    }


-- # Extra helpers

module Extra where

  open Δ.Definitions δ
  open Ψ.WellFormed ψ using (rmw[⇒])


  rmw[⇒]lxsx : Rel[⇒] (rmw src) (lxsx dst-a8)
  rmw[⇒]lxsx x∈src y∈src = rmw⇒lxsx dst-ok ∘ (rmw[⇒] x∈src y∈src)


  R₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (TCG.EvR₌ tag loc val) (Armv8.EvR₌ tag loc val)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-r _ _ _)}  x∈dst ev-r₌ = ev-r₌
  R₌[$⇒] {_} {_} {_} {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  R₌[$⇒] {_} {_} {_} {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  R₌[$⇒] {_} {_} {_} {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst () | inj₁ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  
  R₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (TCG.EvR₌ tag loc val) (Armv8.EvR₌ tag loc val)
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  W₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (TCG.EvW₌ tag loc val) (Armv8.EvW₌ tag loc val)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-w _ _ _)}  x∈dst ev-w₌ = ev-w₌
  W₌[$⇒] {_} {_} {_} {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  W₌[$⇒] {_} {_} {_} {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  W₌[$⇒] {_} {_} {_} {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst () | inj₁ _
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  
  W₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (TCG.EvW₌ tag loc val) (Armv8.EvW₌ tag loc val)
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]


  -- Map fences. RR / RW / RM / WR / WW / WM / MR / MW / MM / SC
  --
  -- RR / RW / RM                -> F-ld
  -- WW                          -> F-st
  -- WR / WM / MR / MW / MM / SC -> F-full

  Frr[$⇒] : Pred[$⇒] (TCG.EvF₌ RR) (Armv8.EvF₌ F-ld)
  Frr[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ = ev-f₌
  -- impossible cases
  Frr[$⇒] {event-init _ _ _}         x∈dst ()
  Frr[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frr[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Frr[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Frr[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Frr[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Frr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Frr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Frr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Frr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Frr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Frr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Frr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
    
  Frr[⇒] : Pred[⇒] (TCG.EvF₌ RR) (Armv8.EvF₌ F-ld)
  Frr[⇒] = [$⇒]→₁[⇒] Frr[$⇒]


  Frw[$⇒] : Pred[$⇒] (TCG.EvF₌ RW) (Armv8.EvF₌ F-ld)
  Frw[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ = ev-f₌
  -- impossible cases
  Frw[$⇒] {event-init _ _ _}         x∈dst ()
  Frw[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frw[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Frw[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Frw[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Frw[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Frw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Frw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Frw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Frw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Frw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Frw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Frw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
    
  Frw[⇒] : Pred[⇒] (TCG.EvF₌ RW) (Armv8.EvF₌ F-ld)
  Frw[⇒] = [$⇒]→₁[⇒] Frw[$⇒]
  
  
  Frm[$⇒] : Pred[$⇒] (TCG.EvF₌ RM) (Armv8.EvF₌ F-ld)
  Frm[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ = ev-f₌
  -- impossible cases
  Frm[$⇒] {event-init _ _ _}         x∈dst ()
  Frm[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Frm[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Frm[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
    
  Frm[⇒] : Pred[⇒] (TCG.EvF₌ RM) (Armv8.EvF₌ F-ld)
  Frm[⇒] = [$⇒]→₁[⇒] Frm[$⇒]
  

  Fwr[$⇒] : Pred[$⇒] (TCG.EvF₌ WR) (Armv8.EvF₌ F-full)
  Fwr[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Fwr[$⇒] {event _ _ (lab-f F-full)} x∈dst _  | inj₁ (opt₁ _) = ev-f₌
  -- impossible cases
  Fwr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Fwr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Fwr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Fwr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Fwr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Fwr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  Fwr[$⇒] {event-init _ _ _}         x∈dst ()
  Fwr[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwr[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Fwr[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Fwr[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Fwr[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  Fwr[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₁ _)
  Fwr[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₂ _)
    
  Fwr[⇒] : Pred[⇒] (TCG.EvF₌ WR) (Armv8.EvF₌ F-full)
  Fwr[⇒] = [$⇒]→₁[⇒] Fwr[$⇒]


  Fww[$⇒] : Pred[$⇒] (TCG.EvF₌ WW) (Armv8.EvF₌ F-st)
  Fww[$⇒] {event _ _ (lab-f F-st)}   x∈dst ev-f₌ = ev-f₌
  -- impossible cases
  Fww[$⇒] {event-init _ _ _}         x∈dst ()
  Fww[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Fww[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Fww[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Fww[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  Fww[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₁ _)
  Fww[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₂ _)
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _

  Fww[⇒] : Pred[⇒] (TCG.EvF₌ WW) (Armv8.EvF₌ F-st)
  Fww[⇒] = [$⇒]→₁[⇒] Fww[$⇒]


  Fwm[$⇒] : Pred[$⇒] (TCG.EvF₌ WM) (Armv8.EvF₌ F-full)
  Fwm[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Fwm[$⇒] {event _ _ (lab-f F-full)} x∈dst _  | inj₁ (opt₂ _) = ev-f₌
  -- impossible cases
  Fwm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Fwm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Fwm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Fwm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Fwm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Fwm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  Fwm[$⇒] {event-init _ _ _}         x∈dst ()
  Fwm[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fwm[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Fwm[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Fwm[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Fwm[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  Fwm[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₁ _)
  Fwm[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₂ _)
    
  Fwm[⇒] : Pred[⇒] (TCG.EvF₌ WM) (Armv8.EvF₌ F-full)
  Fwm[⇒] = [$⇒]→₁[⇒] Fwm[$⇒]


  Fmr[$⇒] : Pred[$⇒] (TCG.EvF₌ MR) (Armv8.EvF₌ F-full)
  Fmr[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Fmr[$⇒] {event _ _ (lab-f F-full)} x∈dst _ | inj₁ (opt₃ _) = ev-f₌
  -- impossible cases
  Fmr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Fmr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Fmr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Fmr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Fmr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Fmr[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  Fmr[$⇒] {event-init _ _ _}         x∈dst ()
  Fmr[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmr[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Fmr[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Fmr[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Fmr[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  Fmr[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₁ _)
  Fmr[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₂ _)
    
  Fmr[⇒] : Pred[⇒] (TCG.EvF₌ MR) (Armv8.EvF₌ F-full)
  Fmr[⇒] = [$⇒]→₁[⇒] Fmr[$⇒]


  Fmw[$⇒] : Pred[$⇒] (TCG.EvF₌ MW) (Armv8.EvF₌ F-full)
  Fmw[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Fmw[$⇒] {event _ _ (lab-f F-full)} x∈dst _ | inj₁ (opt₄ _) = ev-f₌
  -- impossible cases
  Fmw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Fmw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Fmw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Fmw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Fmw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Fmw[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  Fmw[$⇒] {event-init _ _ _}         x∈dst ()
  Fmw[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmw[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Fmw[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Fmw[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Fmw[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  Fmw[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₁ _)
  Fmw[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₂ _)
    
  Fmw[⇒] : Pred[⇒] (TCG.EvF₌ MW) (Armv8.EvF₌ F-full)
  Fmw[⇒] = [$⇒]→₁[⇒] Fmw[$⇒]


  Fmm[$⇒] : Pred[$⇒] (TCG.EvF₌ MM) (Armv8.EvF₌ F-full)
  Fmm[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Fmm[$⇒] {event _ _ (lab-f F-full)} x∈dst _ | inj₁ (opt₅ _) = ev-f₌
  -- impossible cases
  Fmm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Fmm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Fmm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Fmm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Fmm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Fmm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  Fmm[$⇒] {event-init _ _ _}         x∈dst ()
  Fmm[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fmm[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Fmm[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Fmm[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Fmm[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  Fmm[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₁ _)
  Fmm[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₂ _)
    
  Fmm[⇒] : Pred[⇒] (TCG.EvF₌ MM) (Armv8.EvF₌ F-full)
  Fmm[⇒] = [$⇒]→₁[⇒] Fmm[$⇒]


  Fsc[$⇒] : Pred[$⇒] (TCG.EvF₌ SC) (Armv8.EvF₌ F-full)
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst _ | inj₁ (opt₆ _) = ev-f₌
  -- impossible cases
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  Fsc[$⇒] {event-init _ _ _}         x∈dst ()
  Fsc[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Fsc[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₁ _)
  Fsc[$⇒] {event-skip _ _}           x∈dst () | inj₁ (inj₂ _)
  Fsc[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  Fsc[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₁ _)
  Fsc[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₂ _)

  Fsc[⇒] : Pred[⇒] (TCG.EvF₌ SC) (Armv8.EvF₌ F-full)
  Fsc[⇒] = [$⇒]→₁[⇒] Fsc[$⇒]


  Facq[$⇒] : Pred[$⇒] (TCG.EvF₌ ACQ) EvSkip
  Facq[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Facq[$⇒] {event-skip _ _}           x∈dst ev-f₌ | inj₁ (inj₂ _) = ev-skip
  -- impossible cases
  Facq[$⇒] {event-skip _ _}           x∈dst ()    | inj₁ (inj₁ _)
  Facq[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Facq[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Facq[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Facq[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Facq[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Facq[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Facq[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Facq[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  Facq[$⇒] {event-init _ _ _}         x∈dst ()
  Facq[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Facq[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Facq[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Facq[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Facq[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  Facq[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₁ _)
  Facq[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₂ _)
    
  Facq[⇒] : Pred[⇒] (TCG.EvF₌ ACQ) EvSkip
  Facq[⇒] = [$⇒]→₁[⇒] Facq[$⇒]
  

  Frel[$⇒] : Pred[$⇒] (TCG.EvF₌ REL) EvSkip
  Frel[$⇒] {event-skip _ _}           x∈dst _ with ⇔₁-apply-⊆₁ (org-skip-def dst-ok) (x∈dst , ev-skip)
  Frel[$⇒] {event-skip _ _}           x∈dst ev-f₌ | inj₂ _ = ev-skip
  -- impossible cases
  Frel[$⇒] {event-skip _ _}           x∈dst ()    | inj₁ (inj₁ _)
  Frel[$⇒] {event-skip _ _}           x∈dst ()    | inj₁ (inj₂ _)
  Frel[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ (org-f-def dst-ok) (x∈dst , ev-f₌)
  Frel[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₁ _)
  Frel[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₂ _)
  Frel[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₃ _)
  Frel[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₄ _)
  Frel[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₅ _)
  Frel[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ (opt₆ _)
  Frel[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  Frel[$⇒] {event-init _ _ _}         x∈dst ()
  Frel[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frel[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frel[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frel[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frel[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ with ⇔₁-apply-⊆₁ (org-ld-def dst-ok) (x∈dst , ev-f₌)
  Frel[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₁ _)
  Frel[$⇒] {event _ _ (lab-f F-ld)}   x∈dst () | inj₁ (inj₂ _)
    
  Frel[⇒] : Pred[⇒] (TCG.EvF₌ REL) EvSkip
  Frel[⇒] = [$⇒]→₁[⇒] Frel[$⇒]
  

  F[⇒]ld : {m : TCG.F-mode} → m ∈ₗ (RR ∷ RW ∷ RM ∷ [])
    → Pred[⇒] (TCG.EvF₌ m) (Armv8.EvF₌ F-ld)
  F[⇒]ld (here refl)                 = Frr[⇒]
  F[⇒]ld (there (here refl))         = Frw[⇒]
  F[⇒]ld (there (there (here refl))) = Frm[⇒]
  
  F[⇒]ff : {m : TCG.F-mode} → m ∈ₗ (WR ∷ WM ∷ MR ∷ MW ∷ MM ∷ SC ∷ [])
    → Pred[⇒] (TCG.EvF₌ m) (Armv8.EvF₌ F-full)
  F[⇒]ff (here refl)                                         = Fwr[⇒]
  F[⇒]ff (there (here refl))                                 = Fwm[⇒]
  F[⇒]ff (there (there (here refl)))                         = Fmr[⇒]
  F[⇒]ff (there (there (there (here refl))))                 = Fmw[⇒]
  F[⇒]ff (there (there (there (there (here refl)))))         = Fmm[⇒]
  F[⇒]ff (there (there (there (there (there (here refl)))))) = Fsc[⇒]
  
  F[⇒]skip : {m : TCG.F-mode} → m ∈ₗ (ACQ ∷ REL ∷ [])
    → Pred[⇒] (TCG.EvF₌ m) EvSkip
  F[⇒]skip (here refl)         = Facq[⇒]
  F[⇒]skip (there (here refl)) = Frel[⇒]
