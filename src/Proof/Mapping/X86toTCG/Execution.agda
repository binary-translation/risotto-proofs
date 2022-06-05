{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.TCG using (LabelTCG)
open import MapX86toTCG using (TCG-X86Restricted)


module Proof.Mapping.X86toTCG.Execution
  (dst : Execution LabelTCG) (dst-wf : WellFormed dst) (dst-ok : TCG-X86Restricted dst) where

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
open import Arch.X86 as X86
open import MapX86toTCG
import Proof.Framework LabelX86 dst dst-wf as Ψ
import Proof.Mapping.Framework LabelX86 dst dst-wf as Δ

open import Helpers


open Ex.Execution
open Ex.WellFormed
open IsTCGConsistent
open TCG-X86Restricted


dst-consistent = TCG-X86Restricted.consistent dst-ok


-- # Backward Mapping of Relations

-- Instruction mapping:
--
-- RMOV   ↦ LD;F_LD_M
-- WMOV   ↦ F_ST_ST;ST
-- RMW    ↦ RMW
-- MFENCE ↦ F_SC
--
-- Corresponding event mapping:
--
-- Rᵣ(x,v)             ↦ Rᵣ(x,v);F_RM
-- W(x,v)              ↦ F_WW;Wᵣ(x,v)
-- Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;Wₗ(x,v')  || successful RMW
-- Rₗ(x,v)             ↦ Rₗ(x,v)               || failed RMW
-- F                   ↦ F_SC


ev[⇐] : {x : Event LabelTCG}
  → (x∈dst : x ∈ events dst)
    ------------------------
  → Event LabelX86
ev[⇐] {event-init uid loc val}            x∈dst = event-init uid loc val
ev[⇐] {event-skip uid tid}                x∈dst = event-skip uid tid
ev[⇐] {event uid tid (lab-r tag loc val)} x∈dst = event uid tid (lab-r tag loc val)
ev[⇐] {event uid tid (lab-w tag loc val)} x∈dst = event uid tid (lab-w tag loc val)
ev[⇐] {event uid tid (lab-f RM)}          x∈dst = event-skip uid tid
ev[⇐] {event uid tid (lab-f WW)}          x∈dst = event-skip uid tid
ev[⇐] {event uid tid (lab-f SC)}          x∈dst = event uid tid lab-f
-- impossible cases
ev[⇐] {event uid tid (lab-f RR)}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event uid tid (lab-f RW)}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event uid tid (lab-f WR)}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event uid tid (lab-f WM)}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event uid tid (lab-f MR)}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event uid tid (lab-f MW)}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event uid tid (lab-f MM)}  x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event uid tid (lab-f ACQ)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
ev[⇐] {event uid tid (lab-f REL)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


-- # Proof framework

open Ψ.Definitions ev[⇐]

uid[⇐] : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
uid[⇐] {_}                           x∈dst has-uid-init = has-uid-init
uid[⇐] {_}                           x∈dst has-uid-skip = has-uid-skip
uid[⇐] {_} {event _ _ (lab-r _ _ _)} x∈dst has-uid      = has-uid
uid[⇐] {_} {event _ _ (lab-w _ _ _)} x∈dst has-uid      = has-uid
uid[⇐] {_} {event _ _ (lab-f RM)}    x∈dst has-uid      = has-uid-skip
uid[⇐] {_} {event _ _ (lab-f WW)}    x∈dst has-uid      = has-uid-skip
uid[⇐] {_} {event _ _ (lab-f SC)}    x∈dst has-uid      = has-uid
-- impossible cases
uid[⇐] {_} {event _ _ (lab-f RR)}  x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event _ _ (lab-f RW)}  x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event _ _ (lab-f WR)}  x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event _ _ (lab-f WM)}  x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event _ _ (lab-f MR)}  x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event _ _ (lab-f MW)}  x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event _ _ (lab-f MM)}  x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event _ _ (lab-f ACQ)} x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[⇐] {_} {event _ _ (lab-f REL)} x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

uid[$⇒] : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}        x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}          x∈dst has-uid-skip = has-uid-skip
uid[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst has-uid      = has-uid
uid[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst has-uid      = has-uid
uid[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst has-uid-skip = has-uid
uid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst has-uid-skip = has-uid
uid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst has-uid      = has-uid
-- impossible cases
uid[$⇒] {_} {event _ _ (lab-f RR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event _ _ (lab-f RW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event _ _ (lab-f WR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event _ _ (lab-f WM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event _ _ (lab-f MR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event _ _ (lab-f MW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event _ _ (lab-f MM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event _ _ (lab-f ACQ)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
uid[$⇒] {_} {event _ _ (lab-f REL)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


tid[⇐] : {tid : ThreadId} → Pred[⇐]² (HasTid tid)
tid[⇐] {_}                           x∈dst has-tid-skip = has-tid-skip
tid[⇐] {_} {event _ _ (lab-r _ _ _)} x∈dst has-tid      = has-tid
tid[⇐] {_} {event _ _ (lab-w _ _ _)} x∈dst has-tid      = has-tid
tid[⇐] {_} {event _ _ (lab-f RM)}    x∈dst has-tid      = has-tid-skip
tid[⇐] {_} {event _ _ (lab-f WW)}    x∈dst has-tid      = has-tid-skip
tid[⇐] {_} {event _ _ (lab-f SC)}    x∈dst has-tid      = has-tid
-- impossible cases
tid[⇐] {_} {event _ _ (lab-f RR)}  x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event _ _ (lab-f RW)}  x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event _ _ (lab-f WR)}  x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event _ _ (lab-f WM)}  x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event _ _ (lab-f MR)}  x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event _ _ (lab-f MW)}  x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event _ _ (lab-f MM)}  x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event _ _ (lab-f ACQ)} x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[⇐] {_} {event _ _ (lab-f REL)} x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

tid[$⇒] : {tid : ThreadId} → Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}          x∈dst has-tid-skip = has-tid-skip
tid[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst has-tid      = has-tid
tid[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst has-tid      = has-tid
tid[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst has-tid-skip = has-tid
tid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst has-tid-skip = has-tid
tid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst has-tid      = has-tid
-- impossible cases
tid[$⇒] {_} {event _ _ (lab-f RR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event _ _ (lab-f RW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event _ _ (lab-f WR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event _ _ (lab-f WM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event _ _ (lab-f MR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event _ _ (lab-f MW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event _ _ (lab-f MM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event _ _ (lab-f ACQ)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
tid[$⇒] {_} {event _ _ (lab-f REL)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


loc[⇐] : {loc : Location} → Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init          = has-loc-init
loc[⇐] x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[⇐] x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl

loc[$⇒] : {loc : Location} → Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init x x₁ x₂} x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl
loc[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst ()
loc[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst ()
loc[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (has-loc-r () _)
loc[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (has-loc-w () _)
-- impossible cases
loc[$⇒] {_} {event _ _ (lab-f RR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f RW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f WR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f WM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f MR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f MW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f MM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f ACQ)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f REL)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


val[⇐] : {val : Value} → Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init          = has-val-init
val[⇐] x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[⇐] x∈dst (has-val-w is-w refl) = has-val-w is-w refl

val[$⇒] : {val : Value} → Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init x x₁ x₂} x∈dst has-val-init = has-val-init
val[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-val-w is-w refl) = has-val-w is-w refl
val[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst ()
val[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst ()
val[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (has-val-r () _)
val[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (has-val-w () _)
-- impossible cases
val[$⇒] {_} {event _ _ (lab-f RR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f RW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f WR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f WM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f MR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f MW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f MM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f ACQ)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f REL)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init


Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _}      x∈dst ev-init = ev-init
-- impossible cases
Init[$⇒] {event _ _ (lab-f RR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-f RW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-f WR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-f WM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-f MR)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-f MW)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-f MM)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-f ACQ)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-f REL)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Wₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] x∈dst (ev-init refl)   = ev-init refl
Wₜ[⇐] x∈dst (ev-w is-w refl) = ev-w is-w refl


Wₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}        x∈dst (ev-init refl)   = ev-init refl
Wₜ[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (ev-w is-w refl) = ev-w is-w refl
-- impossible cases
Wₜ[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-f RR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-f RW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-f WR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-f WM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-f MR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-f MW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-f MM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-f ACQ)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-f REL)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Rₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] x∈dst (ev-r is-r refl) = ev-r is-r refl


Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (ev-r is-r refl) = ev-r is-r refl
-- impossible cases
Rₜ[$⇒] {_} {event-init _ _ _}        x∈dst ()
Rₜ[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ (lab-f RR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-f RW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-f WR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-f WM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-f MR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-f MW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-f MM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-f ACQ)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-f REL)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


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
  

  R₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (X86.EvR₌ tag loc val) (TCG.EvR₌ tag loc val)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-r _ _ _)} x∈dst ev-r = ev-r₌
  -- impossible cases
  R₌[$⇒] {_} {_} {_} {event-init _ _ _}        x∈dst ()
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-w _ _ _)} x∈dst ()
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}    x∈dst ()
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f RR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f RW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f WR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f WM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f MR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f MW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f MM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f ACQ)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f REL)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

  R₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (X86.EvR₌ tag loc val) (TCG.EvR₌ tag loc val)
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  W₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (X86.EvW₌ tag loc val) (TCG.EvW₌ tag loc val)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-w _ _ _)} x∈dst ev-w₌ = ev-w₌
  -- impossible cases
  W₌[$⇒] {_} {_} {_} {event-init _ _ _}        x∈dst ()
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-r _ _ _)} x∈dst ()
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}    x∈dst ()
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f RR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f RW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f WR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f WM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f MR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f MW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f MM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f ACQ)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f REL)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

  W₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (X86.EvW₌ tag loc val) (TCG.EvW₌ tag loc val)
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]
  

  F[$⇒] : Pred[$⇒] EvF (EvF₌ SC)
  F[$⇒] {event _ _ (lab-f SC)} x∈dst (ev-f is-f) = ev-f₌
  -- impossible cases
  F[$⇒] {event _ _ (lab-r _ _ _)} x∈dst (ev-f ())
  F[$⇒] {event _ _ (lab-w _ _ _)} x∈dst (ev-f ())
  F[$⇒] {event _ _ (lab-f RR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event _ _ (lab-f RW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event _ _ (lab-f WR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event _ _ (lab-f WM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event _ _ (lab-f MR)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event _ _ (lab-f MW)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event _ _ (lab-f MM)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event _ _ (lab-f ACQ)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  F[$⇒] {event _ _ (lab-f REL)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

  F[⇒] : Pred[⇒] EvF (EvF₌ SC)
  F[⇒] = [$⇒]→₁[⇒] F[$⇒]
