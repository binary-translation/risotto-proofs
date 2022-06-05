{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.Armv8 using (LabelArmv8)
open import MapTCGtoArmv8Atomic using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8Atomic.Mapping
  (dst : Execution LabelArmv8)
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-TCGRestricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Level using (Level; _⊔_)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (_∈_; _∉_)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Library imports
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.TCG as TCG
open import Arch.Armv8 as Armv8
import Proof.Mapping.TCGtoArmv8Atomic.Execution

open import MapTCGtoArmv8Atomic
-- defines `ev[⇐]` and `ψ`
open import Proof.Mapping.TCGtoArmv8Atomic.Execution dst dst-wf dst-ok as PE

import Proof.Framework LabelTCG dst dst-wf as Ψ
import Proof.Mapping.Framework LabelTCG dst dst-wf as Δ


open Execution
open Armv8Execution


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ
--
open PE.Extra


-- Instrs: LD ↦ LDR
-- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
src-rule-ld : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
  → TCG.EvR₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvR₌ tmov x v a')
src-rule-ld {a} a-r a∈src =
  ev[⇒] {a} a∈src , events[⇒] {a} a∈src , R₌[⇒] a∈src a-r

-- Instrs: ST ↦ STR
-- Events: Wᵣ(x,v) ↦ W(x,v)ᵣ
src-rule-st : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
  → TCG.EvW₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvW₌ tmov x v a')
src-rule-st {a} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] {a} a∈src , W₌[⇒] a∈src a-w

-- Rₗ;rmw;Wₗ           ↦ Aₗ;amo;Lₗ  || successful RMW
-- Rₗ                  ↦ Aₗ         || failed RMW

src-rule-rmw-dom : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
  → TCG.EvR₌ trmw x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvA₌ trmw x v a')
src-rule-rmw-dom {a} a-r a∈src =
  (ev[⇒] {a} a∈src , events[⇒] {a} a∈src , R₌[⇒]A a∈src a-r)

src-rule-rmw-codom : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
  → TCG.EvW₌ trmw x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvL₌ trmw x v a')
src-rule-rmw-codom {a} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] {a} a∈src , W₌[⇒]L a∈src a-w

private
  r₌⇒rₜ : {x : Event LabelTCG} {loc : Location} {val : Value}
    → TCG.EvR₌ trmw loc val x → EvRₜ trmw x
  r₌⇒rₜ ev-r₌ = ev-r is-r refl

  w₌⇒wₜ : {x : Event LabelTCG} {loc : Location} {val : Value}
    → TCG.EvW₌ trmw loc val x → EvWₜ trmw x
  w₌⇒wₜ ev-w₌ = ev-w is-w refl


src-rule-rmw-ok : ∀ {a b : Event LabelTCG} {x : Location} {v₁ v₂ : Value}
  → TCG.EvR₌ trmw x v₁ a
  → TCG.EvW₌ trmw x v₂ b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] (amo dst-a8 a' b' × Armv8.EvA₌ trmw x v₁ a' × Armv8.EvL₌ trmw x v₂ b')
src-rule-rmw-ok {a} {b} a-r b-w rmw[ab] =
  ev[⇒] a∈src , ev[⇒] b∈src , rmw[⇒]amo a∈src b∈src rmw[ab] , R₌[⇒]A a∈src a-r , W₌[⇒]L b∈src b-w
  where
  a∈src = rmwˡ∈src rmw[ab]
  b∈src = rmwʳ∈src rmw[ab]


src-rule-rmw-fail : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
  → TCG.EvR₌ trmw x v a
  → a ∈ events src
  → a ∉ dom (rmw src)
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvA₌ trmw x v a' × a' ∉ dom (rmw dst))
src-rule-rmw-fail {a} a-rₐ a∈src a∉rmwˡ =
  ev[⇒] a∈src , events[⇒] a∈src , R₌[⇒]A a∈src a-rₐ , ¬rmwˡ[⇒] a∈src a∉rmwˡ


-- Instrs: F_LD_LD F_LD_ST F_LD_M ↦ DMBLD
-- Events: F_RR    F_RW    F_RM   ↦ F_LD

src-rule-f-ld : ∀ {a : Event LabelTCG}
  → {m : TCG.F-mode}
  → m ∈ₗ (RR ∷ RW ∷ RM ∷ [])
  → TCG.EvF₌ m a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-ld a')
src-rule-f-ld p a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , F[⇒]ld p a∈src a-f


-- Instrs: F_ST_ST ↦ DMBST
-- Events: F_WW    ↦ F_ST

src-rule-f-st : ∀ {a : Event LabelTCG}
  → TCG.EvF₌ WW a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-st a')
src-rule-f-st a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , Fww[⇒] a∈src a-f


-- Instrs: F_ST_LD F_ST_M F_M_LD F_M_ST F_M_M F_SC ↦ DMBFF
-- Events: F_WR    F_WM   F_MR   F_MW   F_MM  F_SC ↦ F

src-rule-f-full : ∀ {a : Event LabelTCG}
  → {m : TCG.F-mode}
  → m ∈ₗ (WR ∷ WM ∷ MR ∷ MW ∷ MM ∷ SC ∷ [])
  → TCG.EvF₌ m a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-full a')
src-rule-f-full p a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , F[⇒]ff p a∈src a-f
  

-- Instrs: F_ACQ F_REL ↦ skip
-- Events: F_ACQ F_REL ↦ skip

src-rule-f-skip : ∀ {a : Event LabelTCG}
  → {m : TCG.F-mode}
  → m ∈ₗ (ACQ ∷ REL ∷ [])
  → TCG.EvF₌ m a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvSkip a')
src-rule-f-skip p a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , F[⇒]skip p a∈src a-f


mapping : TCG⇒Armv8 src dst-a8
mapping =
  record
    { rule-ld        = src-rule-ld
    ; rule-st        = src-rule-st
    ; rule-rmw-dom   = src-rule-rmw-dom
    ; rule-rmw-codom = src-rule-rmw-codom
    ; rule-rmw-ok    = src-rule-rmw-ok
    ; rule-rmw-fail  = src-rule-rmw-fail
    ; rule-f-ld      = src-rule-f-ld
    ; rule-f-st      = src-rule-f-st
    ; rule-f-full    = src-rule-f-full
    ; rule-f-skip    = src-rule-f-skip
    }
