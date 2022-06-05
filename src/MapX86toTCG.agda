{-# OPTIONS --safe #-}

module MapX86toTCG where

-- Stdlib imports
open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Unary using (Pred; _∈_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
import Arch.General.Event
import Arch.X86 as X86
open import Arch.X86 using (LabelX86)
import Arch.TCG as TCG
open import Arch.TCG -- using (LabelTCG; IsTCGConsistent; F-mode; RM; WW; SC)

-- Helper imports
open import Arch.General.Execution
open import Arch.General.Event
open Event


open Execution
open WellFormed
open LabelTCG



-- # Definitions

-- Mapping - X86 ⇒ TCG
--
--
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

record X86⇒TCG (src : Execution LabelX86) (dst : Execution LabelTCG) : Set where
  field
    -- Instrs: RMOV    ↦ LD;F_LD_M
    -- Events: Rᵣ(x,v) ↦ Rᵣ(x,v);F_RM
    rule-rmov : ∀ {a b : Event LabelX86} {x : Location} {v : Value}
      → X86.EvR₌ tmov x v a
      → EvSkip b
      → po-imm src a b
      → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × TCG.EvR₌ tmov x v a' × TCG.EvF₌ RM b')

    -- Instrs: WMOV   ↦ F_ST_ST;ST
    -- Events: W(x,v) ↦ F_WW;W(x,v)
    rule-wmov : ∀ {a b : Event LabelX86}
        {x : Location} {v : Value}
      → EvSkip a
      → X86.EvW₌ tmov x v b
      → po-imm src a b
      → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × TCG.EvF₌ WW a' × TCG.EvW₌ tmov x v b')

    -- Instrs: RMW ↦ RMW
    -- Events: Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;W(x,v')  || successful
    --         Rₗ(x,v)             ↦ Rₗ(x,v)              || failed
    rule-rmw-ok : ∀ {a b : Event LabelX86}
        {x : Location} {v₁ v₂ : Value}
      → X86.EvR₌ trmw x v₁ a
      → X86.EvW₌ trmw x v₂ b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × TCG.EvR₌ trmw x v₁ a' × TCG.EvW₌ trmw x v₂ b')
      
    rule-rmw-fail : ∀ {a : Event LabelX86}
        {x : Location} {v : Value}
      → X86.EvR₌ trmw x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × TCG.EvR₌ trmw x v a')

    -- Instrs: MFENCE ↦ F_SC
    -- Events: F      ↦ F_SC
    rule-fence : ∀ {a : Event LabelX86}
      → EvF a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × TCG.EvF₌ TCG.SC a')


-- TCG programs mapped from x86 programs can only contain these events.
-- Rᵣ Rₗ Wᵣ Wₗ F_RM F_WW F_SC
data IsTCGEventX86 : Event LabelTCG → Set where
  ev-init : {uid : UniqueId} {loc : Location} {val : Value} → IsTCGEventX86 (event-init uid loc val)
  ev-r    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → IsTCGEventX86 (event uid tid (lab-r tag loc val))
  ev-w    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → IsTCGEventX86 (event uid tid (lab-w tag loc val))
  ev-frm  : {uid : UniqueId} {tid : ThreadId} → IsTCGEventX86 (event uid tid (lab-f RM))
  ev-fww  : {uid : UniqueId} {tid : ThreadId} → IsTCGEventX86 (event uid tid (lab-f WW))
  ev-fsc  : {uid : UniqueId} {tid : ThreadId} → IsTCGEventX86 (event uid tid (lab-f SC))


-- | A proof that a TCG execution could only have been generated from a TCG program
-- that is mapped from an X86 program.
--
-- This follows from mappings on the instruction-level. (Which we omit)
record TCG-X86Restricted (ex : Execution LabelTCG) : Set₁ where
  field
    consistent : IsTCGConsistent ex
    
    ev-bound : events ex ⊆₁ IsTCGEventX86
    
    -- Read events that are generated from the LD instruction are /always/ followed by a F_RM fence.
    -- By the rule: Rᵣ(x,v) ↦ Rᵣ(x,v);F_RM
    -- There is no other way of obtaining a Rᵣ event.
    r-f-po₁ : ∀ {a : Event LabelTCG} → a ∈ events ex → EvRₜ tmov a → ∃[ b ] (po-imm ex a b × TCG.EvF₌ RM b)
    r-f-po₂ : ∀ {b : Event LabelTCG} → b ∈ events ex → TCG.EvF₌ RM b → ∃[ a ] (po-imm ex a b × EvRₜ tmov a)

    -- Rule: W(x,v) ↦ F_WW;W(x,v)
    -- Every non-rmw write (ST) is preceded by a F_WW event
    f-w-po₁ : ∀ {a b : Event LabelTCG} → b ∈ events ex → EvWₜ tmov b → ∃[ a ] (po-imm ex a b × TCG.EvF₌ WW a)
    -- Every F_WW event is followed by a W event
    f-w-po₂ : ∀ {a b : Event LabelTCG} → a ∈ events ex → TCG.EvF₌ WW a → ∃[ b ] (po-imm ex a b × EvWₜ tmov b)

open TCG-X86Restricted


¬ev-bound : {ex : Execution LabelTCG} (ex-res : TCG-X86Restricted ex) {ev : Event LabelTCG} → ev ∈ events ex → ¬ (IsTCGEventX86 ev) → ⊥
¬ev-bound ex-res ev∈ex ¬is-a8 = ¬is-a8 (⊆₁-apply (ev-bound ex-res) ev∈ex)

-- # Helpers

po-bound : {ex : Execution LabelTCG} (wf : WellFormed ex) (ex-res : TCG-X86Restricted ex)
  → po ex ⊆₂ IsTCGEventX86 ×₂ IsTCGEventX86
po-bound {ex} wf ex-res =
  ⊆₂-trans (×₂-lift-udr (⇔₁-to-⊆₁ (po-elements wf))) (×₂-lift (ev-bound ex-res) (ev-bound ex-res))

rf-bound : {ex : Execution LabelTCG} (wf : WellFormed ex) (ex-res : TCG-X86Restricted ex)
  → rf ex ⊆₂ IsTCGEventX86 ×₂ IsTCGEventX86
rf-bound {ex} wf ex-res =
  ⊆₂-trans (×₂-lift-udr (rf-elements wf)) (×₂-lift (ev-bound ex-res) (ev-bound ex-res))
  
co-bound : {ex : Execution LabelTCG} (wf : WellFormed ex) (ex-res : TCG-X86Restricted ex)
  → co ex ⊆₂ IsTCGEventX86 ×₂ IsTCGEventX86
co-bound {ex} wf ex-res =
  ⊆₂-trans (×₂-lift-udr (co-elements wf)) (×₂-lift (ev-bound ex-res) (ev-bound ex-res))
  
rmw-bound : {ex : Execution LabelTCG} (wf : WellFormed ex) (ex-res : TCG-X86Restricted ex)
  → rmw ex ⊆₂ IsTCGEventX86 ×₂ IsTCGEventX86
rmw-bound wf ex-res = ⊆₂-trans (rmw-def wf) (⊆₂-trans imm-⊆₂ (po-bound wf ex-res))
