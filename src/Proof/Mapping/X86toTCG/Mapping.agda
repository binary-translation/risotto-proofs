{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.TCG using (LabelTCG)
open import MapX86toTCG using (TCG-X86Restricted)


module Proof.Mapping.X86toTCG.Mapping
  (dst : Execution LabelTCG)
  (dst-wf : WellFormed dst)
  (dst-ok : TCG-X86Restricted dst)
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
-- Local imports: Relations
open import Dodo.Binary
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.TCG as TCG
open import Arch.X86 as X86
-- import Proof.Mapping.X86toTCG.Execution

open import MapX86toTCG
-- defines `ev[⇐]` and `ψ`
open import Proof.Mapping.X86toTCG.Execution dst dst-wf dst-ok as PE

import Proof.Framework LabelX86 dst dst-wf as Ψ
import Proof.Mapping.Framework LabelX86 dst dst-wf as Δ


open Execution
open TCG-X86Restricted


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ
--
open PE.Extra


-- R₌⇒Rₜ : {tag : Tag} {x : Location} {v : Value} {a : Event LabelX86}
--   → X86.EvR₌ tag x v a → EvRₜ tag a
-- R₌⇒Rₜ ev-r = ev-r is-r refl

-- Instrs: RMOV    ↦ LD;F_LD_M
-- Events: Rᵣ(x,v) ↦ Rᵣ(x,v);F_RM
src-rule-rmov : ∀ {a b : Event LabelX86} {x : Location} {v : Value}
  → X86.EvR₌ tmov x v a
  → EvSkip b
  → po-imm src a b
  → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × TCG.EvR₌ tmov x v a' × TCG.EvF₌ RM b')
src-rule-rmov {a} {b} ev-r b-skip pi[ab] with r-f-po₁ dst-ok (events[⇒] {a} a∈src) (Rₜ[⇒] a∈src (ev-r is-r refl))
  where a∈src = poˡ∈src (proj₁ pi[ab])
... | z , pi[az] , z-is-f with po-immʳ dst-wf (¬Init[⇒] a∈src (λ{q → disjoint-r/init _ (ev-r is-r , q)})) pi[az] (pi[⇒] a∈src b∈src pi[ab])
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
... | refl = _ , _ , pi[⇒] a∈src b∈src pi[ab] , R₌[⇒] a∈src ev-r , z-is-f
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])

-- Instrs: WMOV   ↦ F_ST_ST;ST
-- Events: W(x,v) ↦ F_WW;W(x,v)
src-rule-wmov : ∀ {a b : Event LabelX86}
    {x : Location} {v : Value}
  → EvSkip a
  → X86.EvW₌ tmov x v b
  → po-imm src a b
  → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × TCG.EvF₌ WW a' × TCG.EvW₌ tmov x v b')
src-rule-wmov {a} {b} ev-skip ev-w₌ pi[ab] with f-w-po₁ dst-ok {ev[⇒] {a} a∈src} (events[⇒] {b} b∈src) (Wₜ[⇒] b∈src (ev-w is-w refl))
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
... | z , pi[zb] , z-is-f with po-immˡ dst-wf pi[zb] (pi[⇒] {a} {b} a∈src b∈src pi[ab])
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
... | refl = 
  ev[⇒] a∈src , ev[⇒] b∈src , pi[⇒] {a} {b} a∈src b∈src pi[ab] , z-is-f , W₌[⇒] b∈src ev-w₌
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])

-- Instrs: RMW ↦ RMW
-- Events: Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;W(x,v')  || successful
--         Rₗ(x,v)             ↦ Rₗ(x,v)              || failed
src-rule-rmw-ok : ∀ {a b : Event LabelX86}
    {x : Location} {v₁ v₂ : Value}
  → X86.EvR₌ trmw x v₁ a
  → X86.EvW₌ trmw x v₂ b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × TCG.EvR₌ trmw x v₁ a' × TCG.EvW₌ trmw x v₂ b')
src-rule-rmw-ok {a} {b} ev-r ev-w₌ rmw[ab] =
  let a∈src = rmwˡ∈src rmw[ab]
      b∈src = rmwʳ∈src rmw[ab]
  in ev[⇒] a∈src , ev[⇒] b∈src , rmw[⇒] a∈src b∈src rmw[ab] , R₌[⇒] a∈src ev-r , W₌[⇒] b∈src ev-w₌

src-rule-rmw-fail : ∀ {a : Event LabelX86}
    {x : Location} {v : Value}
  → X86.EvR₌ trmw x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × TCG.EvR₌ trmw x v a')
src-rule-rmw-fail {a} ev-r a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , R₌[⇒] a∈src ev-r

-- Instrs: MFENCE ↦ F_SC
-- Events: F      ↦ F_SC
src-rule-fence : ∀ {a : Event LabelX86}
  → EvF a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × TCG.EvF₌ TCG.SC a')
src-rule-fence {a} (ev-f is-f) a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , F[⇒] a∈src (ev-f is-f)


mapping : X86⇒TCG src dst
mapping =
  record
    { rule-rmov     = src-rule-rmov
    ; rule-wmov     = src-rule-wmov
    ; rule-rmw-ok   = src-rule-rmw-ok
    ; rule-rmw-fail = src-rule-rmw-fail
    ; rule-fence    = src-rule-fence
    }
