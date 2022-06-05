{-# OPTIONS --safe #-}


open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.Armv8 using (LabelArmv8)
open import MapTCGtoArmv8NonAtomic using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8NonAtomic.Mapping
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
import Proof.Mapping.TCGtoArmv8NonAtomic.Execution

open import MapTCGtoArmv8NonAtomic
-- defines `ev[⇐]` and `ψ`
open import Proof.Mapping.TCGtoArmv8NonAtomic.Execution dst dst-wf dst-ok as PE

import Proof.Framework LabelTCG dst dst-wf as Ψ
import Proof.Mapping.Framework LabelTCG dst dst-wf as Δ


open Execution
open WellFormed
open Armv8Execution
open Armv8-TCGRestricted


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
  ev[⇒] {a} a∈src , events[⇒] a∈src , R₌[⇒] a∈src a-r


-- Instrs: ST ↦ STR
-- Events: Wᵣ(x,v) ↦ W(x,v)ᵣ
src-rule-st : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
  → TCG.EvW₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvW₌ tmov x v a')
src-rule-st {a} {b} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , W₌[⇒] a∈src a-w


-- Rₗ;rmw;Wₗ           ↦ Aₗ;amo;Lₗ  || successful RMW
-- Rₗ                  ↦ Aₗ         || failed RMW

src-rule-rmw-dom : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
  → TCG.EvR₌ trmw x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvR₌ trmw x v a')
src-rule-rmw-dom {a} {b} a-r a∈src =
  (ev[⇒] {a} a∈src , events[⇒] a∈src , R₌[⇒] a∈src a-r)


src-rule-rmw-codom : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
  → TCG.EvW₌ trmw x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvW₌ trmw x v a')
src-rule-rmw-codom {a} {b} a-w a∈src =
  ev[⇒] {a} a∈src , events[⇒] a∈src , W₌[⇒] a∈src a-w


private
  r₌⇒rₜ : {x : Event LabelTCG} {loc : Location} {val : Value}
    → TCG.EvR₌ trmw loc val x → EvRₜ trmw x
  r₌⇒rₜ ev-r₌ = ev-r is-r refl

  w₌⇒wₜ : {x : Event LabelTCG} {loc : Location} {val : Value}
    → TCG.EvW₌ trmw loc val x → EvWₜ trmw x
  w₌⇒wₜ ev-w₌ = ev-w is-w refl


src-rule-rmw-ok : ∀ {a b c d : Event LabelTCG} {x : Location} {v₁ v₂ : Value}
  → EvSkip a
  → TCG.EvR₌ trmw x v₁ b
  → TCG.EvW₌ trmw x v₂ c
  → EvSkip d
  → po-imm src a b
  → rmw src b c
  → po-imm src c d
  → ∃[ a' ] ∃[ b' ] ∃[ c' ] ∃[ d' ] (po-imm dst a' b' × lxsx dst-a8 b' c' × po-imm dst c' d'
      × Armv8.EvF₌ F-full a' × Armv8.EvR₌ trmw x v₁ b' × Armv8.EvW₌ trmw x v₂ c' × Armv8.EvF₌ F-full d')
src-rule-rmw-ok {a} {b} {c} {d} a-skip b-r c-w d-skip pi[ab] rmw[bc] pi[cd] =
  ev[⇒] a∈src , ev[⇒] b∈src , ev[⇒] c∈src , ev[⇒] d∈src ,
    pi[⇒] a∈src b∈src pi[ab] , rmw[⇒]lxsx b∈src c∈src rmw[bc] , pi[⇒] c∈src d∈src pi[cd] ,
    pre-ff , R₌[⇒] b∈src b-r , W₌[⇒] c∈src c-w , post-ff
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
  c∈src = poˡ∈src (proj₁ pi[cd])
  d∈src = poʳ∈src (proj₁ pi[cd])
  ¬init-c : ¬ EvInit (ev[⇒] c∈src)
  ¬init-c c-init = disjoint-wₜ _ (init⇒wₜ (Init[⇐$] c∈src c-init) , w₌⇒wₜ c-w)
  pre-ff : Armv8.EvF₌ F-full (ev[⇒] {a} a∈src)
  pre-ff with rmw-ff-l dst-ok (events[⇒] b∈src) (Rₜ[⇒] b∈src (r₌⇒rₜ b-r))
    where
    b-rt : EvRₜ trmw (ev[⇒] b∈src)
    b-rt = Rₜ[⇒] b∈src (×₂-applyˡ (rmw-r×w src-wf) rmw[bc])
  ... | w , pi[wb] , w-org =
    -- Somehow, matching `w≡a` to `refl` hangs typechecking forever
    let w≡a = po-immˡ dst-wf pi[wb] (pi[⇒] a∈src b∈src pi[ab])
    in org-f-pre-rmw-f dst-ok (subst (org-f-pre-rmw dst-ok) w≡a w-org)
  post-ff : Armv8.EvF₌ F-full (ev[⇒] {d} d∈src)
  post-ff with rmw-ff-r-ok dst-ok (rmw[⇒] b∈src c∈src rmw[bc])
  ... | w , pi[cw] , w-org =
    -- Somehow, matching `w≡d` to `refl` hangs typechecking forever
    let w≡d = po-immʳ dst-wf ¬init-c pi[cw] (pi[⇒] c∈src d∈src pi[cd])
    in org-f-post-rmw-f dst-ok (subst (org-f-post-rmw dst-ok) w≡d w-org)

src-rule-rmw-fail : ∀ {a b c : Event LabelTCG} {x : Location} {v : Value}
  → EvSkip a
  → TCG.EvR₌ trmw x v b
  → EvSkip c
  → po-imm src a b
  → b ∉ dom (rmw src)
  → po-imm src b c
  → ∃[ a' ] ∃[ b' ] ∃[ c' ] (po-imm dst a' b' × b' ∉ dom (rmw dst) × po-imm dst b' c'
      × Armv8.EvF₌ F-full a' × Armv8.EvR₌ trmw x v b' × Armv8.EvF₌ F-full c')
src-rule-rmw-fail {a} {b} {c} a-skip b-r c-skip pi[ab] b∉rmwˡ pi[bc] =
  ev[⇒] a∈src , ev[⇒] b∈src , ev[⇒] c∈src ,
    pi[⇒] a∈src b∈src pi[ab] , ¬rmwˡ[⇒] b∈src b∉rmwˡ , pi[⇒] b∈src c∈src pi[bc] ,
    pre-ff , R₌[⇒] b∈src b-r , post-ff
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
  c∈src = poʳ∈src (proj₁ pi[bc])
  ¬init-b : ¬ EvInit (ev[⇒] b∈src)
  ¬init-b b-init = disjoint-r/init _ (rₜ⇒r (r₌⇒rₜ b-r) , Init[⇐$] b∈src b-init)
  pre-ff : Armv8.EvF₌ F-full (ev[⇒] {a} a∈src)
  pre-ff with rmw-ff-l dst-ok (events[⇒] b∈src) (Rₜ[⇒] b∈src (r₌⇒rₜ b-r))
  ... | w , pi[wb] , w-org =
    -- Somehow, matching `w≡a` to `refl` hangs typechecking forever
    let w≡a = po-immˡ dst-wf pi[wb] (pi[⇒] a∈src b∈src pi[ab])
    in org-f-pre-rmw-f dst-ok (subst (org-f-pre-rmw dst-ok) w≡a w-org)
  -- ... | refl = org-f-pre-rmw-f dst-ok w-org
  post-ff : Armv8.EvF₌ F-full (ev[⇒] {c} c∈src)
  post-ff with rmw-ff-r-fail dst-ok (events[⇒] b∈src) (Rₜ[⇒] b∈src (r₌⇒rₜ b-r)) (¬rmwˡ[⇒] b∈src b∉rmwˡ)
  ... | w , pi[bw] , w-org =
    -- Somehow, matching `w≡c` to `refl` hangs typechecking forever
    let w≡c = po-immʳ dst-wf ¬init-b pi[bw] (pi[⇒] b∈src c∈src pi[bc])
    in org-f-post-rmw-f dst-ok (subst (org-f-post-rmw dst-ok) w≡c w-org)


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
