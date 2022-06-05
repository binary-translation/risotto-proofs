{-# OPTIONS --safe #-}


module MapTCGtoArmv8NonAtomic where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Data.Empty using (⊥-elim; ⊥)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (_∷_; [])
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Tri)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.TCG as TCG
open import Arch.Armv8 as Armv8

open import Helpers


open Execution
open WellFormed
open TCG.F-mode
open Armv8Execution
open IsArmv8Consistent


-- Mapping - TCG ⇒ ARMv8
--
-- Instruction mapping:
--
-- LD       ↦  LDR
-- ST       ↦  STR
-- RMW      ↦  DMBFF;RMW;DMBFF
--
-- F_LD_LD  ↦  DMBLD
-- F_LD_ST  ↦  DMBLD
-- F_LD_M   ↦  DMBLD
--
-- F_ST_ST  ↦  DMBST
--
-- F_ST_LD  ↦  DMBFF
-- F_ST_M   ↦  DMBFF
-- F_M_LD   ↦  DMBFF
-- F_M_ST   ↦  DMBFF
-- F_M_M    ↦  DMBFF
-- F_SC     ↦  DMBFF
--
--
-- Corresponding event mapping:
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


record TCG⇒Armv8 (src : Execution LabelTCG) {dst : Execution LabelArmv8} (dst-a8 : Armv8Execution dst) : Set where
  field
    -- Instrs: LD ↦ LDR
    -- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
    rule-ld : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
      → TCG.EvR₌ tmov x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvR₌ tmov x v a')

    -- Instrs: ST ↦ STR
    -- Events: Wᵣ(x,v) ↦ Wᵣ(x,v)
    rule-st : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
      → TCG.EvW₌ tmov x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvW₌ tmov x v a')

    -- Instrs: RMW ↦ DMBFF;RMW;DMBFF
    -- Events: Rₗ;rmw;Wₗ  ↦ F_FULL;Rₗ;lxsx;Wₗ;F_FULL  || successful RMW
    --         Rₗ         ↦ F_FULL;Rₗ;F_FULL          || failed RMW

    rule-rmw-dom : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
      → TCG.EvR₌ trmw x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvR₌ trmw x v a')
      
    rule-rmw-codom : ∀ {a : Event LabelTCG} {x : Location} {v : Value}
      → TCG.EvW₌ trmw x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvW₌ trmw x v a')

    rule-rmw-ok : ∀ {a b c d : Event LabelTCG} {x : Location} {v₁ v₂ : Value}
      → EvSkip a
      → TCG.EvR₌ trmw x v₁ b
      → TCG.EvW₌ trmw x v₂ c
      → EvSkip d
      → po-imm src a b
      → rmw src b c
      → po-imm src c d
      → ∃[ a' ] ∃[ b' ] ∃[ c' ] ∃[ d' ] (po-imm dst a' b' × lxsx dst-a8 b' c' × po-imm dst c' d'
          × Armv8.EvF₌ F-full a' × Armv8.EvR₌ trmw x v₁ b' × Armv8.EvW₌ trmw x v₂ c' × Armv8.EvF₌ F-full d')
    rule-rmw-fail : ∀ {a b c : Event LabelTCG} {x : Location} {v : Value}
      → EvSkip a
      → TCG.EvR₌ trmw x v b
      → EvSkip c
      → po-imm src a b
      → b ∉ dom (rmw src)
      → po-imm src b c
      → ∃[ a' ] ∃[ b' ] ∃[ c' ] (po-imm dst a' b' × b' ∉ dom (rmw dst) × po-imm dst b' c'
          × Armv8.EvF₌ F-full a' × Armv8.EvR₌ trmw x v b' × Armv8.EvF₌ F-full c')

    -- Instrs: F_LD_LD F_LD_ST F_LD_M ↦ DMBLD
    -- Events: F_RR    F_RW    F_RM   ↦ F_LD
      
    rule-f-ld : ∀ {a : Event LabelTCG}
      → {m : TCG.F-mode}
      → m ∈ₗ (RR ∷ RW ∷ RM ∷ [])
      → TCG.EvF₌ m a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-ld a')
      
    -- Instrs: F_ST_ST ↦ DMBST
    -- Events: F_WW    ↦ F_ST
    
    rule-f-st : ∀ {a : Event LabelTCG}
      → TCG.EvF₌ WW a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-st a')

    -- Instrs: F_ST_LD F_ST_M F_M_LD F_M_ST F_M_M F_SC ↦ DMBFF
    -- Events: F_WR    F_WM   F_MR   F_MW   F_MM  F_SC ↦ F
    
    rule-f-full : ∀ {a b : Event LabelTCG}
      → {m : TCG.F-mode}
      → m ∈ₗ (WR ∷ WM ∷ MR ∷ MW ∷ MM ∷ SC ∷ [])
      → TCG.EvF₌ m a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-full a')

    -- Instrs: F_ACQ F_REL ↦ skip
    -- Events: F_ACQ F_REL ↦ skip
      
    rule-f-skip : ∀ {a : Event LabelTCG}
      → {m : TCG.F-mode}
      → m ∈ₗ (ACQ ∷ REL ∷ [])
      → TCG.EvF₌ m a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvSkip a')
      

-- Armv8 programs mapped from TCG can only contain:
-- R W F_LD F_ST F_FULL
data IsArmv8EventTCG : Event LabelArmv8 → Set where
  ev-init : {uid : UniqueId} {loc : Location} {val : Value} → IsArmv8EventTCG (event-init uid loc val)
  ev-skip : {uid : UniqueId} {tid : ThreadId} → IsArmv8EventTCG (event-skip uid tid)
  ev-r    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → IsArmv8EventTCG (event uid tid (lab-r tag loc val))
  ev-w    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → IsArmv8EventTCG (event uid tid (lab-w tag loc val))
  ev-f    : {uid : UniqueId} {tid : ThreadId} {mode : Armv8.F-mode} → IsArmv8EventTCG (event uid tid (lab-f mode))

-- | Alternative to `a ∪₁ b ∪ c ∪₁ d ∪₁ e ∪₁ f`, which would require pattern matches akin to: `inj₁ (inj₁ (inj₁ (inj₁ (inj₁ ...))))`
data Opt₆ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level} (A₁ : Set ℓ₁) (A₂ : Set ℓ₂) (A₃ : Set ℓ₃) (A₄ : Set ℓ₄) (A₅ : Set ℓ₅) (A₆ : Set ℓ₆) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆) where
  opt₁ : A₁ → Opt₆ A₁ A₂ A₃ A₄ A₅ A₆
  opt₂ : A₂ → Opt₆ A₁ A₂ A₃ A₄ A₅ A₆
  opt₃ : A₃ → Opt₆ A₁ A₂ A₃ A₄ A₅ A₆
  opt₄ : A₄ → Opt₆ A₁ A₂ A₃ A₄ A₅ A₆
  opt₅ : A₅ → Opt₆ A₁ A₂ A₃ A₄ A₅ A₆
  opt₆ : A₆ → Opt₆ A₁ A₂ A₃ A₄ A₅ A₆

OptPred₆ : {a ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level} {A : Set a} (P₁ : Pred A ℓ₁) (P₂ : Pred A ℓ₂) (P₃ : Pred A ℓ₃) (P₄ : Pred A ℓ₄) (P₅ : Pred A ℓ₅) (P₆ : Pred A ℓ₆)
  → Pred A (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)
OptPred₆ P₁ P₂ P₃ P₄ P₅ P₆ x = Opt₆ (P₁ x) (P₂ x) (P₃ x) (P₄ x) (P₅ x) (P₆ x)

record Armv8-TCGRestricted (ex : Execution LabelArmv8) : Set₁ where
  field
    consistent : IsArmv8Consistent ex
    
    ev-bound : events ex ⊆₁ IsArmv8EventTCG

    -- Denotes where the events originate in the target. If the mapping were defined on the
    -- /instruction level/, it is obvious where /instructions/ in the target come from.
    -- However, as the instructions are absent in our model, we annotate events accordingly.

    -- Full fences in Armv8 can be produced from either:
    -- * WR / WM / MR / MW / MM / SC fences in TCG
    -- * Around a RMW operation - corresponding to skip events in the source
    org-f-wr       : Pred (Event LabelArmv8) ℓzero
    org-f-wm       : Pred (Event LabelArmv8) ℓzero
    org-f-mr       : Pred (Event LabelArmv8) ℓzero
    org-f-mw       : Pred (Event LabelArmv8) ℓzero
    org-f-mm       : Pred (Event LabelArmv8) ℓzero
    org-f-sc       : Pred (Event LabelArmv8) ℓzero
    org-f-pre-rmw  : Pred (Event LabelArmv8) ℓzero
    org-f-post-rmw : Pred (Event LabelArmv8) ℓzero

    -- Load fences in Armv8 can be produced from RR / RW / RW fences in TCG
    org-ld-rr : Pred (Event LabelArmv8) ℓzero
    org-ld-rw : Pred (Event LabelArmv8) ℓzero
    org-ld-rm : Pred (Event LabelArmv8) ℓzero

    -- Skip events in Armv8 can be produced from either:
    -- * skips in TCG
    -- * ACQ / REL fences in TCG
    org-skip-skip : Pred (Event LabelArmv8) ℓzero
    org-skip-acq  : Pred (Event LabelArmv8) ℓzero
    org-skip-rel  : Pred (Event LabelArmv8) ℓzero
    
    -- Store fences can only be created from `WW` fences. No need to keep track


    unique-org-f-wr       : UniquePred org-f-wr
    unique-org-f-wm       : UniquePred org-f-wm
    unique-org-f-mr       : UniquePred org-f-mr
    unique-org-f-mw       : UniquePred org-f-mw
    unique-org-f-mm       : UniquePred org-f-mm
    unique-org-f-sc       : UniquePred org-f-sc
    unique-org-f-pre-rmw  : UniquePred org-f-pre-rmw
    unique-org-f-post-rmw : UniquePred org-f-post-rmw

    unique-org-ld-rr : UniquePred org-ld-rr
    unique-org-ld-rw : UniquePred org-ld-rw
    unique-org-ld-rm : UniquePred org-ld-rm

    unique-org-skip-skip : UniquePred org-skip-skip
    unique-org-skip-acq  : UniquePred org-skip-acq
    unique-org-skip-rel  : UniquePred org-skip-rel

    -- Before every RMW-read there is a full fence
    rmw-ff-l : ∀ {b : Event LabelArmv8} → b ∈ events ex → EvRₜ trmw b → ∃[ a ] (po-imm ex a b × org-f-pre-rmw a)
    -- After every successful-RMW-write there is a full fence
    rmw-ff-r-ok : ∀ {a b : Event LabelArmv8} → rmw ex a b → ∃[ c ] (po-imm ex b c × org-f-post-rmw c)
    -- After every failed-RMW-read there is a full fence
    rmw-ff-r-fail : ∀ {a : Event LabelArmv8} → a ∈ events ex → EvRₜ trmw a → a ∉ dom (rmw ex) → ∃[ b ] (po-imm ex a b × org-f-post-rmw b)

    org-f-def    : (events ex ∩₁ Armv8.EvF₌ F-full) ⇔₁ ((OptPred₆ org-f-wr org-f-wm org-f-mr org-f-mw org-f-mm org-f-sc) ∪₁ (org-f-pre-rmw ∪₁ org-f-post-rmw))
    org-ld-def   : (events ex ∩₁ Armv8.EvF₌ F-ld) ⇔₁ (org-ld-rr ∪₁ org-ld-rw ∪₁ org-ld-rm)
    org-skip-def : (events ex ∩₁ EvSkip) ⇔₁ (org-skip-skip ∪₁ org-skip-acq ∪₁ org-skip-rel)

    -- All `rmw` relations are over `lxsx` by the /non-atomic/ mapping
    no-amo : Empty₂ (amo (a8 consistent))

    disjoint-f    : PairwiseDisjoint₁ (org-f-wr ∷ org-f-wm ∷ org-f-mr ∷ org-f-mw ∷ org-f-mm ∷ org-f-sc ∷ org-f-pre-rmw ∷ org-f-post-rmw ∷ [])
    disjoint-ld   : PairwiseDisjoint₁ (org-ld-rr ∷ org-ld-rw ∷ org-ld-rm ∷ [])
    disjoint-skip : PairwiseDisjoint₁ (org-skip-skip ∷ org-skip-acq ∷ org-skip-rel ∷ [])

open Armv8-TCGRestricted


¬ev-bound : {ex : Execution LabelArmv8} (ex-res : Armv8-TCGRestricted ex) {ev : Event LabelArmv8} → ev ∈ events ex → ¬ (IsArmv8EventTCG ev) → ⊥
¬ev-bound ex-res ev∈ex ¬is-a8 = ¬is-a8 (⊆₁-apply (ev-bound ex-res) ev∈ex)


-- # Helpers

po-bound : {ex : Execution LabelArmv8} (wf : WellFormed ex) (ex-res : Armv8-TCGRestricted ex)
  → po ex ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
po-bound {ex} wf ex-res =
  ⊆₂-trans (×₂-lift-udr (⇔₁-to-⊆₁ (po-elements wf))) (×₂-lift (ev-bound ex-res) (ev-bound ex-res))

rf-bound : {ex : Execution LabelArmv8} (wf : WellFormed ex) (ex-res : Armv8-TCGRestricted ex)
  → rf ex ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
rf-bound {ex} wf ex-res =
  ⊆₂-trans (×₂-lift-udr (rf-elements wf)) (×₂-lift (ev-bound ex-res) (ev-bound ex-res))
  
co-bound : {ex : Execution LabelArmv8} (wf : WellFormed ex) (ex-res : Armv8-TCGRestricted ex)
  → co ex ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
co-bound {ex} wf ex-res =
  ⊆₂-trans (×₂-lift-udr (co-elements wf)) (×₂-lift (ev-bound ex-res) (ev-bound ex-res))
  
rmw-bound : {ex : Execution LabelArmv8} (wf : WellFormed ex) (ex-res : Armv8-TCGRestricted ex)
  → rmw ex ⊆₂ IsArmv8EventTCG ×₂ IsArmv8EventTCG
rmw-bound wf ex-res = ⊆₂-trans (rmw-def wf) (⊆₂-trans imm-⊆₂ (po-bound wf ex-res))

org-f-pre-rmw-f : {ex : Execution LabelArmv8} (ex-res : Armv8-TCGRestricted ex)
  → {x : Event LabelArmv8}
  → org-f-pre-rmw ex-res x
  → Armv8.EvF₌ F-full x
org-f-pre-rmw-f ex-res x-pre = proj₂ (⇔₁-apply-⊇₁ (org-f-def ex-res) (inj₂ (inj₁ x-pre)))

org-f-post-rmw-f : {ex : Execution LabelArmv8} (ex-res : Armv8-TCGRestricted ex)
  → {x : Event LabelArmv8}
  → org-f-post-rmw ex-res x
  → Armv8.EvF₌ F-full x
org-f-post-rmw-f ex-res x-post = proj₂ (⇔₁-apply-⊇₁ (org-f-def ex-res) (inj₂ (inj₂ x-post)))

rmw⇒lxsx : ∀ {ex : Execution LabelArmv8} (ex-res : Armv8-TCGRestricted ex) → {x y : Event LabelArmv8}
  → rmw ex x y → lxsx (a8 (consistent ex-res)) x y
rmw⇒lxsx ex-res rmw[xy] with ⇔₂-apply-⊆₂ (amo-lxsx-def (consistent ex-res)) rmw[xy]
... | inj₁ amo[xy]  = ⊥-elim (no-amo ex-res _ _ amo[xy])
... | inj₂ lxsx[xy] = lxsx[xy]
