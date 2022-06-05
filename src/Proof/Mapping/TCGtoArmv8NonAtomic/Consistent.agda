{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.Armv8 using (LabelArmv8)
open import MapTCGtoArmv8NonAtomic using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8NonAtomic.Consistent
  (dst : Execution LabelArmv8) (dst-wf : WellFormed dst) (dst-ok : Armv8-TCGRestricted dst) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_])
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.TCG as TCG
open import Arch.TCG.Detour
open import Arch.Armv8 as Armv8
-- Local imports: Theorem Specification
open import MapTCGtoArmv8NonAtomic
-- Local imports: Proof Components
import Proof.Framework LabelTCG dst dst-wf as Ψ
import Proof.Mapping.Framework LabelTCG dst dst-wf as Δ
open import Proof.Mapping.TCGtoArmv8NonAtomic.Execution dst dst-wf dst-ok as PE


open Execution
open WellFormed
open IsTCGConsistent
open Armv8Execution
open IsArmv8Consistent
open Armv8-TCGRestricted
open PE.Extra


-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ


-- # Proof: Coherence

src-ax-coherence  : Acyclic _≡_ ( Coh src )
src-ax-coherence refl coh[xx] =
  let x∈src = ⁺-lift-predˡ coh-dom coh[xx]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ (cohˡ∈ex src-wf) coh[⇒] x∈src x∈src coh[xx])
  where
  coh-dom : ∀ {x y : Event LabelTCG} → Coh src x y → x ∈ events src
  coh-dom {x} {y} (coh-po-loc po-loc[xy]) = poˡ∈src (proj₁ po-loc[xy])
  coh-dom {x} {y} (coh-rf rf[xy])         = rfˡ∈src rf[xy]
  coh-dom {x} {y} (coh-fr fr[xy])         = frˡ∈src fr[xy]
  coh-dom {x} {y} (coh-co co[xy])         = coˡ∈src co[xy]

  coh[⇒] : ∀ {x y : Event LabelTCG}
    → (x∈src : x ∈ events src) (y∈src : y ∈ events src)
    → Coh src x y
    → (po-loc dst ∪₂ Ca dst ∪₂ rf dst) (ev[⇒] x∈src) (ev[⇒] y∈src)
  coh[⇒] x∈src y∈src (coh-po-loc po-loc[xy]) = inj₁ (inj₁ (po-loc[⇒] x∈src y∈src po-loc[xy]))
  coh[⇒] x∈src y∈src (coh-rf rf[xy])         = inj₂ (rf[⇒] x∈src y∈src rf[xy])
  coh[⇒] x∈src y∈src (coh-fr fr[xy])         = inj₁ (inj₂ (ca-fr (fr[⇒] x∈src y∈src fr[xy])))
  coh[⇒] x∈src y∈src (coh-co co[xy])         = inj₁ (inj₂ (ca-co (co[⇒] x∈src y∈src co[xy])))


-- # Proof: Atomicity

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
  in
  ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] x∈src z∈src fre[xz] ⨾[ ev[⇒] z∈src ]⨾ coe[⇒] z∈src y∈src coe[zy]
    )


-- # Proof: Global Order

-- ## Helpers


-- -- ## Proof

arm-f₌⇒f : {x : Event LabelArmv8} {mode : Armv8.F-mode} → Armv8.EvF₌ mode x → EvF x
arm-f₌⇒f ev-f₌ = ev-f is-f

RW⨾po⨾Rₜ[⇒]bob : {x y : Event LabelTCG} (x∈src : x ∈ events src) (y∈src : y ∈ events src)
  → po src x y → EvRW x → EvRₜ trmw y
  → ( po dst ⨾ ⦗ Armv8.EvF₌ F-full ⦘ ⨾ po dst ) (ev[⇒] x∈src) (ev[⇒] y∈src)
RW⨾po⨾Rₜ[⇒]bob x∈src y∈src po[xy] x-rw y-rₜ =
  let dst-po[xy] = po[⇒] x∈src y∈src po[xy]
      (v , pi[vy] , v-pre) = rmw-ff-l dst-ok (events[⇒] y∈src) (Rₜ[⇒] y∈src y-rₜ)
      v-sc = org-f-pre-rmw-f dst-ok v-pre
  in
  case unsplit-poʳ dst-wf dst-po[xy] pi[vy] of
  λ{ (inj₁ refl)   → ⊥-elim (disjoint-f/rw _ (arm-f₌⇒f v-sc , RW[⇒] x∈src x-rw)) -- x ≡ v
   ; (inj₂ po[xv]) → po[xv] ⨾[ _ ]⨾ (refl , v-sc) ⨾[ _ ]⨾ proj₁ pi[vy]
   }

Wₜ⨾po⨾RW[⇒]bob : {x y : Event LabelTCG} (x∈src : x ∈ events src) (y∈src : y ∈ events src)
  → po src x y → EvWₜ trmw x → EvRW y
  → ( po dst ⨾ ⦗ Armv8.EvF₌ F-full ⦘ ⨾ po dst ) (ev[⇒] x∈src) (ev[⇒] y∈src)
Wₜ⨾po⨾RW[⇒]bob x∈src y∈src po[xy] x-wₜ y-rw =
  let dst-po[xy] = po[⇒] x∈src y∈src po[xy]
      (v , rmw[vx]) = ⇔₁-apply-⊇₁ (rmw-w src-wf) (x∈src , x-wₜ)
      v∈src = rmwˡ∈src rmw[vx]
      dst-rmw[vx] = rmw[⇒] v∈src x∈src rmw[vx]
      (z , pi[xz] , z-post) = rmw-ff-r-ok dst-ok dst-rmw[vx]
      z-sc = org-f-post-rmw-f dst-ok z-post
      ¬x-init = λ{x-init → disjoint-wₜ/init _ (Wₜ[⇒] x∈src x-wₜ , x-init)}
  in
  case unsplit-poˡ dst-wf ¬x-init dst-po[xy] pi[xz] of
  λ{ (inj₁ refl)   → ⊥-elim (disjoint-f/rw _ (arm-f₌⇒f z-sc , RW[⇒] y∈src y-rw)) -- y ≡ z
   ; (inj₂ po[zy]) → proj₁ pi[xz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy]
   }

src-ax-global-ord : Irreflexive _≡_ (ghb src)
src-ax-global-ord refl ghb[xx] =
  let ghbd[xx] = proj₂ (detour src-wf ghb[xx])
      x∈src = ⁺-lift-predˡ (GhbiAltˡ∈ex src-wf) ghbd[xx]
  in ax-global-obs dst-consistent refl (⁺[⇒]ˡ (GhbiAltˡ∈ex src-wf) ghbi[⇒]obi x∈src x∈src ghbd[xx])
  where
  ord[⇒]obi : Rel[⇒] (OrdAlt src) (Obi dst-a8)
  ord[⇒]obi x∈src y∈src (ord-init ((refl , x-init) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
    obi-lob ([ lobi-init ((refl , Init[⇒] x∈src x-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy]) ])

  -- RR
  ord[⇒]obi x∈src y∈src (ord-rr ((refl , x-r) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in -- Frm[⇒]
    obi-lob ([ lobi-bob (bob-fld ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Frr[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy]))] )
  -- RW
  ord[⇒]obi x∈src y∈src (ord-rw ((refl , x-r) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in -- Frm[⇒]
    obi-lob ([ lobi-bob (bob-fld ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Frw[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy]))] )
  -- RM
  ord[⇒]obi x∈src y∈src (ord-rm ((refl , x-r) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in -- Frm[⇒]
    obi-lob ([ lobi-bob (bob-fld ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Frm[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy]))] )
    
  ord[⇒]obi x∈src y∈src (ord-wr ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in
    obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fwr[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  ord[⇒]obi x∈src y∈src (ord-ww ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in
    obi-lob ([ lobi-bob (bob-fst ((refl , W[⇒] x∈src x-w) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fww[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy] ⨾[ _ ]⨾ (refl , W[⇒] y∈src y-w))) ])
  ord[⇒]obi x∈src y∈src (ord-wm ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in
    obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fwm[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
    
  ord[⇒]obi x∈src y∈src (ord-mr ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in
    obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fmr[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  ord[⇒]obi x∈src y∈src (ord-mw ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in
    obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fmw[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  ord[⇒]obi x∈src y∈src (ord-mm ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in
    obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fmm[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
    
  ord[⇒]obi x∈src y∈src (ord-sc ((refl , x-rw) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ z ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in
    obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fsc[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  ord[⇒]obi x∈src y∈src (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ@(z , rmw[yz])))) =
    let y-rₜ = rmwˡ-r src-wf y∈rmwˡ
    in
    obi-lob ([ lobi-bob (bob-f (RW⨾po⨾Rₜ[⇒]bob x∈src y∈src po[xy] x-rw y-rₜ)) ])
  ord[⇒]obi x∈src y∈src (ord-rmw-codom ((refl , x∈rmwʳ@(z , rmw[zx])) ⨾[ x ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    let x-wₜ = rmwʳ-w src-wf x∈rmwʳ
    in obi-lob [ lobi-bob (bob-f (Wₜ⨾po⨾RW[⇒]bob x∈src y∈src po[xy] x-wₜ y-rw)) ]
  -- In TCG, a RMW-write is ordered with whatever comes before. In the Armv8 mapping, this is
  -- enforced by the DMFF /preceding/ the RMW operation. At the event level, the fence occurs
  -- before the read preceding the write. (i.e., F⨾Rₜ⨾Wₜ)
  ord[⇒]obi x∈src y∈src (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-wₜ))) =
    let (v , rmw[vy]) = ⇔₁-apply-⊇₁ (rmw-w src-wf) (y∈src , y-wₜ)
    in
    case unsplit-poʳ src-wf po[xy] (⊆₂-apply (rmw-def src-wf) rmw[vy]) of
    λ{ (inj₁ refl)   → obi-lob [ lobi-aob (aob-rmw (rmw[⇒] x∈src y∈src rmw[vy])) ] -- x ≡ v
     ; (inj₂ po[xv]) → 
         let v∈src = rmwˡ∈src rmw[vy]
             v-rₜ = rmwˡ-r src-wf (take-dom (rmw src) rmw[vy])
             dst-po[vy] = proj₁ (⊆₂-apply (rmw-def dst-wf) (rmw[⇒] v∈src y∈src rmw[vy]))
         in
         case RW⨾po⨾Rₜ[⇒]bob x∈src v∈src po[xv] x-rw v-rₜ of
         λ{(po[xz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zv]) →
             obi-lob [ lobi-bob (bob-f (po[xz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po-trans dst-wf po[zv] dst-po[vy])) ]}
     }
  -- In TCG, a RMW-read is ordered with whatever follows. In the Armv8 mapping, this is enforced by
  -- the DMBFF /following/ the RMW operation. At the event level, the fence occurs either directly
  -- after the read (if the RMW fails), or after the subsequent write (if the RMW succeeds)
  -- (i.e., Rₜ⨾F or Rₜ⨾Wₜ⨾F)
  ord[⇒]obi {x} x∈src y∈src (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)))
    with rmwˡ-dec src-wf x
  ... | yes (v , rmw[xv]) = -- successful RMW
          let v∈src = rmwʳ∈src rmw[xv]
              dst-po[xv] = proj₁ (⊆₂-apply (rmw-def dst-wf) (rmw[⇒] x∈src v∈src rmw[xv]))
              ¬x-init = λ{x-init → disjoint-r/init _ (rₜ⇒r x-rₜ , x-init)}
          in
          case unsplit-poˡ src-wf ¬x-init po[xy] (⊆₂-apply (rmw-def src-wf) rmw[xv]) of
          λ{ (inj₁ refl)   → obi-lob [ lobi-aob (aob-rmw (rmw[⇒] x∈src y∈src rmw[xv])) ] -- v ≡ y
           ; (inj₂ po[vy]) →
               let v-wₜ = rmwʳ-w src-wf (take-codom (rmw src) rmw[xv])
               in case Wₜ⨾po⨾RW[⇒]bob v∈src y∈src po[vy] v-wₜ y-rw of
               λ{(po[vz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy]) →
                   obi-lob [ lobi-bob (bob-f (po-trans dst-wf dst-po[xv] po[vz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy])) ]}
           }
  ... | no x∉rmwˡ = -- failed RMW
          let x∈dst = events[⇒] x∈src
              dst-po[xy] = po[⇒] x∈src y∈src po[xy]
              dst-x∉rmwˡ = ¬rmwˡ[⇒] x∈src x∉rmwˡ
              (v , pi[xv] , v-post) = rmw-ff-r-fail dst-ok x∈dst (Rₜ[⇒] x∈src x-rₜ) dst-x∉rmwˡ
              v-sc = org-f-post-rmw-f dst-ok v-post
              ¬x-init = λ{x-init → disjoint-r/init _ (rₜ⇒r x-rₜ , Init[⇐$] x∈src x-init)}
          in
          case unsplit-poˡ dst-wf ¬x-init dst-po[xy] pi[xv] of
          λ{ (inj₁ refl) → ⊥-elim (disjoint-f/rw _ (arm-f₌⇒f v-sc , RW[⇒] y∈src y-rw)) -- v ≡ y
           ; (inj₂ po[vy]) →
               obi-lob [ lobi-bob (bob-f (proj₁ pi[xv] ⨾[ _ ]⨾ (refl , v-sc) ⨾[ _ ]⨾ po[vy])) ]
           }

  ghbi[⇒]obi : Rel[⇒] (GhbiAlt src) (Obi dst-a8)
  ghbi[⇒]obi x∈src y∈src (ghbi-ord ord[xy]) = ord[⇒]obi x∈src y∈src ord[xy]
  ghbi[⇒]obi x∈src y∈src (ghbi-rfe rfe[xy]) = obi-obs (obs-rfe (rfe[⇒] x∈src y∈src rfe[xy]))
  ghbi[⇒]obi x∈src y∈src (ghbi-coe coe[xy]) = obi-obs (obs-coe (coe[⇒] x∈src y∈src coe[xy]))
  ghbi[⇒]obi x∈src y∈src (ghbi-fre fre[xy]) = obi-obs (obs-fre (fre[⇒] x∈src y∈src fre[xy]))


-- # Result

src-consistent : IsTCGConsistent src
src-consistent =
  record
    { ax-coherence  = src-ax-coherence
    ; ax-atomicity  = src-ax-atomicity
    ; ax-global-ord = src-ax-global-ord
    }
