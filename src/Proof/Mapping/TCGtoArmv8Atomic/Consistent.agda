{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.Armv8 using (LabelArmv8)
open import Arch.TCG using (LabelTCG)
open import MapTCGtoArmv8Atomic using (Armv8-TCGRestricted)


module Proof.Mapping.TCGtoArmv8Atomic.Consistent
  (dst : Execution LabelArmv8) (dst-wf : WellFormed dst) (dst-ok : Armv8-TCGRestricted dst) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_])
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.TCG as TCG
open import Arch.TCG.Detour
open import Arch.Armv8 as Armv8
open import Helpers

open import MapTCGtoArmv8Atomic
open import Proof.Mapping.TCGtoArmv8Atomic.Execution dst dst-wf dst-ok as PE

import Proof.Framework LabelTCG dst dst-wf as Ψ
import Proof.Mapping.Framework LabelTCG dst dst-wf as Δ

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
  let x∈src = ⁺-lift-predˡ (cohˡ∈ex src-wf) coh[xx]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ (cohˡ∈ex src-wf) coh[⇒] x∈src x∈src coh[xx])
  where
  coh[⇒] : Rel[⇒] (Coh src) (po-loc dst ∪₂ Ca dst ∪₂ rf dst)
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


-- ## Proof

src-ax-global-ord : Irreflexive _≡_ (ghb src)
src-ax-global-ord refl ghb[xx] =
  let ghbd[xx] = proj₂ (detour src-wf ghb[xx])
      x∈src = ⁺-lift-predˡ (GhbiAltˡ∈ex src-wf) ghbd[xx]
  in ax-global-obs dst-consistent refl (⁺[⇒]ˡ (GhbiAltˡ∈ex src-wf) ghbi[⇒]obi x∈src x∈src ghbd[xx])
  where
  ord[⇒]obi : ∀ {x y : Event LabelTCG} → (x∈src : x ∈ events src) → (y∈src : y ∈ events src)
    → OrdAlt src x y → Obi dst-a8 (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
  ord[⇒]obi x∈src y∈src (ord-init ((refl , x-init) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
    obi-lob ([ lobi-init ((refl , Init[⇒] x∈src x-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy]) ])
  -- RR
  ord[⇒]obi x∈src y∈src (ord-rr ((refl , x-r) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-fld ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Frr[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy]))] )
  -- RW
  ord[⇒]obi x∈src y∈src (ord-rw ((refl , x-r) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-fld ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Frw[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy]))] )
  -- RM
  ord[⇒]obi x∈src y∈src (ord-rm ((refl , x-r) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-fld ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Frm[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy]))] )
  -- WR
  ord[⇒]obi x∈src y∈src (ord-wr ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fwr[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  -- WW
  ord[⇒]obi x∈src y∈src (ord-ww ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-fst ((refl , W[⇒] x∈src x-w) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fww[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy] ⨾[ _ ]⨾ (refl , W[⇒] y∈src y-w))) ])
  -- WM
  ord[⇒]obi x∈src y∈src (ord-wm ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fwm[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  -- MR
  ord[⇒]obi x∈src y∈src (ord-mr ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fmr[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  -- MW
  ord[⇒]obi x∈src y∈src (ord-mw ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fmw[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  -- MM
  ord[⇒]obi x∈src y∈src (ord-mm ((refl , x-w) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fmm[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  ord[⇒]obi x∈src y∈src (ord-sc ((refl , x-rw) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , ev-f₌) ⨾[ z ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈src po[xz]
    in obi-lob ([ lobi-bob (bob-f (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , Fsc[⇒] z∈src ev-f₌) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ])
  ord[⇒]obi x∈src y∈src (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ@(z , rmw[yz])))) =
    let z∈src = rmwʳ∈src rmw[yz]
    in obi-lob [ lobi-bob (bob-amoˡ (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , ev[⇒] z∈src , rmw[⇒]amo-al y∈src z∈src rmw[yz]))) ]
  ord[⇒]obi x∈src y∈src (ord-rmw-codom ((refl , x∈rmwʳ@(z , rmw[zx])) ⨾[ x ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    let z∈src = rmwˡ∈src rmw[zx]
    in obi-lob [ lobi-bob (bob-amoʳ ((refl , ev[⇒] z∈src , rmw[⇒]amo-al z∈src x∈src rmw[zx]) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])) ]
  ord[⇒]obi x∈src y∈src (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-wₜ))) =
    obi-lob [ lobi-bob (bob-rel (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , Wₜ[⇒]L y∈src y-wₜ))) ]
  ord[⇒]obi {x} x∈src y∈src (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    obi-lob [ lobi-bob (bob-acq ((refl , inj₁ (Rₜ[⇒]A x∈src x-rₜ)) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])) ]
    
  ghbi[⇒]obi : ∀ {x y : Event LabelTCG} → (x∈src : x ∈ events src) → (y∈src : y ∈ events src) → GhbiAlt src x y → Obi dst-a8 (ev[⇒] x∈src) (ev[⇒] y∈src)
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
