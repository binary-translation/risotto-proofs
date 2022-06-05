{-# OPTIONS --safe #-}

-- | A detour is an alternative path through an execution, which satisfies different desired properties.
-- This module defines a detour for TCG's ghb-relation. The detour guarantees that individual relations
-- within the cycle only go through R/W events; Whereas the original path could go between fences as well.
module Arch.TCG.Detour where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _++_; _∷ʳ_)
-- Local library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Relations
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.TCG as TCG


open Execution
open WellFormed
open IsTCGConsistent


--
-- This module contains the following public components:
-- * OrdAlt - alternative definition of `Ord`
-- * GhbiAlt - alternative definition of `Ghbi`
-- * GhbiAlt⁺⇒Ghbi⁺ - converts back to the original ghb definition
-- * detour - converts from a `Ghbi` cycle to a `GhbiAlt` cycle
--

-- | This is an alternative definition of `Ord` (in `Arch.TCG`).
--
-- The following changes are included:
-- * The `SC` fence rules (`po;SC` and `SC;po`) are combined into a single rule
--   (`po;SC;po`)
-- * All edges are guaranteed to go between two R/W events
-- * All ACQ / REL fences are removed (they do nothing anyway)
data OrdAlt (ex : Execution LabelTCG) (x y : Event LabelTCG) : Set where
  ord-init      : ( ⦗ EvInit ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ )                     x y → OrdAlt ex x y
  
  ord-rr        : ( ⦗ EvR ⦘  ⨾ po ex ⨾ ⦗ EvF₌ RR ⦘ ⨾ po ex ⨾ ⦗ EvR ⦘ )  x y → OrdAlt ex x y
  ord-rw        : ( ⦗ EvR ⦘  ⨾ po ex ⨾ ⦗ EvF₌ RW ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ )  x y → OrdAlt ex x y
  ord-rm        : ( ⦗ EvR ⦘  ⨾ po ex ⨾ ⦗ EvF₌ RM ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y
  
  ord-wr        : ( ⦗ EvW ⦘  ⨾ po ex ⨾ ⦗ EvF₌ WR ⦘ ⨾ po ex ⨾ ⦗ EvR ⦘ )  x y → OrdAlt ex x y
  ord-ww        : ( ⦗ EvW ⦘  ⨾ po ex ⨾ ⦗ EvF₌ WW ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ )  x y → OrdAlt ex x y
  ord-wm        : ( ⦗ EvW ⦘  ⨾ po ex ⨾ ⦗ EvF₌ WM ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y
  
  ord-mr        : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ MR ⦘ ⨾ po ex ⨾ ⦗ EvR ⦘ )  x y → OrdAlt ex x y
  ord-mw        : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ MW ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ )  x y → OrdAlt ex x y
  ord-mm        : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ MM ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y
  
  ord-sc        : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ SC ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y

  ord-rmw-dom   : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ dom (rmw ex) ⦘ )   x y → OrdAlt ex x y
  ord-rmw-codom : ( ⦗ codom (rmw ex) ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y

  ord-w         : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvWₜ trmw ⦘ ) x y → OrdAlt ex x y
  ord-r         : ( ⦗ EvRₜ trmw ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y


data GhbiAlt (ex : Execution LabelTCG) (x y : Event LabelTCG) : Set where
  ghbi-ord : OrdAlt ex x y → GhbiAlt ex x y
  ghbi-rfe : rfe ex x y    → GhbiAlt ex x y
  ghbi-coe : coe ex x y    → GhbiAlt ex x y
  ghbi-fre : fre ex x y    → GhbiAlt ex x y


private
  -- | Rotate the cycle such that it starts at a R/W event.
  --
  -- Note that every `ghb` cycle contains at least one R/W event, as every cycle passes through
  -- multiple threads. The only way to switch threads is through either of rfe, coe, or fre.
  -- Those relations all relate R/W events.
  rotate : ∀ {ex : Execution LabelTCG}
    → WellFormed ex
    → {x : Event LabelTCG}
    → TransClosure ( Ghbi ex ) x x
    → ∃[ y ] TransClosure ( Ghbi ex ) y y × EvRW y
  rotate {ex} wf {x} [ ghbi[xx] ] = ⊥-elim (ghbi-irreflexive wf refl ghbi[xx])
  rotate {ex} wf {x} ghbi⁺[xx]@(ghbi-rfe rfe[xy] ∷ ghbi⁺[yx]) = x , ghbi⁺[xx] , w⇒rw (×₂-applyˡ (rfe-w×r wf) rfe[xy])
  rotate {ex} wf {x} ghbi⁺[xx]@(ghbi-coe coe[xy] ∷ ghbi⁺[yx]) = x , ghbi⁺[xx] , w⇒rw (×₂-applyˡ (coe-w×w wf) coe[xy])
  rotate {ex} wf {x} ghbi⁺[xx]@(ghbi-fre fre[xy] ∷ ghbi⁺[yx]) = x , ghbi⁺[xx] , r⇒rw (×₂-applyˡ (fre-r×w wf) fre[xy])
  rotate {ex} wf {x} (ghbi-ord ord[xy] ∷ ghbi⁺[yx]) = step [ ord[xy] ] ghbi⁺[yx]
    where
    step : {x y : Event LabelTCG}
      → TransClosure (Ord ex) x y → TransClosure (Ghbi ex) y x → ∃[ z ] TransClosure (Ghbi ex) z z × EvRW z
    step ord⁺[xy] [ ghbi-ord ord[yx] ] =
      let po[xx] = ord⁺⇒po wf (ord⁺[xy] ∷ʳ ord[yx])
      in ⊥-elim (po-irreflexive wf refl po[xx])
    step {x} {y} ord⁺[xy] [ ghbi-rfe rfe[yx]@(rf[yx] , _) ] =
      x , ⁺-map _ ghbi-ord ord⁺[xy] ++ [ ghbi-rfe rfe[yx] ] , r⇒rw (×₂-applyʳ (rf-w×r wf) rf[yx])
    step {x} {y} ord⁺[xy] [ ghbi-coe coe[yx]@(co[yx] , _) ] = 
      x , ⁺-map _ ghbi-ord ord⁺[xy] ++ [ ghbi-coe coe[yx] ] , w⇒rw (×₂-applyʳ (co-w×w wf) co[yx])
    step {x} {y} ord⁺[xy] [ ghbi-fre fre[yx]@(fr[yx] , _) ] = 
      x , ⁺-map _ ghbi-ord ord⁺[xy] ++ [ ghbi-fre fre[yx] ] , w⇒rw (×₂-applyʳ (fr-r×w wf) fr[yx])
    step ord⁺[xy] (ghbi-ord ord[yw] ∷ ghbi⁺[wx]) =
      step (ord⁺[xy] ∷ʳ ord[yw]) ghbi⁺[wx]
    step {x} {y} ord⁺[xy] (ghbi-rfe rfe[yw]@(rf[yw] , _) ∷ ghbi⁺[wx]) =
      y , (ghbi-rfe rfe[yw] ∷ ghbi⁺[wx] ++ (⁺-map (λ z → z) ghbi-ord ord⁺[xy])) , w⇒rw (×₂-applyˡ (rf-w×r wf) rf[yw])
    step {x} {y} ord⁺[xy] (ghbi-coe coe[yw]@(co[yw] , _) ∷ ghbi⁺[wx]) =
      y , (ghbi-coe coe[yw] ∷ ghbi⁺[wx] ++ (⁺-map (λ z → z) ghbi-ord ord⁺[xy])) , w⇒rw (×₂-applyˡ (co-w×w wf) co[yw])
    step {x} {y} ord⁺[xy] (ghbi-fre fre[yw]@(fr[yw] , _) ∷ ghbi⁺[wx]) =
      y , (ghbi-fre fre[yw] ∷ ghbi⁺[wx] ++ (⁺-map (λ z → z) ghbi-ord ord⁺[xy])) , r⇒rw (×₂-applyˡ (fr-r×w wf) fr[yw])

  -- Internal helper. Subsequent `Ord` elements are chained together, such that both ends
  -- of the chain contains R/W events
  --
  -- `ord⁺⇒alt` (below) traverses the fields of the `chain-ord` constructor to produce
  -- a sequence of `OrdAlt` elements.
  data Chain (ex : Execution LabelTCG) (x y : Event LabelTCG) : Set where
    chain-ord : EvRW x → EvRW y → TransClosure (Ord ex) x y → Chain ex x y
    chain-rfe : rfe ex x y → Chain ex x y
    chain-coe : coe ex x y → Chain ex x y
    chain-fre : fre ex x y → Chain ex x y

  to-chain : ∀ {ex : Execution LabelTCG}
    → (wf : WellFormed ex)
    → {x y : Event LabelTCG}
    → EvRW x
    → EvRW y
    → TransClosure ( Ghbi ex ) x y
    → TransClosure ( Chain ex ) x y
  to-chain wf {x} {y} x-rw y-rw [ ghbi-ord ord[xy] ] = [ chain-ord x-rw y-rw [ ord[xy] ] ]
  to-chain wf {x} {y} x-rw y-rw [ ghbi-rfe rfe[xy] ] = [ chain-rfe rfe[xy] ]
  to-chain wf {x} {y} x-rw y-rw [ ghbi-coe coe[xy] ] = [ chain-coe coe[xy] ]
  to-chain wf {x} {y} x-rw y-rw [ ghbi-fre fre[xy] ] = [ chain-fre fre[xy] ]
  to-chain wf {x} {y} x-rw y-rw (ghbi-rfe rfe[xz] ∷ ghbi⁺[zy]) = chain-rfe rfe[xz] ∷ to-chain wf (r⇒rw (×₂-applyʳ (rfe-w×r wf) rfe[xz])) y-rw ghbi⁺[zy]
  to-chain wf {x} {y} x-rw y-rw (ghbi-coe coe[xz] ∷ ghbi⁺[zy]) = chain-coe coe[xz] ∷ to-chain wf (w⇒rw (×₂-applyʳ (coe-w×w wf) coe[xz])) y-rw ghbi⁺[zy]
  to-chain wf {x} {y} x-rw y-rw (ghbi-fre fre[xz] ∷ ghbi⁺[zy]) = chain-fre fre[xz] ∷ to-chain wf (w⇒rw (×₂-applyʳ (fre-r×w wf) fre[xz])) y-rw ghbi⁺[zy]
  to-chain {ex} wf {x} {y} x-rw y-rw (ghbi-ord ord[xz] ∷ ghbi⁺[zy]) = step [ ord[xz] ] ghbi⁺[zy]
    where
    -- | `ord⁺[xz]` is the accumulator. `step` performs structural recursion on the second (explicit) argument.
    step : {z : Event LabelTCG} → TransClosure (Ord ex) x z → TransClosure (Ghbi ex) z y → TransClosure (Chain ex) x y
    step ord⁺[xz] [ ghbi-ord ord[zy] ] = [ chain-ord x-rw y-rw ( ord⁺[xz] ∷ʳ ord[zy] ) ]
    step ord⁺[xz] [ ghbi-rfe rfe[zy] ] = chain-ord x-rw (w⇒rw (×₂-applyˡ (rfe-w×r wf) rfe[zy])) ord⁺[xz] ∷ [ chain-rfe rfe[zy] ]
    step ord⁺[xz] [ ghbi-coe coe[zy] ] = chain-ord x-rw (w⇒rw (×₂-applyˡ (coe-w×w wf) coe[zy])) ord⁺[xz] ∷ [ chain-coe coe[zy] ]
    step ord⁺[xz] [ ghbi-fre fre[zy] ] = chain-ord x-rw (r⇒rw (×₂-applyˡ (fre-r×w wf) fre[zy])) ord⁺[xz] ∷ [ chain-fre fre[zy] ]
    step ord⁺[xz] (ghbi-ord ord[zq] ∷ ghbi⁺[qy]) = step (ord⁺[xz] ∷ʳ ord[zq]) ghbi⁺[qy]
    step ord⁺[xz] (ghbi-rfe rfe[zq] ∷ ghbi⁺[qy]) =
      let (z-w , q-r) = ⊆₂-apply (rfe-w×r wf) rfe[zq]
      in chain-ord x-rw (w⇒rw z-w) ord⁺[xz] ∷ chain-rfe rfe[zq] ∷ to-chain wf (r⇒rw q-r) y-rw ghbi⁺[qy]
    step ord⁺[xz] (ghbi-coe coe[zq] ∷ ghbi⁺[qy]) =
      let (z-w , q-w) = ⊆₂-apply (coe-w×w wf) coe[zq]
      in chain-ord x-rw (w⇒rw z-w) ord⁺[xz] ∷ chain-coe coe[zq] ∷ to-chain wf (w⇒rw q-w) y-rw ghbi⁺[qy]
    step ord⁺[xz] (ghbi-fre fre[zq] ∷ ghbi⁺[qy]) =
      let (z-r , q-w) = ⊆₂-apply (fre-r×w wf) fre[zq]
      in chain-ord x-rw (r⇒rw z-r) ord⁺[xz] ∷ chain-fre fre[zq] ∷ to-chain wf (w⇒rw q-w) y-rw ghbi⁺[qy]

  ord⁺⇒alt : ∀ {ex : Execution LabelTCG}
    → (wf : WellFormed ex)
    → {x y : Event LabelTCG}
    → EvRW x
    → EvRW y
    → TransClosure (Ord ex) x y
    → TransClosure (OrdAlt ex) x y
  ord⁺⇒alt wf x-rw y-rw [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy]) ] =
    [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw [ ord-rr rr[xy] ] = [ ord-rr rr[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-rw rw[xy] ] = [ ord-rw rw[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-rm rm[xy] ] = [ ord-rm rm[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-wr wr[xy] ] = [ ord-wr wr[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-ww ww[xy] ] = [ ord-ww ww[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-wm wm[xy] ] = [ ord-wm wm[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-mr mr[xy] ] = [ ord-mr mr[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-mw mw[xy] ] = [ ord-mw mw[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-mm mm[xy] ] = [ ord-mm mm[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-rmw-dom (po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ] =
    [ ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ]
  ord⁺⇒alt wf x-rw y-rw [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy]) ] =
    [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw [ ord-w (po[xz] ⨾[ z ]⨾ (refl , z-wₜ)) ] =
    [ ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-wₜ)) ]
  ord⁺⇒alt wf x-rw y-rw [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy]) ] =
    [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw (ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po wf ord⁺[zy]
        po[xy] = po-trans wf po[xz] po[zy]
    in [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-ww ww[xz] ∷ ord⁺[zy]) =
    ord-ww ww[xz] ∷ ord⁺⇒alt wf (w⇒rw (ord-predʳ ex ww[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-rm rm[xz] ∷ ord⁺[zy]) =
    ord-rm rm[xz] ∷ ord⁺⇒alt wf (ord-predʳ ex rm[xz]) y-rw ord⁺[zy]
  ord⁺⇒alt wf x-rw y-rw (ord-sc₁ (po[xz] ⨾[ _ ]⨾ (refl , z-sc)) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po wf ord⁺[zy]
    in [ ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw (ord-rmw-dom (po[xz] ⨾[ _ ]⨾ (refl , z∈rmwˡ)) ∷ ord⁺[zy]) =
    ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z∈rmwˡ)) ∷ ord⁺⇒alt wf (rₜ⇒rw (rmwˡ-r wf z∈rmwˡ)) y-rw ord⁺[zy]
  ord⁺⇒alt wf x-rw y-rw (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po wf ord⁺[zy]
        po[xy] = po-trans wf po[xz] po[zy]
    in [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw (ord-w (po[xz] ⨾[ _ ]⨾ (refl , z-w)) ∷ ord⁺[zy]) =
    ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-w)) ∷ ord⁺⇒alt wf (wₜ⇒rw z-w) y-rw ord⁺[zy]
  ord⁺⇒alt wf x-rw y-rw (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po wf ord⁺[zy]
        po[xy] = po-trans wf po[xz] po[zy]
    in [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw [ ord-acq ((refl , ev-f₌) ⨾[ _ ]⨾ po[xy]) ] = ⊥-elim (disjoint-f/rw _ (f₌⇒f ev-f₌ , x-rw))
  ord⁺⇒alt wf x-rw y-rw [ ord-rel (po[xy] ⨾[ _ ]⨾ (refl , ev-f₌)) ] = ⊥-elim (disjoint-f/rw _ (f₌⇒f ev-f₌ , y-rw))
  -- Impossible cases
  ord⁺⇒alt wf x-rw y-rw [ ord-sc₁ (po[xy] ⨾[ _ ]⨾ (refl , y-sc)) ] = ⊥-elim (disjoint-f/rw _ (f₌⇒f y-sc , y-rw))
  ord⁺⇒alt wf x-rw y-rw [ ord-sc₂ ((refl , x-sc) ⨾[ _ ]⨾ po[xy]) ] = ⊥-elim (disjoint-f/rw _ (f₌⇒f x-sc , x-rw))
  ord⁺⇒alt wf x-rw y-rw (ord-sc₂ ((refl , x-sc) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) = ⊥-elim (disjoint-f/rw _ (f₌⇒f x-sc , x-rw))
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-rr rr[xz] ∷ ord⁺[zy]) = ord-rr rr[xz] ∷ ord⁺⇒alt wf (r⇒rw (ord-predʳ ex rr[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-rw rw[xz] ∷ ord⁺[zy]) = ord-rw rw[xz] ∷ ord⁺⇒alt wf (w⇒rw (ord-predʳ ex rw[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-wr wr[xz] ∷ ord⁺[zy]) = ord-wr wr[xz] ∷ ord⁺⇒alt wf (r⇒rw (ord-predʳ ex wr[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-wm wm[xz] ∷ ord⁺[zy]) = ord-wm wm[xz] ∷ ord⁺⇒alt wf (ord-predʳ ex wm[xz]) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-mr mr[xz] ∷ ord⁺[zy]) = ord-mr mr[xz] ∷ ord⁺⇒alt wf (r⇒rw (ord-predʳ ex mr[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-mw mw[xz] ∷ ord⁺[zy]) = ord-mw mw[xz] ∷ ord⁺⇒alt wf (w⇒rw (ord-predʳ ex mw[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-mm mm[xz] ∷ ord⁺[zy]) = ord-mm mm[xz] ∷ ord⁺⇒alt wf (ord-predʳ ex mm[xz]) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-acq ((refl , ev-f₌) ⨾[ _ ]⨾ po[xy]) ∷ ord⁺[zy]) = ⊥-elim (disjoint-f/rw _ (f₌⇒f ev-f₌ , x-rw))
  ord⁺⇒alt {ex} wf {x} {y} x-rw y-rw (ord-rel (po[xz] ⨾[ _ ]⨾ (refl , ev-f₌)) ∷ ord⁺[zy]) = lemma po[xz] ev-f₌ ord⁺[zy]
    where
    -- Drop the REL fence
    lemma : ∀ {z : Event LabelTCG}
      → po ex x z
      → EvF₌ F-mode.REL z
      → TransClosure (Ord ex) z y
        ----------------------------
      → TransClosure (OrdAlt ex) x y
    -- the REL fence is not needed, as the RMW-domain orders `x` with `y`
    lemma po[xz] ev-f₌ [ ord-rmw-dom (po[zy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ] =
      [ ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po-trans wf po[xz] po[zy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ]
    -- the REL fence is not needed, as the RMW-write orders `x` with `y`
    lemma po[xz] ev-f₌ [ ord-w (po[zy] ⨾[ _ ]⨾ (refl , y-wₜ)) ] =
      [ ord-w ((refl , x-rw) ⨾[ _ ]⨾ po-trans wf po[xz] po[zy] ⨾[ _ ]⨾ (refl , y-wₜ)) ]
    -- Another REL fence. "Merge" them and drop them together
    lemma po[xz] ev-f₌ (ord-rel (po[zk] ⨾[ y ]⨾ (refl , ev-f₌)) ∷ ord⁺[ky]) =
      lemma (po-trans wf po[xz] po[zk]) ev-f₌ ord⁺[ky]
    -- the REL fence is not needed, as the SC fence orders `x` with `y`
    lemma po[xz] ev-f₌ (ord-sc₁ (po[zk] ⨾[ _ ]⨾ (refl , ev-f₌)) ∷ ord⁺[ky]) =
      [ ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po-trans wf po[xz] po[zk] ⨾[ _ ]⨾ (refl , ev-f₌) ⨾[ _ ]⨾ ord⁺⇒po wf ord⁺[ky] ⨾[ _ ]⨾ (refl , y-rw)) ]
    -- the REL fence is not needed, as the RMW-domain orders `x` with `y`
    lemma po[xz] ev-f₌ (ord-rmw-dom (po[zk] ⨾[ _ ]⨾ (refl , k∈rmwˡ)) ∷ ord⁺[ky]) =
      let k-rw = rₜ⇒rw (rmwˡ-r wf k∈rmwˡ)
      in ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po-trans wf po[xz] po[zk] ⨾[ _ ]⨾ (refl , k∈rmwˡ)) ∷ ord⁺⇒alt wf k-rw y-rw ord⁺[ky]
    -- the REL fence is not needed, as the RMW-write orders `x` with `y`
    lemma po[xz] ev-f₌ (ord-w (po[zk] ⨾[ _ ]⨾ (refl , k-wₜ)) ∷ ord⁺[ky]) =
      ord-w ((refl , x-rw) ⨾[ _ ]⨾ po-trans wf po[xz] po[zk] ⨾[ _ ]⨾ (refl , k-wₜ)) ∷ ord⁺⇒alt wf (wₜ⇒rw k-wₜ) y-rw ord⁺[ky]
    -- impossible cases
    lemma po[xz] ev-f₌ [ ord-init ((refl , z-init) ⨾[ _ ]⨾ po[zy]) ] = ⊥-elim (disjoint-f/init _ (ev-f is-f , z-init))
    lemma po[xz] ev-f₌ [ ord-rr rr[zy] ] = ⊥-elim (disjoint-f/r _ (ev-f is-f , ord-predˡ ex rr[zy]))
    lemma po[xz] ev-f₌ [ ord-rw rw[zy] ] = ⊥-elim (disjoint-f/r _ (ev-f is-f , ord-predˡ ex rw[zy]))
    lemma po[xz] ev-f₌ [ ord-rm rm[zy] ] = ⊥-elim (disjoint-f/r _ (ev-f is-f , ord-predˡ ex rm[zy]))
    lemma po[xz] ev-f₌ [ ord-wr wr[zy] ] = ⊥-elim (disjoint-f/w _ (ev-f is-f , ord-predˡ ex wr[zy]))
    lemma po[xz] ev-f₌ [ ord-ww ww[zy] ] = ⊥-elim (disjoint-f/w _ (ev-f is-f , ord-predˡ ex ww[zy]))
    lemma po[xz] ev-f₌ [ ord-wm wm[zy] ] = ⊥-elim (disjoint-f/w _ (ev-f is-f , ord-predˡ ex wm[zy]))
    lemma po[xz] ev-f₌ [ ord-mr mr[zy] ] = ⊥-elim (disjoint-f/rw _ (ev-f is-f , ord-predˡ ex mr[zy]))
    lemma po[xz] ev-f₌ [ ord-mw mw[zy] ] = ⊥-elim (disjoint-f/rw _ (ev-f is-f , ord-predˡ ex mw[zy]))
    lemma po[xz] ev-f₌ [ ord-mm mm[zy] ] = ⊥-elim (disjoint-f/rw _ (ev-f is-f , ord-predˡ ex mm[zy]))
    lemma po[xz] ev-f₌ [ ord-acq ((refl , ()) ⨾[ z ]⨾ po[zy]) ]
    lemma po[xz] ev-f₌ [ ord-rel (po[zy] ⨾[ y ]⨾ (refl , ev-f₌)) ] = ⊥-elim (disjoint-f/rw _ (ev-f is-f , y-rw))
    lemma po[xz] ev-f₌ [ ord-sc₁ (po[zy] ⨾[ y ]⨾ (refl , ev-f₌)) ] = ⊥-elim (disjoint-f/rw _ (ev-f is-f , y-rw))
    lemma po[xz] ev-f₌ [ ord-sc₂ ((refl , ()) ⨾[ _ ]⨾ po[zy]) ]
    lemma po[xz] ev-f₌ [ ord-rmw-codom ((refl , z∈rmwʳ) ⨾[ _ ]⨾ po[zy]) ] = ⊥-elim (disjoint-f/w _ (ev-f is-f , wₜ⇒w (rmwʳ-w wf z∈rmwʳ)))
    lemma po[xz] ev-f₌ [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy]) ] = ⊥-elim (disjoint-f/r _ (ev-f is-f , rₜ⇒r x-rₜ))
    lemma po[xz] ev-f₌ (ord-init ((refl , z-init) ⨾[ _ ]⨾ po[zk]) ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/init _ (ev-f is-f , z-init))
    lemma po[xz] ev-f₌ (ord-rr rr[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/r _ (ev-f is-f , ord-predˡ ex rr[zk]))
    lemma po[xz] ev-f₌ (ord-rw rw[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/r _ (ev-f is-f , ord-predˡ ex rw[zk]))
    lemma po[xz] ev-f₌ (ord-rm rm[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/r _ (ev-f is-f , ord-predˡ ex rm[zk]))
    lemma po[xz] ev-f₌ (ord-wr wr[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/w _ (ev-f is-f , ord-predˡ ex wr[zk]))
    lemma po[xz] ev-f₌ (ord-ww ww[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/w _ (ev-f is-f , ord-predˡ ex ww[zk]))
    lemma po[xz] ev-f₌ (ord-wm wm[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/w _ (ev-f is-f , ord-predˡ ex wm[zk]))
    lemma po[xz] ev-f₌ (ord-mr mr[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/rw _ (ev-f is-f , ord-predˡ ex mr[zk]))
    lemma po[xz] ev-f₌ (ord-mw mw[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/rw _ (ev-f is-f , ord-predˡ ex mw[zk]))
    lemma po[xz] ev-f₌ (ord-mm mm[zk] ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/rw _ (ev-f is-f , ord-predˡ ex mm[zk]))
    lemma po[xz] ev-f₌ (ord-acq ((refl , ()) ⨾[ z ]⨾ po[zk]) ∷ ord⁺[ky])
    lemma po[xz] ev-f₌ (ord-sc₂ ((refl , ()) ⨾[ _ ]⨾ po[zy]) ∷ ord⁺[ky])
    lemma po[xz] ev-f₌ (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[zk]) ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/w _ (ev-f is-f , wₜ⇒w (rmwʳ-w wf x∈rmwʳ)))
    lemma po[xz] ev-f₌ (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy]) ∷ ord⁺[ky]) = ⊥-elim (disjoint-f/r _ (ev-f is-f , rₜ⇒r x-rₜ))
    
  chain⇒alt⁺ : ∀ {ex : Execution LabelTCG} → WellFormed ex → {x y : Event LabelTCG} → Chain ex x y → TransClosure (GhbiAlt ex) x y
  chain⇒alt⁺ wf (chain-ord x-rw y-rw ord⁺[xy]) = ⁺-map _ ghbi-ord (ord⁺⇒alt wf x-rw y-rw ord⁺[xy])
  chain⇒alt⁺ wf (chain-rfe rfe[xy]) = [ ghbi-rfe rfe[xy] ]
  chain⇒alt⁺ wf (chain-coe coe[xy]) = [ ghbi-coe coe[xy] ]
  chain⇒alt⁺ wf (chain-fre fre[xy]) = [ ghbi-fre fre[xy] ]

  chain⁺⇒alt⁺ : ∀ {ex : Execution LabelTCG} → WellFormed ex → {x y : Event LabelTCG}
    → TransClosure (Chain ex) x y → TransClosure (GhbiAlt ex) x y
  chain⁺⇒alt⁺ wf = ⇔₂-apply-⊇₂ ⁺-idem ∘ ⁺-map _ (chain⇒alt⁺ wf)


-- | Converts a `Ghbi` /cycle/ into an alternative `GhbiAlt` cycle, which
-- contains only relations that go between read/write events.
--
-- Note that every ghbi-cycle goes between multiple threads. Moving to another thread
-- always goes through rfe/coe/fre; which are all between read/write events.
detour : ∀ {ex : Execution LabelTCG} (wf : WellFormed ex) → {x : Event LabelTCG}
  → TransClosure ( Ghbi ex ) x x
  → ∃[ y ] TransClosure ( GhbiAlt ex ) y y
detour {ex} wf {x} ghbi⁺[xx] = 
  let (y , ghbi⁺[yy] , y-rw) = rotate wf ghbi⁺[xx]
      chain⁺[yy] = to-chain wf y-rw y-rw ghbi⁺[yy]
  in y , chain⁺⇒alt⁺ wf chain⁺[yy]


OrdAlt⇒Ord⁺ : {ex : Execution LabelTCG} {x y : Event LabelTCG}
  → OrdAlt ex x y
    -------------------------
  → TransClosure (Ord ex) x y
OrdAlt⇒Ord⁺ (ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
  [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy]) ]
OrdAlt⇒Ord⁺ (ord-rr rr[xy]) = [ ord-rr rr[xy] ]
OrdAlt⇒Ord⁺ (ord-rw rw[xy]) = [ ord-rw rw[xy] ]
OrdAlt⇒Ord⁺ (ord-rm rm[xy]) = [ ord-rm rm[xy] ]
OrdAlt⇒Ord⁺ (ord-wr wr[xy]) = [ ord-wr wr[xy] ]
OrdAlt⇒Ord⁺ (ord-ww ww[xy]) = [ ord-ww ww[xy] ]
OrdAlt⇒Ord⁺ (ord-wm wm[xy]) = [ ord-wm wm[xy] ]
OrdAlt⇒Ord⁺ (ord-mr mr[xy]) = [ ord-mr mr[xy] ]
OrdAlt⇒Ord⁺ (ord-mw mw[xy]) = [ ord-mw mw[xy] ]
OrdAlt⇒Ord⁺ (ord-mm mm[xy]) = [ ord-mm mm[xy] ]
OrdAlt⇒Ord⁺ (ord-sc ((refl , x-rw) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
  ord-sc₁ (po[xz] ⨾[ z ]⨾ (refl , z-sc)) ∷ [ ord-sc₂ ((refl , z-sc) ⨾[ z ]⨾ po[zy]) ]
OrdAlt⇒Ord⁺ (ord-rmw-dom ((refl , x-rw) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y∈rmwˡ))) =
  [ ord-rmw-dom (po[xy] ⨾[ y ]⨾ (refl , y∈rmwˡ)) ]
OrdAlt⇒Ord⁺ (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
  [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xy]) ]
OrdAlt⇒Ord⁺ (ord-w ((refl , x-rw) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-r))) =
  [ ord-w (po[xy] ⨾[ y ]⨾ (refl , y-r)) ]
OrdAlt⇒Ord⁺ (ord-r ((refl , x-r) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
  [ ord-r ((refl , x-r) ⨾[ x ]⨾ po[xy]) ]

-- | Converts an alternative path to an original path
GhbiAlt⁺⇒Ghbi⁺ : ∀ {ex : Execution LabelTCG}
  → {x y : Event LabelTCG}
  → TransClosure (GhbiAlt ex) x y
  → TransClosure (Ghbi ex) x y
GhbiAlt⁺⇒Ghbi⁺ {ex} ghbi-alt⁺[xy] =
  ⁺-join (⁺-map _ step ghbi-alt⁺[xy])
  where
  step : ∀ {x y : Event LabelTCG} → GhbiAlt ex x y → TransClosure (Ghbi ex) x y
  step (ghbi-ord ord[xy]) = ⁺-map _ ghbi-ord (OrdAlt⇒Ord⁺ ord[xy])
  step (ghbi-rfe rfe[xy]) = [ ghbi-rfe rfe[xy] ]
  step (ghbi-coe coe[xy]) = [ ghbi-coe coe[xy] ]
  step (ghbi-fre fre[xy]) = [ ghbi-fre fre[xy] ]

OrdAlt⇒po : ∀ {ex : Execution LabelTCG}
  → WellFormed ex
  → {x y : Event LabelTCG}
  → OrdAlt ex x y
    -------------
  → po ex x y
OrdAlt⇒po wf ord[xy] =
  let po⁺[xy] = ⁺-map (λ τ → τ) (ord⇒po wf) (OrdAlt⇒Ord⁺ ord[xy])
  in ⁺-join-trans (po-trans wf) po⁺[xy]

OrdAlt-irreflexive : ∀ {ex : Execution LabelTCG} → WellFormed ex → Irreflexive _≡_ (OrdAlt ex)
OrdAlt-irreflexive wf refl = po-irreflexive wf refl ∘ OrdAlt⇒po wf

GhbiAlt-irreflexive : ∀ {ex : Execution LabelTCG} → WellFormed ex → Irreflexive _≡_ (GhbiAlt ex)
GhbiAlt-irreflexive wf refl (ghbi-ord ord[xx]) = OrdAlt-irreflexive wf refl ord[xx]
GhbiAlt-irreflexive wf refl (ghbi-rfe rfe[xx]) = rf-irreflexive wf refl (proj₁ rfe[xx])
GhbiAlt-irreflexive wf refl (ghbi-coe coe[xx]) = co-irreflexive wf refl (proj₁ coe[xx])
GhbiAlt-irreflexive wf refl (ghbi-fre fre[xx]) = fr-irreflexive wf refl (proj₁ fre[xx])


-- # Helpers

OrdAltˡ∈ex : ∀ {ex : Execution LabelTCG}
  → WellFormed ex
  → {x y : Event LabelTCG}
  → OrdAlt ex x y
    ----------------------
  → x ∈ events ex
OrdAltˡ∈ex wf = ⁺-lift-predˡ (poˡ∈ex wf ∘ (ord⇒po wf)) ∘ OrdAlt⇒Ord⁺

GhbiAltˡ∈ex : ∀ {ex : Execution LabelTCG}
  → WellFormed ex
  → {x y : Event LabelTCG}
  → GhbiAlt ex x y
    ----------------------
  → x ∈ events ex
GhbiAltˡ∈ex wf (ghbi-ord ord[xy]) = OrdAltˡ∈ex wf ord[xy]
GhbiAltˡ∈ex wf (ghbi-rfe rfe[xy]) = rfˡ∈ex wf (proj₁ rfe[xy])
GhbiAltˡ∈ex wf (ghbi-coe coe[xy]) = coˡ∈ex wf (proj₁ coe[xy])
GhbiAltˡ∈ex wf (ghbi-fre fre[xy]) = frˡ∈ex wf (proj₁ fre[xy])


private
  ordfʳ+po :
      {ex : Execution LabelTCG}
    → WellFormed ex
    → {P₁ P₂ : Pred (Event LabelTCG) ℓzero}
    → {m : F-mode}
    → {x y z : Event LabelTCG}
    → ( ⦗ P₁ ⦘  ⨾ po ex ⨾ ⦗ EvF₌ m ⦘ ⨾ po ex ⨾ ⦗ P₂ ⦘ ) x y
    → po ex y z
    → P₂ z
      -----------------------------------------------------
    → ( ⦗ P₁ ⦘  ⨾ po ex ⨾ ⦗ EvF₌ m ⦘ ⨾ po ex ⨾ ⦗ P₂ ⦘ ) x z
  ordfʳ+po wf ((refl , x-p₁) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qy] ⨾[ _ ]⨾ (refl , y-p₂)) po[yz] z-p₂ =
    let po[qz] = po-trans wf po[qy] po[yz]
    in (refl , x-p₁) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qz] ⨾[ _ ]⨾ (refl , z-p₂)


ordʳ+wᵣ : {ex : Execution LabelTCG}
  → WellFormed ex
  → {x y z : Event LabelTCG}
  → OrdAlt ex x y
  → po ex y z
  → EvW y
  → EvW z
    ----------------------------
  → TransClosure (OrdAlt ex) x z
ordʳ+wᵣ wf (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) po[yz] y-w z-w =
  [ ord-init ((refl , x-init) ⨾[ _ ]⨾ po-trans wf po[xy] po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-rw rw[xy]) po[yz] y-w z-w = [ ord-rw (ordfʳ+po wf rw[xy] po[yz] z-w) ]
ordʳ+wᵣ wf (ord-rm rm[xy]) po[yz] y-w z-w = [ ord-rm (ordfʳ+po wf rm[xy] po[yz] (w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-ww ww[xy]) po[yz] y-w z-w = [ ord-ww (ordfʳ+po wf ww[xy] po[yz] z-w) ]
ordʳ+wᵣ wf (ord-wm wm[xy]) po[yz] y-w z-w = [ ord-wm (ordfʳ+po wf wm[xy] po[yz] (w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-mw mw[xy]) po[yz] y-w z-w = [ ord-mw (ordfʳ+po wf mw[xy] po[yz] z-w) ]
ordʳ+wᵣ wf (ord-mm mm[xy]) po[yz] y-w z-w = [ ord-mm (ordfʳ+po wf mm[xy] po[yz] (w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-sc sc[xy]) po[yz] y-w z-w = [ ord-sc (ordfʳ+po wf sc[xy] po[yz] (w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) po[yz] y-w z-w =
  [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po-trans wf po[xy] po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-w w[xy]@(_ ⨾[ _ ]⨾ _ ⨾[ _ ]⨾ (refl , y-wₐ))) po[yz] y-w z-w =
  let y∈ex = poˡ∈ex wf po[yz]
      y∈rmwʳ = ⇔₁-apply-⊇₁ (rmw-w wf) (y∈ex , y-wₐ)
  in ord-w w[xy] ∷ [ ord-rmw-codom ((refl , y∈rmwʳ) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) po[yz] y-w z-w =
  [ ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po-trans wf po[xy] po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
-- impossible cases
ordʳ+wᵣ {ex} wf (ord-rr rr[xy]) po[yz] y-w z-w = ⊥-elim (disjoint-r/w _ (ord-predʳ ex rr[xy] , y-w))
ordʳ+wᵣ {ex} wf (ord-wr wr[xy]) po[yz] y-w z-w = ⊥-elim (disjoint-r/w _ (ord-predʳ ex wr[xy] , y-w))
ordʳ+wᵣ {ex} wf (ord-mr mr[xy]) po[yz] y-w z-w = ⊥-elim (disjoint-r/w _ (ord-predʳ ex mr[xy] , y-w))
ordʳ+wᵣ wf (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ))) po[yz] y-w z-w =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r (rmwˡ-r wf y∈rmwˡ) , y-w))

private
  ordfˡ+po :
      {ex : Execution LabelTCG}
    → WellFormed ex
    → {P₁ P₂ : Pred (Event LabelTCG) ℓzero}
    → {m : F-mode}
    → {x y z : Event LabelTCG}
    → po ex x y
    → ( ⦗ P₁ ⦘  ⨾ po ex ⨾ ⦗ EvF₌ m ⦘ ⨾ po ex ⨾ ⦗ P₂ ⦘ ) y z
    → P₁ x
      -----------------------------------------------------
    → ( ⦗ P₁ ⦘  ⨾ po ex ⨾ ⦗ EvF₌ m ⦘ ⨾ po ex ⨾ ⦗ P₂ ⦘ ) x z
  ordfˡ+po wf po[xy] ((refl , y-p₁) ⨾[ _ ]⨾ po[yq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qz] ⨾[ _ ]⨾ (refl , y-p₂)) x-p₁ =
    let po[xq] = po-trans wf po[xy] po[yq]
    in (refl , x-p₁) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qz] ⨾[ _ ]⨾ (refl , y-p₂)


ordˡ+rᵣ : {ex : Execution LabelTCG}
  → WellFormed ex
  → {x y z : Event LabelTCG}
  → po ex x y
  → OrdAlt ex y z
  → EvRᵣ y
  → EvRᵣ x
    -------------
  → OrdAlt ex x z
ordˡ+rᵣ wf po[xy] (ord-rr rr[yz]) y-rᵣ x-rᵣ = ord-rr (ordfˡ+po wf po[xy] rr[yz] (rₜ⇒r x-rᵣ))
ordˡ+rᵣ wf po[xy] (ord-rw rw[yz]) y-rᵣ x-rᵣ = ord-rw (ordfˡ+po wf po[xy] rw[yz] (rₜ⇒r x-rᵣ))
ordˡ+rᵣ wf po[xy] (ord-rm rm[yz]) y-rᵣ x-rᵣ = ord-rm (ordfˡ+po wf po[xy] rm[yz] (rₜ⇒r x-rᵣ))
ordˡ+rᵣ wf po[xy] (ord-mr mr[yz]) y-rᵣ x-rᵣ = ord-mr (ordfˡ+po wf po[xy] mr[yz] (rₜ⇒rw x-rᵣ))
ordˡ+rᵣ wf po[xy] (ord-mw mw[yz]) y-rᵣ x-rᵣ = ord-mw (ordfˡ+po wf po[xy] mw[yz] (rₜ⇒rw x-rᵣ))
ordˡ+rᵣ wf po[xy] (ord-mm mm[yz]) y-rᵣ x-rᵣ = ord-mm (ordfˡ+po wf po[xy] mm[yz] (rₜ⇒rw x-rᵣ))
ordˡ+rᵣ wf po[xy] (ord-sc sc[yz]) y-rᵣ x-rᵣ = ord-sc (ordfˡ+po wf po[xy] sc[yz] (rₜ⇒rw x-rᵣ))
ordˡ+rᵣ wf po[xy] (ord-rmw-dom ((refl , y-rw) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z∈rmwˡ))) y-rᵣ x-rᵣ =
  let po[xz] = po-trans wf po[xy] po[yz]
  in ord-rmw-dom ((refl , rₜ⇒rw x-rᵣ) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z∈rmwˡ))
ordˡ+rᵣ wf po[xy] (ord-w ((refl , y-rw) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-wₜ))) y-rᵣ x-rᵣ =
  let po[xz] = po-trans wf po[xy] po[yz]
  in ord-w ((refl , rₜ⇒rw x-rᵣ) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-wₜ))
-- impossible cases
ordˡ+rᵣ wf po[xy] (ord-init ((refl , y-init) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-rw))) y-rᵣ x-rᵣ =
  ⊥-elim (disjoint-r/init _ (rₜ⇒r y-rᵣ , y-init))
ordˡ+rᵣ {ex} wf po[xy] (ord-wr wr[yz]) y-rᵣ x-rᵣ = ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , ord-predˡ ex wr[yz]))
ordˡ+rᵣ {ex} wf po[xy] (ord-ww ww[yz]) y-rᵣ x-rᵣ = ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , ord-predˡ ex ww[yz]))
ordˡ+rᵣ {ex} wf po[xy] (ord-wm wm[yz]) y-rᵣ x-rᵣ = ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , ord-predˡ ex wm[yz]))
ordˡ+rᵣ wf po[xy] (ord-rmw-codom ((refl , y∈rmwʳ) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-rw))) y-rᵣ x-rᵣ =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , wₜ⇒w (rmwʳ-w wf y∈rmwʳ)))
ordˡ+rᵣ wf po[xy] (ord-r ((refl , y-rₐ) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-rw))) y-rᵣ x-rᵣ =
  ⊥-elim (disjoint-rₜ _ (y-rᵣ , y-rₐ))


ghbi⇒po/sloc : {ex : Execution LabelTCG}
  → WellFormed ex
  → {x y : Event LabelTCG}
  → GhbiAlt ex x y → (po ex ∪₂ SameLoc) x y
ghbi⇒po/sloc wf (ghbi-ord ord[xy]) = inj₁ (OrdAlt⇒po wf ord[xy])
ghbi⇒po/sloc wf (ghbi-rfe rfe[xy]) = inj₂ (⊆₂-apply (rf-sloc wf) (proj₁ rfe[xy]))
ghbi⇒po/sloc wf (ghbi-coe coe[xy]) = inj₂ (⊆₂-apply (co-sloc wf) (proj₁ coe[xy]))
ghbi⇒po/sloc wf (ghbi-fre fre[xy]) = inj₂ (⊆₂-apply (fr-sloc wf) (proj₁ fre[xy]))


ghbi⇒coh : {ex : Execution LabelTCG}
  → WellFormed ex
  → {x y : Event LabelTCG}
  → SameLoc x y
  → GhbiAlt ex x y
    --------------
  → Coh ex x y
ghbi⇒coh wf xy-sloc (ghbi-ord ord[xy]) = coh-po-loc (OrdAlt⇒po wf ord[xy] , xy-sloc)
ghbi⇒coh wf _       (ghbi-rfe rfe[xy]) = coh-rf (proj₁ rfe[xy])
ghbi⇒coh wf _       (ghbi-coe coe[xy]) = coh-co (proj₁ coe[xy])
ghbi⇒coh wf _       (ghbi-fre fre[xy]) = coh-fr (proj₁ fre[xy])


-- | There exists no GHB cycle of length one
¬ghbi-cycle₁ : {ex : Execution LabelTCG}
  → WellFormed ex
  → {x : Event LabelTCG}
  → GhbiAlt ex x x
  → ⊥
¬ghbi-cycle₁ wf = GhbiAlt-irreflexive wf refl


-- | There exists no GHB cycle of length two
¬ghbi-cycle₂ : {ex : Execution LabelTCG}
  → WellFormed ex
  → Acyclic _≡_ (Coh ex)
  → {x y : Event LabelTCG}
  → GhbiAlt ex x y → GhbiAlt ex y x
  → ⊥
¬ghbi-cycle₂ wf coh ghbi[xy] ghbi[yx] with ghbi⇒po/sloc wf ghbi[yx]
¬ghbi-cycle₂ wf coh (ghbi-ord ord[xy]) _ | inj₁ po[yx]  =
  po-irreflexive wf refl (po-trans wf (OrdAlt⇒po wf ord[xy]) po[yx])
¬ghbi-cycle₂ wf coh (ghbi-rfe rfe[xy]) _ | inj₁ po[yx]  =
  let yx-sloc = sym-same-loc (⊆₂-apply (rf-sloc wf) (proj₁ rfe[xy]))
  in coh refl (coh-rf (proj₁ rfe[xy]) ∷ [ coh-po-loc (po[yx] , yx-sloc) ])
¬ghbi-cycle₂ wf coh (ghbi-coe coe[xy]) _ | inj₁ po[yx]  =
  let yx-sloc = sym-same-loc (⊆₂-apply (co-sloc wf) (proj₁ coe[xy]))
  in coh refl (coh-co (proj₁ coe[xy]) ∷ [ coh-po-loc (po[yx] , yx-sloc) ])
¬ghbi-cycle₂ wf coh (ghbi-fre fre[xy]) _ | inj₁ po[yx]  =
  let yx-sloc = sym-same-loc (⊆₂-apply (fr-sloc wf) (proj₁ fre[xy]))
  in coh refl (coh-fr (proj₁ fre[xy]) ∷ [ coh-po-loc (po[yx] , yx-sloc) ])
¬ghbi-cycle₂ wf coh ghbi[xy]        ghbi[yx] | inj₂ yx-sloc =
  coh refl (ghbi⇒coh wf (sym-same-loc yx-sloc) ghbi[xy] ∷ [ ghbi⇒coh wf yx-sloc ghbi[yx] ])
