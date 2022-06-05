{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.TCG using (LabelTCG)
open import TransformRAW using (RAW-Restricted)


-- | Read-After-Write elimination consistency proof.
--
-- See `Arch.TCG.IsTCGConsistent` for the definition of consistency in TCG.
module Proof.Elimination.RAW.Consistent
  (dst : Execution LabelTCG) (dst-ok : RAW-Restricted dst) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip; id)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (_∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; _++_; [_])
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architecture Definitions
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.TCG as TCG
open import Arch.TCG.Detour
-- Local imports: Theorem Specification
open import TransformRAW
-- Local imports: Proof Components
open import Proof.Elimination.RAW.Execution dst dst-ok as RAW-Ex
open import Proof.Elimination.RAW.WellFormed dst dst-ok as RAW-Wf
import Proof.Framework LabelTCG dst dst-wf as Ψ
import Proof.Elimination.Framework dst dst-wf as Δ


open RAW-Restricted
open Ex.Execution
open Ex.WellFormed
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
open Δ.Definitions δ
open Δ.WellFormed δ
open RAW-Ex.Extra
open IsTCGConsistent


dst-consistent = consistent dst-ok


-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result
--
--
-- # Explanation
--
-- In comparison to the RAR and WAW proofs, this one is more complicated. For RAR & WAW,
-- any `Ord` that goes to the eliminated event, is directly diverted to the preserved event:
--
-- > Ord elim y → Ord preserved y
-- > Ord x elim → Ord x preserved
--
-- For those proofs, the eliminated and preserved event are of equal type (read and write,
-- respectively).
-- However, for this RAW proof, the preserved event is a /write/ while the eliminated
-- event is a /read/. This means, not all `Ord` cases map trivially. Consider:
--
-- > ( ⦗R⦘ ⨾ po ⨾ ⦗F_RM⦘ ⨾ po ⨾ ⦗RW⦘ ) elim y → ( ⦗R⦘ ⨾ po ⨾ ⦗F_RM⦘ ⨾ po ⨾ ⦗RW⦘ ) preserved y
--
-- While the `RM` fence orders the eliminated /read/ event, it does /not/ order the
-- preserved /write/ event. This means the order is externally enforced; In particular, we
-- have to check the preceding ghbi cases in the chain (e.g., see `ghbi[xey]→ghbid⁺[xy]`).
--


-- # Definitions

-- | Alternative definition of `OrdAlt`, specifically for the RAW proof.
--
-- The Read-after-Write elimination /is only correct/ on program where every fence
-- is either a WW, RM, or SC fence. This holds for TCG-programs lifted from X86, but
-- (may or) may not hold for other architectures.
data OrdRAW (x y : Event LabelTCG) : Set where
  ord-init      : ( ⦗ EvInit ⦘ ⨾ po src ⨾ ⦗ EvRW ⦘ )                      x y → OrdRAW x y
  ord-ww        : ( ⦗ EvW ⦘  ⨾ po src ⨾ ⦗ EvF₌ WW ⦘ ⨾ po src ⨾ ⦗ EvW ⦘ )  x y → OrdRAW x y
  ord-rm        : ( ⦗ EvR ⦘  ⨾ po src ⨾ ⦗ EvF₌ RM ⦘ ⨾ po src ⨾ ⦗ EvRW ⦘ ) x y → OrdRAW x y
  ord-sc        : ( ⦗ EvRW ⦘ ⨾ po src ⨾ ⦗ EvF₌ SC ⦘ ⨾ po src ⨾ ⦗ EvRW ⦘ ) x y → OrdRAW x y
  ord-rmw-dom   : ( ⦗ EvRW ⦘ ⨾ po src ⨾ ⦗ dom (rmw src) ⦘ )               x y → OrdRAW x y
  ord-rmw-codom : ( ⦗ codom (rmw src) ⦘ ⨾ po src ⨾ ⦗ EvRW ⦘ )             x y → OrdRAW x y
  ord-w         : ( ⦗ EvRW ⦘ ⨾ po src ⨾ ⦗ EvWₜ trmw ⦘ )                   x y → OrdRAW x y
  ord-r         : ( ⦗ EvRₜ trmw ⦘ ⨾ po src ⨾ ⦗ EvRW ⦘ )                   x y → OrdRAW x y


ord-fence∈src : ∀ {P₁ P₂ : Pred (Event LabelTCG) ℓzero} {m : F-mode} {x y : Event LabelTCG}
  → ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ m ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x y
  → ∃[ z ] ( z ∈ events src × EvF₌ m z )
ord-fence∈src ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) =
  z , poˡ∈src po[zy] , z-f

src-no-rr : Empty₁ (events src ∩₁ EvF₌ RR)
src-no-rr _ (x∈src , x-ff) with F₌[⇒] x∈src x-ff
... | ev-f₌ = absurd (⊆₁-apply (events-bound dst-ok) (events[⇒] x∈src)) λ()

src-no-rw : Empty₁ (events src ∩₁ EvF₌ RW)
src-no-rw _ (x∈src , x-ff) with F₌[⇒] x∈src x-ff
... | ev-f₌ = absurd (⊆₁-apply (events-bound dst-ok) (events[⇒] x∈src)) λ()

src-no-wr : Empty₁ (events src ∩₁ EvF₌ WR)
src-no-wr _ (x∈src , x-ff) with F₌[⇒] x∈src x-ff
... | ev-f₌ = absurd (⊆₁-apply (events-bound dst-ok) (events[⇒] x∈src)) λ()

src-no-wm : Empty₁ (events src ∩₁ EvF₌ WM)
src-no-wm _ (x∈src , x-ff) with F₌[⇒] x∈src x-ff
... | ev-f₌ = absurd (⊆₁-apply (events-bound dst-ok) (events[⇒] x∈src)) λ()

src-no-mr : Empty₁ (events src ∩₁ EvF₌ MR)
src-no-mr _ (x∈src , x-ff) with F₌[⇒] x∈src x-ff
... | ev-f₌ = absurd (⊆₁-apply (events-bound dst-ok) (events[⇒] x∈src)) λ()

src-no-mw : Empty₁ (events src ∩₁ EvF₌ MW)
src-no-mw _ (x∈src , x-ff) with F₌[⇒] x∈src x-ff
... | ev-f₌ = absurd (⊆₁-apply (events-bound dst-ok) (events[⇒] x∈src)) λ()

src-no-mm : Empty₁ (events src ∩₁ EvF₌ MM)
src-no-mm _ (x∈src , x-ff) with F₌[⇒] x∈src x-ff
... | ev-f₌ = absurd (⊆₁-apply (events-bound dst-ok) (events[⇒] x∈src)) λ()

OrdAlt⇒OrdRAW : ∀ {x y : Event LabelTCG} → OrdAlt src x y → OrdRAW x y
OrdAlt⇒OrdRAW (ord-init init[xy])    = ord-init init[xy]
OrdAlt⇒OrdRAW (ord-rm rm[xy])        = ord-rm rm[xy]
OrdAlt⇒OrdRAW (ord-ww ww[xy])        = ord-ww ww[xy]
OrdAlt⇒OrdRAW (ord-sc sc[xy])        = ord-sc sc[xy]
OrdAlt⇒OrdRAW (ord-rmw-dom po[xy])   = ord-rmw-dom po[xy]
OrdAlt⇒OrdRAW (ord-rmw-codom po[xy]) = ord-rmw-codom po[xy]
OrdAlt⇒OrdRAW (ord-w po[xy])         = ord-w po[xy]
OrdAlt⇒OrdRAW (ord-r po[xy])         = ord-r po[xy]
-- impossible
OrdAlt⇒OrdRAW (ord-rr rr[xy]) = ⊥-elim (src-no-rr _ (proj₂ (ord-fence∈src rr[xy])))
OrdAlt⇒OrdRAW (ord-rw rw[xy]) = ⊥-elim (src-no-rw _ (proj₂ (ord-fence∈src rw[xy])))
OrdAlt⇒OrdRAW (ord-wr wr[xy]) = ⊥-elim (src-no-wr _ (proj₂ (ord-fence∈src wr[xy])))
OrdAlt⇒OrdRAW (ord-wm wm[xy]) = ⊥-elim (src-no-wm _ (proj₂ (ord-fence∈src wm[xy])))
OrdAlt⇒OrdRAW (ord-mr mr[xy]) = ⊥-elim (src-no-mr _ (proj₂ (ord-fence∈src mr[xy])))
OrdAlt⇒OrdRAW (ord-mw mw[xy]) = ⊥-elim (src-no-mw _ (proj₂ (ord-fence∈src mw[xy])))
OrdAlt⇒OrdRAW (ord-mm mm[xy]) = ⊥-elim (src-no-mm _ (proj₂ (ord-fence∈src mm[xy])))


OrdRAW⇒OrdAlt : ∀ {x y : Event LabelTCG} → OrdRAW x y → OrdAlt src x y
OrdRAW⇒OrdAlt (ord-init init[xy])    = ord-init init[xy]
OrdRAW⇒OrdAlt (ord-ww ww[xy])        = ord-ww ww[xy]
OrdRAW⇒OrdAlt (ord-rm rm[xy])        = ord-rm rm[xy]
OrdRAW⇒OrdAlt (ord-sc sc[xy])        = ord-sc sc[xy]
OrdRAW⇒OrdAlt (ord-rmw-dom po[xy])   = ord-rmw-dom po[xy]
OrdRAW⇒OrdAlt (ord-rmw-codom po[xy]) = ord-rmw-codom po[xy]
OrdRAW⇒OrdAlt (ord-w po[xy])         = ord-w po[xy]
OrdRAW⇒OrdAlt (ord-r po[xy])         = ord-r po[xy]


-- # Helpers

private
  -- | Somehow, typechecking is /really/ slow without extracting this lemma
  elim-⊥⊎ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
    → ( A → ⊥ ) → ( B → C ) → A ⊎ B → C
  elim-⊥⊎ f _ (inj₁ a) = ⊥-elim (f a)
  elim-⊥⊎ _ g (inj₂ b) = g b
  
src-elim-ev-rᵣ : EvRₜ tmov src-elim-ev
src-elim-ev-rᵣ with elim-ev-skip dst-ok
... | ev-skip with ℕ-dec (elim-uid dst-ok) (elim-uid dst-ok)
... | yes refl = ev-r is-r refl
... | no uid≢uid = ⊥-elim (uid≢uid refl)

src-elim-ev-r : EvR src-elim-ev
src-elim-ev-r = rₜ⇒r src-elim-ev-rᵣ

src-pe-sloc : SameLoc src-preserved-ev src-elim-ev
src-pe-sloc = same-loc (preserved-has-loc dst-ok) src-elim-has-loc

poˡ-e⇒p : {y : Event LabelTCG} → po src src-elim-ev y → po src src-preserved-ev y
poˡ-e⇒p po[ey] = po-trans src-wf (proj₁ src-transform-pair) po[ey]

plˡ-e⇒p : {y : Event LabelTCG} → po-loc src src-elim-ev y → po-loc src src-preserved-ev y
plˡ-e⇒p (po[ey] , ey-sloc) = poˡ-e⇒p po[ey] , trans-same-loc src-pe-sloc ey-sloc

poʳ-e⇒p : {x : Event LabelTCG} → x ≢ src-preserved-ev → po src x src-elim-ev → po src x src-preserved-ev
poʳ-e⇒p ¬x-elim po[xe] = elim-⊥⊎ ¬x-elim id (unsplit-poʳ src-wf po[xe] src-transform-pair)

plʳ-e⇒p : {x : Event LabelTCG} → x ≢ src-preserved-ev → po-loc src x src-elim-ev → po-loc src x src-preserved-ev
plʳ-e⇒p ¬x-elim (po[xe] , xe-sloc) = poʳ-e⇒p ¬x-elim po[xe] , trans-same-loc xe-sloc (sym-same-loc src-pe-sloc)

¬pres-elim : src-preserved-ev ≢ src-elim-ev
¬pres-elim p≡e = po-irreflexive src-wf p≡e (proj₁ src-transform-pair)

rf-pe : rf src src-preserved-ev src-elim-ev
rf-pe = rf-new refl refl

¬w-elim : {x : Event LabelTCG} → EvW x → x ≢ src-elim-ev
¬w-elim x-w refl = disjoint-r/w _ (src-elim-ev-r , x-w)


-- # Coherence

CohDetour : Rel (Event LabelTCG) ℓzero
CohDetour x y = Coh src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)

coh[xey]→cohd⁺[xy] : ∀ {x y : Event LabelTCG}
  → Coh src x src-elim-ev
  → Coh src src-elim-ev y
  → TransClosure CohDetour x y
coh[xey]→cohd⁺[xy] {x} (coh-po-loc pl[xe]) (coh-po-loc pl[ey]) with ev-eq-dec x src-preserved-ev
... | yes refl   = -- x ≡ p
  let ¬y-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[ey])}
  in [ coh-po-loc (plˡ-e⇒p pl[ey]) , ¬pres-elim , ¬y-elim ]
... | no ¬x-pres =
  let ¬x-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[xe])}
      ¬y-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[ey])}
  in (coh-po-loc (plʳ-e⇒p ¬x-pres pl[xe]) , ¬x-elim , ¬pres-elim) ∷ [ ( coh-po-loc (plˡ-e⇒p pl[ey]) , ¬pres-elim , ¬y-elim ) ]
coh[xey]→cohd⁺[xy] {x} (coh-po-loc pl[xe]) (coh-fr fr[ey]@(rf⁻¹[ez] ⨾[ _ ]⨾ co[zy]))
  with wf-rf-≤1 src-wf _ _ _ rf⁻¹[ez] rf-pe -- z ≡ p
... | refl -- z ≡ p
  with ev-eq-dec x src-preserved-ev
... | yes refl = -- x ≡ z ≡ p
   let ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
   in [ coh-co co[zy] , ¬pres-elim , ¬y-elim ] 
... | no ¬x-pres =
  let ¬x-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[xe])}
      ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
  in (coh-po-loc (plʳ-e⇒p ¬x-pres pl[xe]) , ¬x-elim , ¬pres-elim) ∷ [ coh-co co[zy] , ¬pres-elim , ¬y-elim ]
coh[xey]→cohd⁺[xy] (coh-rf rf[xe])     (coh-po-loc pl[ey])
  with wf-rf-≤1 src-wf _ _ _ rf[xe] rf-pe -- x ≡ p
... | refl =
  let ¬y-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[ey])}
  in [ coh-po-loc (plˡ-e⇒p pl[ey]) , ¬pres-elim , ¬y-elim ]
coh[xey]→cohd⁺[xy] (coh-rf rf[xe])     (coh-fr fr[ey]@(rf⁻¹[ez] ⨾[ _ ]⨾ co[zy]))
  with wf-rf-≤1 src-wf _ _ _ rf[xe] rf⁻¹[ez] -- x ≡ z
... | refl =
  let ¬z-elim = λ{refl → rf-irreflexive src-wf refl rf⁻¹[ez]}
      ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
  in [ coh-co co[zy] , ¬z-elim , ¬y-elim ]
coh[xey]→cohd⁺[xy] (coh-rf rf[xe])     (coh-rf rf[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyˡ (rf-w×r src-wf) rf[ey]))
coh[xey]→cohd⁺[xy] (coh-rf rf[xe])     (coh-co co[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyˡ (co-w×w src-wf) co[ey]))
coh[xey]→cohd⁺[xy] (coh-po-loc pl[xe]) (coh-rf rf[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyˡ (rf-w×r src-wf) rf[ey]))
coh[xey]→cohd⁺[xy] (coh-po-loc pl[xe]) (coh-co co[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyˡ (co-w×w src-wf) co[ey]))
coh[xey]→cohd⁺[xy] (coh-fr fr[xe])     _               = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyʳ (fr-r×w src-wf) fr[xe]))
coh[xey]→cohd⁺[xy] (coh-co co[xe])     _               = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyʳ (co-w×w src-wf) co[xe]))

-- |
--
-- General strategy:
-- * If the cycle goes through the eliminated event, identify it. Otherwise, it is a trivial detour.
-- * Handle all cases around the eliminated event
coh-detour : ∀ {x : Event LabelTCG} → TransClosure (Coh src) x x → ∃[ z ] TransClosure CohDetour z z
coh-detour coh⁺[xx] with divert-cycle coh⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
coh-detour coh⁺[xx] | inj₁ (cycle₁ coh[ee]) = ⊥-elim (coh-irreflexive src-wf refl coh[ee])
coh-detour coh⁺[xx] | inj₁ (cycle₂ {y} ¬elim-y coh[ey] coh[ye]) = (y , coh[xey]→cohd⁺[xy] coh[ye] coh[ey])
coh-detour coh⁺[xx] | inj₁ (cycleₙ {x} {y} coh[ex] cohd⁺[xy] coh[ye]) = (y , coh[xey]→cohd⁺[xy] coh[ye] coh[ex] ++ cohd⁺[xy])
coh-detour coh⁺[xx] | inj₂ cohd⁺[xx] = _ , cohd⁺[xx]

frˡ∈src : fr src ˡ∈src
frˡ∈src (rf⁻¹[xz] ⨾[ _ ]⨾ co[zy]) = rfʳ∈src rf⁻¹[xz]

fr[⇒] : CRel[⇒] (fr src) (fr dst)
fr[⇒] ¬x-elim ¬y-elim x∈src y∈src (rf⁻¹[xz] ⨾[ _ ]⨾ co[zy]) =
  let ¬z-elim = ¬w-elim (×₂-applyˡ (co-w×w src-wf) co[zy])
      z∈src = coˡ∈src co[zy]
  in rf[⇒] ¬z-elim ¬x-elim z∈src x∈src rf⁻¹[xz] ⨾[ _ ]⨾ co[⇒] ¬z-elim ¬y-elim z∈src y∈src co[zy]

src-ax-coherence : Acyclic _≡_ (Coh src)
src-ax-coherence refl coh⁺[xx] =
  let cohd⁺[zz] = proj₂ (coh-detour coh⁺[xx])
      z∈src = ⁺-lift-predˡ cohdˡ∈src cohd⁺[zz]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ cohdˡ∈src cohd[⇒]coh z∈src z∈src cohd⁺[zz])
  where
  cohd[⇒]coh : Rel[⇒] CohDetour (Coh dst)
  cohd[⇒]coh x∈src y∈src (coh-po-loc (po[xy] , xy-sloc) , ¬x-elim , ¬y-elim) =
    coh-po-loc (po[⇒] x∈src y∈src po[xy] , sloc[⇒] ¬x-elim ¬y-elim x∈src y∈src xy-sloc)
  cohd[⇒]coh x∈src y∈src (coh-rf rf[xy]     , ¬x-elim , ¬y-elim) =
    coh-rf (rf[⇒] ¬x-elim ¬y-elim x∈src y∈src rf[xy])
  cohd[⇒]coh x∈src y∈src (coh-fr fr[xy]     , ¬x-elim , ¬y-elim) =
    coh-fr (fr[⇒] ¬x-elim ¬y-elim x∈src y∈src fr[xy])
  cohd[⇒]coh x∈src y∈src (coh-co co[xy]     , ¬x-elim , ¬y-elim) =
    coh-co (co[⇒] ¬x-elim ¬y-elim x∈src y∈src co[xy])

  cohˡ∈src : Coh src ˡ∈src
  cohˡ∈src (coh-po-loc pl[xy]) = poˡ∈src (proj₁ pl[xy])
  cohˡ∈src (coh-rf rf[xy])     = rfˡ∈src rf[xy]
  cohˡ∈src (coh-fr fr[xy])     = frˡ∈src fr[xy]
  cohˡ∈src (coh-co co[xy])     = coˡ∈src co[xy]
  
  cohdˡ∈src : CohDetour ˡ∈src
  cohdˡ∈src (coh[xy] , _ , _) = cohˡ∈src coh[xy]


-- # Atomicity

fre[⇒] : CRel[⇒] (fre src) (fre dst)
fre[⇒] ¬x-elim ¬y-elim x∈src y∈src (fr[xy] , ¬po[xy]) =
  fr[⇒] ¬x-elim ¬y-elim x∈src y∈src fr[xy] , ¬po[⇒] x∈src y∈src ¬po[xy]

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy]))
  with ev-eq-dec x src-elim-ev
... | no ¬elim-x =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
      ¬elim-z = ¬w-elim (×₂-applyˡ (co-w×w src-wf) (proj₁ coe[zy]))
      ¬elim-y = ¬w-elim (×₂-applyʳ (co-w×w src-wf) (proj₁ coe[zy]))
      dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
      dst-fre[xz] = fre[⇒] ¬elim-x ¬elim-z x∈src z∈src fre[xz]
      dst-coe[zy] = coe[⇒] ¬elim-z ¬elim-y z∈src y∈src coe[zy]
  in ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src) (dst-rmw[xy] , (dst-fre[xz] ⨾[ _ ]⨾ dst-coe[zy]))
... | yes refl = lemma rmw[xy] refl
  where
  lemma : ∀ {x y : Event LabelTCG} → rmw src x y → x ≢ src-elim-ev
  lemma rmw[xy] refl = disjoint-rₜ _ (src-elim-ev-rᵣ , ×₂-applyˡ (rmw-r×w src-wf) rmw[xy])


-- # Global Order

GhbiAltDetour : Rel (Event LabelTCG) ℓzero
GhbiAltDetour x y = GhbiAlt src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)

-- rf : w × r
-- fr : r × w

¬pres-init : ¬ EvInit src-preserved-ev
¬pres-init _ with preserved-ev-wₙᵣ dst-ok
¬pres-init () | ev-w is-w refl

poˡ-p⇒e : {y : Event LabelTCG} → y ≢ src-elim-ev → po src src-preserved-ev y → po src src-elim-ev y
poˡ-p⇒e ¬y-elim po[py] = elim-⊥⊎ (≢-sym ¬y-elim) id (unsplit-poˡ src-wf ¬pres-init po[py] src-transform-pair)

¬poˡ-e⇒p : {y : Event LabelTCG} → y ≢ src-elim-ev → ¬ po src src-elim-ev y → ¬ po src src-preserved-ev y
¬poˡ-e⇒p = contrapositive ∘ poˡ-p⇒e

fr[ey]→co[py] : {y : Event LabelTCG} → fr src src-elim-ev y → co src src-preserved-ev y
fr[ey]→co[py] (rf⁻¹[ez] ⨾[ _ ]⨾ co[zy]) with wf-rf-≤1 src-wf _ _ _ rf-pe rf⁻¹[ez]
... | refl = co[zy]


--
-- A cycle that goes through `elim;F_RM;y` has to be diverted, because the preserved event
-- is a /write/ which is not ordered by F_RM.
--

-- | The extracted ordering rule of F_RM
OrdRM : Execution LabelTCG → Rel (Event LabelTCG) ℓzero
OrdRM ex = ⦗ EvR ⦘ ⨾ po ex ⨾ ⦗ EvF₌ RM ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘

-- | Subsumes a subsequent RM sequence
OrdRAW+RM :
  ∀ {x y : Event LabelTCG}
  → OrdRAW x src-elim-ev
  → OrdRM src src-elim-ev y
    -----------------------
  → OrdRAW x y
OrdRAW+RM (ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , _))) rm[ey] =
  ord-init ((refl , ev-init) ⨾[ _ ]⨾ po-trans src-wf po[xe] (ord-f⇒po src-wf rm[ey]) ⨾[ _ ]⨾ (refl , ord-predʳ src rm[ey]))
OrdRAW+RM (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , _))) rm[ey] =
  let po[zy] = po-trans src-wf po[ze] (ord-f⇒po src-wf rm[ey])
      y-rw   = ord-predʳ src rm[ey]
  in ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw))
OrdRAW+RM (ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , _))) rm[ey] =
  let po[zy] = po-trans src-wf po[ze] (ord-f⇒po src-wf rm[ey])
      y-rw   = ord-predʳ src rm[ey]
  in ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw))
OrdRAW+RM (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) rm[ey] =
  let po[xy] = po-trans src-wf po[xe] (ord-f⇒po src-wf rm[ey])
      y-rw   = ord-predʳ src rm[ey]
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))
OrdRAW+RM (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) rm[ey] =
  let po[xy] = po-trans src-wf po[xe] (ord-f⇒po src-wf rm[ey])
      y-rw   = ord-predʳ src rm[ey]
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))
-- Impossible cases
OrdRAW+RM (ord-ww ww[xe]) rm[ey] =
  ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ord-predʳ src ww[xe]))
OrdRAW+RM (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e∈rmwˡ))) rm[ey] =
  let e-rₐ = rmwˡ-r src-wf e∈rmwˡ
  in ⊥-elim (disjoint-rₜ _ (src-elim-ev-rᵣ , e-rₐ))
OrdRAW+RM (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-wₐ))) rm[ey] =
  ⊥-elim (disjoint-r/w _ (src-elim-ev-r , wₜ⇒w e-wₐ))


OrdRAWˡ-e⇒p : {y : Event LabelTCG}
  → OrdRAW src-elim-ev y
    -----------------------------------------------------------
  → ( OrdRAW src-preserved-ev y ) ⊎ ( OrdRM src src-elim-ev y )
OrdRAWˡ-e⇒p (ord-rm rm[xy]) = inj₂ rm[xy]
OrdRAWˡ-e⇒p (ord-sc ((refl , e-rw) ⨾[ _ ]⨾ po[ez] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw))) =
  let p-rw   = w⇒rw (preserved-ev-w dst-ok)
      po[pz] = poˡ-e⇒p po[ez]
  in inj₁ (ord-sc ((refl , p-rw) ⨾[ _ ]⨾ po[pz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw)))
OrdRAWˡ-e⇒p (ord-rmw-dom ((refl , e-rw) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y∈rmwˡ))) =
  let p-rw   = w⇒rw (preserved-ev-w dst-ok)
      po[py] = poˡ-e⇒p po[ey]
  in inj₁ (ord-rmw-dom ((refl , p-rw) ⨾[ _ ]⨾ po[py] ⨾[ _ ]⨾ (refl , y∈rmwˡ)))
OrdRAWˡ-e⇒p (ord-w ((refl , e-rw) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-wₐ))) =
  let p-rw   = w⇒rw (preserved-ev-w dst-ok)
      po[py] = poˡ-e⇒p po[ey]
  in inj₁ (ord-w ((refl , p-rw) ⨾[ _ ]⨾ po[py] ⨾[ _ ]⨾ (refl , y-wₐ)))
-- Impossible cases
OrdRAWˡ-e⇒p (ord-init ((refl , e-init) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , _))) =
  ⊥-elim (disjoint-r/init _ (src-elim-ev-r , e-init))
OrdRAWˡ-e⇒p (ord-ww ww[ey]) =
  ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ord-predˡ src ww[ey]))
OrdRAWˡ-e⇒p (ord-rmw-codom ((refl , e∈rmwʳ) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-rw))) =
  let e-w = wₜ⇒w (rmwʳ-w src-wf e∈rmwʳ)
  in ⊥-elim (disjoint-r/w _ (src-elim-ev-r , e-w))
OrdRAWˡ-e⇒p (ord-r ((refl , e-rₐ) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-rw))) =
  ⊥-elim (disjoint-rₜ _ (src-elim-ev-rᵣ , e-rₐ))


OrdRAWʳ-e⇒p : {x : Event LabelTCG}
  → OrdRAW x src-elim-ev
    -------------------------
  → OrdRAW x src-preserved-ev
OrdRAWʳ-e⇒p (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , _))) =
  let p-rw = w⇒rw (preserved-ev-w dst-ok)
      ¬x-pres = λ{refl → ¬pres-init x-init}
      po[xp] = poʳ-e⇒p ¬x-pres po[xe]
  in ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xp] ⨾[ _ ]⨾ (refl , p-rw))
OrdRAWʳ-e⇒p (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , e-rw))) =
  let p-rw = w⇒rw (preserved-ev-w dst-ok)
      ¬z-pres = λ{refl → disjoint-f/w _ (f₌⇒f z-f , preserved-ev-w dst-ok)}
      po[zp] = poʳ-e⇒p ¬z-pres po[ze]
  in ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zp] ⨾[ _ ]⨾ (refl , p-rw))
OrdRAWʳ-e⇒p (ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , e-rw))) =
  let p-rw = w⇒rw (preserved-ev-w dst-ok)
      ¬z-pres = λ{refl → disjoint-f/w _ (f₌⇒f z-f , preserved-ev-w dst-ok)}
      po[zp] = poʳ-e⇒p ¬z-pres po[ze]
  in ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zp] ⨾[ _ ]⨾ (refl , p-rw))
OrdRAWʳ-e⇒p (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let p-rw = w⇒rw (preserved-ev-w dst-ok)
      ¬x-pres = λ{refl → disjoint-wₜ _ (preserved-ev-wᵣ dst-ok , rmwʳ-w src-wf x∈rmwʳ)}
      po[xp] = poʳ-e⇒p ¬x-pres po[xe]
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xp] ⨾[ _ ]⨾ (refl , p-rw))
OrdRAWʳ-e⇒p (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let p-rw = w⇒rw (preserved-ev-w dst-ok)
      ¬x-pres = λ{refl → disjoint-r/w _ (rₜ⇒r x-rₐ , preserved-ev-w dst-ok)}
      po[xp] = poʳ-e⇒p ¬x-pres po[xe]
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xp] ⨾[ _ ]⨾ (refl , p-rw))
-- impossible cases
OrdRAWʳ-e⇒p (ord-ww ((refl , x-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , e-w))) =
  ⊥-elim (disjoint-r/w _ (src-elim-ev-r , e-w))
OrdRAWʳ-e⇒p (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e∈rmwˡ))) =
  let e-rₐ = rmwˡ-r src-wf e∈rmwˡ
  in ⊥-elim (disjoint-rₜ _ (src-elim-ev-rᵣ , e-rₐ))
OrdRAWʳ-e⇒p (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-wₐ))) =
  ⊥-elim (disjoint-r/w _ (src-elim-ev-r , wₜ⇒w e-wₐ))


OrdAltʳ-e⇒p : {x : Event LabelTCG}
  → OrdAlt src x src-elim-ev
    -----------------------------
  → OrdAlt src x src-preserved-ev
OrdAltʳ-e⇒p = OrdRAW⇒OrdAlt ∘ OrdRAWʳ-e⇒p ∘ OrdAlt⇒OrdRAW


ghbi[xey]→ghbid⁺[xy] : ∀ {x y : Event LabelTCG}
  → GhbiAlt src x src-elim-ev
  → GhbiAlt src src-elim-ev y
    ------------------------------
  → TransClosure GhbiAltDetour x y
ghbi[xey]→ghbid⁺[xy] (ghbi-ord ord[xe]) (ghbi-ord ord[ey]) with OrdRAWˡ-e⇒p (OrdAlt⇒OrdRAW ord[ey])
... | inj₁ ord[py] =
  let ¬x-elim = λ{refl → OrdAlt-irreflexive src-wf refl ord[xe]}
      ¬y-elim = λ{refl → OrdAlt-irreflexive src-wf refl ord[ey]}
  in (ghbi-ord (OrdAltʳ-e⇒p ord[xe]) , ¬x-elim , ¬pres-elim) ∷ [ ghbi-ord (OrdRAW⇒OrdAlt ord[py]) , ¬pres-elim , ¬y-elim ]
... | inj₂ rm[ey]  =
  let ¬x-elim = λ{refl → OrdAlt-irreflexive src-wf refl ord[xe]}
      ¬y-elim = λ{refl → OrdAlt-irreflexive src-wf refl ord[ey]}
  in [ ghbi-ord (OrdRAW⇒OrdAlt (OrdRAW+RM (OrdAlt⇒OrdRAW ord[xe]) rm[ey])) , ¬x-elim , ¬y-elim ]
ghbi[xey]→ghbid⁺[xy] (ghbi-ord ord[xe]) (ghbi-fre (fr[ey] , ¬po[ey])) =
  let ¬x-elim = λ{refl → OrdAlt-irreflexive src-wf refl ord[xe]}
      ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
  in (ghbi-ord (OrdAltʳ-e⇒p ord[xe]) , ¬x-elim , ¬pres-elim) ∷ [ ghbi-coe (fr[ey]→co[py] fr[ey] , ¬poˡ-e⇒p ¬y-elim ¬po[ey]) , ¬pres-elim , ¬y-elim ]
-- Impossible Cases
ghbi[xey]→ghbid⁺[xy] (ghbi-coe coe[xe]) ghbi[ey] = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyʳ (co-w×w src-wf) (proj₁ coe[xe])))
ghbi[xey]→ghbid⁺[xy] (ghbi-fre fre[xe]) ghbi[ey] = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyʳ (fr-r×w src-wf) (proj₁ fre[xe])))
ghbi[xey]→ghbid⁺[xy] (ghbi-ord ord[xe]) (ghbi-rfe rfe[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyˡ (rf-w×r src-wf) (proj₁ rfe[ey])))
ghbi[xey]→ghbid⁺[xy] (ghbi-ord ord[xe]) (ghbi-coe coe[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-ev-r , ×₂-applyˡ (co-w×w src-wf) (proj₁ coe[ey])))
ghbi[xey]→ghbid⁺[xy] (ghbi-rfe rfe[xe]) _ with wf-rf-≤1 src-wf _ _ _ (proj₁ rfe[xe]) rf-pe
... | refl = -- x ≡ p
  let ¬po[pe] = proj₂ rfe[xe]
  in ⊥-elim (¬po[pe] (proj₁ src-transform-pair))


ghb-detour : ∀ {x : Event LabelTCG} → TransClosure (GhbiAlt src) x x → ∃[ z ] TransClosure GhbiAltDetour z z
ghb-detour {x} ghbi⁺[xx] with divert-cycle ghbi⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
... | inj₁ (cycle₁ ghbi[xx]) = ⊥-elim (¬ghbi-cycle₁ src-wf ghbi[xx])
... | inj₁ (cycle₂ ¬x-elim ghbi[ex] ghbi[xe])    =
  ⊥-elim (¬ghbi-cycle₂ src-wf src-ax-coherence ghbi[ex] ghbi[xe])
... | inj₁ (cycleₙ ghbi[ex] ghbid⁺[xy] ghbi[ye]) =
  _ , (ghbid⁺[xy] ++ ghbi[xey]→ghbid⁺[xy] ghbi[ye] ghbi[ex])
... | inj₂ ghbid⁺[xx] = (_ , ghbid⁺[xx])


ghbidˡ∈src : GhbiAltDetour ˡ∈src
ghbidˡ∈src (ghbi-ord ord[xy] , _ , _) = OrdAltˡ∈ex src-wf ord[xy]
ghbidˡ∈src (ghbi-rfe rfe[xy] , _ , _) = rfˡ∈ex src-wf (proj₁ rfe[xy])
ghbidˡ∈src (ghbi-coe coe[xy] , _ , _) = coˡ∈ex src-wf (proj₁ coe[xy])
ghbidˡ∈src (ghbi-fre fre[xy] , _ , _) = frˡ∈ex src-wf (proj₁ fre[xy])


ghbi[⇒] : Rel[⇒] GhbiAltDetour (GhbiAlt dst)
ghbi[⇒] x∈src y∈src (ghbi-ord ord[xy] , ¬elim-x , ¬elim-y) = ghbi-ord (ord[⇒] ¬elim-x ¬elim-y x∈src y∈src ord[xy])
ghbi[⇒] x∈src y∈src (ghbi-rfe rfe[xy] , ¬elim-x , ¬elim-y) = ghbi-rfe (rfe[⇒] ¬elim-x ¬elim-y x∈src y∈src rfe[xy])
ghbi[⇒] x∈src y∈src (ghbi-coe coe[xy] , ¬elim-x , ¬elim-y) = ghbi-coe (coe[⇒] ¬elim-x ¬elim-y x∈src y∈src coe[xy])
ghbi[⇒] x∈src y∈src (ghbi-fre fre[xy] , ¬elim-x , ¬elim-y) = ghbi-fre (fre[⇒] ¬elim-x ¬elim-y x∈src y∈src fre[xy])


src-ax-global-ord : Irreflexive _≡_ (ghb src)
src-ax-global-ord refl ghb[xx] =
  -- First, find a detour that only goes between R/W events. Then find a detour that does /not/ go
  -- through the eliminated event.
  let (y , ghbd[yy]) = ghb-detour (proj₂ (detour src-wf ghb[xx]))
      y∈src = ⁺-lift-predˡ (GhbiAltˡ∈ex src-wf ∘ proj₁) ghbd[yy]
  in ax-global-ord dst-consistent refl (GhbiAlt⁺⇒Ghbi⁺ (⁺[⇒]ˡ ghbidˡ∈src ghbi[⇒] y∈src y∈src ghbd[yy]))


src-consistent : IsTCGConsistent src
src-consistent =
  record
    { ax-coherence  = src-ax-coherence
    ; ax-atomicity  = src-ax-atomicity
    ; ax-global-ord = src-ax-global-ord
    }
