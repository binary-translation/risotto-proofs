{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.TCG using (LabelTCG)
open import TransformFRAR using (FRAR-Restricted)


module Proof.Elimination.FRAR.Consistent
  (dst : Execution LabelTCG) (dst-ok : FRAR-Restricted dst) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip; id)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; Irreflexive; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_]; _++_)
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
open import TransformFRAR
-- Local imports: Proof Components
open import Proof.Elimination.FRAR.Execution dst dst-ok as RAR-Ex
open import Proof.Elimination.FRAR.WellFormed dst dst-ok as RAR-Wf
import Proof.Framework LabelTCG dst dst-wf as Ψ
import Proof.Elimination.Framework dst dst-wf as Δ


open FRAR-Restricted
open Ex.Execution
open Ex.WellFormed
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
open Δ.Definitions δ
open Δ.WellFormed δ
open RAR-Ex.Extra
open IsTCGConsistent


dst-consistent = consistent dst-ok


-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result


-- # Helpers

private
  -- | Somehow, typechecking is /really/ slow without extracting this lemma
  elim-⊥⊎ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
    → ( A → ⊥ ) → ( B → C ) → A ⊎ B → C
  elim-⊥⊎ f _ (inj₁ a) = ⊥-elim (f a)
  elim-⊥⊎ _ g (inj₂ b) = g b

  elim-⊎ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
    → ( A → C ) → ( B → C ) → A ⊎ B → C
  elim-⊎ f _ (inj₁ a) = f a
  elim-⊎ _ g (inj₂ b) = g b


poʳ-e⇒p₂ : {x : Event LabelTCG}
  → x ≢ pres₂-ev dst-ok
  → po src x src-elim-ev
  → po src x (pres₂-ev dst-ok)
poʳ-e⇒p₂ ¬x-pres₂ po[xe] =
  elim-⊥⊎ ¬x-pres₂ id (unsplit-poʳ src-wf po[xe] src-pair₂-pi)


poʳ-e⇒p₁ : {x : Event LabelTCG}
  → x ≢ pres₁-ev dst-ok
  → x ≢ pres₂-ev dst-ok
  → po src x src-elim-ev
  → po src x (pres₁-ev dst-ok)
poʳ-e⇒p₁ ¬x-pres₁ ¬x-pres₂ po[xe] =
  elim-⊥⊎ ¬x-pres₁ id (unsplit-poʳ src-wf (poʳ-e⇒p₂ ¬x-pres₂ po[xe]) src-pair₁-pi)


poˡ-e⇒p :{y : Event LabelTCG} → po src src-elim-ev y → po src (pres₁-ev dst-ok) y
poˡ-e⇒p po[ey] = po-trans src-wf src-pair₁₂-po po[ey]


plˡ-e⇒p : ∀ {y : Event LabelTCG} → po-loc src src-elim-ev y → po-loc src (pres₁-ev dst-ok) y
plˡ-e⇒p (po[ey] , ey-sloc) = (poˡ-e⇒p po[ey] , trans-same-loc pe-sloc ey-sloc)


plʳ-e⇒p₁ : ∀ {x : Event LabelTCG}
  → x ≢ pres₁-ev dst-ok
  → po-loc src x src-elim-ev
  → po-loc src x (pres₁-ev dst-ok)
plʳ-e⇒p₁ ¬x-pres₁ (po[xe] , xe-sloc@(same-loc x-loc _)) =
  let ¬x-pres₂ = λ{refl → ¬f-loc (pres₂-f dst-ok) (_ , x-loc)}
  in (poʳ-e⇒p₁ ¬x-pres₁ ¬x-pres₂ po[xe] , trans-same-loc xe-sloc (sym-same-loc pe-sloc))


pres₁-rw : EvRW (pres₁-ev dst-ok)
pres₁-rw = r⇒rw (pres₁-r dst-ok)


ord-fence : ∀ {P₁ P₂ : Pred (Event LabelTCG) ℓzero} {m : F-mode} {x y : Event LabelTCG}
  → ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ m ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x y
  → Event LabelTCG
ord-fence ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) =
  z
  
ord-fence∈src : ∀ {P₁ P₂ : Pred (Event LabelTCG) ℓzero} {m : F-mode} {x y : Event LabelTCG}
  → (f[xy] : ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ m ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x y)
  → ord-fence f[xy] ∈ events src
ord-fence∈src ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) =
  poˡ∈src po[zy] 


ord-fence-F : ∀ {P₁ P₂ : Pred (Event LabelTCG) ℓzero} {m : F-mode} {x y : Event LabelTCG}
  → (f[xy] : (⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ m ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x y)
  → EvF₌ m (ord-fence f[xy])
ord-fence-F ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) = z-f


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


-- # Coherence

CohDetour : Rel (Event LabelTCG) ℓzero
CohDetour x y = Coh src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)

cohˡ-e⇒p : {y : Event LabelTCG} → Coh src src-elim-ev y → Coh src (pres₁-ev dst-ok) y
cohˡ-e⇒p (coh-po-loc pl[ey]) = coh-po-loc (plˡ-e⇒p pl[ey])
cohˡ-e⇒p (coh-fr fr[ey])     = coh-fr (frˡ-e⇒p fr[ey])
cohˡ-e⇒p (coh-rf rf[ey])     = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (rf-w×r src-wf) rf[ey]))
cohˡ-e⇒p (coh-co co[ey])     = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (co-w×w src-wf) co[ey]))

cohʳ-e⇒p : {x : Event LabelTCG} → x ≢ pres₁-ev dst-ok → Coh src x src-elim-ev → Coh src x (pres₁-ev dst-ok)
cohʳ-e⇒p ¬x-pres₁ (coh-po-loc pl[xe]) = coh-po-loc (plʳ-e⇒p₁ ¬x-pres₁ pl[xe])
cohʳ-e⇒p ¬x-pres₁ (coh-rf rf[xe])     = coh-rf (rfʳ-e⇒p rf[xe])
cohʳ-e⇒p ¬x-pres₁ (coh-fr fr[xe])     = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (fr-r×w src-wf) fr[xe]))
cohʳ-e⇒p ¬x-pres₁ (coh-co co[xe])     = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (co-w×w src-wf) co[xe]))


coh-detour : ∀ {x : Event LabelTCG} → TransClosure (Coh src) x x → ∃[ z ] TransClosure CohDetour z z
coh-detour coh⁺[xx] with divert-cycle coh⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
coh-detour coh⁺[xx] | inj₁ (cycle₁ coh[ee]) = ⊥-elim (coh-irreflexive src-wf refl coh[ee])
coh-detour coh⁺[xx] | inj₁ (cycle₂ {y} ¬y-elim coh[ey] coh[ye]) =
  let ¬y-pres₁ = λ{refl → coh-irreflexive src-wf refl (cohˡ-e⇒p coh[ey])}
  in _ , ((cohˡ-e⇒p coh[ey] , ¬pres₁-elimₛ , ¬y-elim)) ∷ [ cohʳ-e⇒p ¬y-pres₁ coh[ye] , ¬y-elim , ¬pres₁-elimₛ ]
coh-detour coh⁺[xx] | inj₁ (cycleₙ {x} {y} coh[ex] cohd⁺[xy] coh[ye])
  with ev-eq-dec y (pres₁-ev dst-ok)
... | yes refl   =
  _ , (cohˡ-e⇒p coh[ex] , ¬pres₁-elimₛ , ⁺-lift-predˡ (proj₁ ∘ proj₂) cohd⁺[xy]) ∷ cohd⁺[xy] -- y ≡ p
... | no ¬pres-y =
  let ¬elim-y = ⁺-lift-predʳ (proj₂ ∘ proj₂) cohd⁺[xy]
      ¬elim-x = ⁺-lift-predˡ (proj₁ ∘ proj₂) cohd⁺[xy]
  in _ , ((cohʳ-e⇒p ¬pres-y coh[ye] , ¬elim-y , ¬pres₁-elimₛ) ∷ (cohˡ-e⇒p coh[ex] , ¬pres₁-elimₛ , ¬elim-x) ∷ cohd⁺[xy])
coh-detour coh⁺[xx] | inj₂ cohd⁺[xx] = _ , cohd⁺[xx]


src-ax-coherence  : Acyclic _≡_ ( Coh src )
src-ax-coherence refl coh⁺[xx] =
  let (z , cohd⁺[zz]) = coh-detour coh⁺[xx]
      z∈src = ⁺-lift-predˡ cohdˡ∈src cohd⁺[zz]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ cohdˡ∈src coh[⇒] z∈src z∈src cohd⁺[zz])
  where
  coh[⇒] : Rel[⇒] CohDetour (Coh dst)
  coh[⇒] x∈src y∈src (coh-po-loc pl[xy] , ¬elim-x , ¬elim-y) =
    coh-po-loc (po-loc[⇒] ¬elim-x ¬elim-y x∈src y∈src pl[xy])
  coh[⇒] x∈src y∈src (coh-rf rf[xy] , ¬elim-x , ¬elim-y) = coh-rf (rf[⇒] ¬elim-x ¬elim-y x∈src y∈src rf[xy])
  coh[⇒] x∈src y∈src (coh-fr fr[xy] , ¬elim-x , ¬elim-y) = coh-fr (fr[⇒] ¬elim-x x∈src y∈src fr[xy])
  coh[⇒] x∈src y∈src (coh-co co[xy] , ¬elim-x , ¬elim-y) = coh-co (co[⇒] ¬elim-x ¬elim-y x∈src y∈src co[xy])

  cohdˡ∈src : CohDetour ˡ∈src
  cohdˡ∈src (coh[xy] , _ , _) = cohˡ∈ex src-wf coh[xy]



-- # Atomicity

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
      ¬elim-x = λ{refl → disjoint-rₜ _ (src-elim-rₜ , ×₂-applyˡ (rmw-r×w src-wf) rmw[xy])}
      ¬elim-y = elim-¬w (src-coʳ-w (proj₁ coe[zy]))
      ¬elim-z = elim-¬w (src-coˡ-w (proj₁ coe[zy]))
  in
  ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] ¬elim-x x∈src z∈src fre[xz] ⨾[ ev[⇒] z∈src ]⨾ coe[⇒] ¬elim-z ¬elim-y z∈src y∈src coe[zy]
    )


-- # Consistency

GhbiAltDetour : Rel (Event LabelTCG) ℓzero
GhbiAltDetour x y = GhbiAlt src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)


¬elim-pres₂ : src-elim-ev ≢ pres₂-ev dst-ok
¬elim-pres₂ e≡p₂ = po-irreflexive src-wf (≡-sym e≡p₂) (proj₁ src-pair₂-pi)


¬po[ep₁] : ¬ po src src-elim-ev (pres₁-ev dst-ok)
¬po[ep₁] po[ep₁] = po-irreflexive src-wf refl (po-trans src-wf po[ep₁] src-pair₁₂-po)


pi[p₁p₂] : po-imm src (pres₁-ev dst-ok) (pres₂-ev dst-ok)
pi[p₁p₂] = src-pair₁-pi


pi[p₂e] : po-imm src (pres₂-ev dst-ok) src-elim-ev
pi[p₂e] = src-pair₂-pi


po[p₁e] : po src (pres₁-ev dst-ok) src-elim-ev
po[p₁e] = src-pair₁₂-po


poʳ-e⇒p : {x : Event LabelTCG}
  → EvRW x
  → x ≢ pres₁-ev dst-ok
  → po src x src-elim-ev
  → po src x (pres₁-ev dst-ok)
poʳ-e⇒p {x} x-rw ¬x-pres₁ po[xe] =
  elim-⊥⊎ (λ{refl → disjoint-f/rw _ (pres₂-f dst-ok , x-rw)}) lemma (unsplit-poʳ src-wf po[xe] pi[p₂e])
  where
  lemma : po src x (pres₂-ev dst-ok) → po src x (pres₁-ev dst-ok)
  lemma po[xp₂] = elim-⊥⊎ ¬x-pres₁ id (unsplit-poʳ src-wf po[xp₂] pi[p₁p₂])


src-po-r-rm : {x : Event LabelTCG} → x ≢ src-elim-ev → x ∈ events src → EvRᵣ x → ∃[ y ] (EvF₌ RM y × po-imm src x y)
src-po-r-rm ¬x-elim x∈src x-r with po-r-rm dst-ok (events[⇒] x∈src) (Rₜ[⇒] ¬x-elim x∈src x-r)
... | z , z-f , pi[xz] =
  let x∈dst = events[⇒] x∈src
      z∈dst = piʳ∈ex dst-wf pi[xz]
      z∈src = events[⇐] z∈dst
  in ev[⇐] z∈dst , F₌[⇐] z∈dst z-f , pi[⇐$] x∈src (events[⇐] z∈dst) pi[xz]


ordRM-e⇒p₁ : {x : Event LabelTCG}
  → x ≢ pres₁-ev dst-ok
  → ( ⦗ EvRᵣ ⦘ ⨾ po src ⨾ ⦗ EvF₌ RM ⦘ ⨾ po src ) x src-elim-ev
  → OrdAlt src x (pres₁-ev dst-ok)
ordRM-e⇒p₁ {x} ¬x-pres₁ ((refl , x-rᵣ) ⨾[ x ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ y ]⨾ po[ye]) =
  -- Somehow, type checking can be /really really really/ slow on some of these equalities.
  -- I'm not sure what's causing that. To avoid it, I've added some type annotations, and
  -- avoid pattern-matching on `refl`. Seems to work..
  elim-⊎
    (λ{y≡p → lemma₁ (subst-rel (po src) refl y≡p po[xy])})
    lemma₂
    (unsplit-poʳ src-wf po[ye] pi[p₂e])
  where
  lemma₁ : po src x (pres₂-ev dst-ok) → OrdAlt src x (pres₁-ev dst-ok)
  lemma₁ po[xp₂] =
    let po[xp₁] : po src x (pres₁-ev dst-ok)
        po[xp₁] = elim-⊥⊎ ¬x-pres₁ id (unsplit-poʳ src-wf po[xp₂] pi[p₁p₂])
        x∈src : x ∈ events src
        x∈src = poˡ∈src po[xy]
        ¬x-elim : x ≢ src-elim-ev
        ¬x-elim = λ{x≡e → po-irreflexive src-wf x≡e (po-trans src-wf po[xy] po[ye])}
        ¬x-init : ¬ EvInit x
        ¬x-init = λ{x-init → disjoint-r/init _ (rₜ⇒r x-rᵣ , x-init)}
        (z , z-rm , pi[xz]) = src-po-r-rm ¬x-elim x∈src x-rᵣ
        τ₂ : ( z ≡ pres₁-ev dst-ok ) ⊎ ( po src z (pres₁-ev dst-ok) )
        τ₂ = unsplit-poˡ src-wf ¬x-init po[xp₁] pi[xz]
        po[zp₁] : po src z (pres₁-ev dst-ok)
        po[zp₁] = elim-⊥⊎ (λ{z≡p₁ → disjoint-f/r _ (f₌⇒f z-rm , subst EvR (≡-sym z≡p₁) (pres₁-r dst-ok))}) id τ₂
    in
    ord-rm ((refl , rₜ⇒r x-rᵣ) ⨾[ _ ]⨾ proj₁ pi[xz] ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zp₁] ⨾[ _ ]⨾ (refl , r⇒rw (pres₁-r dst-ok)))
  lemma₂ : po src y (pres₂-ev dst-ok) → OrdAlt src x (pres₁-ev dst-ok)
  lemma₂ po[yp₂] =
    let τ : (y ≡ pres₁-ev dst-ok) ⊎ po src y (pres₁-ev dst-ok)
        τ = unsplit-poʳ src-wf po[yp₂] pi[p₁p₂]
        po[yp₁] : po src y (pres₁-ev dst-ok)
        po[yp₁] = elim-⊥⊎ (λ{y≡p₁ → disjoint-f/r _ (f₌⇒f y-f , subst EvR (≡-sym y≡p₁) (pres₁-r dst-ok))}) id τ
    in
    ord-rm ((refl , rₜ⇒r x-rᵣ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[yp₁] ⨾[ _ ]⨾ (refl , r⇒rw (pres₁-r dst-ok)))


unsplitʳ-p₁p₂ : {x : Event LabelTCG}
  → x ≢ pres₁-ev dst-ok
  → x ≢ pres₂-ev dst-ok
  → po src x src-elim-ev
  → po src x (pres₁-ev dst-ok)
unsplitʳ-p₁p₂ ¬x-pres₁ ¬x-pres₂ po[xe] =
  let po[xp₂] = elim-⊥⊎ ¬x-pres₂ id (unsplit-poʳ src-wf po[xe] pi[p₂e])
  in elim-⊥⊎ ¬x-pres₁ id (unsplit-poʳ src-wf po[xp₂] pi[p₁p₂])


unsplitˡ-p₁p₂ : {y : Event LabelTCG}
  → y ≢ pres₂-ev dst-ok
  → y ≢ src-elim-ev
  → po src (pres₁-ev dst-ok) y
  → po src src-elim-ev y
unsplitˡ-p₁p₂ {y} ¬y-pres₂ ¬y-elim po[p₁y] =
  let ¬pres₁-init = λ{p₁-init → disjoint-r/init _ (pres₁-r dst-ok , p₁-init)}
      ¬pres₂-init = λ{p₂-init → disjoint-f/init _ (pres₂-f dst-ok , p₂-init)}
      po[p₂y] : po src (pres₂-ev dst-ok) y
      po[p₂y] = elim-⊥⊎ (≢-sym ¬y-pres₂) id (unsplit-poˡ src-wf ¬pres₁-init po[p₁y] pi[p₁p₂])
  in elim-⊥⊎ (≢-sym ¬y-elim) id (unsplit-poˡ src-wf ¬pres₂-init po[p₂y] pi[p₂e])


ordSC-e⇒p₁ : {x : Event LabelTCG}
  → x ≢ pres₁-ev dst-ok
  → ( ⦗ EvRW ⦘ ⨾ po src ⨾ ⦗ EvF₌ SC ⦘ ⨾ po src ) x src-elim-ev
  → OrdAlt src x (pres₁-ev dst-ok)
ordSC-e⇒p₁ {x} ¬x-pres₁ ((refl , x-rw) ⨾[ x ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ y ]⨾ po[ye]) =
  let ¬y-pres₁ = λ{y≡p₁ → disjoint-f/r _ (f₌⇒f y-f , subst EvR (≡-sym y≡p₁) (pres₁-r dst-ok))}
      ¬y-pres₂ = λ{y≡p₂ → disjoint-f/mode (λ()) _ (y-f , subst (EvF₌ RM) (≡-sym y≡p₂) (pres₂-f₌ dst-ok))}
      po[yp₁] = unsplitʳ-p₁p₂ ¬y-pres₁ ¬y-pres₂ po[ye]
  in ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[yp₁] ⨾[ _ ]⨾ (refl , r⇒rw (pres₁-r dst-ok)))


ordʳ-e⇒p : {x : Event LabelTCG}
  → x ≢ pres₁-ev dst-ok
  → OrdAlt src x src-elim-ev
  → OrdAlt src x (pres₁-ev dst-ok)
ordʳ-e⇒p ¬x-pres₁ (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw)))
  with unsplit-po-triʳ src-wf po[xe] po[p₁e]
... | tri<  po[xp₁] x≢p  ¬po[p₁x] = ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , r⇒rw (pres₁-r dst-ok)))
... | tri≈ ¬po[xp₁] refl ¬po[p₁x] = ⊥-elim (disjoint-r/init _ (pres₁-r dst-ok , x-init))
... | tri> ¬po[xp₁] x≢p   po[p₁x] =
  let p₁-init = po-init-first src-wf po[p₁x] x-init
  in ⊥-elim (disjoint-r/init _ (pres₁-r dst-ok , p₁-init))
ordʳ-e⇒p {x} ¬x-pres₁ (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ y ]⨾ po[ye] ⨾[ _ ]⨾ (refl , e-rw)))
  with r/tag x-r
... | inj₂ x-rₐ =
  let po[xe] = po-trans src-wf po[xy] po[ye]
      po[xp₁] = poʳ-e⇒p (r⇒rw x-r) ¬x-pres₁ po[xe]
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , r⇒rw (pres₁-r dst-ok)))
... | inj₁ x-rᵣ =
  ordRM-e⇒p₁ ¬x-pres₁ ((refl , x-rᵣ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[ye])
ordʳ-e⇒p ¬x-pres₁ (ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[ye] ⨾[ _ ]⨾ (refl , e-rw))) =
  ordSC-e⇒p₁ ¬x-pres₁ ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[ye])
ordʳ-e⇒p ¬x-pres₁ (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e∈rmwˡ))) =
  ⊥-elim (disjoint-rₜ _ (src-elim-rₜ , rmwˡ-r src-wf e∈rmwˡ))
ordʳ-e⇒p ¬x-pres₁ (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬x-pres₁ = λ{x≡p₁ → disjoint-r/w _ (pres₁-r dst-ok , subst EvW x≡p₁ (wₜ⇒w (rmwʳ-w src-wf x∈rmwʳ)))}
      ¬x-pres₂ = λ{x≡p₂ → disjoint-f/w _ (pres₂-f dst-ok , subst EvW x≡p₂ (wₜ⇒w (rmwʳ-w src-wf x∈rmwʳ)))}
      po[xp₁] = unsplitʳ-p₁p₂ ¬x-pres₁ ¬x-pres₂ po[xe]
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , r⇒rw (pres₁-r dst-ok)))
ordʳ-e⇒p ¬x-pres₁ (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-wₐ))) =
  ⊥-elim (disjoint-r/w _ (src-elim-r , wₜ⇒w e-wₐ))
ordʳ-e⇒p ¬x-pres₁ (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬x-pres₁ = λ{x≡p₁ → disjoint-rₜ _ (pres₁-rₜ dst-ok , subst EvRₐ x≡p₁ x-rₐ)}
      ¬x-pres₂ = λ{x≡p₂ → disjoint-f/r _ (pres₂-f dst-ok , subst EvR x≡p₂ (rₜ⇒r x-rₐ))}
      po[xp₁] = unsplitʳ-p₁p₂ ¬x-pres₁ ¬x-pres₂ po[xe]
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , r⇒rw (pres₁-r dst-ok)))
-- impssible
ordʳ-e⇒p ¬x-pres₁ (ord-rr rr[xe]) = ⊥-elim (src-no-rr _ (ord-fence∈src rr[xe] , ord-fence-F rr[xe]))
ordʳ-e⇒p ¬x-pres₁ (ord-wr wr[xe]) = ⊥-elim (src-no-wr _ (ord-fence∈src wr[xe] , ord-fence-F wr[xe]))
ordʳ-e⇒p ¬x-pres₁ (ord-wm wm[xe]) = ⊥-elim (src-no-wm _ (ord-fence∈src wm[xe] , ord-fence-F wm[xe]))
ordʳ-e⇒p ¬x-pres₁ (ord-mr mr[xe]) = ⊥-elim (src-no-mr _ (ord-fence∈src mr[xe] , ord-fence-F mr[xe])) 
ordʳ-e⇒p ¬x-pres₁ (ord-mm mm[xe]) = ⊥-elim (src-no-mm _ (ord-fence∈src mm[xe] , ord-fence-F mm[xe]))
ordʳ-e⇒p ¬x-pres₁ (ord-rw rw[xe]) = ⊥-elim (src-no-rw _ (ord-fence∈src rw[xe] , ord-fence-F rw[xe]))
ordʳ-e⇒p ¬x-pres₁ (ord-ww ww[xe]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ord-predʳ src ww[xe]))
ordʳ-e⇒p ¬x-pres₁ (ord-mw mw[xe]) = ⊥-elim (src-no-mw _ (ord-fence∈src mw[xe] , ord-fence-F mw[xe]))


ordˡ-e⇒p : {y : Event LabelTCG}
  → OrdAlt src src-elim-ev y
  → OrdAlt src (pres₁-ev dst-ok) y
ordˡ-e⇒p ord[ey] = ordˡ+rᵣ src-wf po[p₁e] ord[ey] src-elim-rₜ (pres₁-rₜ dst-ok)


¬poˡ-e⇒p : {y : Event LabelTCG}
  → y ≢ pres₂-ev dst-ok
  → y ≢ src-elim-ev
  → ¬ po src src-elim-ev y → ¬ po src (pres₁-ev dst-ok) y
¬poˡ-e⇒p ¬y-pres₂ ¬y-elim ¬po[ey] po[p₁y] = ¬po[ey] (unsplitˡ-p₁p₂ ¬y-pres₂ ¬y-elim po[p₁y])


¬poʳ-e⇒p : {x : Event LabelTCG}
  → ¬ po src x src-elim-ev
  → ¬ po src x (pres₁-ev dst-ok)
¬poʳ-e⇒p ¬po[xe] po[xp₁] = ¬po[xe] (po-trans src-wf po[xp₁] po[p₁e])


freˡ-e⇒p : {y : Event LabelTCG} → fre src src-elim-ev y → fre src (pres₁-ev dst-ok) y
freˡ-e⇒p (fr[ey] , ¬po[ey]) =
  let ¬y-pres₂ = λ{refl → disjoint-f/w _ (pres₂-f dst-ok , ×₂-applyʳ (fr-r×w src-wf) fr[ey])}
      ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
  in frˡ-e⇒p fr[ey] , ¬poˡ-e⇒p ¬y-pres₂ ¬y-elim ¬po[ey]


rfeʳ-e⇒p : {x : Event LabelTCG} → rfe src x src-elim-ev → rfe src x (pres₁-ev dst-ok)
rfeʳ-e⇒p (rf[xe] , ¬po[xe]) = rfʳ-e⇒p rf[xe] , ¬poʳ-e⇒p ¬po[xe]


ghbiʳ-e⇒p : {x : Event LabelTCG}
  → x ≢ pres₁-ev dst-ok
  → GhbiAlt src x src-elim-ev
  → GhbiAlt src x (pres₁-ev dst-ok)
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-ord ord[xe]) = ghbi-ord (ordʳ-e⇒p ¬x-pres₁ ord[xe])
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-rfe rfe[xe]) = ghbi-rfe (rfeʳ-e⇒p rfe[xe])
-- impossible cases
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-coe coe[xe]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (coe-w×w src-wf) coe[xe]))
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-fre fre[xe]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (fre-r×w src-wf) fre[xe]))


ghbiˡ-e⇒p : {y : Event LabelTCG}
  → GhbiAlt src src-elim-ev y
  → GhbiAlt src (pres₁-ev dst-ok) y
ghbiˡ-e⇒p (ghbi-ord ord[ey]) = ghbi-ord (ordˡ-e⇒p ord[ey])
ghbiˡ-e⇒p (ghbi-fre fre[ey]) = ghbi-fre (freˡ-e⇒p fre[ey])
-- impossible cases
ghbiˡ-e⇒p (ghbi-rfe rfe[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (rfe-w×r src-wf) rfe[ey]))
ghbiˡ-e⇒p (ghbi-coe coe[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (coe-w×w src-wf) coe[ey]))


¬pres₁-elim : pres₁-ev dst-ok ≢ src-elim-ev
¬pres₁-elim p₁≡e = po-irreflexive src-wf p₁≡e po[p₁e]


cycleₙ-detour :
  ∀ {x y : Event LabelTCG}
  → GhbiAlt src src-elim-ev x
  → TransClosure GhbiAltDetour x y
  → GhbiAlt src y src-elim-ev
  → ∃[ z ] TransClosure GhbiAltDetour z z
cycleₙ-detour {x} {y} ghbi[ex] ghbi⁺[xy] ghbi[ye]
  with ev-eq-dec y (pres₁-ev dst-ok)
... | yes refl =
  let ghbi[p₁x] = ghbiˡ-e⇒p ghbi[ex]
      ¬x-elim = ⁺-lift-predˡ (proj₁ ∘ proj₂) ghbi⁺[xy]
  in _ , (ghbi[p₁x] , ¬pres₁-elim , ¬x-elim) ∷ ghbi⁺[xy]
... | no ¬y-pres₁ =
  let ghbi[p₁x] = ghbiˡ-e⇒p ghbi[ex]
      ghbi[yp₁] = ghbiʳ-e⇒p ¬y-pres₁ ghbi[ye]
      ¬x-elim = ⁺-lift-predˡ (proj₁ ∘ proj₂) ghbi⁺[xy]
      ¬y-elim = ⁺-lift-predʳ (proj₂ ∘ proj₂) ghbi⁺[xy]
  in _ , (ghbi[yp₁] , ¬y-elim , ¬pres₁-elim) ∷ (ghbi[p₁x] , ¬pres₁-elim , ¬x-elim) ∷ ghbi⁺[xy]


ghb-detour : ∀ {x : Event LabelTCG}
  → TransClosure (GhbiAlt src) x x
  → ∃[ z ] TransClosure GhbiAltDetour z z
ghb-detour {x} ghbi⁺[xx] with divert-cycle ghbi⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
... | inj₁ (cycle₁ ghbi[xx]) =
  ⊥-elim (¬ghbi-cycle₁ src-wf ghbi[xx])
... | inj₁ (cycle₂ ¬elim-x ghbi[ex] ghbi[xe]) =
  ⊥-elim (¬ghbi-cycle₂ src-wf src-ax-coherence ghbi[ex] ghbi[xe])
... | inj₁ (cycleₙ ghbi[ex] ghbid⁺[xy] ghbi[ye]) =
  cycleₙ-detour ghbi[ex] ghbid⁺[xy] ghbi[ye]
... | inj₂ ghbid⁺[xx] = (_ , ghbid⁺[xx])


ghbi[⇒] : Rel[⇒] GhbiAltDetour (GhbiAlt dst)
ghbi[⇒] x∈src y∈src (ghbi-ord ord[xy] , ¬elim-x , ¬elim-y) = ghbi-ord (ord[⇒] ¬elim-x ¬elim-y x∈src y∈src ord[xy])
ghbi[⇒] x∈src y∈src (ghbi-rfe rfe[xy] , ¬elim-x , ¬elim-y) = ghbi-rfe (rfe[⇒] ¬elim-x ¬elim-y x∈src y∈src rfe[xy])
ghbi[⇒] x∈src y∈src (ghbi-coe coe[xy] , ¬elim-x , ¬elim-y) = ghbi-coe (coe[⇒] ¬elim-x ¬elim-y x∈src y∈src coe[xy])
ghbi[⇒] x∈src y∈src (ghbi-fre fre[xy] , ¬elim-x , ¬elim-y) = ghbi-fre (fre[⇒] ¬elim-x x∈src y∈src fre[xy])

ghbidˡ∈src : {x y : Event LabelTCG} → GhbiAltDetour x y → x ∈ events src
ghbidˡ∈src (ghbi[xy] , _ , _) = GhbiAltˡ∈ex src-wf ghbi[xy]

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
