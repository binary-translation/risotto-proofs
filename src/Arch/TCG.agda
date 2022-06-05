{-# OPTIONS --safe #-}

module Arch.TCG where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Level using (Level; _⊔_) renaming (zero to ℓzero; suc to ℓsuc)
open import Function using (_∘_)
open import Data.Product using (_,_; _×_; proj₁; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty; _∈_)
open import Relation.Binary using (Rel; Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Helpers
open import Arch.General.Event
open import Arch.General.Properties using (tag-eq-dec; ev-eq-dec)
open import Arch.General.Execution
open import Arch.General.DerivedWellformed


open Event
open Execution
open WellFormed


-- | Fence mode. (See `lab-f` in `LabelTCG`)
--
-- Naming conventions:
-- * R  =  Read
-- * W  =  Write
-- * M  =  Memory  = Read / Write
data F-mode : Set where
  RR : F-mode -- read / read
  RW : F-mode -- read / write
  RM : F-mode -- read / memory

  WR : F-mode -- write / read
  WW : F-mode -- write / write
  WM : F-mode -- write / memory

  MR : F-mode -- memory / read
  MW : F-mode -- memory / write
  MM : F-mode -- memory / memory

  ACQ : F-mode -- acquire (does nothing - see also `Arch.TCG.Detour`)
  REL : F-mode -- release (does nothing - see also `Arch.TCG.Detour`)
  SC  : F-mode -- Full Fence (Sequentially Consistent)

data LabelTCG : Set where
  lab-r : Tag → Location → Value → LabelTCG
  lab-w : Tag → Location → Value → LabelTCG
  lab-f : F-mode → LabelTCG


data LabR : LabelTCG → Set where
  is-r : ∀ {tag : Tag} {loc : Location} {val : Value} → LabR (lab-r tag loc val)

data LabW : LabelTCG → Set where
  is-w : ∀ {tag : Tag} {loc : Location} {val : Value} → LabW (lab-w tag loc val)

data LabF : LabelTCG → Set where
  is-f : ∀ {mode : F-mode} → LabF (lab-f mode)


-- # Lemmas/Properties

private
  labs-xopt : XOptPred₃ LabR LabW LabF
  labs-xopt (lab-r _ _ _) = xopt₁ is-r  (λ()) (λ())
  labs-xopt (lab-w _ _ _) = xopt₂ (λ()) is-w  (λ())
  labs-xopt (lab-f _)     = xopt₃ (λ()) (λ()) is-f

  r-unique : UniquePred LabR
  r-unique _ is-r is-r = refl

  w-unique : UniquePred LabW
  w-unique _ is-w is-w = refl

  f-unique : UniquePred LabF
  f-unique _ is-f is-f = refl

  r-tag : {lab : LabelTCG} → LabR lab → Tag
  r-tag {lab-r tag _ _} is-r = tag

  w-tag : {lab : LabelTCG} → LabW lab → Tag
  w-tag {lab-w tag _ _} is-w = tag

  r-loc : {lab : LabelTCG} → LabR lab → Location
  r-loc {lab-r _ loc _} is-r = loc

  r-val : {lab : LabelTCG} → LabR lab → Value
  r-val {lab-r _ _ val} is-r = val

  w-loc : {lab : LabelTCG} → LabW lab → Location
  w-loc {lab-w _ loc _} is-w = loc

  w-val : {lab : LabelTCG} → LabW lab → Value
  w-val {lab-w _ _ val} is-w = val
  
  -- Yay to the line count.
  fence-dec : DecRel (_≡_ {_} {F-mode})
  fence-dec RR  RR  = yes refl
  fence-dec RW  RW  = yes refl
  fence-dec RM  RM  = yes refl
  fence-dec WR  WR  = yes refl
  fence-dec WW  WW  = yes refl
  fence-dec WM  WM  = yes refl
  fence-dec MR  MR  = yes refl
  fence-dec MW  MW  = yes refl
  fence-dec MM  MM  = yes refl
  fence-dec ACQ ACQ = yes refl
  fence-dec REL REL = yes refl
  fence-dec SC  SC  = yes refl
  fence-dec RR  RW  = no (λ ())
  fence-dec RR  RM  = no (λ ())
  fence-dec RR  WR  = no (λ ())
  fence-dec RR  WW  = no (λ ())
  fence-dec RR  WM  = no (λ ())
  fence-dec RR  MR  = no (λ ())
  fence-dec RR  MW  = no (λ ())
  fence-dec RR  MM  = no (λ ())
  fence-dec RR  ACQ = no (λ ())
  fence-dec RR  REL = no (λ ())
  fence-dec RR  SC  = no (λ ())
  fence-dec RW  RR  = no (λ ())
  fence-dec RW  RM  = no (λ ())
  fence-dec RW  WR  = no (λ ())
  fence-dec RW  WW  = no (λ ())
  fence-dec RW  WM  = no (λ ())
  fence-dec RW  MR  = no (λ ())
  fence-dec RW  MW  = no (λ ())
  fence-dec RW  MM  = no (λ ())
  fence-dec RW  ACQ = no (λ ())
  fence-dec RW  REL = no (λ ())
  fence-dec RW  SC  = no (λ ())
  fence-dec RM  RR  = no (λ ())
  fence-dec RM  RW  = no (λ ())
  fence-dec RM  WR  = no (λ ())
  fence-dec RM  WW  = no (λ ())
  fence-dec RM  WM  = no (λ ())
  fence-dec RM  MR  = no (λ ())
  fence-dec RM  MW  = no (λ ())
  fence-dec RM  MM  = no (λ ())
  fence-dec RM  ACQ = no (λ ())
  fence-dec RM  REL = no (λ ())
  fence-dec RM  SC  = no (λ ())
  fence-dec WR  RR  = no (λ ())
  fence-dec WR  RW  = no (λ ())
  fence-dec WR  RM  = no (λ ())
  fence-dec WR  WW  = no (λ ())
  fence-dec WR  WM  = no (λ ())
  fence-dec WR  MR  = no (λ ())
  fence-dec WR  MW  = no (λ ())
  fence-dec WR  MM  = no (λ ())
  fence-dec WR  ACQ = no (λ ())
  fence-dec WR  REL = no (λ ())
  fence-dec WR  SC  = no (λ ())
  fence-dec WW  RR  = no (λ ())
  fence-dec WW  RW  = no (λ ())
  fence-dec WW  RM  = no (λ ())
  fence-dec WW  WR  = no (λ ())
  fence-dec WW  WM  = no (λ ())
  fence-dec WW  MR  = no (λ ())
  fence-dec WW  MW  = no (λ ())
  fence-dec WW  MM  = no (λ ())
  fence-dec WW  ACQ = no (λ ())
  fence-dec WW  REL = no (λ ())
  fence-dec WW  SC  = no (λ ())
  fence-dec WM  RR  = no (λ ())
  fence-dec WM  RW  = no (λ ())
  fence-dec WM  RM  = no (λ ())
  fence-dec WM  WR  = no (λ ())
  fence-dec WM  WW  = no (λ ())
  fence-dec WM  MR  = no (λ ())
  fence-dec WM  MW  = no (λ ())
  fence-dec WM  MM  = no (λ ())
  fence-dec WM  ACQ = no (λ ())
  fence-dec WM  REL = no (λ ())
  fence-dec WM  SC  = no (λ ())
  fence-dec MR  RR  = no (λ ())
  fence-dec MR  RW  = no (λ ())
  fence-dec MR  RM  = no (λ ())
  fence-dec MR  WR  = no (λ ())
  fence-dec MR  WW  = no (λ ())
  fence-dec MR  WM  = no (λ ())
  fence-dec MR  MW  = no (λ ())
  fence-dec MR  MM  = no (λ ())
  fence-dec MR  ACQ = no (λ ())
  fence-dec MR  REL = no (λ ())
  fence-dec MR  SC  = no (λ ())
  fence-dec MW  RR  = no (λ ())
  fence-dec MW  RW  = no (λ ())
  fence-dec MW  RM  = no (λ ())
  fence-dec MW  WR  = no (λ ())
  fence-dec MW  WW  = no (λ ())
  fence-dec MW  WM  = no (λ ())
  fence-dec MW  MR  = no (λ ())
  fence-dec MW  MM  = no (λ ())
  fence-dec MW  ACQ = no (λ ())
  fence-dec MW  REL = no (λ ())
  fence-dec MW  SC  = no (λ ())
  fence-dec MM  RR  = no (λ ())
  fence-dec MM  RW  = no (λ ())
  fence-dec MM  RM  = no (λ ())
  fence-dec MM  WR  = no (λ ())
  fence-dec MM  WW  = no (λ ())
  fence-dec MM  WM  = no (λ ())
  fence-dec MM  MR  = no (λ ())
  fence-dec MM  MW  = no (λ ())
  fence-dec MM  ACQ = no (λ ())
  fence-dec MM  REL = no (λ ())
  fence-dec MM  SC  = no (λ ())
  fence-dec ACQ RR  = no (λ ())
  fence-dec ACQ RW  = no (λ ())
  fence-dec ACQ RM  = no (λ ())
  fence-dec ACQ WR  = no (λ ())
  fence-dec ACQ WW  = no (λ ())
  fence-dec ACQ WM  = no (λ ())
  fence-dec ACQ MR  = no (λ ())
  fence-dec ACQ MW  = no (λ ())
  fence-dec ACQ MM  = no (λ ())
  fence-dec ACQ REL = no (λ ())
  fence-dec ACQ SC  = no (λ ())
  fence-dec REL RR  = no (λ ())
  fence-dec REL RW  = no (λ ())
  fence-dec REL RM  = no (λ ())
  fence-dec REL WR  = no (λ ())
  fence-dec REL WW  = no (λ ())
  fence-dec REL WM  = no (λ ())
  fence-dec REL MR  = no (λ ())
  fence-dec REL MW  = no (λ ())
  fence-dec REL MM  = no (λ ())
  fence-dec REL ACQ = no (λ ())
  fence-dec REL SC  = no (λ ())
  fence-dec SC  RR  = no (λ ())
  fence-dec SC  RW  = no (λ ())
  fence-dec SC  RM  = no (λ ())
  fence-dec SC  WR  = no (λ ())
  fence-dec SC  WW  = no (λ ())
  fence-dec SC  WM  = no (λ ())
  fence-dec SC  MR  = no (λ ())
  fence-dec SC  MW  = no (λ ())
  fence-dec SC  MM  = no (λ ())
  fence-dec SC  ACQ = no (λ ())
  fence-dec SC  REL = no (λ ())

  lab-eq-dec : DecRel (_≡_ {_} {LabelTCG})
  lab-eq-dec (lab-r tag₁ loc₁ val₁) (lab-r tag₂ loc₂ val₂) =
    cong₃-dec lab-r (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-w tag₁ loc₁ val₁) (lab-w tag₂ loc₂ val₂) =
    cong₃-dec lab-w (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-f m₁) (lab-f m₂) =
    cong-dec lab-f (λ{refl → refl}) (fence-dec m₁ m₂)
  -- Impossible cases
  lab-eq-dec (lab-r _ _ _) (lab-w _ _ _) = no (λ ())
  lab-eq-dec (lab-r _ _ _) (lab-f _)     = no (λ ())
  lab-eq-dec (lab-w _ _ _) (lab-r _ _ _) = no (λ ())
  lab-eq-dec (lab-w _ _ _) (lab-f _)     = no (λ ())
  lab-eq-dec (lab-f _)     (lab-r _ _ _) = no (λ ())
  lab-eq-dec (lab-f _)     (lab-w _ _ _) = no (λ ())


-- # LabelClass

instance
  LabelLIMM-ok : LabelClass LabelTCG
  LabelLIMM-ok =
    record
      { labs-r        = LabR
      ; labs-w        = LabW
      ; labs-f        = LabF
      ; labs-xopt     = labs-xopt
      ; labs-r-unique = r-unique
      ; labs-w-unique = w-unique
      ; labs-f-unique = f-unique
      ; lab-r-tag     = r-tag
      ; lab-w-tag     = w-tag
      ; lab-r-loc     = r-loc
      ; lab-r-val     = r-val
      ; lab-w-loc     = w-loc
      ; lab-w-val     = w-val
      ; lab-eq-dec    = lab-eq-dec
      }

data EvR₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelTCG → Set where
  ev-r₌ : {uid : UniqueId} {tid : ThreadId} → EvR₌ tag loc val (event uid tid (lab-r tag loc val))

data EvW₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelTCG → Set where
  ev-w₌ : {uid : UniqueId} {tid : ThreadId} → EvW₌ tag loc val (event uid tid (lab-w tag loc val))

data EvF₌ (mode : F-mode) : Event LabelTCG → Set where
  ev-f₌ : {uid : UniqueId} {tid : ThreadId} → EvF₌ mode (event uid tid (lab-f mode))
  

-- | Events ordered across the program order (po).
--
--
-- # Design Decision: Not Union Representation
--
-- Consider this the union over all relations in it's constructors.
--
-- This data structure is much easier to handle than taking _∪₂_ over all these,
-- as constructing (or pattern-matching on) an instance looks like: inj₁ (inj₁ (inj₁ ...)))
data Ord (ex : Execution LabelTCG) (x y : Event LabelTCG) : Set where
  ord-init      : ( ⦗ EvInit ⦘ ⨾ po ex )                                x y → Ord ex x y


  -- memory fences
  
  ord-rr        : ( ⦗ EvR ⦘  ⨾ po ex ⨾ ⦗ EvF₌ RR ⦘ ⨾ po ex ⨾ ⦗ EvR ⦘ )  x y → Ord ex x y
  ord-rw        : ( ⦗ EvR ⦘  ⨾ po ex ⨾ ⦗ EvF₌ RW ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ )  x y → Ord ex x y
  ord-rm        : ( ⦗ EvR ⦘  ⨾ po ex ⨾ ⦗ EvF₌ RM ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → Ord ex x y
  
  ord-wr        : ( ⦗ EvW ⦘  ⨾ po ex ⨾ ⦗ EvF₌ WR ⦘ ⨾ po ex ⨾ ⦗ EvR ⦘ )  x y → Ord ex x y
  ord-ww        : ( ⦗ EvW ⦘  ⨾ po ex ⨾ ⦗ EvF₌ WW ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ )  x y → Ord ex x y
  ord-wm        : ( ⦗ EvW ⦘  ⨾ po ex ⨾ ⦗ EvF₌ WM ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → Ord ex x y
  
  ord-mr        : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ MR ⦘ ⨾ po ex ⨾ ⦗ EvR ⦘ )  x y → Ord ex x y
  ord-mw        : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ MW ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ )  x y → Ord ex x y
  ord-mm        : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ MM ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → Ord ex x y


  -- other fences
  
  ord-acq       : ( ⦗ EvF₌ ACQ ⦘ ⨾ po ex )                              x y → Ord ex x y
  ord-rel       : ( po ex ⨾ ⦗ EvF₌ REL ⦘ )                              x y → Ord ex x y
  
  ord-sc₁       : ( po ex ⨾ ⦗ EvF₌ SC ⦘ )                               x y → Ord ex x y
  ord-sc₂       : ( ⦗ EvF₌ SC ⦘ ⨾ po ex )                               x y → Ord ex x y


  -- other ordering operations
  
  ord-rmw-dom   : ( po ex ⨾ ⦗ dom (rmw ex) ⦘ )                          x y → Ord ex x y
  ord-rmw-codom : ( ⦗ codom (rmw ex) ⦘ ⨾ po ex )                        x y → Ord ex x y
  
  ord-w         : ( po ex ⨾ ⦗ EvWₜ trmw ⦘ )                             x y → Ord ex x y
  ord-r         : ( ⦗ EvRₜ trmw ⦘ ⨾ po ex )                             x y → Ord ex x y


-- | Immediate global happens before. (See `ghb` below)
data Ghbi (ex : Execution LabelTCG) (x y : Event LabelTCG) : Set where
  ghbi-ord : Ord ex x y → Ghbi ex x y
  ghbi-rfe : rfe ex x y → Ghbi ex x y
  ghbi-coe : coe ex x y → Ghbi ex x y
  ghbi-fre : fre ex x y → Ghbi ex x y

-- | Coherence
data Coh (ex : Execution LabelTCG) (x y : Event LabelTCG) : Set where
  coh-po-loc : po-loc ex x y → Coh ex x y
  coh-rf     : rf ex     x y → Coh ex x y
  coh-fr     : fr ex     x y → Coh ex x y
  coh-co     : co ex     x y → Coh ex x y


-- | Global happens before
ghb : Execution LabelTCG → Rel (Event LabelTCG) ℓzero
ghb ex = TransClosure (Ghbi ex)


record IsTCGConsistent (ex : Execution LabelTCG) : Set₁ where
  field
    ax-coherence  : Acyclic _≡_ (Coh ex)
    ax-atomicity  : Empty₂ (rmw ex ∩₂ (fre ex ⨾ coe ex))
    ax-global-ord : Irreflexive _≡_ (ghb ex)


-- # Helpers

f₌⇒f : {m : F-mode} {x : Event LabelTCG} → EvF₌ m x → EvF x
f₌⇒f ev-f₌ = ev-f is-f


disjoint-f/mode : {m₁ m₂ : F-mode} → m₁ ≢ m₂ → Disjoint₁ (EvF₌ m₁) (EvF₌ m₂)
disjoint-f/mode m₁≢m₂ _ (ev-f₌ , ev-f₌) = ⊥-elim (m₁≢m₂ refl)


coh-irreflexive : {ex : Execution LabelTCG} → WellFormed ex → Irreflexive _≡_ (Coh ex)
coh-irreflexive wf refl (coh-po-loc (po[xx] , _)) = po-irreflexive wf refl po[xx]
coh-irreflexive wf refl (coh-rf rf[xx])           = rf-irreflexive wf refl rf[xx]
coh-irreflexive wf refl (coh-fr fr[xx])           = fr-irreflexive wf refl fr[xx]
coh-irreflexive wf refl (coh-co co[xx])           = co-irreflexive wf refl co[xx]

cohˡ∈ex : Coh ˡ∈ex
cohˡ∈ex wf (coh-po-loc po-loc[xy]) = poˡ∈ex wf (proj₁ po-loc[xy])
cohˡ∈ex wf (coh-rf rf[xy])         = rfˡ∈ex wf rf[xy]
cohˡ∈ex wf (coh-fr fr[xy])         = frˡ∈ex wf fr[xy]
cohˡ∈ex wf (coh-co co[xy])         = coˡ∈ex wf co[xy]


ord-f⇒po :
  ∀ {p₁ : Pred (Event LabelTCG) ℓzero}
  → {f : F-mode}
  → {p₂ : Pred (Event LabelTCG) ℓzero}
  → {ex : Execution LabelTCG}
  → WellFormed ex
  → {x y : Event LabelTCG}
  → (⦗ p₁ ⦘ ⨾ po ex ⨾ ⦗ EvF₌ f ⦘ ⨾ po ex ⨾ ⦗ p₂ ⦘) x y
  → po ex x y
ord-f⇒po wf ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) =
  po-trans wf po[xz] po[zy]


ord⇒po : {ex : Execution LabelTCG}
  → WellFormed ex
  → {x y : Event LabelTCG}
  → Ord ex x y
    ----------------------
  → po ex x y
ord⇒po wf (ord-init ((refl , _) ⨾[ _ ]⨾ po[xy])) = po[xy]
ord⇒po wf (ord-rr rr[xy]) = ord-f⇒po wf rr[xy]
ord⇒po wf (ord-rw rw[xy]) = ord-f⇒po wf rw[xy]
ord⇒po wf (ord-rm rm[xy]) = ord-f⇒po wf rm[xy]
ord⇒po wf (ord-wr rw[xy]) = ord-f⇒po wf rw[xy]
ord⇒po wf (ord-ww ww[xy]) = ord-f⇒po wf ww[xy]
ord⇒po wf (ord-wm wm[xy]) = ord-f⇒po wf wm[xy]
ord⇒po wf (ord-mr mr[xy]) = ord-f⇒po wf mr[xy]
ord⇒po wf (ord-mw mw[xy]) = ord-f⇒po wf mw[xy]
ord⇒po wf (ord-mm mm[xy]) = ord-f⇒po wf mm[xy]
ord⇒po wf (ord-acq ((refl , _) ⨾[ _ ]⨾ po[xy]))       = po[xy]
ord⇒po wf (ord-rel (po[xy] ⨾[ _ ]⨾ (refl , _)))       = po[xy]
ord⇒po wf (ord-sc₁ (po[xy] ⨾[ _ ]⨾ (refl , _)))       = po[xy]
ord⇒po wf (ord-sc₂ ((refl , _) ⨾[ _ ]⨾ po[xy]))       = po[xy]
ord⇒po wf (ord-rmw-dom (po[xy] ⨾[ _ ]⨾ (refl , _)))   = po[xy]
ord⇒po wf (ord-rmw-codom ((refl , _) ⨾[ _ ]⨾ po[xy])) = po[xy]
ord⇒po wf (ord-w (po[xy] ⨾[ _ ]⨾ (refl , _)))         = po[xy]
ord⇒po wf (ord-r ((refl , _) ⨾[ _ ]⨾ po[xy]))         = po[xy]

ord⁺⇒po : {ex : Execution LabelTCG} → WellFormed ex → {x y : Event LabelTCG}
  → TransClosure (Ord ex) x y → po ex x y
ord⁺⇒po {ex} wf = ⁺-join-trans (po-trans wf) ∘ (⁺-map (λ τ → τ) (ord⇒po wf))


ord-predˡ : ∀ (ex : Execution LabelTCG) {x y : Event LabelTCG}
  → {P Q R : Pred (Event LabelTCG) ℓzero}
  → ( ⦗ P ⦘ ⨾ po ex ⨾ ⦗ Q ⦘ ⨾ po ex ⨾ ⦗ R ⦘ ) x y
  → P x
ord-predˡ _ ((refl , Px) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) = Px

ord-predʳ : ∀ (ex : Execution LabelTCG) {x y : Event LabelTCG}
  → {P Q R : Pred (Event LabelTCG) ℓzero}
  → ( ⦗ P ⦘ ⨾ po ex ⨾ ⦗ Q ⦘ ⨾ po ex ⨾ ⦗ R ⦘ ) x y
  → R y
ord-predʳ _ ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , Ry)) = Ry
  

ord-irreflexive : {ex : Execution LabelTCG} → WellFormed ex → Irreflexive _≡_ (Ord ex)
ord-irreflexive wf refl ord[xx] = po-irreflexive wf refl (ord⇒po wf ord[xx])

ghbi-irreflexive : {ex : Execution LabelTCG} → WellFormed ex → Irreflexive _≡_ (Ghbi ex)
ghbi-irreflexive wf refl (ghbi-ord ord[xx]) = ord-irreflexive wf refl ord[xx]
ghbi-irreflexive wf refl (ghbi-rfe rfe[xx]) = rf-irreflexive wf refl (proj₁ rfe[xx])
ghbi-irreflexive wf refl (ghbi-coe coe[xx]) = co-irreflexive wf refl (proj₁ coe[xx])
ghbi-irreflexive wf refl (ghbi-fre fre[xx]) = fr-irreflexive wf refl (proj₁ fre[xx])


ordˡ∈ex : Ord ˡ∈ex
ordˡ∈ex wf ord[xy] = poˡ∈ex wf (ord⇒po wf ord[xy])

ordʳ∈ex : Ord ʳ∈ex
ordʳ∈ex wf ord[xy] = poʳ∈ex wf (ord⇒po wf ord[xy])


ghbiˡ∈ex : Ghbi ˡ∈ex
ghbiˡ∈ex wf (ghbi-ord ord[xy]) = ordˡ∈ex wf ord[xy]
ghbiˡ∈ex wf (ghbi-rfe rfe[xy]) = rfˡ∈ex wf (proj₁ rfe[xy])
ghbiˡ∈ex wf (ghbi-coe coe[xy]) = coˡ∈ex wf (proj₁ coe[xy])
ghbiˡ∈ex wf (ghbi-fre fre[xy]) = frˡ∈ex wf (proj₁ fre[xy])

ghbiʳ∈ex : Ghbi ʳ∈ex
ghbiʳ∈ex wf (ghbi-ord ord[xy]) = ordʳ∈ex wf ord[xy]
ghbiʳ∈ex wf (ghbi-rfe rfe[xy]) = rfʳ∈ex wf (proj₁ rfe[xy])
ghbiʳ∈ex wf (ghbi-coe coe[xy]) = coʳ∈ex wf (proj₁ coe[xy])
ghbiʳ∈ex wf (ghbi-fre fre[xy]) = frʳ∈ex wf (proj₁ fre[xy])
