{-# OPTIONS --safe #-}


-- | The Armv8 model as obtained from the "Armed Cats" paper,
-- with our proposed change to the `amo` case in the `bob` relation.
module Arch.Armv8 where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) renaming (sym to ≡-sym)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Level using (Level; _⊔_) renaming (zero to ℓzero; suc to ℓsuc)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty)
open import Relation.Binary using (Rel; Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Helpers
open import Arch.General.Event
open import Arch.General.Properties using (tag-eq-dec; ev-eq-dec)
open import Arch.General.Execution


open Event
open Execution


-- Notes on model:
--
-- RMW creates R and W events
-- RMW_A creates A and W events
-- RMW_L creates A and L events

data F-mode : Set where
  F-full : F-mode
  F-ld   : F-mode
  F-st   : F-mode

data LabelArmv8 : Set where
  lab-r : Tag → Location → Value → LabelArmv8
  lab-a : Tag → Location → Value → LabelArmv8 -- ^ acquire read
  lab-q : Location → Value → LabelArmv8 -- ^ acquirePC read (always tmov)
  
  lab-w : Tag → Location → Value → LabelArmv8 -- ^ write
  lab-l : Tag → Location → Value → LabelArmv8 -- ^ release write

  lab-f   : F-mode → LabelArmv8 -- ^ fence
  lab-isb : LabelArmv8 -- ^ ISB (control) fence


data LabR : LabelArmv8 → Set where
  is-r : ∀ {tag : Tag} {loc : Location} {val : Value} → LabR (lab-r tag loc val)
  is-a : ∀ {tag : Tag} {loc : Location} {val : Value} → LabR (lab-a tag loc val)
  is-q : ∀ {loc : Location} {val : Value} → LabR (lab-q loc val)

data LabW : LabelArmv8 → Set where
  is-w : ∀ {tag : Tag} {loc : Location} {val : Value} → LabW (lab-w tag loc val)
  is-l : ∀ {tag : Tag} {loc : Location} {val : Value} → LabW (lab-l tag loc val)

data LabF : LabelArmv8 → Set where
  is-f   : ∀ {mode : F-mode} → LabF (lab-f mode)
  is-isb : LabF lab-isb


-- # Lemmas/Properties

private

  labs-xopt : XOptPred₃ LabR LabW LabF
  labs-xopt (lab-r _ _ _) = xopt₁ is-r  (λ()) (λ())
  labs-xopt (lab-a _ _ _) = xopt₁ is-a  (λ()) (λ())
  labs-xopt (lab-q _ _)   = xopt₁ is-q  (λ()) (λ())
  labs-xopt (lab-w _ _ _) = xopt₂ (λ()) is-w  (λ())
  labs-xopt (lab-l _ _ _) = xopt₂ (λ()) is-l  (λ())
  labs-xopt (lab-f _)     = xopt₃ (λ()) (λ()) is-f
  labs-xopt lab-isb       = xopt₃ (λ()) (λ()) is-isb

  r-unique : UniquePred LabR
  r-unique _ is-r is-r = refl
  r-unique _ is-a is-a = refl
  r-unique _ is-q is-q = refl

  w-unique : UniquePred LabW
  w-unique _ is-w is-w = refl
  w-unique _ is-l is-l = refl

  f-unique : UniquePred LabF
  f-unique _ is-f   is-f   = refl
  f-unique _ is-isb is-isb = refl

  r-tag : {lab : LabelArmv8} → LabR lab → Tag
  r-tag {lab-r tag _ _} is-r = tag
  r-tag {lab-a tag _ _} is-a = tag
  r-tag {lab-q _ _}     is-q = tmov

  w-tag : {lab : LabelArmv8} → LabW lab → Tag
  w-tag {lab-w tag _ _} is-w = tag
  w-tag {lab-l tag _ _} is-l = tag

  r-loc : {lab : LabelArmv8} → LabR lab → Location
  r-loc {lab-r _ loc _} is-r = loc
  r-loc {lab-a _ loc _} is-a = loc
  r-loc {lab-q loc _}   is-q = loc

  r-val : {lab : LabelArmv8} → LabR lab → Value
  r-val {lab-r _ _ val} is-r = val
  r-val {lab-a _ _ val} is-a = val
  r-val {lab-q _ val}   is-q = val

  w-loc : {lab : LabelArmv8} → LabW lab → Location
  w-loc {lab-w _ loc _} is-w = loc
  w-loc {lab-l _ loc _} is-l = loc

  w-val : {lab : LabelArmv8} → LabW lab → Value
  w-val {lab-w _ _ val} is-w = val
  w-val {lab-l _ _ val} is-l = val

  fence-dec : DecRel (_≡_ {_} {F-mode})
  fence-dec F-full F-full = yes refl
  fence-dec F-ld   F-ld   = yes refl
  fence-dec F-st   F-st   = yes refl
  -- false cases
  fence-dec F-full F-ld   = no (λ ())
  fence-dec F-full F-st   = no (λ())
  fence-dec F-ld   F-full = no (λ())
  fence-dec F-ld   F-st   = no (λ())
  fence-dec F-st   F-full = no (λ())
  fence-dec F-st   F-ld   = no (λ())

  lab-eq-dec : DecRel (_≡_ {_} {LabelArmv8})
  lab-eq-dec (lab-r tag₁ loc₁ val₁) (lab-r tag₂ loc₂ val₂) =
    cong₃-dec lab-r (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-a tag₁ loc₁ val₁) (lab-a tag₂ loc₂ val₂) =
    cong₃-dec lab-a (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-q loc₁ val₁) (lab-q loc₂ val₂) =
    cong₂-dec lab-q (λ{refl → refl}) (λ{refl → refl}) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-w tag₁ loc₁ val₁) (lab-w tag₂ loc₂ val₂) =
    cong₃-dec lab-w (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-l tag₁ loc₁ val₁) (lab-l tag₂ loc₂ val₂) =
    cong₃-dec lab-l (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-f m₁) (lab-f m₂) = cong-dec lab-f (λ{refl → refl}) (fence-dec m₁ m₂)
  lab-eq-dec lab-isb lab-isb = yes refl
  -- false cases
  lab-eq-dec (lab-r _ _ _) (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-r _ _ _) (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-r _ _ _) (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-r _ _ _) (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-r _ _ _) (lab-f _)     = no (λ())
  lab-eq-dec (lab-r _ _ _) lab-isb       = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-f _)     = no (λ())
  lab-eq-dec (lab-a _ _ _) lab-isb       = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-f _)     = no (λ())
  lab-eq-dec (lab-q _ _)   lab-isb       = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-f _)     = no (λ())
  lab-eq-dec (lab-w _ _ _) lab-isb       = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-f _)     = no (λ())
  lab-eq-dec (lab-l _ _ _) lab-isb       = no (λ())
  lab-eq-dec (lab-f _)     (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-f _)     (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-f _)     (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-f _)     (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-f _)     (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-f _)     lab-isb       = no (λ())
  lab-eq-dec lab-isb       (lab-r _ _ _) = no (λ())
  lab-eq-dec lab-isb       (lab-a _ _ _) = no (λ())
  lab-eq-dec lab-isb       (lab-q _ _)   = no (λ())
  lab-eq-dec lab-isb       (lab-w _ _ _) = no (λ())
  lab-eq-dec lab-isb       (lab-l _ _ _) = no (λ())
  lab-eq-dec lab-isb       (lab-f _)     = no (λ())


instance
  LabelArmv8-ok : LabelClass LabelArmv8
  LabelArmv8-ok =
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


-- release write
data EvL : Event LabelArmv8 → Set where
  ev-l : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → EvL (event uid tid (lab-l tag loc val))

-- acquire read
data EvA : Event LabelArmv8 → Set where
  ev-a : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → EvA (event uid tid (lab-a tag loc val))

-- release write indexed by tag
data EvLₜ (tag : Tag) : Event LabelArmv8 → Set where
  ev-l : {uid : UniqueId} {tid : ThreadId} {loc : Location} {val : Value} → EvLₜ tag (event uid tid (lab-l tag loc val))

-- acquire read indexed by tag
data EvAₜ (tag : Tag) : Event LabelArmv8 → Set where
  ev-a : {uid : UniqueId} {tid : ThreadId} {loc : Location} {val : Value} → EvAₜ tag (event uid tid (lab-a tag loc val))

-- acquirePC read
data EvQ : Event LabelArmv8 → Set where
  ev-q : {uid : UniqueId} {tid : ThreadId} {loc : Location} {val : Value} → EvQ (event uid tid (lab-q loc val))

data EvISB : Event LabelArmv8 → Set where
  ev-isb : {uid : UniqueId} {tid : ThreadId} → EvISB (event uid tid lab-isb)
  
data EvA₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelArmv8 → Set where
  ev-a₌ : {uid : UniqueId} {tid : ThreadId} → EvA₌ tag loc val (event uid tid (lab-a tag loc val))
  
data EvL₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelArmv8 → Set where
  ev-l₌ : {uid : UniqueId} {tid : ThreadId} → EvL₌ tag loc val (event uid tid (lab-l tag loc val))
  
data EvR₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelArmv8 → Set where
  ev-r₌ : {uid : UniqueId} {tid : ThreadId} → EvR₌ tag loc val (event uid tid (lab-r tag loc val))

data EvW₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelArmv8 → Set where
  ev-w₌ : {uid : UniqueId} {tid : ThreadId} → EvW₌ tag loc val (event uid tid (lab-w tag loc val))

data EvF₌ (mode : F-mode) : Event LabelArmv8 → Set where
  ev-f₌ : {uid : UniqueId} {tid : ThreadId} → EvF₌ mode (event uid tid (lab-f mode))


record Armv8Execution (ex : Execution LabelArmv8) : Set₁ where
  field
    -- # Armv8-specific relations
    
    data₋ : Rel (Event LabelArmv8) ℓzero -- called `data₋`, because `data` is a keyword
    addr  : Rel (Event LabelArmv8) ℓzero
    ctrl  : Rel (Event LabelArmv8) ℓzero

    -- rmw relation that is created by single-instruction RMWs
    amo  : Rel (Event LabelArmv8) ℓzero
    -- rmw relation that is created by load-linked/store-conditional RMWs.
    lxsx : Rel (Event LabelArmv8) ℓzero


open Armv8Execution


InterveningWrite : Rel (Event LabelArmv8) ℓzero → Rel (Event LabelArmv8) ℓzero
InterveningWrite R = R ⨾ ⦗ EvW ⦘ ⨾ R

-- Local read successor
lrs : (ex : Execution LabelArmv8) → Rel (Event LabelArmv8) ℓzero
lrs ex = ⦗ EvW ⦘ ⨾ (po-loc ex \₂ InterveningWrite (po-loc ex)) ⨾ ⦗ EvR ⦘

-- Local write successor
lws : (ex : Execution LabelArmv8) → Rel (Event LabelArmv8) ℓzero
lws ex = po-loc ex ⨾ ⦗ EvW ⦘

-- Coherence after
--
-- Intuitively, a write is coherence-after another event, if it overwrites its value.
data Ca (ex : Execution LabelArmv8) (x y : Event LabelArmv8) : Set where
  ca-co : co ex x y → Ca ex x y -- w × w
  ca-fr : fr ex x y → Ca ex x y -- r × w . rf⁻¹;co

-- Observed by
data Obs (ex : Execution LabelArmv8) (x y : Event LabelArmv8) : Set where
  obs-rfe : rfe ex x y → Obs ex x y
  obs-coe : coe ex x y → Obs ex x y
  obs-fre : fre ex x y → Obs ex x y

-- Barrier-ordered-before
--
-- Consider this the union over all relations in it's constructors.
--
-- This data structure is much easier to handle than taking _∪₂_ over all,
-- as constructing (or pattern-matching on) an instance looks like: inj₁ (inj₁ (inj₁ ...)))
data Bob {ex : Execution LabelArmv8} (a8 : Armv8Execution ex) (x y : Event LabelArmv8) : Set where
  bob-f    : ( po ex ⨾ ⦗ EvF₌ F-full ⦘ ⨾ po ex )                   x y → Bob a8 x y
  bob-la   : ( ⦗ EvL ⦘ ⨾ po ex ⨾ ⦗ EvA ⦘ )                         x y → Bob a8 x y
  bob-fld  : ( ⦗ EvR ⦘ ⨾ po ex ⨾ ⦗ EvF₌ F-ld ⦘ ⨾ po ex )           x y → Bob a8 x y
  bob-fst  : ( ⦗ EvW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ F-st ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ ) x y → Bob a8 x y  
  bob-acq  : ( ⦗ EvA ∪₁ EvQ ⦘ ⨾ po ex )                            x y → Bob a8 x y
  bob-rel  : ( po ex ⨾ ⦗ EvL ⦘ )                                   x y → Bob a8 x y
  -- Our proposed `amo` rules
  bob-amoˡ : ( po ex ⨾ ⦗ dom ( ⦗ EvA ⦘ ⨾ amo a8 ⨾ ⦗ EvL ⦘ ) ⦘ )    x y → Bob a8 x y
  bob-amoʳ : ( ⦗ codom ( ⦗ EvA ⦘ ⨾ amo a8 ⨾ ⦗ EvL ⦘ ) ⦘ ⨾ po ex )  x y → Bob a8 x y

-- Data ordered before
data Dob {ex : Execution LabelArmv8} (a8 : Armv8Execution ex) (x y : Event LabelArmv8) : Set where
  dob-addr    : addr a8                                                              x y → Dob a8 x y
  dob-data    : data₋ a8                                                             x y → Dob a8 x y
  dob-ctrl    : ( ctrl a8 ⨾ ⦗ EvW ⦘ )                                                x y → Dob a8 x y
  dob-isb     : ( ( ctrl a8 ∪₂ ( addr a8 ⨾ po ex ) ) ⨾ ⦗ EvISB ⦘ ⨾ po ex ⨾ ⦗ EvR ⦘ ) x y → Dob a8 x y
  dob-addr-po : ( addr a8 ⨾ po ex ⨾ ⦗ EvW ⦘ )                                        x y → Dob a8 x y
  dob-lrs     : ( ( addr a8 ∪₂ data₋ a8 ) ⨾ lrs ex )                                 x y → Dob a8 x y

-- Atomic ordered before
data Aob (ex : Execution LabelArmv8) (x y : Event LabelArmv8) : Set where
  aob-rmw : rmw ex                                           x y → Aob ex x y
  aob-lrs : ( ⦗ codom (rmw ex) ⦘ ⨾ lrs ex ⨾ ⦗ EvA ∪₁ EvQ ⦘ ) x y → Aob ex x y

-- Immediate Locally-ordered-before
data Lobi {ex : Execution LabelArmv8} (a8 : Armv8Execution ex) (x y : Event LabelArmv8) : Set where
  lobi-init : ( ⦗ EvInit ⦘ ⨾ po ex ) x y → Lobi a8 x y
  lobi-lws  : lws ex                 x y → Lobi a8 x y
  lobi-dob  : Dob a8                 x y → Lobi a8 x y
  lobi-aob  : Aob ex                 x y → Lobi a8 x y
  lobi-bob  : Bob a8                 x y → Lobi a8 x y

-- Locally-ordered-before
Lob : {ex : Execution LabelArmv8} (a8 : Armv8Execution ex) → Rel (Event LabelArmv8) ℓzero
Lob a8 = TransClosure (Lobi a8)

-- Immediate Ordered before
data Obi {ex : Execution LabelArmv8} (a8 : Armv8Execution ex) (x y : Event LabelArmv8) : Set where
  obi-obs : Obs ex x y → Obi a8 x y
  obi-lob : Lob a8 x y → Obi a8 x y

-- Ordered before
Ob : {ex : Execution LabelArmv8} (a8 : Armv8Execution ex) → Rel (Event LabelArmv8) ℓzero
Ob a8 = TransClosure (Obi a8)


record IsArmv8Consistent (ex : Execution LabelArmv8) : Set₁ where
  field
    a8 : Armv8Execution ex
    
    -- # Armv8-specific relations
    
    -- The `rmw` relation is obtained either by atomic read-modify-write instructions (amo)
    -- or load-linked/store-conditional instruction pairs.
    amo-lxsx-def : rmw ex ⇔₂ amo a8 ∪₂ lxsx a8

    data-def₁ : data₋ a8 ⊆₂ EvR ×₂ EvW
    data-def₂ : data₋ a8 ⊆₂ po ex
    addr-def₁ : addr a8  ⊆₂ EvR ×₂ ( EvR ∪₁ EvW )
    addr-def₂ : data₋ a8 ⊆₂ po ex
    ctrl-def₁ : ctrl a8  ⊆₂ EvR ×₂ EvE
    ctrl-def₂ : ctrl a8  ⊆₂ po ex
    ctrl-def₃ : ( ctrl a8 ⨾ po ex ) ⊆₂ ctrl a8

    -- # Armv8-specific consistency constraints

    ax-coherence  : Acyclic _≡_ ( po-loc ex ∪₂ Ca ex ∪₂ rf ex ) -- "Internal Visibility"
    ax-atomicity  : Empty₂ ( rmw ex ∩₂ (fre ex ⨾ coe ex) )
    ax-global-obs : Irreflexive _≡_ (Ob a8) -- "External Visibility"

open IsArmv8Consistent


-- # Helpers

amo-def : {ex : Execution LabelArmv8} (ex-ok : IsArmv8Consistent ex)
  → amo (a8 ex-ok) ⊆₂ rmw ex
amo-def = ∪₂-elimʳ-⊆₂ ∘ ⇔₂-to-⊇₂ ∘ amo-lxsx-def

lxsx-def : {ex : Execution LabelArmv8} (ex-ok : IsArmv8Consistent ex)
  → lxsx (a8 ex-ok) ⊆₂ rmw ex
lxsx-def = ∪₂-elimˡ-⊆₂ ∘ ⇔₂-to-⊇₂ ∘ amo-lxsx-def
