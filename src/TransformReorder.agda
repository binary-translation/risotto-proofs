{-# OPTIONS --safe #-}

-- | Reorders one event with one other event
--
-- > a ∘ b  →  b ∘ a
module TransformReorder where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; proj₁)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (_∈_)
-- Library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.TCG


open Execution


-- # Definitions

--
-- The table of valid reorders specified by this description. ("X" means valid)
-- Note that the holes are covered by the rules in `ReorderRestricted`.
--
-- Rᵣ and Wᵣ are /non-atomic/ (i.e., "regular") read and write events, respectively.
--
-- a \ b | Rᵣ    | Wᵣ    | F_RM  | F_WW  | F_SC
-- ------+-------+-------+-------+-------+-----
-- Rᵣ    | X     | X     |       | X     |  
-- Wᵣ    | X     | X     | X     |       |  
-- F_RM  |       |       | X     | X     | X
-- F_WW  | X     |       | X     | X     | X
-- F_SC  |       |       | X     | X     | X
--


-- | A proof stating the /target/ execution could only have been generated from a
-- program that is mapped through the reordering transformation.
--
--
-- # Order
--
-- Note that the /target/ order is:
--
-- > ev₁  -pi-  ev₂
--
-- While the /source/ order is:
--
-- > ev₂  -pi-  ev₁
record ReorderRestricted (ex : Execution LabelTCG) : Set₁ where
  field
    consistent : IsTCGConsistent ex
    wellformed : WellFormed ex
    
    ev₁ : Event LabelTCG
    ev₂ : Event LabelTCG

    ¬same-loc : ¬ SameLoc ev₁ ev₂
    ¬init₁ : ¬ EvInit ev₁
    ¬init₂ : ¬ EvInit ev₂

    ¬skip₁ : ¬ EvSkip ev₁
    ¬skip₂ : ¬ EvSkip ev₂

    ¬ra₁ : ¬ (EvRₜ trmw ev₁)
    ¬wa₁ : ¬ (EvWₜ trmw ev₁)
    ¬ra₂ : ¬ (EvRₜ trmw ev₂)
    ¬wa₂ : ¬ (EvWₜ trmw ev₂)
    

    -- Note that `ev₂`-`ev₁` is the /order in the source/.
    -- While `ev₁`-`ev₂` is the /order in the target/.

    -- The rules below specify which pairs /cannot/ reorder.
    -- Any pairs /not/ covered by these, /can reorder/.

    pord-rrˡ : ¬ (EvR ev₂ × EvF₌ RR ev₁)
    pord-rrʳ : ¬ (EvF₌ RR ev₂ × EvR ev₁)
    
    pord-rwˡ : ¬ (EvR ev₂ × EvF₌ RW ev₁)
    pord-rwʳ : ¬ (EvF₌ RW ev₂ × EvW ev₁)
    
    pord-rmˡ : ¬ (EvR ev₂ × EvF₌ RM ev₁)
    pord-rmʳ : ¬ (EvF₌ RM ev₂ × EvRW ev₁)
    

    pord-wrˡ : ¬ (EvW ev₂ × EvF₌ WR ev₁)
    pord-wrʳ : ¬ (EvF₌ WR ev₂ × EvR ev₁)
    
    pord-wwˡ : ¬ (EvW ev₂ × EvF₌ WW ev₁)
    pord-wwʳ : ¬ (EvF₌ WW ev₂ × EvW ev₁)
    
    pord-wmˡ : ¬ (EvW ev₂ × EvF₌ WM ev₁)
    pord-wmʳ : ¬ (EvF₌ WM ev₂ × EvRW ev₁)


    pord-mrˡ : ¬ (EvRW ev₂ × EvF₌ MR ev₁)
    pord-mrʳ : ¬ (EvF₌ MR ev₂ × EvR ev₁)
    
    pord-mwˡ : ¬ (EvRW ev₂ × EvF₌ MW ev₁)
    pord-mwʳ : ¬ (EvF₌ MW ev₂ × EvW ev₁)
    
    pord-mmˡ : ¬ (EvRW ev₂ × EvF₌ MM ev₁)
    pord-mmʳ : ¬ (EvF₌ MM ev₂ × EvRW ev₁)
    

    pord-scˡ : ¬ (EvRW ev₂ × EvF₌ SC ev₁)
    pord-scʳ : ¬ (EvF₌ SC ev₂ × EvRW ev₁)

    pi[12]ᵗ : po-imm ex ev₁ ev₂


-- | Relates the events in the source and target executions, following the
-- transformation on the instructions.
--
-- They are mostly identical, except for the reordered pair.
record ReordersTo (src : Execution LabelTCG) {dst : Execution LabelTCG} (dst-ok : ReorderRestricted dst) : Set₁ where
  open ReorderRestricted dst-ok
  
  field
    events-preserved : events src ⇔₁ events dst
    co-preserved     : co src  ⇔₂ co dst
    rf-preserved     : rf src  ⇔₂ rf dst
    rmw-preserved    : rmw src ⇔₂ rmw dst

    po-preserved⇒ : ∀ {x y : Event LabelTCG} → ¬ (x ≡ ev₂ × y ≡ ev₁) → po src x y → po dst x y
    po-preserved⇐ : ∀ {x y : Event LabelTCG} → ¬ (x ≡ ev₁ × y ≡ ev₂) → po dst x y → po src x y


-- # Operations

-- | Helpers. The definitions and properties are derived from `ReorderRestricted` alone.
module Extra {ex : Execution LabelTCG} (δ : ReorderRestricted ex) where

  open ReorderRestricted δ

  po[12]ᵗ : po ex ev₁ ev₂
  po[12]ᵗ = proj₁ pi[12]ᵗ
    
  ev₁∈poˡ : ev₁ ∈ dom (po ex)
  ev₁∈poˡ = take-dom (po ex) po[12]ᵗ

  ev₂∈poʳ : ev₂ ∈ codom (po ex)
  ev₂∈poʳ = take-codom (po ex) po[12]ᵗ

  ev₁∈po : ev₁ ∈ udr (po ex)
  ev₁∈po = take-udrˡ (po ex) po[12]ᵗ

  ev₂∈po : ev₂ ∈ udr (po ex)
  ev₂∈po = take-udrʳ (po ex) po[12]ᵗ

  ev₁∈ex : ev₁ ∈ events ex
  ev₁∈ex = poˡ∈ex wellformed po[12]ᵗ

  ev₂∈ex : ev₂ ∈ events ex
  ev₂∈ex = poʳ∈ex wellformed po[12]ᵗ

  ¬po[21]ᵗ : ¬ po ex ev₂ ev₁
  ¬po[21]ᵗ po[21] =
    let po[22] = po-trans wellformed po[21] po[12]ᵗ
    in po-irreflexive wellformed refl po[22]
