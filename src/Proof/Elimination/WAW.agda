{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.TCG using (LabelTCG)
open import TransformWAW using (WAW-Restricted)


-- | Read-after-Read elimination proof
module Proof.Elimination.WAW
  (dst : Execution LabelTCG) (dst-ok : WAW-Restricted dst) where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
open import Arch.General.Execution
open import Arch.TCG
-- Local imports: Relations
open import Dodo.Binary
-- Local imports: Proofs
open import TransformWAW using (WAWMapping)
open import Proof.Elimination.WAW.Execution dst dst-ok
open import Proof.Elimination.WAW.WellFormed dst dst-ok
open import Proof.Elimination.WAW.Consistent dst dst-ok
open import Proof.Elimination.WAW.Mapping dst dst-ok
open import Proof.Elimination.WAW.Behavior dst dst-ok
import Proof.Elimination.Framework dst dst-wf as Δ


open Δ.Definitions δ
open Arch.General.Execution


proof-WAW :
  ∃[ src ]
    ( WellFormed src
    × IsTCGConsistent src
    × WAWMapping src dst-ok
    × behavior src ⇔₂ behavior dst
    )
proof-WAW =
  ( src
  , src-wf
  , src-consistent
  , src-mapping
  , src-behavior
  )
