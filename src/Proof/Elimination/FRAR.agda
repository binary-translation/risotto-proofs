{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.TCG using (LabelTCG)
open import TransformFRAR using (FRAR-Restricted)


-- | Read-after-Read with fence elimination proof
module Proof.Elimination.FRAR
  (dst : Execution LabelTCG) (dst-ok : FRAR-Restricted dst) where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
open import Arch.General.Execution
open import Arch.TCG
-- Local imports: Relations
open import Dodo.Binary
-- Local imports: Proofs
open import TransformFRAR using (FRARMapping)
open import Proof.Elimination.FRAR.Execution dst dst-ok
open import Proof.Elimination.FRAR.WellFormed dst dst-ok
open import Proof.Elimination.FRAR.Consistent dst dst-ok
open import Proof.Elimination.FRAR.Mapping dst dst-ok
open import Proof.Elimination.FRAR.Behavior dst dst-ok
import Proof.Elimination.Framework dst dst-wf as Δ


open Δ.Definitions δ
open Arch.General.Execution


proof-FRAR :
  ∃[ src ]
    ( WellFormed src
    × IsTCGConsistent src
    × FRARMapping src dst-ok
    × behavior src ⇔₂ behavior dst
    )
proof-FRAR =
  ( src
  , src-wf
  , src-consistent
  , src-mapping
  , src-behavior
  )
