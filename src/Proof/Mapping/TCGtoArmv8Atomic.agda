{-# OPTIONS --safe #-}

open import Arch.General.Execution
open import Arch.Armv8
open import MapTCGtoArmv8Atomic


module Proof.Mapping.TCGtoArmv8Atomic
  (dst : Execution LabelArmv8) (dst-wf : WellFormed dst) (dst-ok : Armv8-TCGRestricted dst) where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
open import Arch.TCG
-- Local imports: Relations
open import Dodo.Binary
-- Local imports: Proofs
open import Proof.Mapping.TCGtoArmv8Atomic.Execution dst dst-wf dst-ok
open import Proof.Mapping.TCGtoArmv8Atomic.Consistent dst dst-wf dst-ok
open import Proof.Mapping.TCGtoArmv8Atomic.Mapping dst dst-wf dst-ok
import Proof.Mapping.Framework LabelTCG dst dst-wf as Δ


open Armv8-TCGRestricted
open IsArmv8Consistent
open Δ.Definitions δ
open Δ.WellFormed δ
open Δ.Behavior δ


proof-TCG⇒Armv8 :
  ∃[ src ]
    ( WellFormed src
    × IsTCGConsistent src
    × TCG⇒Armv8 src (a8 (consistent dst-ok))
    × behavior src ⇔₂ behavior dst
    )
proof-TCG⇒Armv8 =
  ( src
  , src-wf
  , src-consistent
  , mapping
  , proof-behavior
  )
