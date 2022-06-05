{-# OPTIONS --safe #-}

open import Arch.General.Execution
open import Arch.TCG
open import MapX86toTCG


module Proof.Mapping.X86toTCG
  (dst : Execution LabelTCG)
  (dst-wf : WellFormed dst)
  (dst-ok : TCG-X86Restricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
open import Arch.X86
-- Local imports: Relations
open import Dodo.Binary
-- Local imports: Proofs
open import Proof.Mapping.X86toTCG.Execution dst dst-wf dst-ok
open import Proof.Mapping.X86toTCG.Consistent dst dst-wf dst-ok
open import Proof.Mapping.X86toTCG.Mapping dst dst-wf dst-ok
import Proof.Mapping.Framework LabelX86 dst dst-wf as Δ


open TCG-X86Restricted
open IsTCGConsistent
open Δ.Definitions δ
open Δ.WellFormed δ
open Δ.Behavior δ


proof-X86⇒TCG :
  ∃[ src ]
    ( WellFormed src
    × IsX86Consistent src
    × X86⇒TCG src dst
    × behavior src ⇔₂ behavior dst
    )
proof-X86⇒TCG =
  ( src
  , src-wf
  , src-consistent
  , mapping
  , proof-behavior
  )
