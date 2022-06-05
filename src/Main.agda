{-# OPTIONS --safe #-}


module Main where


--
-- + Proof intuition
--
-- All proofs follow a similar structure. We map a /source program/ Pₛ to a
-- /target program/ Pₜ . So we have:
--
-- > Pₛ  == maps to ==>  Pₜ
--
-- Of course, Pₜ needs to be /correct/. That is, it should behave similarly to Pₛ.
--
-- When Pₛ is a /concurrent program/, it can display many different behaviors,
-- which depend on thread-interleaving and CPU intricacies, such as instruction
-- reordering. So, we need to ensure Pₜ is /correct for all possible behaviors/.
-- That is:
--
-- " Every behavior of Pₜ must be justified by a corresponding behavior of Pₛ "
--
-- We thus model individual executions, which we denote by Xₛ and Xₜ,
-- for Pₛ and Pₜ, respectively. Thus we get:
--
-- > Xₛ == justifies ==> Xₜ
-- > 
-- > ↑                   ↑
-- >
-- > Pₛ === maps to ===> Pₜ
--
-- So, for /every execution/ Xₜ of Pₜ, we need to find a /corresponding execution/
-- Xₛ of Pₛ. If that is possible, the mapping is /correct/. Intuitively:
--
-- > ∀ Xₜ . { is-ok(Xₜ) → ∃ Xₛ . ( is-ok(Xₛ)  ∧  behavior(Xₛ) ≡ behavior(Xₜ) ) }
--
--
--
-- + Proof specifics
--
-- In the proofs, we only model the executions. We /specify/ constraints on the target
-- execution Xₜ:
--
-- * /Events follow syntax/ - For instance, if from the mapping we know every `LD`
--   /instruction/ is followed by a `F_RM` /instruction/, then in the execution we
--   know every Read /event/ is followed by a F_RM /event/.
--
-- * /Xₜ is wellformed/ - Wellformedness declares an execution "makes sense". That is,
--   for instance, every Read event reads from exactly one Write event. Only
--   executions that "make sense" can actually be observed from Pₜ.
--
-- * /Xₜ is consistent/ - Consistency declares that a behavior is observable
--   within a particular architecture's memory model. That is, the execution must
--   satisfy some architecture-specific constraints, which restrict the observable
--   behavior of Pₜ.
--
-- Note that we are /given/ such an execution Xₜ, for which we /construct/ a
-- corresponding execution Xₛ. We then demonstrate:
--
-- * /Xₛ is wellformed/ - We demonstrate Xₛ also "makes sense".
--
-- * /Xₛ is consistent/ - We demonstrate Xₛ can be observed in the source
--   architecture.
--
-- * /Xₛ "maps to" Xₜ/ - We demonstrate that the events in Xₛ map to the
--   event in Xₜ, following the syntactic mapping from Pₛ to Pₜ.
--
-- * /Xₛ "behaves like" Xₜ/ - We demonstrate that, upon termination, the state of
--   memory is identical for Xₛ and Xₜ.
--
-- And that is it. If such an execution Xₛ of Pₛ exists for every execution Xₜ of
-- Pₜ, then the corresponding mapping is correct. All the proofs follow that
-- structure.
--


-- # Architecture specifications

open import Arch.General.Execution
open import Arch.X86
-- The "Armed Cats" Armv8 model, with our proposed chance
open import Arch.Armv8
open import Arch.TCG


-- # Architecture mapping proofs

-- ## x86 ⇒ TCG
import MapX86toTCG                        -- specification
import Proof.Mapping.X86toTCG             -- proof

-- ## TCG ⇒ Armv8, /without/ atomic Compare-And-Swap instruction
import MapTCGtoArmv8NonAtomic             -- specification
import Proof.Mapping.TCGtoArmv8NonAtomic  -- proof

-- ## TCG ⇒ Armv8, /with/ atomic Compare-And-Swap instruction
import MapTCGtoArmv8Atomic                -- specification
import Proof.Mapping.TCGtoArmv8Atomic     -- proof


-- # Elimination Transformations on TCG

-- ## RAR: Read-after-Read
import TransformRAR           -- specification
import Proof.Elimination.RAR  -- proof

-- ## WAW: Write-after-Write
import TransformWAW           -- specification
import Proof.Elimination.WAW  -- proof

-- ## RAW: Read-after-Write
import TransformRAW           -- specification
import Proof.Elimination.RAW  -- proof

-- ## FRAR: Read-after-Write with Fence
import TransformFRAR          -- specification
import Proof.Elimination.FRAR -- proof

-- ## FWAW: Read-after-Write with Fence
import TransformFWAW          -- specification
import Proof.Elimination.FWAW -- proof

-- ## FRAW: Read-after-Write with Fence
import TransformFRAW          -- specification
import Proof.Elimination.FRAW -- proof


-- # Reordering Transformations on TCG

import TransformReorder     -- specification
import Proof.Reorder.Single -- proof
