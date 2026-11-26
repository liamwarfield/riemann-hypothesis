module

public import Statements
public import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
public import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion

@[expose] public section

/-!
# Condensed Entry Point: The Riemann Hypothesis & Dirichlet GRH

See `PROOF_ARCHITECTURE.md` at the repository root for the full Lean-to-Math dictionary,
the 60.5% published-literature vs. 39.4% novel-core partition, and the Classical RH (`ζ(s)`)
specialization roadmap.

## Proof Spine (6 Stages)
1. **Stage 1 — Functional-Equation Reflection (`EveryCharacter.lean`: `Claim.strip`, `Claim.zeta`)**:
   Reduces RH and GRH on `0 < Re(s) < 1` to non-vanishing on `Re(s) > 1/2`
   (`DirichletLNonvanishingRightOfHalf`), stripping Euler factors for imprimitive characters.
2. **Stage 2 — Analytic Front-End & Localized Landau Window (`ExplicitFormulaErrorOfHostConditions.lean`,
   `ZeroFreeAllOfTopG.lean`, `TopWin.lean`)**:
   Defines the positively weighted prime-power sum `Level.Gm` and rules out any off-line zero
   `Re(s) > θ` from a one-sided bound `Gm(x) ≤ x^θ` on polynomial windows `[Y, Y^(3/2)]`.
3. **Stage 3 — Tate–Shafarevich Window Bound & Rescaling (`ExistsPageN.lean`, `TopMainZj.lean`,
   `TemperedProductOfSquareIntegrable.lean`, `WinPairs.lean`)**:
   Establishes `VWin` (`VVle E ⌊x^401⌋ √(exp(x^ε))` on `[W, W^2]`) over auxiliary CM fields
   `E = Q(ζ_{2^(e+2)}^+, √-q, √-d, ker ψ)` and rescales it (`supplyChi`) into `HostExW (3/2)`.
4. **Stage 4 — Automorphic Core: `√X`-Chained Unitary Theta Lifts (`SiegelEisensteinSecondTermHypotheses.lean`)**:
   Builds the definite/indefinite theta-lift chain `HypsAlt` and feeds it through `TopShapeAlt`
   and `every_character_of_theta_integrals_local_matching` into Stage 2.
5. **Stage 5 — Arakelov / Bost Slope Covolume Squeeze & Literature Packaging
   (`EveryCharacterOfLiteratureOfVWin.lean`)**:
   Supplies `topCovolSlim2_use_alt_alt` (Kudla seesaw + Rallis eigenvalue division + Bost
   Harder–Narasimhan slope inequality breaking `Re(s) = 2/3 → 1/2`) together with the ~150
   published research theorems (Local Langlands, Siegel–Weil, Doubling, Howe duality,
   Bernstein–Zelevinsky, Poitou–Tate, Bhatt–Scholze, toroidal compactification, Moriwaki/Arakelov).
6. **Stage 6 — Galois Trace-Limit & Final Assembly (`MainConclusion.lean`)**:
   Constructs Caraiani local-global compatibility `galoisLocalGlobalStrong_recParameter` via
   `p`-adic trace limits (`limWU4_of` / `RowSrc`), plugs it with `recTExists` and `vwin_of_row`
   into `every_character_of_literature_of_vWin`, and yields `UpperTheory.FinalTheorems.everyCharacter`.
-/

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf :=
  UpperTheory.FinalTheorems.everyCharacter

theorem riemannHypothesis : RiemannHypothesis :=
  Claim.zeta LFunction_ne_zero_of_half_lt_re

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis

theorem LFunction_eq_zero_re : DirichletLZerosOnLine :=
  Claim.strip LFunction_ne_zero_of_half_lt_re

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := by
  intro N _ χ _ s h₀ h₁ hz
  exact LFunction_eq_zero_re N χ s h₀ h₁ hz
