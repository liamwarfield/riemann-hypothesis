module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.gr_aff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationViaTruncation

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationViaTruncationStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_filtration_via_truncation : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (s : ℕ)
    (hs : ∀ α, U.d α < s) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (j : ℕ), Function.Bijective (resK q (KS q s 𝒱) j) ∧
      ∀ r ≤ s, ∀ x : HdR q j, x ∈ FilR q j r ↔ quoK q (KS q s 𝒱) r j x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KIso.k_iso | exact GlobalTheory.CompanionTheory.KIso.k_iso | (intros; apply GlobalTheory.CompanionTheory.KIso.k_iso <;> assumption)
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem k_iso_pf : KH.KIso :=
  GlobalTheory.T.hodge_filtration_via_truncation locGr_h locVan_h polyTf_h globSerreSt_h globVanSt_h gr_aff_pf

end CrystallineSemistableComparison.Pb
