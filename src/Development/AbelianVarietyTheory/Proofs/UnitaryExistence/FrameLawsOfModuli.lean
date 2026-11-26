module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Exist

theorem frame_laws_of_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (ChartCoverF Xo c ∧ FrChartF Xo c ∧ BorChartF Xo c ∧ IntLatU Xo c ∧ AllTest Xo c ∧ ∀ σ : c.F →+* ℂ, BCEx Xo c σ ∧ WtC Xo c σ) ∧ (1 ≤ Dw.p + Dw.q → Nonempty Xo.X ∧ AlgPtLa Xo c ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrExt Xo c ∧ IntAll Xo c)) := by
  intro E _ _ _ H Dw l Xo c
  have hL := GlobalTheory.lawsFieldsSeparately
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := hL.2.1
  have hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hC := GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hN : N1c := GlobalTheory.closing_of_abelianSchemeLaws
  refine ⟨⟨hC, frChartF_of hC, borChartF_of_cover hC, GlobalTheory.Frames.intLatU_holds E H Dw l Xo c, hA,
    fun σ => ⟨fun p y ψ => ?_, wtC_of (borChartF_of_cover hC) hA σ⟩⟩, fun hpq => ⟨?_,
    GlobalTheory.algPtLa_moduli hN E H Dw l Xo c hpq, fun hg => ⟨?_, ?_⟩⟩⟩
  · exact GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ ψ y
  · obtain ⟨L, _, _, j, x, -⟩ := GlobalTheory.moduli_exists_numberField_point hN E H Dw l Xo c hpq
    exact ⟨x (IsLocalRing.closedPoint L)⟩
  · exact GlobalTheory.Exist.intFrExt_of_good GlobalTheory.partI_closed GlobalTheory.Moduli.moduli_scheme_exists hS hT
      E H Dw l Xo c hpq hg
  · exact (Formalism.L2.PjFree.intAll_iff Xo c).1 (GlobalTheory.IntegralFrames.intAll GlobalTheory.partI_closed
      GlobalTheory.Moduli.moduli_scheme_exists hS hT E H Dw l Xo c hpq hg)

end GlobalTheory.Exist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.UnifFamily

theorem dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r) :
    X.dom.Nonempty := by
  choose P _ hP using X.signature
  exact ⟨fun τ => P τ, ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm
    X.Gm_herm).2.1 (fun τ => P τ) hP).1⟩

theorem exists_unf_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∃ U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ) ∧ Nonempty (U σ).Comp ∧ (∀ k, ((U σ).X k).dom.Nonempty) ∧ (∀ k la γ, ((U σ).X k).χ la γ = 1) ∧ ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ Formalism.L2.PjFree.CuspFD Xo c U ∧ Formalism.L2.PjFree.CuspMul Xo c U ∧ Formalism.L2.PjFree.SupDef Xo c U ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → Formalism.L2.PjFree.regular₂ Xo c U) := by
  intro E _ _ _ H Dw l Xo c hpq
  classical
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  have key : ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Formalism.L2.PjFree.GoodEmb c σ →
      Formalism.L2.PjFree.IsUnf U ∧ Nonempty U.Comp ∧ (∀ k, (U.X k).dom.Nonempty) ∧
      (∀ k la γ, (U.X k).χ la γ = 1) ∧
      ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) := by
    intro σ
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · obtain ⟨U, h1, h2, h3, -, h5, -⟩ := GlobalTheory.T.exists_frameUniformisation_prescribedSpace GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.T.hasse_norm_theorem_quadratic_extension hB hT
        E H Dw l Xo c σ (Dw.p + Dw.q) ξ₀ Gm φ hpq hσ hcc him hφ
      exact ⟨U, fun _ => ⟨h1, h2, fun k => dom_nonempty _, h3, h5⟩⟩
    · obtain ⟨U, -⟩ := GlobalTheory.T.exists_uniformisationData_nonempty_component E H Dw l Xo c hpq σ
      exact ⟨U, fun h => absurd h hσ⟩
  choose U hU using key
  have h₀ : Formalism.L2.PjFree.GoodEmb c (c.F.val : c.F →+* ℂ) := by
    exact rfl
  refine ⟨U, hU, GlobalTheory.T.cuspForms_dominantWeight_finiteDimensional hB E H Dw l Xo c _ U _ h₀ (hU _ h₀).1,
    GlobalTheory.CuspProduct.cuspMul_holds E H Dw l Xo c _ U,
    GlobalTheory.T.supNorm_definite_on_cuspForms_goodEmbedding E H Dw l Xo c _ U (fun σ h => (hU σ h).1), fun hg => ?_⟩
  exact (GlobalTheory.Reg.sCharts_and_transfer_of_good_level GlobalTheory.T.compactifiedModuli_partOne GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level E H Dw l Xo c hpq hg).2.1 _ U

end GlobalTheory.UnifFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicLawsModuliSchemeGoodLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicLawsModuliSchemeGoodLevel
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem algebraic_laws_of_good_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ∧ UnitIndep Xo c ∧ IntFrNe Xo c (algCls Xo c) ∧ IntAll Xo c ∧ AllTest Xo c ∧ ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), regular₂ Xo c U ∧ CuspMul Xo c U ∧ ((∀ σ, GoodEmb c σ → IsUnf (U σ)) → CuspFD Xo c U ∧ SupDef Xo c U) := by
  intro E _ _ _ H Dw l Xo c hpq hg
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := GlobalTheory.firstFiveLaws.2.1.secTwist
  have hP : PartI := GlobalTheory.T.compactifiedModuli_partOne
  have hA : N1ab := GlobalTheory.Moduli.moduli_scheme_exists
  have hC : N1c := GlobalTheory.closing_of_abelianSchemeLaws
  have h3 := GlobalTheory.Frames.algebraic_laws hS E H Dw l Xo c
  have hR := GlobalTheory.Reg.sCharts_and_transfer_of_good_level hP hA E H Dw l Xo c hpq hg
  refine ⟨h3.2.2.1, h3.2.2.2.2.2.1,
    GlobalTheory.integralAlgebraicFramedPoint_exists hP hA hC hS hT E H Dw l Xo c hpq hg,
    (Formalism.L2.PjFree.intAll_iff Xo c).1 (GlobalTheory.IntegralFrames.intAll hP hA hS hT E H Dw l Xo c hpq hg),
    GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c, fun r U => ⟨?_, ?_, fun hU => ⟨?_, ?_⟩⟩⟩
  · exact (Formalism.L2.PjFree.regP_ofPj U).1 (hR.2.1 r _)
  · exact (Formalism.L2.PjFree.cuspMul_ofPj U).1 (GlobalTheory.CuspProduct.cuspMul_holds E H Dw l Xo c r _)
  · have h0 : GoodEmb c (goodOf c c.F.val.toRingHom) := goodEmb_goodOf c _
    exact (Formalism.L2.PjFree.cuspFD_ofPj U).1
      (GlobalTheory.cuspForms_finiteDimensional_of_isUnf hS E H Dw l Xo c r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) _ h0
        ((Formalism.L2.PjFree.isUnf_ofPj (U _)).2 (hU _ h0)))
  · exact (Formalism.L2.PjFree.supDef_ofPj U).1
      (GlobalTheory.supNorm_definite_on_cusp E H Dw l Xo c r _ fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ))

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicLawsModuliSchemeGoodLevelStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_laws_moduli_scheme_good_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ∧ UnitIndep Xo c ∧ IntFrNe Xo c (algCls Xo c) ∧ IntAll Xo c ∧ AllTest Xo c ∧ ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), regular₂ Xo c U ∧ CuspMul Xo c U ∧ ((∀ σ, GoodEmb c σ → IsUnf (U σ)) → CuspFD Xo c U ∧ SupDef Xo c U) := by
  first | exact @GlobalTheory.Member.algebraic_laws_of_good_level | exact GlobalTheory.Member.algebraic_laws_of_good_level | (intros; apply GlobalTheory.Member.algebraic_laws_of_good_level <;> assumption)
end
end
