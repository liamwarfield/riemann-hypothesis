module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypWitt

theorem e0_linearIndependent (K : Type) [CommRing K] (M : ℕ) : LinearIndependent K (e0 K M) := by
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  rw [Subsingleton.elim i 0]
  have h := congrFun hg 0
  simpa [e0] using h

theorem gramR_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    gramR R σ (hypOne J) (e0 (R ⊗[F] E) M) = 0 := by
  ext a b
  simp [gramR, hR, hform, JR, e0, Fin.sum_univ_succ, hypOne_zero_zero]

theorem witt_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, LinearIndependent (R ⊗[F] E) x → gramR R σ (hypOne J) x = 0 → ∃ g : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = x := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL x hx gx
  exact FreeTrans.transitive_free_isotropic F E σ hσ (M + 2) (hypOne J) (isHermND_hypOne σ hJ) R hL
    (e0 _ M) x (e0_linearIndependent _ M) hx (gramR_e0 R σ J) gx

end GlobalTheory.CompanionTheory.WeilSiegel.HypWitt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0Statement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_witt_isotropic_to_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, LinearIndependent (R ⊗[F] E) x → gramR R σ (hypOne J) x = 0 → ∃ g : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = x := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypWitt.witt_e0 | exact GlobalTheory.CompanionTheory.WeilSiegel.HypWitt.witt_e0 | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypWitt.witt_e0 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviFactor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviFactor
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelNM
open GlobalTheory.StdUnn.Model

theorem unip_mul_levi : ∀ (D : D7) (p : ℕ) (q : G D p), q ∈ P D p → ∀ a : GL (Fin p) (AE D), blkA (mat q) = a.1 →
    ∃ (g₁ g₂ : G D p) (b : Mx D p p), q = g₁ * g₂ ∧ mat g₁ = blk4 1 b 0 1 ∧ mat g₂ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  intro D p q hq a ha
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  obtain ⟨m', hm'⟩ := GlobalTheory.StdUnn.Model.exists_levi (D := D) (n := p) a⁻¹
  rw [inv_inv] at hm'
  have hmm : m * m' = 1 := GlobalTheory.StdUnn.LeftInvSect.mat_inj (by
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_one, hm, hm',
      GlobalTheory.StdUnn.LeftInvSect.levi_mul_inv])
  have hmm' : m' * m = 1 := by
    rw [eq_inv_of_mul_eq_one_right hmm, inv_mul_cancel]
  have h2 : (adj (a⁻¹).1 : Mx D p p) * adj a.1 = 1 := by
    rw [← adj_mul]; simp [adj_one]
  refine ⟨m * u * m', m, a.1 * b * adj a.1, ?_, ?_, hm⟩
  · rw [mul_assoc (m * u), hmm', mul_one, e]
  · rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm, hu, hm']
    simp [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, h2, -Matrix.coe_units_inv]

end GlobalTheory.CompanionTheory.SiegelNM
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviFactorStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_unipotent_levi_factor : ∀ (D : D7) (p : ℕ) (q : G D p), q ∈ P D p → ∀ a : GL (Fin p) (AE D), blkA (mat q) = a.1 →
  ∃ (g₁ g₂ : G D p) (b : Mx D p p), q = g₁ * g₂ ∧ mat g₁ = blk4 1 b 0 1 ∧ mat g₂ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi | exact GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi | (intros; apply GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittaker
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittaker
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWGlue

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

theorem weil_cell_zero {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : hermA D n)
    (hu : mat u = blk4 1 b.1 0 1) (Φ : schwartzA θ V.rank n) (g : G D n) :
    (ω (w * u * g) Φ).1 0 = Jt ψ V μ (ω g Φ).1 b := by
  have e : ω (w * u * g) Φ = ω w (ω u (ω g Φ)) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e, hω.weyl w hw _ 0]
  unfold Jt
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj]
  simp only [h0, Matrix.trace_zero, map_zero, AddChar.map_zero_eq_one, mul_one]
  rw [hω.unip u b.1 hu (ω g Φ) y, mul_comm]

theorem ndOfWhit : PositivityTheory.PfSWUS.NDOfWhit := by
  intro hU hT hW D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC β hβ g
  obtain ⟨w, hw⟩ := GlobalTheory.StdUnn.Model.exists_weyl (D := D) (n := n)
  have h1 := hW D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ g
  rw [hT D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC β hβ g]
  refine h1.congr ⟨(n : ℝ) / 2, fun z hz => ?_⟩
  show _ = fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g
  rw [(hU D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC w hw β hβ z hz g).2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  show _ * _ = sect ω H Φ z (w * nb b * g) * _
  rw [sect, weil_cell_zero hS.hω hw b (hC.1 b) Φ g]

end GlobalTheory.CompanionTheory.SWGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittakerStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_of_whittaker : PositivityTheory.PfSWUS.NDOfWhit := by
  first | exact @GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | exact GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | (intros; apply GlobalTheory.CompanionTheory.SWGlue.ndOfWhit <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOne
noncomputable section

namespace GlobalTheory.CompanionTheory.ResidueInvolution

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_tmul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) (e : E) :
    sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl

theorem sigR_sigR {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [sigR_tmul, sigR_tmul, sigma_sigma h]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

theorem sigR_algebraMap (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (c : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R (R ⊗[F] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, sigR_tmul]
  simp

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

theorem eq_zero_of_forall_pow {v : HeightOneSpectrum (𝓞 F)} {ϖ c : Fv F v} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hc : ∀ j : ℕ, (ϖ⁻¹) ^ j * c ∈ v.adicCompletionIntegers F) : c = 0 := by
  by_contra hne
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hne) h1
  have h2 : ‖(ϖ⁻¹) ^ j * c‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (hc j)
  rw [norm_mul, norm_pow, norm_inv, inv_pow] at h2
  have h3 : 0 < ‖ϖ‖ ^ j := pow_pos (norm_pos_iff.2 h0) j
  rw [inv_mul_le_iff₀ h3, mul_one] at h2
  exact absurd hj (not_lt.2 h2)

theorem q1 : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hH hϖ
  obtain ⟨hσ, -, hcar, hsig, h0, h1, -, -⟩ := hH
  refine ⟨fun a => Subtype.ext ?_, Subtype.ext ?_, ?_, ?_, one_lt_absNorm v⟩
  · rw [hsig, hsig, sigR_sigR hσ]
  · rw [hsig, sigR_algebraMap]
  · intro x y hxy
    have e : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (x : Fv F v ⊗[F] E) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (y : Fv F v ⊗[F] E) := congrArg Subtype.val hxy
    rw [← Algebra.smul_def, ← Algebra.smul_def] at e
    exact Subtype.ext (smul_right_injective _ h0 e)
  · intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb1 : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (b : Fv F v ⊗[F] E) = 1 := congrArg Subtype.val hb
    have hb2 : (b : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ := by
      have e : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ *
          algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h0, map_one]
      calc (b : Fv F v ⊗[F] E)
          = (algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ *
              algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) * (b : Fv F v ⊗[F] E) := by rw [e, one_mul]
        _ = _ := by rw [mul_assoc, hb1, mul_one]
    have hc : ∀ k, (Algebra.TensorProduct.basis (Fv F v) bs).repr 1 k = 0 := fun k => by
      refine eq_zero_of_forall_pow h0 h1 fun j => ?_
      have hm : ((b ^ j : S) : Fv F v ⊗[F] E) ∈ Rv bs v := by
        rw [← hcar]
        exact (b ^ j).2
      have e : ((b ^ j : S) : Fv F v ⊗[F] E) = ((ϖ : Fv F v)⁻¹ ^ j) • (1 : Fv F v ⊗[F] E) := by
        rw [Subring.coe_pow, hb2, ← map_pow, Algebra.algebraMap_eq_smul_one]
      have := hm k
      rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
      exact this
    have h10 : (1 : Fv F v ⊗[F] E) = 0 :=
      (Algebra.TensorProduct.basis (Fv F v) bs).repr.map_eq_zero_iff.1 (Finsupp.ext hc)
    exact one_ne_zero h10

end GlobalTheory.CompanionTheory.ResidueInvolution

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOneStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_one : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  first | exact @GlobalTheory.CompanionTheory.ResidueInvolution.q1 | exact GlobalTheory.CompanionTheory.ResidueInvolution.q1 | (intros; apply GlobalTheory.CompanionTheory.ResidueInvolution.q1 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExist
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExist
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HtEx

theorem continuous_of_decomp {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace X]
    {Q : Subgroup Γ} (hQ : IsClosed (Q : Set Γ)) {C : Set Γ} (hC : IsCompact C) (H : Γ → X) (δ : Q → X)
    (hδ : Continuous δ) (hI : ∀ g, ∃ p ∈ Q, ∃ k ∈ C, g = p * k)
    (hH : ∀ (p : Q), ∀ k ∈ C, H ((p : Γ) * k) = δ p) : Continuous H := by
  rw [continuous_iff_isClosed]
  intro F hF
  have hQF : IsClosed ((Subtype.val : Q → Γ) '' (δ ⁻¹' F)) :=
    hQ.isClosedMap_subtype_val _ (hF.preimage hδ)
  have heq : H ⁻¹' F = Set.image2 (· * ·) ((Subtype.val : Q → Γ) '' (δ ⁻¹' F)) C := by
    ext g
    constructor
    · intro hg
      obtain ⟨p, hp, k, hk, rfl⟩ := hI g
      refine Set.mem_image2.mpr ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩
      have h1 := hH ⟨p, hp⟩ k hk
      simp only [Set.mem_preimage] at hg ⊢
      rw [← h1]
      exact hg
    · intro hg
      obtain ⟨x, ⟨q, hq, rfl⟩, k, hk, rfl⟩ := Set.mem_image2.mp hg
      simp only [Set.mem_preimage] at hq ⊢
      rw [hH q k hk]
      exact hq
  rw [heq]
  exact hQF.mul_right_of_isCompact hC

variable {D : D7} {n : ℕ}

def delta : P D n →* ℝ≥0 :=
  (absA D).comp (Matrix.GeneralLinearGroup.det.comp HeightExists.leviBlock)

theorem continuous_delta : Continuous (delta (D := D) (n := n)) := by
  have hA : Continuous (absA D) := GlobalTheory.Doubling.continuous_absE
  exact hA.comp (HeightExists.continuous_detGL.comp HeightExists.continuous_leviBlock)

theorem absA_pos (u : (AE D)ˣ) : 0 < absA D u := by
  have h : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h)

theorem delta_eq {p : G D n} (hp : p ∈ P D n) {a : GL (Fin n) (AE D)} (ha : blkA (mat p) = a.1) :
    delta (⟨p, hp⟩ : P D n) = absA D (Matrix.GeneralLinearGroup.det a) := by
  have hl : HeightExists.leviBlock (D := D) (n := n) (⟨p, hp⟩ : P D n) = a := by
    ext1
    exact ha
  show absA D (Matrix.GeneralLinearGroup.det (HeightExists.leviBlock (D := D) (n := n) (⟨p, hp⟩ : P D n))) = _
  rw [hl]

theorem height_eq {H : G D n → ℝ≥0} (hH : IsHeight H) (p : P D n) {k : G D n} (hk : k ∈ K D n) :
    H ((p : G D n) * k) = delta p := by
  obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA p.2
  rw [hH p p.2 a ha k hk, ← delta_eq p.2 ha]

theorem isHt_of_isHeight {H : G D n → ℝ≥0} (hH : IsHeight H) : PositivityTheory.Rg.Rsw.IsHt H := by
  refine ⟨continuous_of_decomp HeightExists.isClosed_P HeightExists.isCompact_K H delta continuous_delta
    (Iwasawa.exists_mul D n) (fun p k hk => height_eq hH p hk), ?_, ?_⟩
  · intro g
    obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    rw [height_eq hH ⟨p, hp⟩ hk]
    obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp
    rw [delta_eq hp ha]
    exact absA_pos _
  · intro q hq a ha g
    obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    rw [← mul_assoc, height_eq hH ⟨q * p, (P D n).mul_mem hq hp⟩ hk, height_eq hH ⟨p, hp⟩ hk,
      ← delta_eq hq ha]
    exact map_mul delta (⟨q, hq⟩ : P D n) ⟨p, hp⟩

theorem htExist : PositivityTheory.Rg.Rsw.HtExist := by
  intro D n
  refine ⟨?_, (K D n : Set (G D n)), HeightExists.isCompact_K, fun g => ?_⟩
  · obtain ⟨H, hH⟩ := exists_height D n
    exact ⟨H, isHt_of_isHeight hH⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := Iwasawa.exists_mul D n g
    exact ⟨p, hp, k, hk, rfl⟩

end GlobalTheory.CompanionTheory.HtEx

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExistStatement
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_functions_exist : HtExist := by
  first | exact @GlobalTheory.CompanionTheory.HtEx.htExist | exact GlobalTheory.CompanionTheory.HtEx.htExist | (intros; apply GlobalTheory.CompanionTheory.HtEx.htExist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegral
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthConv

open GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def rmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := rmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    mul_add (Matrix.of z) (Matrix.of x) (Matrix.of y)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.mul_smul (Matrix.of z) c (Matrix.of x)

def lmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := lmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.smul_mul c (Matrix.of x) (Matrix.of z)

theorem continuous_rmul : Continuous (rmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (rmulLin (E := E) (a := a)).continuous_of_finiteDimensional

theorem continuous_lmul : Continuous (lmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (lmulLin (E := E) (a := a)).continuous_of_finiteDimensional

def bnd (c : GL (Fin a) (Cinf E)) : ℝ := 1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖

theorem height_mul_le_bnd (c y : GL (Fin a) (Cinf E)) : height (y * c) ≤ bnd c * height y := by
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height bnd
  rw [h1, h2]
  nlinarith

theorem toGL_inv (u : AutomorphicForm.archGroup E a) : toGL E a u⁻¹ = (toGL E a u)⁻¹ := by
  simp only [toGL, map_inv]

theorem continuous_bnd : Continuous fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u) := by
  have hm : Continuous (mMap E a) := (mMap E a).continuous_of_finiteDimensional
  have hv : Continuous fun u : AutomorphicForm.archGroup E a =>
      ((u : (AutomorphicForm.ArchMatrix E a)ˣ) : AutomorphicForm.ArchMatrix E a) :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun u : AutomorphicForm.archGroup E a => toL (toGL E a u).val := by
    simp_rw [toL_toGL]
    exact hm.comp hv
  have h2 : Continuous fun u : AutomorphicForm.archGroup E a => toL ((toGL E a u)⁻¹).val := by
    simp_rw [← toGL_inv, toL_toGL]
    exact hm.comp (hv.comp continuous_inv)
  unfold bnd
  exact (continuous_const.add (continuous_rmul.comp h1).norm).add (continuous_lmul.comp h2).norm

theorem growth_conv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ ψ : GA E a → ℂ), Continuous φ → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ D : AutomorphicForm.archGroup E a → ℂ, Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * AutomorphicForm.infEmb E a y) * D y ∂ν) → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a _ _ ν _ φ ψ _ hgrow D hD hDc hψ g
  obtain ⟨C, N, hC⟩ := hgrow g
  have hpos : ∀ y : GL (Fin a) (Cinf E), 0 ≤ height y := fun y => by
    linarith [one_le_height y]
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (f := fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u))
    hDc continuous_bnd.continuousOn
  have hint : Integrable (fun u => ‖D u‖) ν := (hD.integrable_of_hasCompactSupport hDc).norm
  refine ⟨C * B ^ N * ∫ u, ‖D u‖ ∂ν, N, fun y => ?_⟩
  have pt : ∀ u, ‖φ (g * infGL E a y * AutomorphicForm.infEmb E a u) * D u‖ ≤
      (C * (B * height y) ^ N) * ‖D u‖ := fun u => by
    by_cases hu : u ∈ tsupport D
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have e : g * infGL E a y * AutomorphicForm.infEmb E a u = g * infGL E a (y * toGL E a u) := by
        rw [infEmb_eq, mul_assoc, map_mul]
      rw [e]
      refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _) ?_ N) C0)
      exact (height_mul_le_bnd _ y).trans
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hB u hu)) (hpos y))
    · rw [image_eq_zero_of_notMem_tsupport hu]
      simp
  have key := norm_integral_le_of_norm_le (hint.const_mul (C * (B * height y) ^ N)) (Filter.Eventually.of_forall pt)
  rw [hψ]
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul, mul_pow]
  ring

end GlobalTheory.CompanionTheory.GrowthConv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegralStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderate_growth_convolution_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ ψ : GA E a → ℂ), Continuous φ → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ D : AutomorphicForm.archGroup E a → ℂ, Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * AutomorphicForm.infEmb E a y) * D y ∂ν) → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.CompanionTheory.GrowthConv.growth_conv | exact GlobalTheory.CompanionTheory.GrowthConv.growth_conv | (intros; apply GlobalTheory.CompanionTheory.GrowthConv.growth_conv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionThree
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionThree
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrResCard

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def redCoord {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (x : S) (k : Fin d) :
    v.adicCompletionIntegers F ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.mk _ ⟨(Algebra.TensorProduct.basis (Fv F v) bs).repr x k,
    (show (x : Fv F v ⊗[F] E) ∈ Rv bs v from hS ▸ x.2) k⟩

theorem redCoord_eq_iff {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) (x y : S) :
    redCoord bs v S hS ϖ x = redCoord bs v S hS ϖ y ↔ x - y ∈ lev (⟨_, hϖ⟩ : S) 1 := by
  set B := Algebra.TensorProduct.basis (Fv F v) bs with hB
  have hsm : ∀ z : Fv F v ⊗[F] E, z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (ϖ : Fv F v) • z := by
    intro z
    rw [Algebra.smul_def, mul_comm]
  rw [show lev (⟨_, hϖ⟩ : S) 1 = Ideal.span {(⟨_, hϖ⟩ : S) ^ 1} from rfl, pow_one,
    Ideal.mem_span_singleton']
  constructor
  · intro h
    have hk : ∀ k, ∃ t : v.adicCompletionIntegers F, (t : Fv F v) * ϖ = B.repr x k - B.repr y k := by
      intro k
      have h1 := congrFun h k
      simp only [redCoord] at h1
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      refine ⟨t, ?_⟩
      have h2 := congrArg Subtype.val ht
      push_cast at h2
      exact h2
    choose t ht using hk
    let z : Fv F v ⊗[F] E := B.equivFun.symm (fun k => (t k : Fv F v))
    have hz : ∀ k, B.repr z k = t k := by
      intro k
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hzS : z ∈ S := by
      have hzR : z ∈ Rv bs v := by
        intro k
        rw [hz k]
        exact (t k).2
      rw [← hS] at hzR
      exact hzR
    refine ⟨⟨z, hzS⟩, ?_⟩
    apply Subtype.ext
    show z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (x : Fv F v ⊗[F] E) - y
    rw [hsm, B.ext_elem_iff]
    intro k
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hz k, map_sub, Finsupp.sub_apply, mul_comm]
    exact ht k
  · rintro ⟨a, ha⟩
    have hxy : (x : Fv F v ⊗[F] E) - y = (ϖ : Fv F v) • (a : Fv F v ⊗[F] E) := by
      rw [← hsm]
      exact (congrArg Subtype.val ha).symm
    have haR : (a : Fv F v ⊗[F] E) ∈ Rv bs v := hS ▸ a.2
    funext k
    simp only [redCoord]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨⟨B.repr a k, haR k⟩, ?_⟩
    apply Subtype.ext
    push_cast
    have h3 := congrArg (fun w => B.repr w k) hxy
    simp only [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3
    rw [mul_comm, ← h3]

theorem redCoord_surjective {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) : Function.Surjective (redCoord bs v S hS ϖ) := by
  intro g
  set B := Algebra.TensorProduct.basis (Fv F v) bs with hB
  choose t ht using fun k => Ideal.Quotient.mk_surjective (g k)
  let z : Fv F v ⊗[F] E := B.equivFun.symm (fun k => (t k : Fv F v))
  have hz : ∀ k, B.repr z k = t k := by
    intro k
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hzS : z ∈ S := by
    have hzR : z ∈ Rv bs v := by
      intro k
      rw [hz k]
      exact (t k).2
    rw [← hS] at hzR
    exact hzR
  refine ⟨⟨z, hzS⟩, ?_⟩
  funext k
  simp only [redCoord]
  rw [← ht k]
  congr 1
  exact Subtype.ext (hz k)

theorem card_quot {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) :
    Nat.card (S ⧸ lev (⟨_, hϖ⟩ : S) 1) = Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) ^ d := by
  have hsurj := Ideal.Quotient.mk_surjective (I := lev (⟨_, hϖ⟩ : S) 1)
  let sec := Function.surjInv hsurj
  have hsec : ∀ q, Ideal.Quotient.mk _ (sec q) = q := Function.surjInv_eq hsurj
  let g : S ⧸ lev (⟨_, hϖ⟩ : S) 1 → (Fin d → v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) :=
    fun q => redCoord bs v S hS ϖ (sec q)
  have hg : Function.Bijective g := by
    constructor
    · intro q₁ q₂ h
      rw [← hsec q₁, ← hsec q₂, Ideal.Quotient.eq]
      exact (redCoord_eq_iff bs v S hS ϖ hϖ _ _).mp h
    · intro w
      obtain ⟨x, hx⟩ := redCoord_surjective bs v S hS ϖ w
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      rw [← hx]
      apply (redCoord_eq_iff bs v S hS ϖ hϖ _ _).mpr
      rw [← Ideal.Quotient.eq, hsec]
  rw [Nat.card_congr (Equiv.ofBijective g hg), Nat.card_fun, Nat.card_fin]

theorem q3 : PositivityTheory.SiegelWeilFormula.Gunr.Q3 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ
  obtain ⟨hCM, -, hS, -, -, -, -, hcard⟩ := hQ
  have hd : d = 2 := by
    rw [← hCM.2.2.1, Module.finrank_eq_card_basis bs, Fintype.card_fin]
  subst hd
  rw [card_quot bs v S hS ϖ hϖ, hcard]

end GlobalTheory.CompanionTheory.GunrResCard
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionThreeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_three : PositivityTheory.SiegelWeilFormula.Gunr.Q3 := by
  first | exact @GlobalTheory.CompanionTheory.GunrResCard.q3 | exact GlobalTheory.CompanionTheory.GunrResCard.q3 | (intros; apply GlobalTheory.CompanionTheory.GunrResCard.q3 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionTwo
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionTwo
noncomputable section

namespace GlobalTheory.CompanionTheory.ValuationCompleteness

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr Filter Topology
open scoped TensorProduct

section Abstract

variable {K A : Type} [NormedField K] [CommRing A] [Algebra K A] {d : ℕ}
  (b : Module.Basis (Fin d) K A) (S : Subring A)

theorem mem_lev_iff (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (k : ℕ) :
    a ∈ lev (⟨_, hϖ⟩ : S) k ↔ ∀ i, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k := by
  have hpow : ∀ c : A, c * (algebraMap K A ϖ) ^ k = ϖ ^ k • c := by
    intro c
    rw [← map_pow, Algebra.smul_def, mul_comm]
  have hcoe : ∀ c : S, ((c * (⟨_, hϖ⟩ : S) ^ k : S) : A) = ϖ ^ k • (c : A) := by
    intro c
    rw [← hpow]
    rfl
  constructor
  · intro ha i
    rw [lev, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    have hc' : (a : A) = ϖ ^ k • (c : A) := by
      rw [← hc, hcoe]
    rw [hc', map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    have hci := (hS c).1 c.2 i
    calc ‖ϖ‖ ^ k * ‖b.repr (c : A) i‖ ≤ ‖ϖ‖ ^ k * 1 := by gcongr
      _ = ‖ϖ‖ ^ k := mul_one _
  · intro ha
    rw [lev, Ideal.mem_span_singleton']
    have hpos : 0 < ‖ϖ‖ ^ k := pow_pos (norm_pos_iff.mpr h0) k
    have hcS : (ϖ ^ k)⁻¹ • (a : A) ∈ S := by
      rw [hS]
      intro i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv, norm_pow,
        inv_mul_le_iff₀ hpos, mul_one]
      exact ha i
    refine ⟨⟨_, hcS⟩, ?_⟩
    apply Subtype.ext
    rw [hcoe]
    change ϖ ^ k • ((ϖ ^ k)⁻¹ • (a : A)) = (a : A)
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero k h0), one_smul]

theorem separated (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (h : ∀ k, a ∈ lev (⟨_, hϖ⟩ : S) k) : a = 0 := by
  have hi : ∀ i, b.repr (a : A) i = 0 := by
    intro i
    have hle : ∀ k : ℕ, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k :=
      fun k => (mem_lev_iff b S hS h0 hϖ a k).1 (h k) i
    have ht : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1
    exact norm_le_zero_iff.mp (ge_of_tendsto' ht hle)
  have hr : b.repr (a : A) = 0 := by
    ext i
    exact hi i
  have ha : (a : A) = 0 := (LinearEquiv.map_eq_zero_iff b.repr).mp hr
  exact_mod_cast ha

variable [CompleteSpace K] [IsUltrametricDist K]

theorem complete (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (f : ℕ → S) (hf : ∀ k, f (k + 1) - f k ∈ lev (⟨_, hϖ⟩ : S) k) :
    ∃ a, ∀ k, a - f k ∈ lev (⟨_, hϖ⟩ : S) k := by
  set x : ℕ → Fin d → K := fun k i => b.repr (f k : A) i with hx
  have hstep : ∀ k i, ‖x (k + 1) i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro k i
    have := (mem_lev_iff b S hS h0 hϖ _ k).1 (hf k) i
    simpa [hx, map_sub] using this
  have hn0 : 0 ≤ ‖ϖ‖ := norm_nonneg _
  have hle1 : ‖ϖ‖ ≤ 1 := le_of_lt h1
  have hfar : ∀ i k m, k ≤ m → ‖x m i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have e : x (m + 1) i - x k i = (x (m + 1) i - x m i) + (x m i - x k i) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hstep m i).trans (pow_le_pow_of_le_one hn0 hle1 hkm)
  have hcau : ∀ i, CauchySeq (fun k => x k i) := by
    intro i
    refine cauchySeq_of_le_geometric ‖ϖ‖ 1 h1 (fun n => ?_)
    rw [dist_eq_norm, ← norm_neg, neg_sub, one_mul]
    exact hstep n i
  choose c hc using fun i => cauchySeq_tendsto_of_complete (hcau i)
  have hbd : ∀ i k, ‖c i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k
    have ht : Tendsto (fun m => ‖x m i - x k i‖) atTop (𝓝 ‖c i - x k i‖) :=
      ((hc i).sub_const _).norm
    refine le_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop k] with m hm
    exact hfar i k m hm
  set aA : A := b.equivFun.symm c with haA
  have hrep : ∀ i, b.repr aA i = c i := by
    intro i
    rw [← b.equivFun_apply, haA, LinearEquiv.apply_symm_apply]
  have hmem : aA ∈ S := by
    rw [hS]
    intro i
    rw [hrep]
    have e : c i = (c i - x 0 i) + x 0 i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · simpa using hbd i 0
    · exact (hS _).1 (f 0).2 i
  refine ⟨⟨aA, hmem⟩, fun k => ?_⟩
  rw [mem_lev_iff b S hS h0 hϖ]
  intro i
  have e : ((⟨aA, hmem⟩ - f k : S) : A) = aA - (f k : A) := rfl
  rw [e, map_sub, Finsupp.sub_apply, hrep]
  exact hbd i k

end Abstract

theorem q2 : Q2 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ
  obtain ⟨-, -, hSR, -, h0, h1, -, -⟩ := hQ
  have hS : ∀ x, x ∈ S ↔ ∀ i, ‖(Algebra.TensorProduct.basis (Fv F v) bs).repr x i‖ ≤ 1 := by
    intro x
    rw [← SetLike.mem_coe, hSR]
    exact forall_congr' fun i =>
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).trans
        Valued.toNormedField.norm_le_one_iff.symm
  exact ⟨fun a ha => separated _ S hS h0 h1 hϖ a ha, fun f hf => complete _ S hS h0 h1 hϖ f hf⟩

end GlobalTheory.CompanionTheory.ValuationCompleteness

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionTwoStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_two : PositivityTheory.SiegelWeilFormula.Gunr.Q2 := by
  first | exact @GlobalTheory.CompanionTheory.ValuationCompleteness.q2 | exact GlobalTheory.CompanionTheory.ValuationCompleteness.q2 | (intros; apply GlobalTheory.CompanionTheory.ValuationCompleteness.q2 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Brat
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisBrat

open scoped TensorProduct NumberField.AdeleRing
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

theorem brat : BRat := by
  intro F E _ _ _ _ _ σ χ c _ _ _ _
  refine ⟨fun y => ?_, fun e x h => ?_⟩
  · change (algebraMap F (AF F) y) ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] (algebraMap F E y)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · obtain ⟨g, hg⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F E))
    have g1 : g 1 = 1 := by
      have := LinearMap.congr_fun hg (1 : F)
      simpa using this
    have h' : (1 : AF F) ⊗ₜ[F] e = x ⊗ₜ[F] (1 : E) := h
    have h2 := congrArg (fun t => TensorProduct.rid F (AF F) (LinearMap.lTensor (AF F) g t)) h'
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at h2
    refine ⟨g e, ?_⟩
    rw [← h2, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CompanionTheory.EisBrat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseCM
open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.CompanionTheory.SgOneBase

theorem baseCM : CMGood → BFix → BRat → BInt → BInf → BLg → BDel → BaseCM := by
  intro _ hFix hRat hInt hInf hLg hDel F E _ _ _ _ _ σ χ c hCM hUn hHk hRes ε
  obtain ⟨hνc, hνi, hνfix, r, hrc, hrfix⟩ := hFix F E σ χ c hCM hUn hHk hRes
  obtain ⟨hrat, hrat'⟩ := hRat F E σ χ c hCM hUn hHk hRes
  have hint := hInt F E σ χ c hCM hUn hHk hRes
  obtain ⟨hinf, hinf'⟩ := hInf F E σ χ c hCM hUn hHk hRes
  obtain ⟨hlg, hlgσ⟩ := hLg F E σ χ c hCM hUn hHk hRes
  obtain ⟨δ0, α0, u0, hσδ, hδα, huO, huiO, hun⟩ := hDel F E σ χ c hCM hUn hHk hRes
  have hσi : ∀ x : E, (adCM σ χ).σ ((adCM σ χ).i x) = (adCM σ χ).i (σ x) := by
    intro x
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (σ x)
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  let f : IdeleGroup F →* Circle := χ.comp (Units.map (nuCM F E).toMonoidHom)
  have hker : (IdeleGroup.diagonal F).range ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    have e : Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a) =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* TensorProduct F (AF F) E) (Units.map (algebraMap F E : F →* E) a) :=
      Units.ext (hrat a)
    show χ (Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a)) = 1
    rw [e]
    exact hHk.2 _
  have hfc : Continuous f := hHk.1.comp (Continuous.units_map _ hνc)
  let ω : HeckeCharacter F :=
    ⟨QuotientGroup.lift _ f hker, (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hfc⟩
  have hω : ∀ x : IdeleGroup F, ω.toIdele x = (adCM σ χ).χ (Units.map (nuCM F E).toMonoidHom x) := fun x => rfl
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine ⟨r, δ0, α0, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨u0, hδα, huO, huiO, hun⟩, hω⟩⟩
    rw [hσi, hσδ, map_neg]
    simp
  · refine ⟨r, 1, 1, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨1, ?_, ?_, ?_, ?_⟩, hω⟩⟩
    · simp
    · simp
    · simpa using (adCM σ χ).O.one_mem
    · simpa using (adCM σ χ).O.one_mem
    · intro w
      simp

end GlobalTheory.CompanionTheory.SgOneBase
end
