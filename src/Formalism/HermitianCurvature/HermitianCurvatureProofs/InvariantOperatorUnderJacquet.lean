module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RttUpperRelationsFromDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLineCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
namespace Formalism.FourierDecayAlt.P

theorem jacquet_derivative_formula : Formalism.FourierDecayAlt.JF.JWords :=
  bessel_words_of_domain bessel_integral_domain

theorem jacquet_smooth_coordinates : Formalism.FourierDecayAlt.JF.JqSmooth :=
  bessel_smooth_of_parts jacquet_derivative_formula big_cell_domain

theorem casimir_under_jacquet_integral : Formalism.FourierDecayAlt.JF.CVUnderInt :=
  capelli_under_integral_of_parts jacquet_derivative_formula capelli_word_sum rewrite_rho_action

theorem right_transfer_upper_levels : Formalism.FourierDecayAlt.Q.RTTUpper :=
  rtt_upper_relations_from_descent chain_descent_relation resSurj_statement capelli_commutation operator_preserves_fusion_forms
    transfer_triples rtt_sandwich rtt_independence leading_term_alt transfer_linear_local

theorem right_transfer_all_levels : Formalism.FourierDecayAlt.Q.RTTLevel :=
  rtt_level_from_upper right_transfer_upper_levels level_transfer level_group_image flag_frame_transfer
    transfer_linear_local

namespace JacquetIntegral

theorem detCore : Formalism.FourierDecayAlt.Q.DetAt fun P => Fin.last P.r :=
  determinant_capelli_from_descent right_transfer_all_levels quantum_determinant_from_rtt determinant_hat right_type_action
    left_type_action operator_preserves_fusion_forms transfer_linear_local

end JacquetIntegral

theorem actual_operators_exist : Formalism.FourierDecayAlt.Q.ActualOpsExist :=
  actual_operators_from_parts operator_preserves_fusion_forms transfer_linear_local transfer_joint_smooth radial_operators

theorem actual_adjointness : Formalism.FourierDecayAlt.Q.ActualAdjoint :=
  actual_adjointness_from_hermitian hermitian_haar_invariance

theorem actual_start : Formalism.FourierDecayAlt.Q.ActualStart :=
  actual_start_from_level_starts right_transfer_all_levels JacquetIntegral.detCore transfer_linear_local

namespace JacquetIntegral

theorem normalFormActual_of_fromModule (h : Formalism.FourierDecayAlt.Q.NormalFormFromModule) : Formalism.FourierDecayAlt.Q.NormalFormActual :=
  h actual_start zeta_commutes leading_term_alt spectral_two_by_two actual_operators_exist

theorem levelStartActual_of_normalForm (h : Formalism.FourierDecayAlt.Q.NormalFormActual) : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  level_start_from_normal_form h actual_start model_is_normal_form interlace_sign_two

theorem levelStartActual_of_fromModule (h : Formalism.FourierDecayAlt.Q.NormalFormFromModule) : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  levelStartActual_of_normalForm (normalFormActual_of_fromModule h)

end JacquetIntegral

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SupportPhiZeroSubset
namespace Formalism.FourierDecayAlt.P.PBI

open Finset Filter Topology MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

open Classical

def gPoly {r : ℕ} (TT : ℝ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ℝ :=
  Complex.normSq M.det - TT * Complex.normSq (M.submatrix Fin.castSucc Fin.castSucc).det

theorem gf_eq_gPoly (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Gf k r z z' g = gPoly (Tz k r z * Tz k r z') (Zhat k r z z' g) := by
  first
    | rfl
    | (unfold Gf gPoly Dmin; rfl)
    | (simp only [Gf, gPoly, Dmin]; rfl)

theorem continuous_gPoly (r : ℕ) (TT : ℝ) : Continuous fun Z : G.Mat (r + 1) => gPoly TT (Matrix.of Z) := by
  have hc : Continuous fun Z : G.Mat (r + 1) =>
      (Matrix.of Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := continuous_id
  unfold gPoly
  exact (Complex.continuous_normSq.comp hc.matrix_det).sub
    (continuous_const.mul (Complex.continuous_normSq.comp (hc.matrix_submatrix _ _).matrix_det))

section fibre

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def fibInt (Bs : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p, B.rho Bs p F g ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0'))

def phi0 (Bs : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (sec : G.Mat (r + 1) → Mt k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) : G.Mat (r + 1) → (Wq →L[ℂ] Wp) := fun Z =>
  if 0 < gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z) then fibInt Bs μ0 μ0' F (Matrix.of (sec Z)) else 0

def IsSec (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (sec : G.Mat (r + 1) → Mt k r) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sec {Z | 0 < gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z)} ∧
    ∀ Z, 0 < gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z) →
      Matrix.of (sec Z) ∈ B.GV k r ∧ Zhat k r Bs.z Bs.z' (Matrix.of (sec Z)) = Matrix.of Z ∧
        D.IsDFrame Bs ν' m₀ (Matrix.of (sec Z))

theorem cpt_of_fibre {E : Type*} [NormedAddCommGroup E] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) (Ψ : G.Mat (r + 1) → E)
    (hΨ : ∀ Z, Ψ Z ≠ 0 → ∃ g ∈ B.GV k r, F g ≠ 0 ∧ Zhat k r Bs.z Bs.z' g = Matrix.of Z) :
    HasCompactSupport Ψ ∧ ∀ Z ∈ tsupport Ψ, G.detM Z ≠ 0 := by
  obtain ⟨_, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  obtain ⟨C, hC⟩ := zhat_norm_bound k r Bs.z Bs.z'
  set TT : ℝ := Tz k r Bs.z * Tz k r Bs.z' with hTT
  set K : Set (G.Mat (r + 1)) :=
    Metric.closedBall 0 (max C 0 * R) ∩ {Z | ε ≤ gPoly TT (Matrix.of Z)} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 _).inter_right (isClosed_le continuous_const (continuous_gPoly r TT))
  have hsub : Function.support Ψ ⊆ K := by
    intro Z hZ
    obtain ⟨g, hg, hFg, hZg⟩ := hΨ Z hZ
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : C2.mx (Zhat k r Bs.z Bs.z' g) ≤ C * B.gN g := hC g
      rw [hZg] at h1
      have h2 : C2.mx (Matrix.of Z) = ‖Z‖ := rfl
      rw [h2] at h1
      have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
      have hRg : B.gN g ≤ R := hR g hg hFg
      calc ‖Z‖ ≤ C * B.gN g := h1
        _ ≤ max C 0 * B.gN g := mul_le_mul_of_nonneg_right (le_max_left _ _) hgN
        _ ≤ max C 0 * R := mul_le_mul_of_nonneg_left hRg (le_max_right _ _)
    · show ε ≤ gPoly TT (Matrix.of Z)
      have := hεG g hg hFg
      rw [gf_eq_gPoly, hZg] at this
      exact this
  have hts : tsupport Ψ ⊆ K := closure_minimal hsub hKc.isClosed
  refine ⟨hKc.of_isClosed_subset (isClosed_tsupport Ψ) hts, fun Z hZ => ?_⟩
  have hZK := (hts hZ).2
  simp only [Set.mem_ofPred_eq, gPoly] at hZK
  have hTT0 : 0 ≤ TT := mul_nonneg Bs.T_pos.le Bs.T'_pos.le
  have hpos : 0 < Complex.normSq (Matrix.of Z).det := by
    have := mul_nonneg hTT0 (Complex.normSq_nonneg ((Matrix.of Z).submatrix Fin.castSucc Fin.castSucc).det)
    linarith
  intro h0
  unfold G.detM at h0
  rw [h0, map_zero] at hpos
  exact lt_irrefl _ hpos

theorem support_phi_zero_subset (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (μ0 μ0' : Measure (Mt k r)) (hμ0 : B.IsHaarOn (C2.N0set k r Bs.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r Bs.z') μ0') (sec : G.Mat (r + 1) → Mt k r) (hsec : IsSec Bs ν' m₀ sec)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Z : G.Mat (r + 1)) (hZ : phi0 Bs μ0 μ0' sec F Z ≠ 0) :
    ∃ g ∈ B.GV k r, F g ≠ 0 ∧ Zhat k r Bs.z Bs.z' g = Matrix.of Z := by
  unfold phi0 at hZ
  split_ifs at hZ with hG
  · obtain ⟨hg0, hZg0, -⟩ := hsec.2 Z hG
    set g0 : B.Mat k r := Matrix.of (sec Z) with hg0def
    by_contra hno
    push Not at hno
    apply hZ
    unfold fibInt
    have hW := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW
    have hW' := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW'
    have hN := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0
    have hN' := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0'
    have b1 : ∀ᵐ q ∂(Bs.μW.prod μ0), Matrix.of q.1 ∈ UWset k r Bs.z :=
      (Measure.quasiMeasurePreserving_fst (μ := Bs.μW) (ν := μ0)).ae
        (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem Bs.haarW)
    have b2 : ∀ᵐ q ∂(Bs.μW.prod μ0), Matrix.of q.2 ∈ C2.N0set k r Bs.z :=
      (Measure.quasiMeasurePreserving_snd (μ := Bs.μW) (ν := μ0)).ae (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hμ0)
    have c1 : ∀ᵐ q ∂(Bs.μW'.prod μ0'), Matrix.of q.1 ∈ UWset k r Bs.z' :=
      (Measure.quasiMeasurePreserving_fst (μ := Bs.μW') (ν := μ0')).ae
        (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem Bs.haarW')
    have c2 : ∀ᵐ q ∂(Bs.μW'.prod μ0'), Matrix.of q.2 ∈ C2.N0set k r Bs.z' :=
      (Measure.quasiMeasurePreserving_snd (μ := Bs.μW') (ν := μ0')).ae (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hμ0')
    have d1 : ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')),
        Matrix.of p.1.1 ∈ UWset k r Bs.z ∧ Matrix.of p.1.2 ∈ C2.N0set k r Bs.z :=
      (Measure.quasiMeasurePreserving_fst (μ := Bs.μW.prod μ0) (ν := Bs.μW'.prod μ0')).ae (b1.and b2)
    have d2 : ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')),
        Matrix.of p.2.1 ∈ UWset k r Bs.z' ∧ Matrix.of p.2.2 ∈ C2.N0set k r Bs.z' :=
      (Measure.quasiMeasurePreserving_snd (μ := Bs.μW.prod μ0) (ν := Bs.μW'.prod μ0')).ae (c1.and c2)
    apply integral_eq_zero_of_ae
    filter_upwards [d1, d2] with p h1 h2
    have hGG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
    have hNN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
    have hz : C2.StdZ k r Bs.z := ⟨Bs.z_mem, Bs.T_pos⟩
    have hz' : C2.StdZ k r Bs.z' := ⟨Bs.z'_mem, Bs.T'_pos⟩
    set h := (Matrix.of p.1.1 : B.Mat k r)
    set n := (Matrix.of p.1.2 : B.Mat k r)
    set h' := (Matrix.of p.2.1 : B.Mat k r)
    set n' := (Matrix.of p.2.2 : B.Mat k r)
    have hhG : h ∈ B.GV k r := h1.1.1
    have hnG : n ∈ B.GV k r := h1.2.1.1
    have hh'G : h' ∈ B.GV k r := h2.1.1
    have hn'G : n' ∈ B.GV k r := h2.2.1.1
    have hsgs : B.sgs p g0 = h⁻¹ * (n⁻¹ * g0 * n') * h' := by
      simp only [B.sgs, Matrix.mul_assoc]; rfl
    have hmem : B.sgs p g0 ∈ B.GV k r := by
      rw [hsgs]
      exact hGG.mul_mem _ (hGG.mul_mem _ (hGG.inv_mem _ hhG)
        _ (hGG.mul_mem _ (hGG.mul_mem _ (hGG.inv_mem _ hnG) _ hg0) _ hn'G)) _ hh'G
    have hS_h : h ∈ Sset k r Bs.z := ⟨h, h1.1, 1, hNN.one_mem, (Matrix.mul_one h).symm⟩
    have hS_h' : h' ∈ Sset k r Bs.z' := ⟨h', h2.1, 1, hNN.one_mem, (Matrix.mul_one h').symm⟩
    have hS_n : n ∈ Sset k r Bs.z :=
      ⟨1, (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs.z).one_mem, n, h1.2.1, (Matrix.one_mul n).symm⟩
    have hS_n' : n' ∈ Sset k r Bs.z' :=
      ⟨1, (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs.z').one_mem, n', h2.2.1, (Matrix.one_mul n').symm⟩
    have e1 := Formalism.FourierDecayAlt.P.zhat_equivalence k r Bs.z Bs.z' hz hz' h hS_h h' hS_h' (n⁻¹ * g0 * n')
    have e2 := Formalism.FourierDecayAlt.P.zhat_equivalence k r Bs.z Bs.z' hz hz' n hS_n n' hS_n' g0
    have u1 : C2.uMap k r Bs.z h = 1 := (Formalism.FourierDecayAlt.P.unipotent_map_frame k r Bs.z hz).2 h h1.1
    have u1' : C2.uMap k r Bs.z' h' = 1 := (Formalism.FourierDecayAlt.P.unipotent_map_frame k r Bs.z' hz').2 h' h2.1
    rw [u1, u1', Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at e1
    rw [h1.2.2, h2.2.2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at e2
    have hZs : Zhat k r Bs.z Bs.z' (B.sgs p g0) = Matrix.of Z := by rw [hsgs, e1, e2, hZg0]
    have hF0 : F (B.sgs p g0) = 0 := by
      by_contra hne
      exact hno _ hmem hne hZs
    simp [B.rho, hF0]
  · exact absurd rfl hZ

end fibre

def SectionExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r),
    D.IsBaseFrame Bs ν' m₀ → ∃ sec : G.Mat (r + 1) → Mt k r, IsSec Bs ν' m₀ sec

def FibIntSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (μ0 μ0' : Measure (Mt k r)) (sec : G.Mat (r + 1) → Mt k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    D.IsBaseFrame Bs ν' m₀ → B.IsHaarOn (C2.N0set k r Bs.z) μ0 → B.IsHaarOn (C2.N0set k r Bs.z') μ0' →
    IsSec Bs ν' m₀ sec → KB.CptCoef Bs F → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phi0 Bs μ0 μ0' sec F)

def FibIntCells : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    ∃ (μ0 μ0' : Measure (Mt P.k P.r)) (c : ℂ), B.IsHaarOn (C2.N0set P.k P.r p.T.base.z) μ0 ∧
      B.IsHaarOn (C2.N0set P.k P.r p.T.base.z') μ0' ∧
      ∀ sec : G.Mat (P.r + 1) → Mt P.k P.r, IsSec p.T.base p.ν' p.m₀ sec →
      ∀ F, KB.CptCoef p.T.base F →
      ∀ (a : C.LPt) (σ : Equiv.Perm (Fin (P.r + 1))) (d : Fin (P.r + 1) → ℂ), D.IsLocPt a (P.r + 1) →
        U.hMat σ d = D.ptMatN a (P.r + 1) →
        p.V F a = U.PhiTop (p := P.r + 1) (s := 0) U.betaU σ d (c • phi0 p.T.base μ0 μ0' sec F)
          fun x => x.elim0

def Phi0Support : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (μ0 μ0' : Measure (Mt k r)) (sec : G.Mat (r + 1) → Mt k r) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.IsHaarOn (C2.N0set k r Bs.z) μ0 → B.IsHaarOn (C2.N0set k r Bs.z') μ0' → IsSec Bs ν' m₀ sec →
    KB.CptCoef Bs F → HasCompactSupport (phi0 Bs μ0 μ0' sec F) ∧
      ∀ Z ∈ tsupport (phi0 Bs μ0 μ0' sec F), G.detM Z ≠ 0

def PhiZeroOfParts : Prop := SectionExists → FibIntSmooth → FibIntCells → KB.PhiZero

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Formalism.FourierDecayAlt

theorem phi_zero_support : PBI.Phi0Support := by
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ μ0 μ0' sec F hμ0 hμ0' hsec hF
  exact PBI.cpt_of_fibre Bs F hF (PBI.phi0 Bs μ0 μ0' sec F)
    (fun Z hZ => PBI.support_phi_zero_subset Bs ν' m₀ μ0 μ0' hμ0 hμ0' sec hsec F Z hZ)

theorem phi_zero_of_parts : PBI.PhiZeroOfParts := by
  intro hSec hSm hCells Wp Wq _ _ _ _ _ _ P p F hF
  obtain ⟨μ0, μ0', c, hμ0, hμ0', hV⟩ := hCells Wp Wq P p
  obtain ⟨sec, hsec⟩ := hSec P.k P.r Wp Wq p.T.base p.ν' p.m₀ p.hF
  have hsupp := phi_zero_support P.k P.r Wp Wq p.T.base p.ν' p.m₀ μ0 μ0' sec F hμ0 hμ0' hsec hF
  refine ⟨c • PBI.phi0 p.T.base μ0 μ0' sec F, ?_, ?_, ?_, ?_⟩
  · exact (hSm P.k P.r Wp Wq p.T.base p.ν' p.m₀ μ0 μ0' sec F p.hF hμ0 hμ0' hsec hF).const_smul c
  · exact hsupp.1.mono (Function.support_const_smul_subset c _)
  · intro Z hZ
    exact hsupp.2 Z (closure_mono (Function.support_const_smul_subset c _) hZ)
  · intro a σ d ha hd
    exact hV sec hsec F hF a σ d ha hd

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RealInputsBuiltClosedForm
open Finset NumberField MeasureTheory Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

noncomputable section

theorem jct_rd_pos (E : Type) [Field E] [NumberField E] : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  exact Int.cast_pos.mpr (abs_pos.mpr (NumberField.discr_ne_zero E))

theorem jct_isBuiltPlace_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ Cc c : ℝ} (hc : c ≤ Cc) (h : JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀) :
    JCT.IsBuiltPlace c S T f χ ν' m₀ top A₀ := by
  unfold JCT.IsBuiltPlace at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, le_trans hc h9, h10, h11, ?_, h13⟩
  · unfold JCT.LongCut at h8 ⊢
    intro v
    exact le_trans (mul_le_mul_of_nonneg_right hc (by positivity)) (h8 v)
  · exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)) h12

theorem energy_of_built_setting : JCT.EnergyOfLemmaE := by
  intro hBC
  obtain ⟨Cc, hBC⟩ := hBC
  refine ⟨Cc, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ jv hBP hL v
  obtain ⟨-, -, -, hB, -, -, -, -, -, hsm, -, -, -⟩ := id hBP
  have hpd := (hB.2 v).1
  set Γ := D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0 with hΓ
  obtain ⟨-, hlim⟩ := hBC E Wp Wq S T f χ ν' m₀ top A₀ hBP v
  have hemp : S.empW.1 v = [] := rfl
  have h1 := hL S.empW v
  have h2 : Filter.Tendsto (fun ε => (S.pd v).RR ε 0 (S.empW.1 v) [] []) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((((1 / Γ : ℝ)) : ℂ) * (((B.normSq (T v).base (f v)).toReal : ℝ) : ℂ))) := by
    refine (hlim.const_mul _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hsm' := cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε
    rw [hpd]
    simp only [D.componentFamilySetting_ofSetting, D.bSt, D.toStd, List.map_nil, List.prod_nil]
    rw [level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hsm' (good_of_admissible _ _ _ S S.empW v)]
    rw [hemp]
    simp only [C7.principalHermitianLattice, List.foldr_nil]
    push_cast
    ring
  have h3 := tendsto_nhds_unique h1 h2
  rw [hemp] at h3
  have hsz : S.sizeAt v [] = 1 := by simp [C.HidaSetting.sizeAt]
  rw [hsz, one_mul] at h3
  have h4 : jv v = 1 / Γ * (B.normSq (T v).base (f v)).toReal := by exact_mod_cast h3
  rw [h4]
  ring

end

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def dTy (P : M.Par) (ρ : M.Ty P) : M.Ty P → ℂ := fun σ => if σ = ρ then 1 else 0

def GTCCurvId : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ ρ : M.Ty P,
      (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
        algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) *
          (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)

def GTCCurvTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → (∀ ρ, ∀ ζ ∈ Ann P, B ρ ζ = star (A ρ ζ)) →
        (∀ ρ : M.Ty P, (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
          algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) *
            (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)) →
        ∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A ρ w) ζ).re = 0

def GTCRefTrace : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e0 ∧ KapF P Bs d e0 ∧
      ∃ A0 B0 : M.Ty P → ℂ → ℂ, SmAB P A0 B0 ∧ ConnF P Bs d e0 A0 B0 ∧
        ∀ ρ, ∃ n : ℤ, ∀ ζ ∈ Ann P, (ζ * (modA P ρ ζ - A0 ρ ζ)).re = (n : ℝ) / 2

def GTCRefAn : Prop :=
  ∀ (TT : ℝ) (α : ℂ → ℂ) (c : ℝ), 0 ≤ TT →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → (ζ * α ζ).re = c) →
    ∀ R : ℝ, 0 < R → TT < R ^ 2 → (circleIntegral α 0 R).im = 2 * Real.pi * c

def GTCRefOfCut : Prop := GTCReal → GTCCurvId → GTCCurvTr → GTCRefTrace → GTCRefAn → GTCRef

private theorem contDiffOn_modA_ann (P : M.Par) (ρ : M.Ty P) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h : modA P ρ = fun ζ : ℂ => (M.aC P ρ : ℂ) * star ζ * (ζ * star ζ - (P.TT : ℂ))⁻¹ := by
    funext ζ
    simp only [modA, div_eq_mul_inv]
    rw [← Complex.mul_conj]
    rfl
  rw [h]
  apply ContDiffOn.mul
  · exact (contDiff_const.mul hs).contDiffOn
  · apply ContDiffOn.inv
    · exact ((contDiff_id.mul hs).sub contDiff_const).contDiffOn
    · intro ζ hζ
      have hz : ζ * star ζ = ((Complex.normSq ζ : ℝ) : ℂ) := Complex.mul_conj ζ
      rw [hz, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hζ).ne'

theorem gTCRef_of_cut : GTCRefOfCut := by
  intro hReal hCurvId hCurvTr hTrace hAn Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨e0, he0, hk0, A0, B0, hAB, hC, hn⟩ := hTrace Wp Wq P Bs X d hH
  have hB : ∀ ρ, ∀ ζ ∈ Ann P, B0 ρ ζ = star (A0 ρ ζ) := hReal Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC
  refine ⟨e0, he0, hk0, A0, B0, hAB, hC,
    hCurvTr Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC hB (hCurvId Wp Wq P Bs X d hH), ?_⟩
  intro ρ R hR hR2
  obtain ⟨n, hn'⟩ := hn ρ
  refine ⟨n, ?_⟩
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := contDiffOn_modA_ann P ρ
  have key := hAn (max P.TT 0) (fun w => modA P ρ w - A0 ρ w) ((n : ℝ) / 2) (le_max_right _ _)
    ((hsm.sub (hAB ρ).1).mono (fun ζ hζ => show P.TT < Complex.normSq ζ from
      lt_of_le_of_lt (le_max_left _ _) (show max P.TT 0 < Complex.normSq ζ from hζ)))
    (fun ζ hζ => hn' ζ (show P.TT < Complex.normSq ζ from lt_of_le_of_lt (le_max_left _ _) hζ)) R hR (max_lt hR2 (pow_pos hR 2))
  rw [key]; ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ebM (k r : ℕ) (v b : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  Matrix.of fun p q => v p * herm (Hpk k r) (bvec q) b

section tht

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sandw (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B')

def tht (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p) •
    sandw (QrD.ecOp π (ebM k r (Bw p) (SSn.prWv k r z a))) (QrD.ecOp π' (ebM k r (SSn.prWv k r z' a') (Bw' q)))

def thtA (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, conj (herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p)) •
    sandw (QrD.ecOp π (ebM k r (SSn.prWv k r z a) (Bw p))) (QrD.ecOp π' (ebM k r (Bw' q) (SSn.prWv k r z' a')))

end tht

def ThtFacts : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      (∀ a a' ι A B', B.hsInner (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι A) B' =
        B.hsInner A (thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι B')) ∧
      (∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z', ∀ a a' ι X,
        tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹)) ∧
        thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹))) ∧
      ∀ (c : ℂ) a a' ι, tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (c • a) (conj c • a') ι =
        (conj c) ^ 2 • tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι

def DatumUnit : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ), BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ (v : Fin S.f) (ζ : ℂ), (D.parOf S v).TT < Complex.normSq ζ →
      SSn.prWv S.G.k S.G.r (T v).base.z (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1 ∧
        SSn.prWv S.G.k S.G.r (T v).base.z' (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1

def ThtGaugeConst : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    PRho.Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k → ∀ l ∈ Finset.Icc 1 (S.G.k - 1),
    ∀ Bw Bw' : Fin S.G.k → Fin (2 * S.G.r + S.G.k + 1) → ℂ,
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z] Bw → Q.IsFrameOf S.G.k S.G.r [(T v).base.z'] Bw' →
      ∃ κ : M.Ty (D.parOf S v) → ℂ, ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ π ρ : M.Ty (D.parOf S v),
        M.Up (D.parOf S v) l π ρ →
        κ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw'
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) (e π ζ))) =
          ((Real.sqrt (M.Nrm (D.parOf S v) l π) : ℝ) : ℂ)

def SSnRepOfCut : Prop :=
  PRho.PRhoExists → PRho.GaugeLines → ThtFacts → DatumUnit → ThtGaugeConst → SSnRep

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroPointOver
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def levelZeroPointOver {k r : ℕ} (a : C.LPt) (hle : D.ptSize a ≤ r) (g : B.Mat k (r - D.ptSize a)) : B.Mat k r :=
  D.castM (by omega) (U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g)

def LeftFubini : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (T : D.LevTower k r Wp Wq),
    D.TowerNormalised T → ∀ (j : ℕ) (hj : j ≤ r), 1 ≤ j → ∀ (a : C.LPt) (ha : D.IsLocPt a j),
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (sx : X → B.Mat k r),
      (∀ x, sx x ∈ Sset k r T.base.z) ∧
      ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z', ∀ H : B.Mat k r → (Wq →L[ℂ] Wp),
        ContinuousOn H {x | x ∈ B.GV k r ∧ Dmin k r T.base.z T.base.z' x ⟨j, by omega⟩ ≠ 0} →
        (∃ R : ℝ, ∀ x ∈ B.GV k r, H x ≠ 0 → B.gN x ≤ R) →
        Integrable (fun x => ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj)
          (D.castM (by rw [ha.2]) g)))) μ ∧
        B.JF (T.bs j) (D.castF (by rw [ha.2]) (D.sliceAt k r T.base.z T.base.z' H a)) g =
          ∫ x, ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj) (D.castM (by rw [ha.2]) g))) ∂μ

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocalCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def SliceLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∀ (Φ Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c c' : Fin P.r → ℂ), c ∈ OmX P.r → c' ∈ OmX P.r →
    (∀ ζ ∈ Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)) →
    ∀ ζ ∈ Ann P, (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)

end preds

def GTSSLSliceDZ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), RadDZ P Bs T → SliceLoc P Bs T

def GTSSLSliceSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → (∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1

def GTSSLMat : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    (∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1) →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfExhaustOfAvgCutoff
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxI

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def AvgCutoff : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (K : Set ((Fin r → ℂ) × ℂ)),
    IsCompact K → K ⊆ QDom k r D.z D.z' →
    ∃ φ : B.Mat k r → ℂ, B.CkOn ⊤ (B.GV k r) φ ∧
      (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → φ g = 0) ∧
      ∀ p₀, D.inSS p₀ → ∀ q ∈ K, ∫ p, φ (B.sgs p (B.sgs p₀ (B.gq D q))) ∂D.μSS = 1

def AdjLeibniz : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq),
    B.SmoothCoef (Om k r D.z D.z') Θ →
    ∃ Θ' : B.DiffOp k r Wp Wq, B.opOrder Θ' = B.opOrder Θ ∧
      ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn (B.opOrder Θ : ℕ∞) (Om k r D.z D.z') f →
        ∀ g ∈ Om k r D.z D.z', B.opApply Θ' f g = B.opAdj Θ f g

variable {k r : ℕ}

theorem ckOn_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U V : Set (Mat k r)}
    (hUV : U ⊆ V) {f : Mat k r → E} (h : CkOn m V f) : CkOn m U f := by
  exact fun g₀ hg => h g₀ (hUV hg)

theorem om_sub_gv (z z' : Fin (2 * r + k + 1) → ℂ) : Om k r z z' ⊆ GV k r := by
  exact Set.inter_subset_left

end Formalism.FourierDecayAlt.P.JFxI

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGauge
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem mulQ_zbP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zbP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = star q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := mul_conjCoordinate_apply P f q

theorem mulQ_zP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := algebraMap_comp_ofPadicInt_apply P f q

theorem mulQ_ggiP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P ((MA.DQ P).ggiP P.TT) f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (f : MA.Qp P.r P.TT → ℂ) q := ggiP_apply P f q

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nabF_phase (P : M.Par) (hTT : 0 ≤ P.TT) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A B u : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hC : ConnF P Bs d e A B) (hu : PhaseEq P A B u) :
    NabF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  intro Φ
  constructor
  · funext ρ
    rw [actA_nabA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).1]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, hA, _⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).1
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Pi.add_apply, Pi.mul_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zbP, mulQ_ggiP, dzQ_apply P hTT, dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).1, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modA at hA
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hA
  · funext ρ
    rw [actA_nabsA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).2]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, _, hB⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).2
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Subalgebra.coe_neg, Pi.add_apply,
      Pi.mul_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zP, mulQ_ggiP, dzbQ_apply P hTT, dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).2, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modB at hB
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hB

end main

theorem gauge_transform_holds : GTCGauge := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk A B' u hAB hC hu
  have hTT : 0 ≤ P.TT := torus_parameter Wp Wq P Bs X d hH
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  exact ⟨isFrameB_phase P Bs e u he hu', kapF_phase P Bs d e u hu' hk,
    nabF_phase P hTT Bs d e A B' u hAB hC hu⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ZJ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r N : ℕ) (f : Q.Mx k r → E) (g₀ : Q.Mx k r) : Prop :=
  ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧
    (∀ g ∈ U, g ∈ Q.Glev k r (Fin.last r) → f g = F g) ∧ ∀ j ≤ N, iteratedFDeriv ℝ j F g₀ = 0

def GTCLRJetT : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (a b : Fin 2), ∃ N : ℕ, ∀ (f : Q.Mx k r → E) (g₀ : Q.Mx k r), g₀ ∈ Q.Glev k r (Fin.last r) →
      ZJ k r N f g₀ → Q.tL k r z z' (Fin.last r) Y a b f g₀ = 0

def GTCLRJetRad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
    ∀ N : ℕ, (∀ j ≤ N, iteratedFDeriv ℝ j
        (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2 = 0) →
      ZJ P.k P.r N ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1) (NF.muZ P.k P.r Bs.μsec q.2)

def GTCLRTaylor : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (ψ : ℂ → V) (U : Set ℂ) (ζ₀ : ℂ) (N : ℕ),
    IsOpen U → ζ₀ ∈ U → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ U →
    ∀ i ≤ N, iteratedFDeriv ℝ i (fun ζ => ψ ζ - ∑ j ∈ Finset.range (N + 1),
        ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ = 0

def GTCLRadTOfCut : Prop := GTCLRJetT → GTCLRJetRad → GTCLRTaylor → GTCLRadT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

def GLRight : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Gauge.IsFrameB P Bs e →
    (∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr →
    ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ (Y : ℝ) (X' : Wq →L[ℂ] Wp),
      (∀ v, X' v = X (Q.capRep P.k P.r Bs.π' Fr ((Y : ℂ) + ((P.k : ℂ) - 2) / 2) v)) →
      ∀ ρ : M.Ty P, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X') = M.xC P ρ (Y : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X)

def GLLeft : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [Bs.z, SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ] Fr →
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) ∧
      ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ (w : ℂ) (v : Wq),
        Q.capRep P.k P.r Bs.π Fr w (X v) =
          X (Q.capRep P.k P.r Bs.π' (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) w v)

def GaugeLinesOfCut : Prop := GLRight → GLLeft → GaugeLines

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end
