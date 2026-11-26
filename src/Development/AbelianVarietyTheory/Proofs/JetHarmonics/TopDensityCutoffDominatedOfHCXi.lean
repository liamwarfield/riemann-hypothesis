module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficients
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedDerivBddOfEventuallyConst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficient
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BasicOperatorsPolynomialLiftNoInversePower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityDominated
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundSmoothDecayingCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecOpApplyCutFEq
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem vec_opApply_cutF_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Θ : B.DiffOp P.k P.r Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (δ : ℝ) (γ : C.LPt), C6.IsCut0 χ → 0 < δ → δ < TBB.Gp p γ → p.V (B.opApply Θ (D.cutF p.T.base χ f δ)) γ = p.V (B.opApply Θ f) γ := by
  intro Wp Wq _ _ _ _ _ _ P p Θ f χ δ γ hχ hδ hlt
  have hlt0 : δ < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ := hlt
  have hopen : IsOpen {x : B.Mat P.k P.r | δ < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have hloc : ∀ g, δ < Gf P.k P.r p.T.base.z p.T.base.z' g →
      B.opApply Θ (D.cutF p.T.base χ f δ) g = B.opApply Θ f g := by
    intro g hg
    refine Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Θ hopen (fun x hx => ?_) g hg
    have hx' : δ < Gf P.k P.r p.T.base.z p.T.base.z' x := hx
    simp only [D.cutF]
    rw [hχ.2.2 _ ((one_le_div hδ).mpr hx'.le), Complex.ofReal_one, one_smul]
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · have hG := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r p.T.base.z p.T.base.z' γ h'.choose h.1 h'.choose_spec.2.1
    have hlt' : δ < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := hG ▸ hlt0
    have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae p.T.base h'.choose
      (D.muR p.T.base h'.choose (h.1.2 ▸ D.ptPerm γ)) (B.opApply Θ (D.cutF p.T.base χ f δ)) (B.opApply Θ f) 1 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS p.T.base] with q hq
        simp only [D.orbIntegrand, B.rho, one_smul]
        rw [hloc _ (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs p.T.base hq]; exact hlt')])
    rw [e, one_smul]
  · rfl
  · rfl

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContinuousOfIsPolyDeg
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Filter Topology

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma norm_opApply_le_of_polynomial_coeffs_lemma {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (A : ℝ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (B : ℝ), _root_.Formalism.FourierDecayAlt.B.CCle A o G B →
      ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ ≤ C * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
  induction Θ with
  | nil => exact ⟨0, le_rfl, fun G B hG g _ => by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply]⟩
  | cons T Θ ih =>
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih (fun S hS => hΘ S (List.mem_cons_of_mem _ hS))
    obtain ⟨hlen, Q, hQ, hcoef⟩ := hΘ T List.mem_cons_self
    obtain ⟨CQ, hCQ0, hCQ⟩ := _root_.PI.UnitaryCorollaryDerivatives.pb_nonneg (_root_.PI.UnitaryCorollaryDerivatives.pb_poly hQ) 0
    have hunit : ∀ X ∈ List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word, _root_.Formalism.FourierDecayAlt.B.unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm_unit (T.word_lie Y hY)
    set ν : ℝ := ‖((List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nz T.word).prod : ℂ)‖ with hν
    refine ⟨CQ * ν + C₁, by positivity, fun G B hG g hg => ?_⟩
    have hgpos : 0 < _root_.Formalism.FourierDecayAlt.B.gN g := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg
    have hB : 0 ≤ B := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hG
    have hRw : _root_.Formalism.FourierDecayAlt.B.CCle A 0 (_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G) B :=
      _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw hunit (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by simpa using hlen) hG)
    have hRw' := hRw.2 [] [] (by simp) (by simp) (by simp) g hg
    simp only [_root_.Formalism.FourierDecayAlt.B.dLR, List.foldr_nil, _root_.Formalism.FourierDecayAlt.B.Rw] at hRw'
    have hword : ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖ ≤ B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A) := by
      rw [Real.rpow_neg hgpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgpos _),
        mul_comm]
      simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using hRw'
    have hQg : ‖Q g‖ ≤ CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) := by
      have := hCQ [] (by simp) (by simp) g hg
      simpa [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw] using this
    have hterm : ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
      rw [hcoef, smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        congrFun (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_scale T.word G) g, norm_smul, ← hν, sub_eq_add_neg,
        Real.rpow_add hgpos]
      calc ‖Q g‖ * (ν * ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖)
          ≤ (CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ)) * (ν * (B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A))) := by
            gcongr
        _ = CQ * ν * B * (_root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A)) := by ring
    have hrest := hC₁ G B hG g hg
    have hsplit : _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) G g = (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g := by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply]
    rw [hsplit]
    calc ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖
        ≤ ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ + ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ := norm_add_le _ _
      _ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) + C₁ * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) :=
          add_le_add hterm hrest
      _ = (CQ * ν + C₁) * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by ring

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma continuousOn_opApply_of_polynomial_coeffs_lemma_2 {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) G) :
    ContinuousOn (_root_.Formalism.FourierDecayAlt.B.opApply Θ G) (_root_.Formalism.FourierDecayAlt.B.GV k r) := by
  apply _root_.Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
  intro T hT
  obtain ⟨-, Q, hQ, hcoef⟩ := hΘ T hT
  have hQc : Continuous Q := (_root_.Formalism.FourierDecayAlt.P.poly_adm (n := 0) hQ).1.continuous
  have hRw : ContinuousOn (_root_.Formalism.FourierDecayAlt.B.Rw T.word G) (_root_.Formalism.FourierDecayAlt.B.GV k r) :=
    _root_.Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' subset_rfl (_root_.Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hG T.word_lie)
  have hfun : (fun g => (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)) =
      fun g => Q g • _root_.Formalism.FourierDecayAlt.B.Rw T.word G g := by
    funext g
    rw [hcoef]
    simp
  rw [hfun]
  exact hQc.continuousOn.smul hRw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem _root_.GlobalTheory.HatNF.vecV_cut_polyOp : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (o κ : ℕ) (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp P.k P.r Wp Wq) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o κ Θ → _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F → _root_.Formalism.FourierDecayAlt.B.InCC A o F → c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A - 1 - κ → ∀ cut : ℕ → _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, (∀ n g, cut n g = ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) → ∀ γ : _root_.Formalism.FourierDecayAlt.C.LPt, Filter.Tendsto (fun n => p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) γ) Filter.atTop (nhds (p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) γ)) := by
  obtain ⟨c₃, hc₃⟩ := _root_.Formalism.FourierDecayAlt.P.PBE.vecV_tendsto
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p o κ Θ F A hΘ hF hCC hA cut hcut γ
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hΘ
  have hΘ' : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := by
    intro T hT
    obtain ⟨hl, Q, hQ, hc, -⟩ := hΘ T hT
    exact ⟨hl, Q, hQ, hc⟩
  have hcutφ : ∀ n : ℕ, cut n = fun g => _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := by
    intro n
    funext g
    rw [hcut]
    rfl
  have hψ : ∀ (n : ℕ) g, cut n g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    have h : _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := rfl
    rw [hcutφ, h]
    ring
  unfold _root_.Formalism.FourierDecayAlt.B.InCC at hCC
  obtain ⟨b, hb⟩ := hCC
  have hb0 : 0 ≤ b := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hb
  have hb1 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F b := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨K, hK0, hK⟩ := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) o
  have hGn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o (fun g => cut n g • F g) (b + K * b) := by
    intro n
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb1 (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) (hK ((n : ℝ) + 1) hR A F b hb))
    refine _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (_root_.Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr ?_ h3) ?_
    · intro g _
      rw [hψ n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    · rw [norm_neg, norm_one, one_mul]
      linarith [div_le_self (mul_nonneg hK0 hb0) (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)]
  have hG0 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F (b + K * b) := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb1 (by nlinarith)
  obtain ⟨C, hC0, hC⟩ := norm_opApply_le_of_polynomial_coeffs_lemma o κ (A - 1) Θ hΘ'
  have hexp : (κ : ℝ) - (A - 1) = -(A - 1 - κ) := by ring
  have hckn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) (fun g => cut n g • F g) := by
    intro n
    have h := (_root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_nice (R := (n : ℝ) + 1) (by positivity) hF).1
    rw [hcutφ n]
    exact h
  unfold _root_.Formalism.FourierDecayAlt.KB.Pl.V
  refine hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ (A - 1 - κ) hA
    (fun n => _root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) (C * (b + K * b))
    (by positivity)
    (fun n => (continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' (hckn n)).mono
      (fun g hg => hg.1))
    ((continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' hF).mono (fun g hg => hg.1))
    (fun n g hg => by
      have := hC _ _ (hGn n) g hg.1
      rwa [hexp] at this)
    (fun g hg => by
      have := hC _ _ hG0 g hg.1
      rwa [hexp] at this) ?_
  intro g _
  set S : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℝ := fun h => ∑ i, ∑ j, Complex.normSq (h i j) with hS
  have hScont : Continuous S :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  have hO : IsOpen {h | S h < S g + 1} := isOpen_lt hScont continuous_const
  obtain ⟨N, hN⟩ := exists_nat_ge (S g + 1)
  apply tendsto_const_nhds.congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  symm
  apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Θ hO _ g (by simp)
  intro h hh
  have hSh : S h < S g + 1 := hh
  have hS0 : 0 ≤ S h := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Complex.normSq_nonneg _
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hscaled : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • h) i j) =
      ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h := by
    simp only [hS, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
      Complex.normSq_ofReal, Finset.mul_sum]
  have hle : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h ≤ 1 := by
    rw [← mul_inv, inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hone : cut n h = 1 := by
    rw [hcut, hscaled, Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  simp only [hone, one_smul]

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundSmoothDecayingCoefficients
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Filter Topology

namespace GlobalTheory.HatNF

theorem tendsto_list_map_sum_real {α : Type*} (l : List α) (u : α → ℕ → ℝ) (v : α → ℝ)
    (h : ∀ x ∈ l, Tendsto (u x) atTop (𝓝 (v x))) :
    Tendsto (fun n => (l.map fun x => u x n).sum) atTop (𝓝 (l.map v).sum) :=
  tendsto_list_sum l h

theorem wordBound_decay : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → w.length ≤ N → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ∃ (e : ℕ) (A : ℝ), CutPow e φ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧ Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - (2 * (P.r : ℝ) + 2) * e) := by
  intro a ha Cb
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.HatNF.vecV_cut_polyOp
  obtain ⟨c₂, hc₂⟩ := Formalism.FourierDecayAlt.P.PBE.vecV_cut_op
  refine ⟨5 * max Cb 8 + max Cb 8 ^ 2 + 1 + |max c₁ c₂|, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p N w hDD hw hwN
  obtain ⟨C, J, Θs, hC, hpoly, hB⟩ := GlobalTheory.T.wordBound_compactSupportCoefficients a ha Wp Wq P0 p w hw
  refine ⟨C, J, Θs, hC, hpoly, ?_⟩
  rintro φ f ⟨e₀, A, hφ, hf, hfA, hA⟩ e c hc hG
  have hXn : ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) = 2 * (P0.r : ℝ) + P0.k + 1 := by push_cast; ring
  have hr0 : (0 : ℝ) ≤ P0.r := Nat.cast_nonneg _
  have hrX : (P0.r : ℝ) + 1 ≤ 2 * (P0.r : ℝ) + P0.k + 1 := by
    have : (0 : ℝ) ≤ P0.k := Nat.cast_nonneg _
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hCb8 : (8 : ℝ) ≤ max Cb 8 := le_max_right _ _
  have hCb0 : (0 : ℝ) ≤ max Cb 8 := by linarith
  have hwN' : (w.length : ℝ) ≤ N := by exact_mod_cast hwN
  have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ (2 * (P0.r : ℝ) + 2) * e₀ := by positivity
  have hcut' : ∀ n g, Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r n g = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    simp [Formalism.FourierDecayAlt.P.CutBP.cutN, Formalism.FourierDecayAlt.P.JCx2.pdPsi, Formalism.FourierDecayAlt.P.JCx2.pdPhi, Formalism.FourierDecayAlt.P.JCx2.pdChi,
      Formalism.FourierDecayAlt.P.JCx2.pdSq]
  have hmono : ∀ c : ℝ, c ≤ max c₁ c₂ → ∀ B' : ℝ,
      max c₁ c₂ * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) + 1) ≤ B' →
      c * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) + 1) ≤ B' := by
    intro c hc B' hB
    rw [hXn]
    refine le_trans ?_ hB
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
  obtain ⟨δ₀, hδ₀, hφ0⟩ := hφ.2.1
  set γ := TBB.bigPt P0.r c with hγ
  set δ : ℝ := min δ₀ (TBB.Gp p γ / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδ1 : δ ≤ δ₀ := min_le_left _ _
  have hδ2 : δ < TBB.Gp p γ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ → ℝ, C6.IsCut0 χ := ⟨_, Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation⟩
  have hmul : ∀ n, mulG p.T.base φ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n) =
      fun g => Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r n g • mulG p.T.base φ f g := by
    intro n
    funext g
    simp only [mulG, Formalism.FourierDecayAlt.P.CutBP.apx, D.cutF]
    by_cases hg : Gf P0.k P0.r p.T.base.z p.T.base.z' g < δ₀
    · simp [hφ0 _ hg]
    · rw [hχ.2.2 _ ((one_le_div hδ).2 (hδ1.trans (not_lt.1 hg)))]
      simp only [Complex.ofReal_one, one_smul]
      exact smul_comm _ _ _
  have hn := fun n => hB φ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n)
    ⟨hφ.1, Formalism.FourierDecayAlt.P.CutBP.cptCoef_apx P0 p.T.base hχ hf hδ n⟩ e c hc hG
  simp only [hmul] at hn
  refine le_of_tendsto_of_tendsto' (b := atTop) ?_ ?_ hn
  · refine Tendsto.norm ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_)
    obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hDD w hw e
    have hcongr : ∀ G, p.V (p.Θ.Θ w e G) γ = D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop G) γ :=
      fun G => Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ γ
        (fun g hg => hΘ G g ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
    rw [hcongr]
    have ho' : (o : ℝ) ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
      calc (o : ℝ) ≤ Cb * w.length * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) := ho
        _ ≤ max Cb 8 * w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by
          rw [hXn]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
            (by linarith)
        _ ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwN' hCb0) (by linarith)
    have hκ' : (κ : ℝ) ≤ max Cb 8 * ((P0.r : ℝ) + 1) * o :=
      hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
        (Nat.cast_nonneg _))
    have hthr := Formalism.FourierDecayAlt.P.PBE.thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 8) (max c₁ c₂) o κ _
      hr0 hrX hN0 hCb0 (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
    obtain ⟨hck, bF, hbF⟩ := GlobalTheory.HatNF.mulG_ckOn_inCC Wp Wq P0 p.T.base e₀ o φ f A hφ hf (hfA o)
    have hv : ∀ g, Gf P0.k P0.r p.T.base.z p.T.base.z' g < δ₀ → mulG p.T.base φ f g = 0 := by
      intro g hg
      simp [mulG, hφ0 _ hg]
    have hth := hmono c₂ (le_max_right _ _)
      (A - (2 * (P0.r : ℝ) + 2) * ((e₀ : ℝ) + o) - 1 - ((κ : ℝ) + 3 * ((P0.r : ℝ) + 1) * o)) (by linarith [hthr])
    have key := hc₂ P0.k P0.r Wp Wq p.T.base p.ν' p.m₀ γ (mulG p.T.base φ f) (Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r)
      nf fib o κ Dop δ₀ _ bF hfib hIn hδ₀ hv hck hbF hcut' hth
    exact key.congr fun n => (hcongr _).symm
  · refine Tendsto.const_mul _ (tendsto_list_map_sum_real Θs
      (fun Θ n => ‖B.hsVec (p.V (B.opApply Θ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n)) γ)‖)
      (fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) γ)‖) fun Θ hΘ => ?_)
    refine Tendsto.norm ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_)
    rw [← GlobalTheory.HatNF.vec_opApply_cutF_eq Wp Wq P0 p Θ f χ δ γ hχ hδ hδ2]
    set o : ℕ := w.length * (2 * P0.r + P0.k + 1) with ho
    set κ : ℕ := w.length * (8 * (P0.r + 1) * (2 * P0.r + P0.k + 1)) with hκ
    have hoR : (o : ℝ) = w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by rw [ho]; push_cast; ring
    have hκR : (κ : ℝ) = 8 * ((P0.r : ℝ) + 1) * o := by rw [hoR, hκ]; push_cast; ring
    have ho' : (o : ℝ) ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
      rw [hoR]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    have hκ' : (κ : ℝ) ≤ max Cb 8 * ((P0.r : ℝ) + 1) * o := by
      rw [hκR]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb8 (by linarith)) (Nat.cast_nonneg _)
    have hthr := Formalism.FourierDecayAlt.P.PBE.thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 8) (max c₁ c₂) o κ _
      hr0 hrX hN0 hCb0 (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
    have h3 : (0 : ℝ) ≤ 3 * ((P0.r : ℝ) + 1) * o := by positivity
    exact hc₁ Wp Wq P0 p o κ Θ (D.cutF p.T.base χ f δ) (A - 2 * ((P0.r : ℝ) + 1) * o) (hpoly Θ hΘ)
      (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf δ)
      (Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hfA hδ _ o (by linarith))
      (hmono c₁ (le_max_left _ _) _ (by linarith [hthr])) (Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r) (fun _ _ => rfl) γ

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundSmoothDecayingCoefficientsStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordBound_smooth_decaying_coefficients : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → w.length ≤ N → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ∃ (e : ℕ) (A : ℝ), CutPow e φ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧ Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - (2 * (P.r : ℝ) + 2) * e) := by
  first | exact @GlobalTheory.HatNF.wordBound_decay | exact GlobalTheory.HatNF.wordBound_decay | (intros; apply GlobalTheory.HatNF.wordBound_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableEmptyWordDensityDecayingCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableEmptyWordDensityDecayingCoefficients
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

namespace GlobalTheory.HatNF.EmptyWordL2

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem integrable_weight_normSq (hXi : B.XiExists) {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ)
    (hF : ∀ m : ℕ, B.InCC A m F) (hAB : B.AB k r ≤ A) (hT : JF.TransportedAlt k r A 0) :
    Integrable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) := by
  obtain ⟨-, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.BXiAsm.any_of hXi k r Wp Wq D A hAB
  obtain ⟨c4, hc4⟩ := hF 4
  have hfin := (hB1 F F c4 c4 (hF 5) (hF 5) hc4 hc4).1
  have h := Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates k r Wp Wq D A 0 F hT (hF 0)
  have h2 : ContinuousOn (fun q => B.JF D F (B.gq D q)) (Formalism.FourierDecayAlt.P.B7.Q0 D) := h.continuousOn
  have h3 : ContinuousOn (fun q => B.hsVec (B.JF D F (B.gq D q))) (Formalism.FourierDecayAlt.P.B7.Q0 D) :=
    (LinearMap.continuous_of_finiteDimensional
      (⟨⟨B.hsVec, fun X Y => by ext; simp [B.hsVec]⟩, fun a X => by ext; simp [B.hsVec]⟩ :
        (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp))).comp_continuousOn h2
  have hmeas : AEStronglyMeasurable
      (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) volume :=
    Formalism.FourierDecayAlt.P.JCx2.rb_aesm D _ ((Formalism.FourierDecayAlt.P.JCx2.rb_contOn_bcW D).mul (h3.norm.pow 2)) fun q h => by simp [h]
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q =>
    mul_nonneg (Formalism.FourierDecayAlt.P.JCx2.rb_bcWeight_nonneg _ _ q) (sq_nonneg _))]
  exact lt_of_le_of_ne le_top hfin

theorem Ew_bigPt_eq_indicator {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      (Formalism.FourierDecayAlt.P.B7.Q0 p.T.base).indicator
        (fun q => bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q *
          ‖B.hsVec (B.JF p.T.base F (B.gq p.T.base q))‖ ^ 2)
        ((fun j => c j.castSucc), c (Fin.last P.r)) := by
  by_cases hq : ((fun j : Fin P.r => c j.castSucc), c (Fin.last P.r)) ∈ Formalism.FourierDecayAlt.P.B7.Q0 p.T.base
  · rw [Set.indicator_of_mem hq]
    obtain ⟨hc, hlt⟩ := hq
    dsimp only at hc hlt
    have hTT : 0 < Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' := mul_pos p.T.base.T_pos p.T.base.T'_pos
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p F hl, Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt P.k P.r _ _ c hlt.le
    rw [hn, Real.mul_self_sqrt (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _)]
    rfl
  · rw [Set.indicator_of_notMem hq]
    refine Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p F fun h => hq ⟨fun a => ?_, ?_⟩
    · exact (h.1.1 (1, c a.castSucc) (by
        unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a.castSucc, rfl⟩)).2
    · exact Formalism.FourierDecayAlt.P.PBM.zeta_big _ c h.2

end

theorem integrable_density_nil_of_xiExists (hXi : B.XiExists) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) := by
  refine ⟨10, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p H A _ hCC hA
  have ha : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  set x : ℝ := (P.r : ℝ) + 1 with hx
  set n : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hn
  have hx1 : 1 ≤ x := by linarith
  have hn1 : 1 ≤ n := by linarith
  have h1 : x ≤ x ^ 4 := le_self_pow₀ hx1 (by norm_num)
  have h2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have h3 : x * n ^ 2 ≤ x ^ 4 * n ^ 3 := mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 : 10 * (x * n ^ 2) ≤ A := by nlinarith
  have h5 : n ≤ n ^ 2 := le_self_pow₀ hn1 (by norm_num)
  have h6 : x * n ≤ x * n ^ 2 := mul_le_mul_of_nonneg_left h5 (by linarith)
  have h7 : 1 ≤ x * n := by nlinarith
  have hAB : B.AB P.k P.r ≤ A := by
    unfold B.AB
    rw [← hx]
    have : ((P.k : ℝ) + P.r) * x ≤ n * x := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have hT : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    rw [← hx, ← hn]
    nlinarith
  have hint := (integrable_weight_normSq hXi p.T.base H A hCC hAB hT).indicator
    (Formalism.FourierDecayAlt.P.B7.isOpen_good_set p.T.base).measurableSet
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  have h8 := (hmp.integrable_comp_emb e.measurableEmbedding).2 hint
  refine h8.congr (Filter.Eventually.of_forall fun c => ?_)
  simp only [Function.comp]
  rw [he c]
  exact (Ew_bigPt_eq_indicator p H c).symm

theorem integrable_density_nil : GlobalTheory.HCXi.BesselXiIntegrable → ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) :=
  fun h => integrable_density_nil_of_xiExists (GlobalTheory.HCXi.xiExists_of_besselXiIntegrable h)

end GlobalTheory.HatNF.EmptyWordL2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableEmptyWordDensityDecayingCoefficientsStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_emptyWordDensity_decayingCoefficients : GlobalTheory.HCXi.BesselXiIntegrable → ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) := by
  first | exact @GlobalTheory.HatNF.EmptyWordL2.integrable_density_nil | exact GlobalTheory.HatNF.EmptyWordL2.integrable_density_nil | (intros; apply GlobalTheory.HatNF.EmptyWordL2.integrable_density_nil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NeZeroOfIsLocPt
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

namespace GlobalTheory.TopDensityBound

section aux

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_comp_sq_le (E : Wp →L[ℂ] Wp) (X : Wq →L[ℂ] Wp) :
    ‖B.hsVec (E.comp X)‖ ^ 2 ≤ ‖E‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact E.le_opNorm _

variable {P : M.Par}

theorem V_eq_zero (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt)
    (h : ¬ 0 < TBB.Gp p γ) : p.V F γ = 0 := by
  unfold KB.Pl.V D.vecV
  rw [dite_eq_right]
  exact fun h' => h h'.2

theorem RR_cons (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (hw : w ≠ [])
    {γ : C.LPt} (hγ : D.IsLocPt γ (P.r + 1)) :
    p.RR F (P.r + 1) w γ γ = ((∑ e : Ix (Fin w.length), ∑ ρ : M.Ty P,
      Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e F) γ))‖ ^ 2 : ℝ) : ℂ) := by
  have : p.RR F (P.r + 1) w γ γ = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w γ γ := by
    simp [KB.Pl.RR, D.RRplace, hγ, hw]
  rw [this]
  unfold Top.topOf
  push_cast
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self]
  simp only [TBB.TTp, KB.Pl.V]
  push_cast
  ring

theorem Ew_eq (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) w γ =
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ)) *
        (p.RR F (P.r + 1) w γ γ).re := by
  unfold TBB.Ew TBB.NP TBB.normC
  rw [Complex.re_ofReal_mul]
  simp

theorem ne_zero_of_isLocPt {r : ℕ} (c : Fin (r + 1) → ℂ) (h : D.IsLocPt (TBB.bigPt r c) (r + 1)) (l : Fin (r + 1)) :
    c l ≠ 0 := by
  have := h.1 (1, c l) (by unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨l, rfl⟩)
  exact this.2

theorem wPt_bigPt (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) :
    Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c) = ‖∏ l, c l‖ ^ 2 / TBB.Gp p (TBB.bigPt P.r c) := by
  unfold Top.wPt TBB.Gp
  have h : D.ptMatN (TBB.bigPt P.r c) (P.r + 1) = U.hMat 1 c := Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt c
  rw [h, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Complex.normSq_eq_norm_sq]

end aux

theorem top_density_le : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), ∃ C : ℝ, 0 ≤ C ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬((∀ l, c l ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = 0) ∧ ((∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) ∧ TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) = TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 ∧ |TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c)| ≤ C * TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * (‖∏ l, c l‖ ^ 2 / TBB.Gp p (TBB.bigPt P.r c)) ^ w.length * ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2) := by
  intro Wp Wq _ _ _ _ _ _ P p w
  set K : Ix (Fin w.length) → ℝ := fun e => ∑ ρ : M.Ty P, |(Top.cW P p.l0 w e ρ).re| * ‖p.TP.E ρ‖ ^ 2 with hK
  have hK0 : ∀ e, 0 ≤ K e := fun e => Finset.sum_nonneg fun ρ _ => by positivity
  have hS0 : 0 ≤ ∑ e, K e := Finset.sum_nonneg fun e _ => hK0 e
  refine ⟨1 + ∑ e, K e, by linarith, fun H c => ⟨fun hn => ?_, fun hc hG => ?_⟩⟩
  · rw [Ew_eq]
    by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
    · have hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c) := fun h => hn ⟨ne_zero_of_isLocPt c hl, h⟩
      by_cases hw : w = []
      · subst hw
        rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.RR_top p H hl, V_eq_zero p _ _ hG, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self,
          Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_zero]
        simp
      · rw [RR_cons p H w hw hl]
        simp [V_eq_zero p _ _ hG, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_zero]
    · have : p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c) = 0 := by
        simp [KB.Pl.RR, D.RRplace, hl]
      rw [this]; simp
  · have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
    have hn : 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) := by
      unfold TBB.TTp
      rw [Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt _ _ _ _ c hζ.le]
      exact Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _
    have hnil : TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) =
        TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 := by
      rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p H hl, Real.mul_self_sqrt hn]
    refine ⟨hn, hnil, ?_⟩
    by_cases hw : w = []
    · subst hw
      rw [hnil, abs_of_nonneg (by positivity)]
      simp only [p.Θ.nil, List.length_nil, pow_zero, mul_one]
      rw [Finset.sum_const]
      have hcard : (Finset.univ : Finset (Ix (Fin 0))).card = 1 := by simp [Ix]
      rw [hcard, one_smul]
      have : 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 := by
        positivity
      rw [mul_assoc]
      exact le_mul_of_one_le_left this (le_add_of_nonneg_right hS0)
    · rw [Ew_eq, Real.mul_self_sqrt hn, RR_cons p H w hw hl, Complex.ofReal_re, abs_of_nonneg (by positivity),
        ← wPt_bigPt]
      set Wt := Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c) with hWt
      have hW0 : 0 ≤ Wt := by rw [hWt, wPt_bigPt]; positivity
      have key : (∑ e : Ix (Fin w.length), ∑ ρ : M.Ty P,
          Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
            ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c)))‖ ^ 2) ≤
          (1 + ∑ e, K e) * Wt ^ w.length *
            ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun e _ => ?_
        set v := ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2 with hv
        have hv0 : 0 ≤ v := by positivity
        have hKe : K e ≤ 1 + ∑ e, K e := by
          have := Finset.single_le_sum (f := K) (fun e _ => hK0 e) (Finset.mem_univ e)
          linarith
        calc _ ≤ K e * Wt ^ w.length * v := by
              simp only [hK]
              rw [Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_le_sum fun ρ _ => ?_
              have h1 : Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 ≤
                  Wt ^ w.length * |(Top.cW P p.l0 w e ρ).re| := by
                unfold Top.dH
                rw [← hWt, Real.sq_sqrt']
                exact max_le (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) (by positivity)
              have h2 := hsVec_comp_sq_le (p.TP.E ρ) (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))
              calc _ ≤ (Wt ^ w.length * |(Top.cW P p.l0 w e ρ).re|) * (‖p.TP.E ρ‖ ^ 2 * v) :=
                    mul_le_mul h1 h2 (by positivity) (by positivity)
                _ = _ := by ring
          _ ≤ _ := by gcongr
      calc _ ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ((1 + ∑ e, K e) * Wt ^ w.length *
            ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left key hn
        _ = _ := by ring

end GlobalTheory.TopDensityBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompExpIteratedDerivBounded
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology

theorem cutoff_comp_exp_iteratedDeriv_bounded (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv p (fun t => χ (Real.exp t)) t| ≤ C := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hc : ∀ k t : ℝ, iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
    intro k t
    cases p with
    | zero => simp
    | succ n => simp [iteratedDeriv_succ']
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hs.comp Real.contDiff_exp
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log δ → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have := Real.exp_lt_exp.mpr hs
      rw [Real.exp_log hδ] at this
      simp only [hh, h0 _ this]
    rw [this.iteratedDeriv_eq p, hc]; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, h1 _ this]
    rw [this.iteratedDeriv_eq p, hc]
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log δ) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C0 1, le_trans zero_le_one (le_max_right _ _), fun t => ?_⟩
  rcases lt_or_ge t (Real.log δ) with h1 | h1
  · rw [hlow t h1]; simp
  · rcases lt_or_ge 0 t with h2 | h2
    · rw [hhigh t h2]; split_ifs <;> simp
    · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)

theorem ld_cut_pow_bound (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (e j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  choose B hB0 hB using cutoff_comp_exp_iteratedDeriv_bounded χ hχ
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * (e : ℝ) ^ (j - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB0 i)) (by positivity), ?_⟩
  intro ε x hε hx
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hχ.1.comp Real.contDiff_exp
  unfold LE.ld
  have e1 : (fun u : ℝ => χ (Real.exp u / ε) * Real.exp u ^ e) =
      fun u : ℝ => h (u - Real.log ε) * Real.exp ((e : ℝ) * u) := by
    funext u
    simp only [hh]
    rw [Real.exp_sub, Real.exp_log hε, Real.exp_nat_mul]
  have c1 : ContDiff ℝ j (fun u : ℝ => h (u - Real.log ε)) :=
    (hsm.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have c2 : ContDiff ℝ j (fun u : ℝ => Real.exp ((e : ℝ) * u)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  beta_reduce
  rw [e1, iteratedDeriv_fun_mul c1.contDiffAt c2.contDiffAt, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [iteratedDeriv_comp_sub_const, iteratedDeriv_exp_const_mul]
  beta_reduce
  rw [Real.exp_nat_mul, Real.exp_log hx, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j.choose i : ℝ)),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (e : ℝ) ^ (j - i) * x ^ e), ← mul_assoc]
  have := hB i (Real.log x - Real.log ε)
  gcongr

theorem ld_cut_pow : ∀ (χ : ℝ → ℝ) (e J : ℕ), C6.IsCut0 χ →
    (∀ ε : ℝ, 0 < ε → CutPow e fun y => χ (y / ε) * y ^ e) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → ∀ j, j ≤ J →
        |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  intro χ e J hχ
  constructor
  · intro ε hε
    obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
    refine ⟨(hs.comp (contDiff_id.div_const ε)).mul (contDiff_id.pow e), ⟨δ * ε, by positivity, fun x hx => ?_⟩,
      1, ε, fun x hx => ?_⟩
    · have : x / ε < δ := by rwa [div_lt_iff₀ hε]
      simp [h0 _ this]
    · have : 1 ≤ x / ε := by rwa [le_div_iff₀ hε, one_mul]
      simp [h1 _ this]
  · choose C hC0 hC using ld_cut_pow_bound χ hχ e
    refine ⟨∑ j ∈ Finset.range (J + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun ε x hε hx j hj => ?_⟩
    refine (hC j ε x hε hx).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.mpr (by omega))

end GlobalTheory.HatNF
end

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem dom_pow_le (G : ℝ) (hG : 0 < G) (m q : ℕ) (h : m ≤ q) : G ^ m ≤ 1 + G ^ q := by
  rcases le_total G 1 with h1 | h1
  · have := pow_le_one₀ (n := m) hG.le h1
    have := pow_pos hG q
    linarith
  · have := pow_le_pow_right₀ h1 h
    linarith

theorem dom_real_bound {ι κ : Type} [Fintype ι] [Fintype κ] (E Ct n D G C S C' : ℝ) (L a p₀ : ℕ)
    (u : ι → ℝ) (v : κ → ℝ) (hCt : 0 ≤ Ct) (hn : 0 ≤ n) (hD : 0 < D) (hG : 0 < G) (hC : 0 ≤ C)
    (hS0 : 0 ≤ S) (hS : S ≤ C' * G ^ p₀) (hu0 : ∀ e, 0 ≤ u e) (hv0 : ∀ t, 0 ≤ v t)
    (hL : L * (1 + 2 * a) ≤ 2 * p₀)
    (hu : ∀ e, u e ≤ C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * S * ∑ t, v t)
    (hE : E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2) :
    E ≤ (Ct * Fintype.card ι * (C * C') ^ 2 * Fintype.card κ) *
      ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hL
  have hT0 : 0 ≤ ∑ t, v t := Finset.sum_nonneg fun t _ => hv0 t
  have hT : (∑ t, v t) ^ 2 ≤ Fintype.card κ * ∑ t, v t ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ)) (f := v)
  have hV0 : 0 ≤ ∑ t, v t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
  have h1 : ∑ e, u e ^ 2 ≤ Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
    have : ∀ e ∈ (Finset.univ : Finset ι),
        u e ^ 2 ≤ (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
      intro e _
      refine pow_le_pow_left₀ (hu0 e) ((hu e).trans ?_) 2
      gcongr
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  have h2 : (D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2 = G ^ m := by
    have e : (G ^ p₀) ^ 2 = G ^ L * (G ^ (a * L)) ^ 2 * G ^ m := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      rw [mul_comm p₀ 2, hm]; ring
    rw [mul_pow, e, div_pow, inv_pow, inv_pow, ← pow_mul D 2 L, mul_comm 2 L, pow_mul D L 2]
    have := pow_pos hD L
    have := pow_pos hG L
    have := pow_pos hG (a * L)
    field_simp
  have h3 : G ^ m ≤ 1 + (G ^ p₀) ^ 2 := by
    rw [← pow_mul]
    exact dom_pow_le G hG _ _ (by omega)
  have h4 : ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) = n * (1 + (G ^ p₀) ^ 2) * ∑ t, v t ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  calc E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2 := hE
    _ ≤ Ct * n * (D ^ 2 / G) ^ L *
        (Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2) := by gcongr
    _ = Ct * n * Fintype.card ι * (C * C') ^ 2 *
        ((D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2) * (∑ t, v t) ^ 2 := by ring
    _ ≤ Ct * n * Fintype.card ι * (C * C') ^ 2 * (1 + (G ^ p₀) ^ 2) * (Fintype.card κ * ∑ t, v t ^ 2) := by
        rw [h2]; gcongr
    _ = _ := by rw [h4]; ring

theorem dom_thr (Cc r k : ℝ) (N L : ℝ) (hCc : 8 ≤ Cc) (hr : 0 ≤ r) (hk : 0 ≤ k) (hL : L ≤ N) (hN : 0 ≤ N) :
    L * (8 * (r + 1) * (2 * r + k + 1)) ≤ Cc * (r + 1) ^ 4 * (N * (2 * r + k + 1) ^ 2) := by
  have h1 : r + 1 ≤ (r + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have h2 : 2 * r + k + 1 ≤ (2 * r + k + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  calc L * (8 * (r + 1) * (2 * r + k + 1)) ≤ N * (Cc * (r + 1) ^ 4 * (2 * r + k + 1) ^ 2) := by
        have : 0 ≤ Cc := by linarith
        gcongr
    _ = _ := by ring

theorem top_density_dominated : GlobalTheory.HCXi.BesselXiIntegrable → ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ) (w : List C.Letter), C6.IsCut0 χ → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) → N * (1 + 2 * a P.r) ≤ 2 * p₀ → KB.CutWord P p.l0 w → w.length ≤ N → (∀ ε : ℝ, 0 < ε → AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ ε : ℝ, 0 < ε → ∀ c₀ : Fin (P.r + 1) → ℂ, ‖(fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) c₀‖ ≤ h c₀ := by
  intro hXi a ha Cb
  obtain ⟨C1, h1⟩ := GlobalTheory.T.wordBound_smooth_decaying_coefficients a ha Cb
  obtain ⟨C2, h2⟩ := GlobalTheory.T.integrable_emptyWordDensity_decayingCoefficients hXi
  refine ⟨max C1 (max C2 8), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ N w hχ hDD hf hfA hth hN hw hwN
  have hc1 : C1 ≤ max C1 (max C2 8) := le_max_left _ _
  have hc2 : C2 ≤ max C1 (max C2 8) := (le_max_left _ _).trans (le_max_right _ _)
  have hc8 : 8 ≤ max C1 (max C2 8) := (le_max_right _ _).trans (le_max_right _ _)
  generalize max C1 (max C2 8) = Cc at hth hc1 hc2 hc8
  obtain ⟨C, J, Θs, hC, hpoly, hb⟩ := h1 Wp Wq P p N w hDD hw hwN
  obtain ⟨hcut, C', hC', hld⟩ := ld_cut_pow χ p₀ J hχ
  obtain ⟨Ct, hCt, htop⟩ := GlobalTheory.TopDensityBound.top_density_le Wp Wq P p w
  constructor
  · intro ε hε
    have hs := (GlobalTheory.HatNF.mulG_ckOn_inCC Wp Wq P p.T.base p₀ 0 _ f A₀ (hcut ε hε) hf (hfA 0)).1
    have hm := GlobalTheory.TopVec.aestronglyMeasurable_tv Wp Wq P p Cb _ w hDD hw hs
    simp only [GlobalTheory.TopVec.Ew_eq_norm_tv_sq]
    exact hm.norm.pow 2
  have hth1 : C1 * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (2 * (P.r : ℝ) + 2) * p₀ := by
    refine le_trans ?_ (hth.trans (le_of_eq (by push_cast; ring)))
    gcongr
  set d : ℝ := ((w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1)) : ℕ) : ℝ) with hd
  have hth2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by
    have e1 := dom_thr Cc P.r P.k N w.length hc8 (by positivity) (by positivity) (by exact_mod_cast hwN) (by positivity)
    have e2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤
        Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by gcongr
    have e3 : d = (w.length : ℝ) * (8 * ((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1)) := by
      rw [hd]; push_cast; ring
    rw [mul_add] at hth
    linarith
  have hΘ : ∀ t : Fin Θs.length, B.CkOn ⊤ (B.GV P.k P.r) (B.opApply Θs[t.1] f) ∧
      ∀ m : ℕ, B.InCC (A₀ - d) m (B.opApply Θs[t.1] f) := fun t =>
    Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds P.k P.r Wp Wq _ d A₀ (by positivity)
      ((polyOp_ok P.k P.r Wp Wq _ _ _ (hpoly _ (List.getElem_mem t.2))).2.1 d le_rfl) f hf hfA
  refine ⟨fun c => (Ct * Fintype.card (Ix (Fin w.length)) * (C * ((J + 1) * C')) ^ 2 * Fintype.card (Fin Θs.length)) *
    ∑ t : Fin Θs.length, (TBB.Ew p (fun _ => 1) (B.opApply Θs[t.1] f) (P.r + 1) [] (TBB.bigPt P.r c) +
      TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Θs[t.1] f g)
        (P.r + 1) [] (TBB.bigPt P.r c)), ?_, ?_⟩
  · refine Integrable.const_mul (integrable_finsetSum _ fun t _ => Integrable.add ?_ ?_) _
    · refine h2 Wp Wq P p _ (A₀ - d) (hΘ t).1 (hΘ t).2 (hth2.trans ?_)
      have : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by positivity
      linarith
    · exact h2 Wp Wq P p _ _ (Formalism.FourierDecayAlt.P.CutBP.ckOn_Gpow_smul _ _ p₀ (hΘ t).1)
        (Formalism.FourierDecayAlt.P.CutBP.inCC_Gpow_smul _ _ p₀ (hΘ t).2) hth2
  intro ε hε c
  beta_reduce
  by_cases hc : (∀ l, c l ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  swap
  · rw [(htop _ c).1 hc, norm_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ =>
      add_nonneg (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _) (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _))
  obtain ⟨hc0, hG⟩ := hc
  obtain ⟨hn, -, hE⟩ := (htop (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) c).2 hc0 hG
  have hGp : ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      p.V (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • F g) (TBB.bigPt P.r c) =
        ((TBB.Gp p (TBB.bigPt P.r c) ^ p₀ : ℝ) : ℂ) • p.V F (TBB.bigPt P.r c) := by
    intro F
    by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
    · exact Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow p F p₀ hl hG
    · rw [Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), smul_zero]
  simp only [fun H => ((htop H c).2 hc0 hG).2.1, hGp, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
  rw [Real.norm_eq_abs]
  refine dom_real_bound _ Ct _ ‖∏ l, c l‖ _ C
    (∑ j ∈ Finset.range (J + 1), |LE.ld j (fun y => χ (y / ε) * y ^ p₀) (TBB.Gp p (TBB.bigPt P.r c))|) _
    w.length (a P.r) p₀ _ (fun t : Fin Θs.length => ‖B.hsVec (p.V (B.opApply Θs[t.1] f) (TBB.bigPt P.r c))‖)
    hCt hn (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun l _ => hc0 l)) hG hC
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    ((Nat.mul_le_mul_right _ hwN).trans hN) ?_ hE
  · have := Finset.sum_le_card_nsmul (Finset.range (J + 1)) _ _ fun j hj =>
      hld ε _ hε hG j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    simpa [mul_assoc] using this
  · intro e
    have := hb _ f ⟨p₀, A₀, hcut ε hε, hf, hfA, hth1⟩ e c hc0 hG
    rwa [← Fin.sum_univ_fun_getElem] at this

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffDominatedOfHCXi
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem topDensity_cut_dominated_all :
    GlobalTheory.HCXi.BesselXiIntegrable → Formalism.FourierDecayAlt.P.CutBP.NFTopDomAll := by
  intro hΞ Cb
  obtain ⟨Cc, H⟩ := GlobalTheory.HatNF.top_density_dominated hΞ (fun _ => 0) GlobalTheory.T.basicOperators_polynomialLift_no_inversePower Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  obtain ⟨hm, h, hi, hb⟩ := H Wp Wq P p f A₀ p₀ χ N w a1 a2 a3 a4 a5 (by simpa using a6) hw.1 hN
  have e : ∀ ε : ℝ,
      D.cutF p.T.base χ (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε =
      mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f := by
    intro ε
    funext g
    simp only [D.cutF, Formalism.FourierDecayAlt.P.TBBx4.fpm, mulG, ContinuousLinearMap.comp_id, smul_smul]
    try push_cast
    try rfl
  refine ⟨eventually_nhdsWithin_of_forall fun ε hε => ?_, h, hi,
    eventually_nhdsWithin_of_forall fun ε hε => ae_of_all _ fun c => ?_⟩
  · rw [e]; exact hm ε hε
  · rw [e]; exact hb ε hε c
end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffDominatedOfHCXiStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDensity_cutoff_dominated_of_HC_xi : GlobalTheory.HCXi.BesselXiIntegrable → Formalism.FourierDecayAlt.P.CutBP.NFTopDomAll := by
  first | exact @GlobalTheory.HatNF.topDensity_cut_dominated_all | exact GlobalTheory.HatNF.topDensity_cut_dominated_all | (intros; apply GlobalTheory.HatNF.topDensity_cut_dominated_all <;> assumption)
end
