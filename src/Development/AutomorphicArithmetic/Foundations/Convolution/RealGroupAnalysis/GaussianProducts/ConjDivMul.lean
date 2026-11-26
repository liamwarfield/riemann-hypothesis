module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatSurj
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CharZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.BdInv
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExpInt
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.FockGauss
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem sq_le_qInf {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ e : F →+* ℝ, e δ < 0) (v : V4 F) : ∑ w, TR.pInf F (v 1) w ^ 2 ≤ qInf δ v := by
  rw [qInf]
  refine Finset.sum_le_sum fun w _ => ?_
  have hd : TR.pInf F (rt δ) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ :=
    congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap F δ) w
  have hneg := hδ (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  simp only [map_add (f := _), map_mul, map_pow, map_sub, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, map_ofNat, Pi.ofNat_apply, hd]
  have h3 : 0 ≤ -(InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ) * TR.pInf F (v 3) w ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [sq_nonneg (TR.pInf F (v 0) w), sq_nonneg (TR.pInf F (v 2) w)]

private theorem exp_le_gauss {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ e : F →+* ℝ, e δ < 0) (R : ℝ) (v : V4 F) :
    Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * Real.exp (-(Real.pi / 2) * qInf δ v) ≤
      Real.exp (∑ _w : InfinitePlace F, R ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hq := sq_le_qInf δ hδ v
  have hs : 0 ≤ ∑ w, TR.pInf F (v 1) w ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have h1 : ∑ w, TR.pInf F (v 1) w ^ 2 ≤ Real.pi / 2 * qInf δ v := by nlinarith
  have h2 : R * ∑ w, |TR.pInf F (v 1) w| ≤ ∑ w, TR.pInf F (v 1) w ^ 2 + ∑ _w : InfinitePlace F, R ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    have h := sq_abs (TR.pInf F (v 1) w)
    nlinarith [sq_nonneg (|TR.pInf F (v 1) w| - R), sq_nonneg R, sq_nonneg (|TR.pInf F (v 1) w|)]
  linarith

theorem UpperTheory.ConvolutionTheory.R2.G.fockGauss :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ e : F →+* ℝ, e δ < 0) → ∀ χ ∈ FockFn δ, ∀ (R : ℝ) (N : ℕ), ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧
    ∀ v, Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖χ v‖ ≤ B * wt4 L N v := by
  intro F _ _ _ δ hδ χ hχ
  induction hχ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨p, hp, g, hg, rfl⟩ := h
    intro R N
    have hmem := UpperTheory.ConvolutionTheory.R2.G.pgMem F δ hδ (Real.pi / 2) (by positivity) p hp g hg
    obtain ⟨M, L, hM, hb⟩ := GlobalTheory.CompanionTheory.EpConvB.exists_majorant hmem (C := {1}) isCompact_singleton N
    refine ⟨Real.exp (∑ _w : InfinitePlace F, R ^ 2) * M, L, mul_nonneg (Real.exp_pos _).le hM, fun v => ?_⟩
    have h1 := hb 1 rfl v
    rw [Units.val_one, Matrix.one_mulVec] at h1
    have hsplit : ‖p v * gauss δ v * g (finPartPi v)‖ =
        Real.exp (-(Real.pi / 2) * qInf δ v) *
          ‖p v * Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * (qInf δ v : ℝ)) * g (finPartPi v)‖ := by
      have hg2 : ‖gauss δ v‖ = Real.exp (-(Real.pi / 2) * qInf δ v) * Real.exp (-(Real.pi / 2) * qInf δ v) := by
        rw [gauss_eq, ← Real.exp_add, Complex.norm_exp]
        congr 1
        simp
        ring
      have hg3 : ‖Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * (qInf δ v : ℝ))‖ = Real.exp (-(Real.pi / 2) * qInf δ v) := by
        rw [Complex.norm_exp]
        congr 1
        simp
      simp only [norm_mul, hg2, hg3]
      ring
    rw [hsplit, ← mul_assoc]
    calc _ ≤ Real.exp (∑ _w : InfinitePlace F, R ^ 2) *
          ‖p v * Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * (qInf δ v : ℝ)) * g (finPartPi v)‖ :=
          mul_le_mul_of_nonneg_right (exp_le_gauss δ hδ R v) (norm_nonneg _)
      _ ≤ Real.exp (∑ _w : InfinitePlace F, R ^ 2) * (M * wt4 L N v) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = _ := by ring
  | zero =>
    intro R N
    exact ⟨0, 1, le_rfl, fun v => by simp⟩
  | add f g _ _ hf hg =>
    intro R N
    obtain ⟨B₁, L₁, h₁, hb₁⟩ := hf R N
    obtain ⟨B₂, L₂, h₂, hb₂⟩ := hg R N
    have hmono : ∀ {L' : (FractionalIdeal (𝓞 F)⁰ F)ˣ},
        (L' : FractionalIdeal (𝓞 F)⁰ F) ≤ (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂ : (FractionalIdeal (𝓞 F)⁰ F)ˣ) →
        ∀ v : V4 F, wt4 L' N v ≤ wt4 (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂) N v := fun h v =>
      Finset.prod_le_prod₀ (fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _)
        fun i _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_mono h N _
    refine ⟨B₁ + B₂, GroundTheory.Global.fractionalIdealSupUnit L₁ L₂, add_nonneg h₁ h₂, fun v => ?_⟩
    have he := (Real.exp_pos (R * ∑ w, |TR.pInf F (v 1) w|)).le
    calc Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖(f + g) v‖
        ≤ Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * (‖f v‖ + ‖g v‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) he
      _ = Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖f v‖ + Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖g v‖ := by ring
      _ ≤ B₁ * wt4 L₁ N v + B₂ * wt4 L₂ N v := add_le_add (hb₁ v) (hb₂ v)
      _ ≤ B₁ * wt4 (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂) N v + B₂ * wt4 (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂) N v :=
          add_le_add (mul_le_mul_of_nonneg_left (hmono le_sup_left v) h₁)
            (mul_le_mul_of_nonneg_left (hmono le_sup_right v) h₂)
      _ = _ := by ring
  | smul r f _ hf =>
    intro R N
    obtain ⟨B, L, hB, hb⟩ := hf R N
    refine ⟨‖r‖ * B, L, by positivity, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_left_comm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v) (norm_nonneg r)
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.expIntegrability

variable {F : Type} [Field F] [NumberField F]

private theorem adelicWeightFour_eq_product (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (x y : A F) :
    wt4 L N ![0, x, y, 0] = GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N x * GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N y := by
  simp [wt4, Fin.prod_univ_four, GlobalTheory.CompanionTheory.EpConvB.adeleWeight_zero]

private theorem term_int {N : ℕ} (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hN : ∫⁻ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
      ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ∂(ideleMeasure F) ≠ ⊤) :
    Integrable (fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 * wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0]) (ideleMeasure F) := by
  have hc : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 * wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
    simp only [adelicWeightFour_eq_product]
    have h1 := GlobalTheory.CompanionTheory.EpConvB.continuous_adeleWeight L N
    refine ((UpperTheory.ConvolutionTheory.R2.continuous_ab.inv₀ fun a => UpperTheory.ConvolutionTheory.R2.ab_ne_zero a).pow 2).mul
      ((h1.comp Units.continuous_coe_inv).mul (h1.comp Units.continuous_val))
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun a => ?_) (lt_top_iff_ne_top.2 hN)
  have hnn : 0 ≤ (ab a)⁻¹ ^ 2 * wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
    have : 0 ≤ wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] :=
      Finset.prod_nonneg fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    positivity
  rw [Real.enorm_of_nonneg hnn, ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' le_rfl ?_
  have h := ENNReal.le_tsum (f := fun ξ : Fin 2 → F =>
    ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)])) ![1, 0]
  simpa using h

variable [IsTotallyReal F]

private theorem abs_entry_le {k : G1 F} (hk : k ∈ KK F) (j : Fin 2) (w : InfinitePlace F) :
    |TR.pInf F (k 1 j) w| ≤ 1 := by
  have h1 : TR.pInf F ((k.1 * k.1ᵀ) 1 1) = TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) 1 1) :=
    congrArg (TR.infEq F).symm (hk.1 1 1)
  have h2 : (TR.pInf F (k 1 0) w) ^ 2 + (TR.pInf F (k 1 1) w) ^ 2 = 1 := by
    have h3 := congrFun h1 w
    simpa [Matrix.mul_apply, Fin.sum_univ_two, pow_two] using h3
  rw [abs_le_one_iff_mul_self_le_one]
  fin_cases j
  · show TR.pInf F (k 1 0) w * TR.pInf F (k 1 0) w ≤ 1
    nlinarith [sq_nonneg (TR.pInf F (k 1 1) w)]
  · show TR.pInf F (k 1 1) w * TR.pInf F (k 1 1) w ≤ 1
    nlinarith [sq_nonneg (TR.pInf F (k 1 0) w)]

private theorem sz_le (a : (A F)ˣ) {k : G1 F} (hk : k ∈ KK F) :
    sz (row (mD a * k)) ≤ 2 * ∑ w, |TR.pInf F ((a⁻¹ : (A F)ˣ) : A F) w| := by
  have e : ∀ (j : Fin 2) w, |TR.pInf F (row (mD a * k) j) w| ≤ |TR.pInf F ((a⁻¹ : (A F)ˣ) : A F) w| := by
    intro j w
    have h : row (mD a * k) j = ((a⁻¹ : (A F)ˣ) : A F) * k 1 j := by
      rw [row, specialLinear_mul_entry]
      simp [mD]
    rw [h, map_mul, Pi.mul_apply, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_entry_le hk j w)
  simp only [sz, Fin.sum_univ_two]
  rw [two_mul]
  exact add_le_add (Finset.sum_le_sum fun w _ => e 0 w) (Finset.sum_le_sum fun w _ => e 1 w)

private theorem sz_nonneg (r : Fin 2 → A F) : 0 ≤ sz r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem continuous_sz : Continuous fun g : G1 F => sz (row g) := by
  have h : Continuous (TR.infEq F).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  have hp : Continuous (TR.pInf F) := h.comp continuous_fst
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun w _ => ?_
  exact ((continuous_apply w).comp (hp.comp (UpperTheory.ConvolutionTheory.R2.continuous_entry 1 i))).abs

end UpperTheory.ConvolutionTheory.R2.G.expIntegrability

open UpperTheory.ConvolutionTheory.R2.G.expIntegrability in
theorem UpperTheory.ConvolutionTheory.R2.G.expInt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ R : ℝ,
    Integrable (fun p : IdeleGroup F × G1 F => ((Real.exp (R * sz (row (mD p.1 * p.2))) : ℝ) : ℂ) * iw (w1 W f.1 φ 1) p) M.ν := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ R
  have hS := UpperTheory.ConvolutionTheory.R2.hatSt F E D W
  have hK : IsCompact (KK F) := (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2
  obtain ⟨U, hUle, hUfd, hUmem⟩ := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).om φ hφ (KK F) hK fun k hk => hk.1
  obtain ⟨n, b, c, Bc, hb, -, hbd⟩ := UpperTheory.ConvolutionTheory.R2.G.coefBd F E D W φ (KK F) U hK hUfd hUmem
  obtain ⟨H, hH⟩ := UpperTheory.ConvolutionTheory.R2.G.hatLin F
  obtain ⟨N, hN⟩ := UpperTheory.ConvolutionTheory.R2.G.zetaFin F
  have hhat : ∀ i, hat (b i).1 ∈ FockFn D.δ := fun i =>
    UpperTheory.ConvolutionTheory.R2.G.hatFock F D.δ _ (mem_fock.1 (hUle (hb i)))
  have hg := fun i => UpperTheory.ConvolutionTheory.R2.G.fockGauss F D.δ D.neg (hat (b i).1) (hhat i) (2 * |R|) N
  choose Bg L hBg0 hBg using hg
  obtain ⟨Bf, hBf0, hBf⟩ := UpperTheory.ConvolutionTheory.R2.G.bdInv F π f hf (gl '' KK F) (hK.image UpperTheory.ConvolutionTheory.R2.continuous_gl)
  obtain ⟨-, -, -, -, hint⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ 1
  haveI := M.prob

  let T : Fin n → IdeleGroup F → ℝ := fun i a =>
    (ab a)⁻¹ ^ 2 * wt4 (L i) N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0]
  have hT : ∀ i, Integrable (T i) (ideleMeasure F) := fun i => term_int (L i) (hN (L i))
  let G : IdeleGroup F × G1 F → ℝ := fun p => ∑ i, Bf * |Bc| * Bg i * T i p.1
  have hG : Integrable G M.ν := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact ((hT i).comp_fst M.κ).const_mul (Bf * |Bc| * Bg i)
  have hexp : Continuous fun p : IdeleGroup F × G1 F => ((Real.exp (R * sz (row (mD p.1 * p.2))) : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul ?_))
    exact continuous_sz.comp ((UpperTheory.ConvolutionTheory.R2.continuous_mD.comp continuous_fst).mul continuous_snd)
  refine hG.mono' (hexp.aestronglyMeasurable.mul hint.1) ?_
  have hae : ∀ᵐ p ∂M.ν, p.2 ∈ KK F := by
    have h0 : ∀ᵐ k ∂M.κ, k ∈ KK F := by
      rw [ae_iff]
      exact M.supp
    exact Measure.quasiMeasurePreserving_snd.ae h0
  filter_upwards [hae] with p hp
  obtain ⟨a, k⟩ := p
  change k ∈ KK F at hp
  have hnu : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
  have hA0 : 0 < ab a := UpperTheory.ConvolutionTheory.R2.ab_pos a
  set v : V4 F := ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] with hv
  have hw : w1 W f.1 φ 1 (mD a * k) =
      Wf f.1 (gl (mD a * k)) * (((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) * hat (W.Om k φ).1 v) := by
    rw [w1, hnu, UpperTheory.ConvolutionTheory.R2.dM_one, mul_one, map_one, Module.End.one_apply, map_mul, Module.End.mul_apply, hS.m, hv]
    simp
  have hsum : hat (W.Om k φ).1 v = ∑ i, c i k * hat (b i).1 v := by
    have h1 := (hbd k hp).2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hH, h1, map_sum]
    simp [Finset.sum_apply, hH]
  have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
    have h1 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
      have := congrArg (Units.val) (W.η_sq a)
      simpa using this
    have h2 : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  have hWf : ‖Wf f.1 (gl (mD a * k))‖ * ab a ≤ Bf := by
    have h1 := (hBf 0 a (gl k) ⟨k, hp, rfl⟩).2
    rw [UpperTheory.ConvolutionTheory.R2.nU_zero, one_mul, ← UpperTheory.ConvolutionTheory.R2.gl_mul] at h1
    calc ‖Wf f.1 (gl (mD a * k))‖ * ab a ≤ Bf * (ab a)⁻¹ * ab a := mul_le_mul_of_nonneg_right h1 hA0.le
      _ = Bf := by field_simp
  set e : ℝ := Real.exp (R * sz (row (mD a * k))) with he
  have he0 : 0 < e := Real.exp_pos _
  have hterm : ∀ i, e * ‖hat (b i).1 v‖ ≤ Bg i * wt4 (L i) N v := by
    intro i
    have h1 : e ≤ Real.exp (2 * |R| * ∑ w, |TR.pInf F (v 1) w|) := by
      refine Real.exp_le_exp.2 ?_
      have h2 := sz_le a hp
      have h3 := sz_nonneg (row (mD a * k))
      have h4 : v 1 = ((a⁻¹ : (A F)ˣ) : A F) := by simp [hv]
      rw [h4]
      calc R * sz (row (mD a * k)) ≤ |R| * sz (row (mD a * k)) := mul_le_mul_of_nonneg_right (le_abs_self R) h3
        _ ≤ |R| * (2 * ∑ w, |TR.pInf F ((a⁻¹ : (A F)ˣ) : A F) w|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg R)
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans (hBg i v)
  have hS1 : e * ‖∑ i, c i k * hat (b i).1 v‖ ≤ ∑ i, |Bc| * (Bg i * wt4 (L i) N v) := by
    calc e * ‖∑ i, c i k * hat (b i).1 v‖ ≤ e * ∑ i, ‖c i k * hat (b i).1 v‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) he0.le
      _ = ∑ i, ‖c i k‖ * (e * ‖hat (b i).1 v‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul]
          ring
      _ ≤ ∑ i, |Bc| * (Bg i * wt4 (L i) N v) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul (((hbd k hp).1 i).trans (le_abs_self _)) (hterm i)
            (mul_nonneg he0.le (norm_nonneg _)) (abs_nonneg _)
  have hn : ‖((e : ℝ) : ℂ) * iw (w1 W f.1 φ 1) (a, k)‖ =
      (ab a)⁻¹ ^ 2 * (‖Wf f.1 (gl (mD a * k))‖ * ab a) * (e * ‖∑ i, c i k * hat (b i).1 v‖) := by
    simp only [iw]
    rw [hw, hsum]
    simp only [norm_mul, hη, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he0, abs_of_pos hA0, abs_pow, abs_inv]
    ring
  show ‖((e : ℝ) : ℂ) * iw (w1 W f.1 φ 1) (a, k)‖ ≤ ∑ i, Bf * |Bc| * Bg i * T i a
  rw [hn]
  have hq : 0 ≤ (ab a)⁻¹ ^ 2 := by positivity
  calc (ab a)⁻¹ ^ 2 * (‖Wf f.1 (gl (mD a * k))‖ * ab a) * (e * ‖∑ i, c i k * hat (b i).1 v‖)
      ≤ (ab a)⁻¹ ^ 2 * Bf * ∑ i, |Bc| * (Bg i * wt4 (L i) N v) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hWf hq) hS1 (by positivity) (by positivity)
    _ = ∑ i, Bf * |Bc| * Bg i * T i a := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [T, ← hv]
        ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.EqNUMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem eq_nU_mul {F : Type} [Field F] [NumberField F] {g g' : G1 F} (hr : row g = row g') :
    ∃ b, g' = nU b * g := by
  have h0 : g 1 0 = g' 1 0 := congrFun hr 0
  have h1 : g 1 1 = g' 1 1 := congrFun hr 1
  have hi : ∀ i j, (g⁻¹) i j = (!![g 1 1, -g 0 1; -g 1 0, g 0 0] : Matrix (Fin 2) (Fin 2) (A F)) i j :=
    fun i j => congrFun (congrFun (specialLinear_inv_val g) i) j
  have hn : g' * g⁻¹ = nU ((g' * g⁻¹) 0 1) := by
    have d := specialLinear_det_entries g
    have d' := specialLinear_det_entries g'
    apply specialLinear_ext_entries
    · rw [specialLinear_mul_entry, hi, hi]
      simp only [nU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      simp
      rw [h0, h1]
      linear_combination d'
    · simp [nU]
    · rw [specialLinear_mul_entry, hi, hi]
      simp [nU]
      rw [h0, h1]
      ring
    · rw [specialLinear_mul_entry, hi, hi]
      simp [nU]
      rw [← h0, ← h1]
      linear_combination d
  exact ⟨_, by rw [← hn, inv_mul_cancel_right]⟩

theorem UpperTheory.ConvolutionTheory.R2.G.contW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ,
    ContinuousOn (fun p : IdeleGroup F × G1 F => w1 W f.1 φ 1 (mD p.1 * p.2)) (Set.univ ×ˢ KK F) ∧
    ∀ g g', row g = row g' → w1 W f.1 φ 1 g = w1 W f.1 φ 1 g' := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ
  refine ⟨?_, fun g g' hr => ?_⟩
  · have hL : ∀ g, w1 W f.1 φ 1 g = Wf f.1 (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
      intro g
      have h1 : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
      simp [w1, h1]
    simp only [hL]
    obtain ⟨hLf, -⟩ := UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf
    obtain ⟨hWc, -⟩ := UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 hLf
    have hKc : IsCompact (KK F) := (_root_.UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2
    obtain ⟨U, -, hfd, hmem⟩ := (fockSt F E D W).om φ hφ (KK F) hKc (fun k hk => hk.1)
    obtain ⟨n, b, c, B, -, hc, hk⟩ := coefBd F E D W φ (KK F) U hKc hfd hmem
    obtain ⟨H, hH⟩ := hatLin F
    have hS := hatSt F E D W
    have e : ∀ p ∈ (Set.univ ×ˢ KK F : Set (IdeleGroup F × G1 F)),
        hat (W.Om (mD p.1 * p.2) φ).1 ![0, 1, 1, 0] = ((W.η.1 p.1 : ℂˣ) : ℂ) * ((ab p.1 : ℝ) : ℂ) *
          ∑ i, c i p.2 * (H (b i)).1 ![0, ((p.1⁻¹ : (A F)ˣ) : A F), (p.1 : A F), 0] := by
      rintro ⟨a, k⟩ ⟨-, hk'⟩
      have hv : (![(a : A F) * (![0, 1, 1, 0] : V4 F) 0, ((a⁻¹ : (A F)ˣ) : A F) * (![0, 1, 1, 0] : V4 F) 1,
          (a : A F) * (![0, 1, 1, 0] : V4 F) 2, (a : A F) * (![0, 1, 1, 0] : V4 F) 3] : V4 F) =
          ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
        funext i
        fin_cases i <;> simp
      simp only []
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, Module.End.mul_apply, hS.m, hv, (hk k hk').2, ← hH, map_sum]
      simp [Finset.sum_apply]
    have hcont1 : Continuous fun p : IdeleGroup F × G1 F => Wf f.1 (gl (mD p.1 * p.2)) :=
      hWc.comp (continuous_gl.comp ((continuous_mD.comp continuous_fst).mul continuous_snd))
    refine hcont1.continuousOn.mul (ContinuousOn.congr ?_ e)
    refine ContinuousOn.mul (Continuous.continuousOn ?_) (continuousOn_finsetSum _ fun i _ => ?_)
    · refine Continuous.mul ?_ ?_
      · exact Units.continuous_val.comp (W.η.2.1.comp continuous_fst)
      · exact Complex.continuous_ofReal.comp (continuous_ab.comp continuous_fst)
    · refine ContinuousOn.mul ((hc i).comp continuousOn_snd fun p hp => hp.2) (Continuous.continuousOn ?_)
      refine (continuous_of_mem_schwartzBruhatPi (H (b i)).2).comp (continuous_pi fun j => ?_)
      fin_cases j
      · exact continuous_const
      · exact Units.continuous_coe_inv.comp continuous_fst
      · exact Units.continuous_val.comp continuous_fst
      · exact continuous_const
  · obtain ⟨b, rfl⟩ := eq_nU_mul hr
    exact ((conv F E D W M π f hf φ hφ 1).2.2.2.1 b g).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomZero
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.RowMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.rowMul :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (p : (Fin 2 → A F) → ℂ) (φ φ' : S4 F), (∀ v, hat φ'.1 v = p ![v 0, v 1] * hat φ.1 v) →
    ∀ (g : G1 F) v, hat (W.Om g φ').1 v = p (![v 0, v 1] ᵥ* g.1) * hat (W.Om g φ).1 v := by
  intro F E _ _ _ _ _ _ _ D W
  have hS := hatSt F E D W
  let P : G1 F → Prop := fun g => ∀ (p : (Fin 2 → A F) → ℂ) (φ φ' : S4 F),
    (∀ v, hat φ'.1 v = p ![v 0, v 1] * hat φ.1 v) →
      ∀ v, hat (W.Om g φ').1 v = p (![v 0, v 1] ᵥ* g.1) * hat (W.Om g φ).1 v
  have hone : P 1 := by
    intro p φ φ' h v
    simpa using h v
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    intro a b ha hb p φ φ' h v
    have h1 := ha (fun r => p (r ᵥ* b.1)) (W.Om b φ) (W.Om b φ') (hb p φ φ' h) v
    simp only [map_mul, Module.End.mul_apply, Matrix.SpecialLinearGroup.coe_mul]
    rw [h1, Matrix.vecMul_vecMul]
  have hn : ∀ b, P (nU b) := by
    intro b p φ φ' h v
    rw [hS.n, hS.n, h]
    have e : ![Function.update v 1 (v 1 + b * v 0) 0, Function.update v 1 (v 1 + b * v 0) 1] =
        ![v 0, v 1] ᵥ* (nU b).1 := by
      ext i
      fin_cases i <;> simp [nU, Matrix.vecMul, dotProduct, Fin.sum_univ_two, add_comm, mul_comm]
    rw [e]
    ring
  have hw : P (wW F) := by
    intro p φ φ' h v
    rw [hS.w, hS.w]
    have e : ![-v 1, v 0] = ![v 0, v 1] ᵥ* (wW F).1 := by
      ext i
      fin_cases i <;> simp [wW, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [← e, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [h]
    simp [mul_assoc]
  have hninv : ∀ b : A F, (nU b)⁻¹ = nU (-b) := by
    intro b
    refine inv_eq_of_mul_eq_one_right ?_
    refine Subtype.ext ?_
    show (nU b).1 * (nU (-b)).1 = 1
    simp [nU, Matrix.one_fin_two, Matrix.mul_fin_two]
  have hwinv : (wW F)⁻¹ = wW F * wW F * wW F := by
    refine inv_eq_of_mul_eq_one_right ?_
    refine Subtype.ext ?_
    show (wW F).1 * ((wW F).1 * (wW F).1 * (wW F).1) = 1
    simp [wW, Matrix.one_fin_two, Matrix.mul_fin_two]
  let T : Subgroup (G1 F) :=
    { carrier := {g | P g ∧ P g⁻¹}
      mul_mem' := fun {a b} ha hb => ⟨hmul a b ha.1 hb.1, by
        rw [_root_.mul_inv_rev]; exact hmul _ _ hb.2 ha.2⟩
      one_mem' := ⟨hone, by rw [inv_one]; exact hone⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  have hle : Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) ≤ T := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨b, rfl⟩ | rfl)
    · exact ⟨hn b, by rw [hninv]; exact hn _⟩
    · exact ⟨hw, by rw [hwinv]; exact hmul _ _ (hmul _ _ hw hw) hw⟩
  intro p φ φ' h g v
  have hg : g ∈ T := hle (by rw [(gen F).1]; exact Subgroup.mem_top g)
  exact hg.1 p φ φ' h v
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.momZero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, (∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0) → ∀ φ ∈ Fock D.δ, ∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T →
    ∫ x : IdeleGroup F × G1 F, p (row (mD x.1 * x.2)) * T.indicator 1 (finPartPi (row (mD x.1 * x.2))) * iw (w1 W f.1 φ 1) x ∂M.ν = 0 := by
  intro F E _ _ _ _ _ _ _ D W M π f hf h0 φ hφ p hp T hc ho
  obtain ⟨φ', hφ', he⟩ := hatSurj F D.δ D.neg _
    ((fockMul F D.δ).1 _ (hatFock F D.δ _ (mem_fock.1 hφ)) p hp T hc ho)
  have hrow := rowMul F E D W (fun r => p r * T.indicator 1 (finPartPi r)) φ φ'
    (fun v => by rw [he])
  have hw : ∀ g : G1 F, w1 W f.1 φ' 1 g =
      p (row g) * T.indicator 1 (finPartPi (row g)) * w1 W f.1 φ 1 g := by
    intro g
    have hr : (![(0 : A F), 1] ᵥ* g.1) = row g := by
      ext i
      simp [row, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have h1 := hrow g ![0, 1, 1, 0]
    have h2 : (![(![0, 1, 1, 0] : V4 F) 0, (![0, 1, 1, 0] : V4 F) 1] : Fin 2 → A F) = ![0, 1] := by
      ext i
      fin_cases i <;> rfl
    rw [h2, hr] at h1
    simp only [w1, map_one, Module.End.one_apply]
    rw [h1]
    ring
  have hz := h0 φ' hφ'
  rw [← hz]
  simp only [W1, Meas.I0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [iw, hw]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomAdel
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem td_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

private theorem td_fin (F : Type) [Field F] [NumberField F] :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) :=
    fun v => td_adic v
  refine ⟨isTotallyDisconnected_of_image (f := fun (x : FiniteAdeleRing (𝓞 F) F) v => x v)
    (continuous_pi fun v => RestrictedProduct.continuous_eval v).continuousOn
    (fun x y h => Subtype.ext (funext fun v => congrFun h v))
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem basis_fin (F : Type) [Field F] [NumberField F] :
    TopologicalSpace.IsTopologicalBasis
      {T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) | IsCompact T ∧ IsOpen T} := by
  haveI := td_fin F
  have hb : TopologicalSpace.IsTopologicalBasis
      {s : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun T hT => hT.2) ?_
  intro x U hx hU
  obtain ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCU⟩ := hb.exists_subset_of_mem_open hxK isOpen_interior
  exact ⟨C, ⟨hKc.of_isClosed_subset hC.isClosed (hCU.trans interior_subset), hC.isOpen⟩, hxC,
    hCU.trans (interior_subset.trans hKU)⟩

section
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

private theorem cont_symm : Continuous (TR.infEq F).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem cont_pInf : Continuous (TR.pInf F) := (cont_symm F).comp continuous_fst

private noncomputable def xc (v : Fin 2 → A F) : Fin 2 × InfinitePlace F → ℝ := fun p => TR.pInf F (v p.1) p.2

private noncomputable def ec (y : (Fin 2 × InfinitePlace F → ℝ) × (Fin 2 → FiniteAdeleRing (𝓞 F) F)) :
    Fin 2 → A F :=
  fun i => ((TR.infEq F (fun w => y.1 (i, w)), y.2 i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

private theorem cont_xc : Continuous (xc F) :=
  continuous_pi fun p => (continuous_apply p.2).comp ((cont_pInf F).comp (continuous_apply p.1))

private theorem cont_fin : Continuous (finPartPi : (Fin 2 → A F) → Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

private theorem cont_ec : Continuous (ec F) := by
  refine continuous_pi fun i => ?_
  exact ((TR.continuous_infEq F).comp (continuous_pi fun w =>
    (continuous_apply (i, w)).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

private theorem ec_xc (v : Fin 2 → A F) : ec F (xc F v, finPartPi v) = v := by
  funext i
  refine TR.ad_ext ?_ rfl
  exact (TR.infEq F).symm_apply_apply _

private theorem poly_mem (t : Fin 2 × InfinitePlace F → ℝ) (n : ℕ) :
    (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ) ^ n) ∈ polyOn F (Fin 2) := by
  have h : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ))
      = ∑ p, (t p : ℂ) • (fun v : Fin 2 → A F => ((TR.pInf F (v p.1) p.2 : ℝ) : ℂ)) := by
    funext v
    simp [Finset.sum_apply, xc]
  have h1 : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ)) ∈ polyOn F (Fin 2) := by
    rw [h]
    refine Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ ?_ _
    exact Algebra.subset_adjoin (show _ ∈ {g : (Fin 2 → A F) → ℂ | ∃ i w, g = fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)} from ⟨p.1, p.2, rfl⟩)
  exact Subalgebra.pow_mem _ h1 n

private theorem sum_xc (v : Fin 2 → A F) : ∑ p, |xc F v p| = sz v := by
  rw [Fintype.sum_prod_type]; rfl

end

theorem UpperTheory.ConvolutionTheory.R2.G.momAdel :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : Ω → Fin 2 → A F) (ρ : Ω → ℂ), Measurable r →
    (∀ R : ℝ, Integrable (fun ω => ((Real.exp (R * sz (r ω)) : ℝ) : ℂ) * ρ ω) ν) →
    (∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T → ∫ ω, p (r ω) * T.indicator 1 (finPartPi (r ω)) * ρ ω ∂ν = 0) →
    ∀ q : (Fin 2 → A F) → ℂ, Measurable q → (∀ x, ‖q x‖ ≤ 1) → ∫ ω, q (r ω) * ρ ω ∂ν = 0 := by
  intro F _ _ _ Ω _ ν r ρ hr hint hmom q hq hq1
  have hρ : Integrable ρ ν := by simpa using hint 0
  have hX : Measurable fun ω => xc F (r ω) := (cont_xc F).measurable.comp hr
  have hs : Measurable fun ω => (finPartPi (r ω) : Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
    (cont_fin F).measurable.comp hr
  have hT : ∀ (T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)) (S : Set (Fin 2 × InfinitePlace F → ℝ)),
      MeasurableSet S → IsCompact T → IsOpen T →
      ∫ ω, S.indicator 1 (xc F (r ω)) * (T.indicator 1 (finPartPi (r ω)) * ρ ω) ∂ν = 0 := by
    intro T S hS hTc hTo
    have hi : Measurable fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) :=
      (measurable_one.indicator hTo.measurableSet).comp hs
    have hib : ∀ ω, ‖T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω))‖ ≤ 1 := by
      intro ω
      by_cases h : finPartPi (r ω) ∈ T <;> simp [h]
    have hI : ∀ g : Ω → ℂ, Integrable g ν →
        Integrable (fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) * g ω) ν :=
      fun g hg => hg.bdd_mul hi.aestronglyMeasurable (Eventually.of_forall hib)
    refine charZero Ω _ ν _ _ hX (hI ρ hρ) ?_ S hS
    refine momChar Ω _ ν _ _ hX (fun R => ?_) (fun n t => ?_)
    · simp only [sum_xc]
      refine (hI _ (hint R)).congr (Eventually.of_forall fun ω => ?_)
      simp only
      ring
    · have := hmom _ (poly_mem F t n) T hTc hTo
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      ring
  have hQ : Measurable fun y => q (ec F y) := hq.comp (cont_ec F).measurable
  have := prodExt Ω _ _ ν (fun ω => xc F (r ω)) (fun ω => finPartPi (r ω)) ρ (basis_fin F) hX hs hρ
    (fun S T hS hTc hTo => hT T S hS hTc hTo) _ hQ (fun y => hq1 _)
  simpa only [ec_xc] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Factor
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.factor :
    ∀ (X Y : Type) [TopologicalSpace X] [SigmaCompactSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (r : X → Y) (H : X → ℂ), Continuous r → Continuous H → (∀ x x', r x = r x' → H x = H x') → ∃ h : Y → ℂ, Measurable h ∧ ∀ x, h (r x) = H x := by
  intro X Y _ _ _ _ _ _ r H hr hH hf
  have key : ∀ F : Set X, IsClosed F → MeasurableSet (r '' F) := by
    intro F hF
    have e : r '' F = ⋃ n, r '' (F ∩ compactCovering X n) := by
      rw [← Set.image_iUnion, ← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
    rw [e]
    refine MeasurableSet.iUnion fun n => ?_
    exact (((isCompact_compactCovering X n).inter_left hF).image hr).isClosed.measurableSet
  have hrange : MeasurableSet (Set.range r) := by
    rw [← Set.image_univ]
    exact key _ isClosed_univ
  let h : Y → ℂ := fun y => if hy : ∃ x, r x = y then H hy.choose else 0
  have hh : ∀ x, h (r x) = H x := by
    intro x
    have hy : ∃ x', r x' = r x := ⟨x, rfl⟩
    simp only [h, dif_pos hy]
    exact hf _ _ hy.choose_spec
  refine ⟨h, measurable_of_isClosed fun C hC => ?_, hh⟩
  have himg : MeasurableSet (r '' (H ⁻¹' C)) := key _ (hC.preimage hH)
  have hout : ∀ y, y ∉ Set.range r → h y = 0 := by
    intro y hy
    have hy' : ¬ ∃ x, r x = y := hy
    simp only [h, dif_neg hy']
  by_cases h0 : (0 : ℂ) ∈ C
  · have e : h ⁻¹' C = r '' (H ⁻¹' C) ∪ (Set.range r)ᶜ := by
      ext y
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range r
        · obtain ⟨x, rfl⟩ := hyr
          refine Or.inl ⟨x, ?_, rfl⟩
          have : h (r x) ∈ C := hy
          rw [hh] at this
          exact this
        · exact Or.inr hyr
      · rintro (⟨x, hx, rfl⟩ | hy)
        · show h (r x) ∈ C
          rw [hh]
          exact hx
        · show h y ∈ C
          rw [hout y hy]
          exact h0
    rw [e]
    exact himg.union hrange.compl
  · have e : h ⁻¹' C = r '' (H ⁻¹' C) := by
      ext y
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range r
        · obtain ⟨x, rfl⟩ := hyr
          refine ⟨x, ?_, rfl⟩
          have : h (r x) ∈ C := hy
          rw [hh] at this
          exact this
        · have : h y ∈ C := hy
          rw [hout y hyr] at this
          exact absurd this h0
      · rintro ⟨x, hx, rfl⟩
        show h (r x) ∈ C
        rw [hh]
        exact hx
    rw [e]
    exact himg
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AeZero
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem kappa_ne_zero {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F)
    {U : Set (G1 F)} (hU : IsOpen U) {k : G1 F} (hk : k ∈ KK F) (hkU : k ∈ U) : M.κ U ≠ 0 := by
  intro h0
  obtain ⟨hKs, hC⟩ := UpperTheory.ConvolutionTheory.R2.M.kkCpt F
  have hmem : ∀ x ∈ KK F, ∀ y ∈ KK F, x * y⁻¹ ∈ KK F := by
    intro x hx y hy
    rw [hKs] at hx hy ⊢
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks F).mul_mem hx ((UpperTheory.ConvolutionTheory.R2.M.Ks F).inv_mem hy)
  have hnull : ∀ c ∈ KK F, M.κ ((fun x => c * x) ⁻¹' U) = 0 := by
    intro c hc
    have hm : Measurable (fun x : G1 F => c * x) := (continuous_const.mul continuous_id).measurable
    rw [← Measure.map_apply hm hU.measurableSet, M.κ_left c hc]
    exact h0
  obtain ⟨t, ht, hcov⟩ := hC.elim_nhds_subcover (fun x => (fun y => (k * x⁻¹) * y) ⁻¹' U) (by
    intro x hx
    refine ((continuous_const.mul continuous_id).isOpen_preimage _ hU).mem_nhds ?_
    simpa using hkU)
  have hK0 : M.κ (KK F) = 0 := by
    refine measure_mono_null hcov ?_
    exact (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => hnull _ (hmem k hk x (ht x hx))
  haveI := M.prob
  have hle : M.κ Set.univ ≤ M.κ (KK F) + M.κ (KK F)ᶜ := by
    rw [← Set.union_compl_self (KK F)]
    exact measure_union_le _ _
  rw [hK0, M.supp, measure_univ] at hle
  simp at hle

theorem UpperTheory.ConvolutionTheory.R2.G.aeZero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (u : IdeleGroup F × G1 F → ℂ), ContinuousOn u (Set.univ ×ˢ KK F) → (∀ᵐ p ∂M.ν, u p = 0) →
    ∀ a, ∀ k ∈ KK F, u (a, k) = 0 := by
  intro F _ _ _ M u hu h a k hk
  by_contra hne
  haveI := M.prob
  have hc : ContinuousWithinAt u (Set.univ ×ˢ KK F) (a, k) := hu (a, k) ⟨Set.mem_univ _, hk⟩
  have h1 : {p | u p ≠ 0} ∈ 𝓝[Set.univ ×ˢ KK F] (a, k) := hc.eventually_ne hne
  rw [nhdsWithin_prod_eq, Filter.mem_prod_iff] at h1
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := h1
  rw [nhdsWithin_univ, mem_nhds_iff] at ht₁
  obtain ⟨V, hVt, hVo, haV⟩ := ht₁
  obtain ⟨U, hUo, hkU, hUt⟩ := mem_nhdsWithin.1 ht₂
  have hnull : M.ν (V ×ˢ (U ∩ KK F)) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro p hp
    exact hsub ⟨hVt hp.1, hUt hp.2⟩
  have hprod : ideleMeasure F V * M.κ (U ∩ KK F) = 0 := by
    rw [← Measure.prod_prod]
    exact hnull
  have hV : ideleMeasure F V ≠ 0 := hVo.measure_ne_zero _ ⟨a, haV⟩
  have hU : M.κ (U ∩ KK F) ≠ 0 := by
    intro h0
    refine kappa_ne_zero M hUo hk hkU (measure_mono_null (t := (U ∩ KK F) ∪ (KK F)ᶜ) ?_ ?_)
    · intro x hx
      by_cases hxK : x ∈ KK F
      · exact Or.inl ⟨hx, hxK⟩
      · exact Or.inr hxK
    · exact measure_union_null h0 M.supp
  exact (mul_ne_zero hV hU) hprod
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem row_mD {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (g : G1 F) :
    UpperTheory.ConvolutionTheory.R2.G.row (mD a * g) = fun j => ((a⁻¹ : (A F)ˣ) : A F) * g 1 j := by
  funext j
  change ((mD a).1 * g.1) 1 j = _
  simp [mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem cont_row {F : Type} [Field F] [NumberField F] :
    Continuous (fun p : IdeleGroup F × G1 F => UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) := by
  have e : (fun p : IdeleGroup F × G1 F => UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) =
      fun p j => (((p.1 : (A F)ˣ)⁻¹ : (A F)ˣ) : A F) * p.2 1 j := by
    funext p
    exact row_mD _ _
  rw [e]
  refine continuous_pi fun j => ?_
  have h1 : Continuous fun p : IdeleGroup F × G1 F => (((p.1 : (A F)ˣ)⁻¹ : (A F)ˣ) : A F) :=
    Units.continuous_val.comp (continuous_inv.comp continuous_fst)
  have h2 : Continuous fun g : G1 F => g 1 j :=
    (continuous_apply j).comp ((continuous_apply (1 : Fin 2)).comp
      (Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous))
  exact h1.mul (h2.comp continuous_snd)

private theorem conj_div_mul (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    (starRingEnd ℂ z) / (‖z‖ : ℂ) * ((c : ℂ) * z) = ((‖(c : ℂ) * z‖ : ℝ) : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  have h1 : starRingEnd ℂ z * z = (‖z‖ : ℂ) ^ 2 := Complex.conj_mul' z
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  push_cast
  field_simp
  linear_combination (c : ℂ) * h1

private theorem ae_KK {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) :
    ∀ᵐ p ∂M.ν, p.2 ∈ KK F := by
  rw [ae_iff]
  have e : {p : IdeleGroup F × G1 F | ¬ p.2 ∈ KK F} = Set.univ ×ˢ (KK F)ᶜ := by
    ext p
    simp
  haveI := M.prob
  rw [e, Meas.ν, Measure.prod_prod, M.supp, mul_zero]

private theorem exists_q {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (u : G1 F → ℂ)
    (hc : ContinuousOn (fun p : IdeleGroup F × G1 F => u (mD p.1 * p.2)) (Set.univ ×ˢ KK F))
    (hrow : ∀ g g', UpperTheory.ConvolutionTheory.R2.G.row g = UpperTheory.ConvolutionTheory.R2.G.row g' → u g = u g') :
    ∃ h : (Fin 2 → A F) → ℂ, Measurable h ∧ ∀ (a : IdeleGroup F), ∀ k ∈ KK F,
      h (UpperTheory.ConvolutionTheory.R2.G.row (mD a * k)) = u (mD a * k) := by
  have hr := cont_row (F := F)
  haveI : CompactSpace (KK F) := isCompact_iff_compactSpace.1 (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2
  have hι : Continuous fun x : IdeleGroup F × KK F => ((x.1, x.2.1) : IdeleGroup F × G1 F) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hmem : ∀ x : IdeleGroup F × KK F,
      ((x.1, x.2.1) : IdeleGroup F × G1 F) ∈ (Set.univ ×ˢ KK F : Set (IdeleGroup F × G1 F)) :=
    fun x => Set.mk_mem_prod (Set.mem_univ _) x.2.2
  have hH : Continuous fun x : IdeleGroup F × KK F => u (mD x.1 * x.2.1) := by
    have h := ContinuousOn.comp_continuous (g := fun p : IdeleGroup F × G1 F => u (mD p.1 * p.2))
      (f := fun x : IdeleGroup F × KK F => ((x.1, x.2.1) : IdeleGroup F × G1 F)) hc hι hmem
    simpa only [Function.comp_def] using h
  have hR : Continuous fun x : IdeleGroup F × KK F => UpperTheory.ConvolutionTheory.R2.G.row (mD x.1 * x.2.1) := by
    have h := hr.comp hι
    simpa only [Function.comp_def] using h
  obtain ⟨h, hm, hh⟩ := UpperTheory.ConvolutionTheory.R2.G.factor (IdeleGroup F × KK F) (Fin 2 → A F)
    (fun x => UpperTheory.ConvolutionTheory.R2.G.row (mD x.1 * x.2.1)) (fun x => u (mD x.1 * x.2.1))
    hR hH (fun x x' e => hrow _ _ e)
  exact ⟨h, hm, fun a k hk => hh (a, ⟨k, hk⟩)⟩

private theorem core {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F)
    (u : G1 F → ℂ)
    (hc : ContinuousOn (fun p : IdeleGroup F × G1 F => u (mD p.1 * p.2)) (Set.univ ×ˢ KK F))
    (hrow : ∀ g g', UpperTheory.ConvolutionTheory.R2.G.row g = UpperTheory.ConvolutionTheory.R2.G.row g' → u g = u g')
    (hI : Integrable (iw u) M.ν)
    (hmom : ∀ q : (Fin 2 → A F) → ℂ, Measurable q → (∀ x, ‖q x‖ ≤ 1) →
      ∫ p : IdeleGroup F × G1 F, q (UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) * iw u p ∂M.ν = 0) :
    ∀ a, ∀ k ∈ KK F, u (mD a * k) = 0 := by
  obtain ⟨h, hm, hh⟩ := exists_q u hc hrow
  let q : (Fin 2 → A F) → ℂ := fun y => (starRingEnd ℂ (h y)) / (‖h y‖ : ℂ)
  have hqm : Measurable q :=
    (Complex.continuous_conj.measurable.comp hm).div (Complex.continuous_ofReal.measurable.comp hm.norm)
  have hq1 : ∀ y, ‖q y‖ ≤ 1 := by
    intro y
    by_cases e : h y = 0
    · simp [q, e]
    · have hn : ‖h y‖ ≠ 0 := by simpa using e
      simp [q, hn]
  have hae : (fun p : IdeleGroup F × G1 F => q (UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) * iw u p) =ᵐ[M.ν]
      fun p => ((‖iw u p‖ : ℝ) : ℂ) := by
    filter_upwards [ae_KK M] with p hp
    have e' : h (UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) = u (mD p.1 * p.2) := hh p.1 p.2 hp
    simp only [q, e', iw]
    exact conj_div_mul _ (by positivity) _
  have hz : ∫ p, ‖iw u p‖ ∂M.ν = 0 := by
    have h1 : ∫ p, ((‖iw u p‖ : ℝ) : ℂ) ∂M.ν = 0 := by
      rw [← integral_congr_ae hae]
      exact hmom q hqm hq1
    rw [integral_complex_ofReal] at h1
    exact_mod_cast h1
  have hz' := (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hI.norm).1 hz
  refine UpperTheory.ConvolutionTheory.R2.G.aeZero F M (fun p => u (mD p.1 * p.2)) hc ?_
  filter_upwards [hz'] with p hp
  have hp' : iw u p = 0 := by simpa using hp
  have hpos : 0 < ab (p.1 : (A F)ˣ) := (IdeleGroup.ideleModule F p.1).2
  have hne : ((((ab p.1)⁻¹ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    have : ((ab p.1)⁻¹ ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  exact (mul_eq_zero.1 hp').resolve_left hne

theorem UpperTheory.ConvolutionTheory.R2.G.zeroW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, (∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0) → ∀ φ ∈ Fock D.δ, ∀ a, ∀ k ∈ KK F, w1 W f.1 φ 1 (mD a * k) = 0 := by
  intro F E _ _ _ _ _ _ _ D W M π f hf h0 φ hφ
  obtain ⟨hc, hrow⟩ := UpperTheory.ConvolutionTheory.R2.G.contW F E D W M π f hf φ hφ
  have hE := UpperTheory.ConvolutionTheory.R2.G.expInt F E D W M π f hf φ hφ
  have hI : Integrable (iw (w1 W f.1 φ 1)) M.ν := by
    simpa using hE 0
  exact core M _ hc hrow hI fun q hq hq1 =>
    UpperTheory.ConvolutionTheory.R2.G.momAdel F (IdeleGroup F × G1 F) M.ν (fun p => UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2))
      (iw (w1 W f.1 φ 1)) cont_row.measurable hE
      (UpperTheory.ConvolutionTheory.R2.G.momZero F E D W M π f hf h0 φ hφ) q hq hq1
