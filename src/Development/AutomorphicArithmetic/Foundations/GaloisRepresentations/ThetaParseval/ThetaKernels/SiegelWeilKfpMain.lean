module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.KFinPolyOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLineC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKKfpGeoLine
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLrhoPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpRotVac

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilOswgenHg
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def zInv_k (z : InfinitePlace F → Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ :=
  fun i => if i.2.2.2 then (z i.1 i.2.1 i.2.2.1).re else (z i.1 i.2.1 i.2.2.1).im
variable (d) in
def zLE_k : (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ) ≃ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (d := d)
  invFun := _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zInv_k (d := d)
  map_add' u v := by
    funext w a j
    apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k]
  map_smul' c u := by
    funext w a j
    apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k]
  left_inv u := by
    funext i
    obtain ⟨w, a, j, b⟩ := i
    cases b <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zInv_k]
  right_inv z := by
    funext w a j
    apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zInv_k]
theorem hg_sch_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg' : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) : ∃ h : 𝓢(_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d, ℂ), ⇑h = _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  let Zc : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).trans (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zLE_k d).toContinuousLinearEquiv
  let c : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin d.m × Fin d.n × Fin 2 → AF F) := fun u y k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (Zc u) k)) (y k) : AF F)
  have hc1 : ∀ u y, (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c u y k).1) = L.symm (Zc u) := by
    intro u y
    funext k
    exact RingEquiv.apply_symm_apply _ _
  have hjn : ∀ u y, _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y = d.cmb (c u y) := by
    intro u y
    refine (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).unique ⟨_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k R u y, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R u y⟩ ⟨?_, ?_⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k]
      intro w
      rw [← hL (c u y) w, hc1, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    · funext k
      show (d.crd (d.cmb (c u y)) k).2 = y k
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k]
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  have hint : ∀ g' ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), Integrable (fun y => g' y * star (g y)) νf := by
    intro g' hg''
    have hc : Continuous (fun y => g' y * star (g y)) :=
      hg''.1.continuous.mul (continuous_star.comp hg'.1.continuous)
    exact hc.integrable_of_hasCompactSupport (hg''.2.mul_right (f' := fun y => star (g y)))
  have key : ∀ Φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), (∀ u, Integrable (fun y => Φ (c u y) * star (g y)) νf) ∧
      ∃ h : 𝓢(_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d, ℂ), ∀ u, h u = ∫ y, Φ (c u y) * star (g y) ∂νf := by
    intro Φ hΦ
    unfold schA at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hmem =>
      obtain ⟨φ, g', hg'', rfl⟩ := hmem
      have e : ∀ u y, pureA F φ g' (c u y) = φ (L.symm (Zc u)) * g' y := by
        intro u y
        simp only [pureA]
        rw [hc1]
      refine ⟨fun u => ?_, ⟨(∫ y, g' y * star (g y) ∂νf) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Zc.trans L.symm) φ,
        fun u => ?_⟩⟩
      · simp only [e, mul_assoc]
        exact (hint g' hg'').const_mul _
      · simp only [e, mul_assoc, integral_const_mul, SchwartzMap.smul_apply,
          SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, ContinuousLinearEquiv.trans_apply,
          smul_eq_mul]
        ring
    | zero => exact ⟨fun u => by simp, 0, fun u => by simp⟩
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      obtain ⟨i1, k1, e1⟩ := h₁
      obtain ⟨i2, k2, e2⟩ := h₂
      refine ⟨fun u => ?_, k1 + k2, fun u => ?_⟩
      · simp only [Pi.add_apply, add_mul]
        exact (i1 u).add (i2 u)
      · simp only [Pi.add_apply, add_mul, SchwartzMap.add_apply, e1, e2]
        rw [integral_add (i1 u) (i2 u)]
    | smul a Φ _ h =>
      obtain ⟨i1, k1, e1⟩ := h
      refine ⟨fun u => ?_, a • k1, fun u => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact (i1 u).const_mul a
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, SchwartzMap.smul_apply, e1, integral_const_mul]
  obtain ⟨-, h, eh⟩ := key (f ∘ d.cmb) hf
  refine ⟨h, funext fun u => ?_⟩
  rw [eh u]
  show _ = ∫ y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (g y) ∂νf
  simp only [hjn, Function.comp_apply]
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLine
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLineB
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLineD
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def ev_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ℂ :=
  2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
    4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
    ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ)
def bv_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ℂ := star (Complex.exp (_root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z u))
theorem norm_add_smul_sq_k (w u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (x : ℝ) :
    ‖u + x • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * x * ⟪w, u⟫_ℝ + x ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm]
  ring
theorem T_vline_k (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hTΩ : d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g)
    {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (z : ℂ) (X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) X = _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W) z (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.T_rho_sum'_k hH hΩ, _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_sp_k R hW, _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_tw_k R hW, hTΩ]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.gau_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_add_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_realAd_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_add_of_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_realAd_smul_k hW z.re)]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k]
  rw [show star (Complex.exp _) = Complex.exp (conj _) from (Complex.exp_conj _).symm, Complex.ofReal_exp,
    ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_add_smul_sq_k]
  simp only [map_add (f := _), map_sub, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring
theorem continuous_bv_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k
  refine continuous_star.comp (Complex.continuous_exp.comp ?_)
  fun_prop
theorem norm_bv_le_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z u‖ ≤ 1 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k
  rw [norm_star, Complex.norm_exp]
  apply Real.exp_le_one_iff.2
  have h : ‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2 ≥ 0 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_add_smul_sq_k]
    positivity
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.mul_im]
  nlinarith [Real.pi_pos]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem B_vline_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ (C : ℂ) (c s : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)), C ≠ 0 ∧ s ≠ 0 ∧
      ν.IsAddHaarMeasure ∧ νf.IsAddHaarMeasure ∧
      ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → ∀ Φ ∈ d.sch, ∀ W : Mx F E d.m d.n, finOne F • W = 0 → ∀ z : ℂ,
        _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
              Complex.exp (z * ⟪s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W, u⟫_ℝ)) := by
  obtain ⟨νf, hνf, hν⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.exists_nuf_k R
  refine ⟨1, 1 / (16 * Real.pi), -(4 * Real.pi), Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf), νf,
    one_ne_zero, neg_ne_zero.2 (by positivity), hν, hνf, ?_⟩
  intro g hg' Ω hΩ hTΩ Φ hΦ W hW z
  set w := _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W with hw
  let e : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z
  let b : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z
  have hTv : ∀ X, d.T (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) X = b (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) :=
    _root_.PositivityTheory.SiegelWeilFormula.KFP.T_vline_k hH R hΩ hTΩ hW z
  have hb : Continuous b := _root_.PositivityTheory.SiegelWeilFormula.KFP.continuous_bv_k w z
  have hb1 : ∀ u, ‖b u‖ ≤ 1 := _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_bv_le_k w z
  have hTΦ : d.T Φ ∈ d.schM := (hT.1 F E σ d).1 Φ hΦ
  have e1 : _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k (Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)) Φ (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) =
      ∫ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.B_k, hTv]
    exact _root_.PositivityTheory.SiegelWeilFormula.KFP.integral_jnp_k R hνf hTΦ hg' hb hb1
  rw [e1]
  have key : ∀ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u =
      ((Real.exp (-(1 / (16 * Real.pi) * ‖z‖ ^ 2 * ‖(-(4 * Real.pi)) • w‖ ^ 2)) : ℝ) : ℂ) *
        Complex.exp (-(z ^ 2 * (‖(-(4 * Real.pi)) • w‖ ^ 2 : ℝ) / (16 * Real.pi))) *
          (_root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
            Complex.exp (z * ⟪(-(4 * Real.pi)) • w, u⟫_ℝ)) := by
    intro u
    have hz : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
    have h1 := exp_alg z.re z.im (‖w‖ ^ 2) ⟪w, u⟫_ℝ (‖u‖ ^ 2)
    rw [← hz] at h1
    have hn : ‖(-(4 * Real.pi)) • w‖ ^ 2 = 16 * Real.pi ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    have hi : ⟪(-(4 * Real.pi)) • w, u⟫_ℝ = -(4 * Real.pi) * ⟪w, u⟫_ℝ := real_inner_smul_left _ _ _
    have hzn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [b, _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k, star_star, hn, hi, hzn]
    have h2 : _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z u = 2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
        4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
        ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ) := by
      rfl
    rw [h2, h1]
    ring
  simp_rw [key]
  rw [integral_const_mul]
  simp only [one_mul, Complex.ofReal_exp]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpRel
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem memLp_schM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : MemLp f 2 ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).symm
  have h1 : MemLp (f ∘ e) 2 (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    exact memLpSchA _ BorelSpace.measurable_eq _ inferInstance hf'
  have h2 := (e.memLp_map_measure_iff).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def TL_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k d
  map_smul' a Φ := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k d a Φ
theorem rho_smul_k (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • φ) = c • d.dd.rho d.B.ψ w φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring
theorem B_rel'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) {ν : Measure (Mx F E d.m d.n)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  have hrho : ∀ w, ∀ φ ∈ d.sch, d.dd.rho d.B.ψ w φ ∈ d.sch := fun w φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ hψ d.κ _ φ hφ
  have hpow : ∀ i : ℕ, d.om (k ^ i) Ω = χ ^ i • Ω := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hk, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hact : ∀ i : ℕ, actB (cA σ) (k ^ i) (actB (cA σ) (k⁻¹ ^ i) v) = v := by
    intro i
    have e1 : k ^ i * k⁻¹ ^ i = 1 := by rw [inv_pow, mul_inv_cancel]
    simp only [actB]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, e1]
    simp
  set Ψ := d.dd.rho d.B.ψ v Ω with hΨdef
  have hΨ : Ψ ∈ d.sch := hrho v Ω hΩ
  have hterm : ∀ i : ℕ, (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) =
      _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν (d.om (k ^ i) Φ) Ψ := by
    intro i
    have h1 := hU F E σ d ν hν (k ^ i) Φ hΦ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      (hrho (actB (cA σ) (k⁻¹ ^ i) v) Ω hΩ)
    have h2 : d.om (k ^ i) (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = χ ^ i • Ψ := by
      rw [hS.impl _ _ Ω hΩ, hact, hpow, _root_.PositivityTheory.SiegelWeilFormula.KFP.rho_smul_k]
    rw [h2, _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k] at h1
    unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k
    rw [← h1]
    have e3 : ∀ X, d.T (d.om (k ^ i) Φ) X * star ((χ ^ i • d.T Ψ) X) =
        star χ ^ i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) := by
      intro X
      rw [Pi.smul_apply, smul_eq_mul, star_mul', star_pow]
      ring
    simp_rw [e3]
    rw [integral_const_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (star_ne_zero.2 hχ), one_pow, one_mul]
  have hint : ∀ i : ℕ, Integrable (fun X => d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ν := by
    intro i
    have hA := _root_.PositivityTheory.SiegelWeilFormula.KFP.memLp_schM_k d ν hν ((hT.1 F E σ d).1 (d.om (k ^ i) Φ) (hS.pres (k ^ i) Φ hΦ))
    have hB := (_root_.PositivityTheory.SiegelWeilFormula.KFP.memLp_schM_k d ν hν ((hT.1 F E σ d).1 Ψ hΨ)).star
    exact hA.integrable_mul hB
  calc ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i * (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν (d.om (k ^ i) Φ) Ψ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, hterm]
    _ = ∫ X, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ∂ν := by
        unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k
        rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
        simp_rw [integral_const_mul]
    _ = ∫ X, _root_.PositivityTheory.SiegelWeilFormula.KFP.TL_k d (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ) X * star (d.T Ψ X) ∂ν := by
        congr 1
        funext X
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rfl
    _ = 0 := by
        rw [hq, map_zero]
        simp
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem line_data_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k)
    (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ (k : d.G) (ω χ C : ℂ) (c : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d))
      (vv : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)),
      k ∈ d.K ∧ ‖ω‖ = 1 ∧ (∀ j : ℕ, 0 < j → ω ^ j ≠ 1) ∧ χ ≠ 0 ∧ C ≠ 0 ∧ ν.IsAddHaarMeasure ∧
      νf.IsAddHaarMeasure ∧
      (∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → d.om k Ω = χ • Ω) ∧
      (∀ ξ z, actB (cA σ) k (vv ξ z) = vv ξ (ω * z)) ∧
      ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → ∀ Φ ∈ d.sch, ∀ ξ z,
        _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (vv ξ z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
  obtain ⟨C, c, s, ν, νf, hC, hs, hν, hνf, hB⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.B_vline_k hT hU hH hA hF R
  obtain ⟨χ, hχ, heig⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.om_rot_vac'_k hT hLO hLI R 1
  let W : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → Mx F E d.m d.n := fun ξ => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R (s⁻¹ • ξ) 0
  have hW : ∀ ξ, finOne F • W ξ = 0 := fun ξ => (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_eq_zero_iff_k _).1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R _ _)
  have hsW : ∀ ξ, s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (W ξ) = ξ := fun ξ => by
    simp only [W, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, smul_smul, mul_inv_cancel₀ hs, one_smul]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R 1, Complex.exp (-((1 : ℝ) * Complex.I)), χ, C, c, ν, νf, fun ξ z => _root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R (W ξ) z, _root_.PositivityTheory.SiegelWeilFormula.KFP.rot_mem_k R 1,
    ?_, ?_, hχ, hC, hν, hνf, heig, fun ξ z => _root_.PositivityTheory.SiegelWeilFormula.KFP.actB_rot_vline'_k R 1 (hW ξ) z, fun g hg Ω hΩ hTΩ Φ hΦ ξ z => ?_⟩
  · rw [Complex.norm_exp]
    simp
  · intro j hj h
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have h3 : -(j : ℝ) = 2 * Real.pi * k := by
      have := congrArg Complex.im hk
      simp at this
      linarith
    have hk0 : (k : ℝ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, neg_eq_zero] at h3
      exact (Nat.cast_pos.2 hj).ne' h3
    refine irrational_pi ⟨-(j : ℚ) / (2 * k), ?_⟩
    push_cast
    field_simp
    linarith
  · have := hB g hg Ω hΩ hTΩ Φ hΦ (W ξ) (hW ξ) z
    rwa [hsW] at this
theorem B_rel_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) {ν : Measure (Mx F E d.m d.n)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.B_rel'_k hT hU hν hχ hΩ hk hΦ q hq v
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpFin
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilOswgenFockOf
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilOswgenPoly
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem arc_apply_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) (i : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i = if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im := rfl
theorem norm_arc_sq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) :
    ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2 = ∑ w, ∑ a, ∑ j, ‖R.loc w X a j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k, if_true, Bool.false_eq_true, if_false,
    Real.norm_eq_abs, sq_abs]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring
theorem gauss_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) :
    ((Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℝ) : ℂ) = ∏ w, gs (2 * Real.pi) (R.loc w X) := by
  rw [Complex.ofReal_exp, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.norm_arc_sq_k]
  simp only [gs]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_neg_distrib]
def lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) : PX d.m d.n :=
  if b then MvPolynomial.C (1 / 2) * (MvPolynomial.X (a, j, false) + MvPolynomial.X (a, j, true))
  else MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X (a, j, false) - MvPolynomial.X (a, j, true))
theorem evX_lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) (z : Fin d.m → Fin d.n → ℂ) :
    evX (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k (d := d) a j b) z = ((if b then (z a j).re else (z a j).im : ℝ) : ℂ) := by
  cases b
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, Bool.false_eq_true, if_false, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
      if_true]
    apply Complex.ext <;> simp <;> ring
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, if_true, Bool.false_eq_true, if_false, map_mul, map_add (f := _), MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    apply Complex.ext <;> simp <;> ring
theorem fP_mul_k (P Q : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ) : fP (P * Q) u = evX P u * fP Q u := by
  simp only [fP, evX, map_mul]
  ring
theorem mul_coord_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (i : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) {h : Mx F E d.m d.n → ℂ} (hh : h ∈ R.fock) :
    (fun X => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ) * h X) ∈ R.fock := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn at hh ⊢
  induction hh using Submodule.span_induction with
  | mem h hmem =>
    obtain ⟨P, g, hg, rfl⟩ := hmem
    apply Submodule.subset_span
    refine ⟨Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1), g, hg, ?_⟩
    funext X
    have e1 : ∏ w ∈ Finset.univ, fP (Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) w) (R.loc w X) =
        fP (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.1), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    have e2 : ∏ w ∈ Finset.univ, fP (P w) (R.loc w X) =
        fP (P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i.1)).symm
    dsimp only
    rw [e1, e2, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.fP_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.evX_lin_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k]
    ring
  | zero =>
    convert Submodule.zero_mem _ using 1
    ext X
    simp
  | add h₁ h₂ _ _ i₁ i₂ =>
    convert Submodule.add_mem _ i₁ i₂ using 1
    funext X
    simp [mul_add]
  | smul a h _ i₁ =>
    convert Submodule.smul_mem _ a i₁ using 1
    ext X
    simp [smul_eq_mul, mul_comm, mul_assoc]
theorem poly_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Q : MvPolynomial (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℂ) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) :
    (fun X => MvPolynomial.eval (fun i => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ)) Q * (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) *
      g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
  have base : (fun X => (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn
    apply Submodule.subset_span
    refine ⟨fun _ => 1, g, hg, ?_⟩
    funext X
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.gauss_eq_k]
    simp only [fP, evX, map_one, one_mul]
    rfl
  induction Q using MvPolynomial.induction_on with
  | C a =>
    convert Submodule.smul_mem _ a base using 1
    ext X
    simp [smul_eq_mul, mul_assoc]
  | add p q hp hq =>
    convert Submodule.add_mem _ hp hq using 1
    ext X
    simp [add_mul]
  | mul_X p i hp =>
    convert _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.mul_coord_mem_k R i hp using 1
    ext X
    simp only [map_mul, MvPolynomial.eval_X]
    ring
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem crd_inf_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ))
    (hL : ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
      L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c)) (X : Mx F E d.m d.n) :
    (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) =
      L.symm (((EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).trans (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zLE_k d).toContinuousLinearEquiv) (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X)) := by
  apply L.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext w
  rw [hL, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k]
  exact (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k R X (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X)).1 rfl w
theorem mem_fock_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) (H : ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∃ P : MvPolynomial (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℂ,
      ∀ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) :
    f ∈ R.fock := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  set Zc : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).trans (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zLE_k d).toContinuousLinearEquiv with hZc
  have hΦ : f ∘ d.cmb ∈ Submodule.span ℂ {Φ | ∃ (φ : SchwartzMap (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ℂ)
      (g : (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ),
      g ∈ SB (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F φ g} := hf
  obtain ⟨N, a, x, hx⟩ := Submodule.mem_span_set'.1 hΦ
  choose φ gg hgg hxeq using fun i => (x i).2
  have hfX : ∀ X, f X = ∑ i, a i * (φ i (L.symm (Zc (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X))) * gg i (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) := by
    intro X
    have e1 : f X = (f ∘ d.cmb) (d.crd X) := by simp [_root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k]
    rw [e1, ← hx, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hxeq i, smul_eq_mul]
    congr 1
    simp only [pureA]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.crd_inf_eq_k R L hL X]
    rfl
  have hfjn : ∀ u y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) = ∑ i, a i * (φ i (L.symm (Zc u)) * gg i y) := by
    intro u y
    rw [hfX, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k]
  let Φv : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin N → ℂ) := fun y i => gg i y
  have hloc : IsLocallyConstant Φv := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
    have h := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hgg i).1 y
    filter_upwards [h] with z hz
    funext i
    exact hz i
  set K : Set (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := ⋃ i, tsupport (gg i) with hK
  have hKc : IsCompact K := isCompact_iUnion fun i => (hgg i).2
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun c : Fin N → ℂ => {y | Φv y = c}) (fun c => hloc.isOpen_fiber c)
    (fun y _ => Set.mem_iUnion.2 ⟨Φv y, rfl⟩)
  set Vals := t.filter (fun c => c ≠ 0) with hVals
  have hfib_sub : ∀ c : Fin N → ℂ, c ≠ 0 → {y | Φv y = c} ⊆ K := by
    intro c hc y hy
    by_contra hyK
    apply hc
    rw [← show Φv y = c from hy]
    funext i
    show gg i y = 0
    exact image_eq_zero_of_notMem_tsupport (f := gg i) fun h => hyK (Set.mem_iUnion.2 ⟨i, h⟩)
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  let ψ : (Fin N → ℂ) → _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := fun c u => ∑ i, a i * (φ i (L.symm (Zc u)) * c i)
  have hterm : ∀ c ∈ Vals, (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    set Nc : Set (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := {y | Φv y = c} with hNc
    have hNo : IsOpen Nc := hloc.isOpen_fiber c
    have hNcl : IsClosed Nc := hloc.isClosed_fiber c
    have hNk : IsCompact Nc := hKc.of_isClosed_subset hNcl (hfib_sub c hc0)
    rcases Nc.eq_empty_or_nonempty with he | hne
    · have : (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * Nc.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) = 0 := by
        funext X
        rw [he, Set.indicator_empty, mul_zero]
        rfl
      rw [this]
      exact Submodule.zero_mem _
    · have hSB := indicator_mem_SB hNo hNcl hNk
      obtain ⟨P, hP⟩ := H _ hSB
      have hm0 : 0 < νf.real Nc := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (hNo.measure_pos νf hne).ne' hNk.measure_lt_top.ne
      have hval : ∀ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f (Nc.indicator fun _ => (1 : ℂ)) u = ψ c u * (νf.real Nc : ℂ) := by
        intro u
        have e : (fun y => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y)) =
            Nc.indicator (fun _ => ψ c u) := by
          funext y
          by_cases hy : y ∈ Nc
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, star_one, mul_one, hfjn]
            have hy' : ∀ i, gg i y = c i := fun i => congrFun hy i
            simp only [ψ, hy']
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, star_zero, mul_zero]
        show ∫ y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y) ∂νf = _
        rw [e, integral_indicator_const _ hNo.measurableSet, Complex.real_smul, mul_comm]
      have hψ : ∀ u, ψ c u = ((νf.real Nc)⁻¹ : ℂ) *
          (MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) := by
        intro u
        rw [← hP u, hval u]
        have : (νf.real Nc : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
        field_simp
      have e2 : (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * Nc.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) =
          ((νf.real Nc)⁻¹ : ℂ) • (fun X => MvPolynomial.eval (fun i => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ)) P *
            (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) * Nc.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) := by
        funext X
        simp only [Pi.smul_apply, smul_eq_mul, hψ]
        ring
      rw [e2]
      exact Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.poly_mem_k R P hSB)
  have hsum : f = ∑ c ∈ Vals, (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) := by
    funext X
    rw [Finset.sum_apply, hfX]
    by_cases h0 : Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) = 0
    · have hz : ∀ i, gg i (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) = 0 := fun i => congrFun h0 i
      simp only [hz, mul_zero, Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      have : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∉ {y | Φv y = c} := fun h => hc0 (h.symm.trans h0)
      rw [Set.indicator_of_notMem this, mul_zero]
    · have hmemK : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∈ K := hfib_sub _ h0 rfl
      have hmemt : Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) ∈ t := by
        have := ht hmemK
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
        obtain ⟨c, hct, hc⟩ := this
        rw [hc]
        exact hct
      have hmemV : Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) ∈ Vals := Finset.mem_filter.2 ⟨hmemt, h0⟩
      rw [Finset.sum_eq_single_of_mem _ hmemV]
      · rw [Set.indicator_of_mem (show _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∈ {y | Φv y = Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)} from rfl), mul_one]
      · intro c _ hne
        have : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∉ {y | Φv y = c} := fun h => hne h.symm
        rw [Set.indicator_of_notMem this, mul_zero]
  rw [hsum]
  exact Submodule.sum_mem _ hterm
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem hg_sch_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg' : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) : ∃ h : 𝓢(_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d, ℂ), ⇑h = _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.hg_sch_k R hνf hf hg'
theorem mem_fock_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) (H : ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∃ P : MvPolynomial (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℂ,
      ∀ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) :
    f ∈ R.fock := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.mem_fock_of_k R hνf hf H
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKKfpMin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem exists_poly_k {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0 := by
  set V := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ) with hV
  have : FiniteDimensional ℂ V := hΦ.2
  have hmap : ∀ v ∈ V, d.om k v ∈ V := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => d.om k v ∈ V) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨⟨k * k'.1, d.K.mul_mem hk k'.2⟩, ?_⟩
      simp [map_mul]
    · simp
    · intro x y _ _ hx hy; simpa using V.add_mem hx hy
    · intro a x _ hx; simpa using V.smul_mem a hx
  have hΦV : Φ ∈ V := Submodule.subset_span ⟨1, by simp⟩
  set f : V →ₗ[ℂ] V := (d.om k).restrict hmap
  have hpow : ∀ (i : ℕ) (v : V), (((f ^ i) v : V) : d.Fn) = d.om (k ^ i) v := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, map_mul, Module.End.mul_apply]
      rfl
  refine ⟨minpoly ℂ f, minpoly.ne_zero (Algebra.IsIntegral.isIntegral f), ?_⟩
  have h0 := congrArg (fun g : Module.End ℂ V => ((g ⟨Φ, hΦV⟩ : V) : d.Fn)) (minpoly.aeval ℂ f)
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum] at h0
  simpa only [LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply, ZeroMemClass.coe_zero] using h0
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem actB_mul_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (a b : d.G) (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    actB (cA σ) (a * b) u = actB (cA σ) a (actB (cA σ) b u) := by
  simp only [actB, Units.val_mul, Subgroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]
theorem actB_one_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    actB (cA σ) (1 : d.G) u = u := by
  simp [actB]
theorem kFinPoly_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k)
    (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k := by
  intro F E _ _ _ _ _ σ d R Φ hK
  have hΦ : Φ ∈ d.sch := hK.1
  obtain ⟨k, ω, χ, C, c, ν, νf, vv, hk, hω1, hω, hχ, hC, hν, hνf, heig, hrot, hB⟩ :=
    _root_.PositivityTheory.SiegelWeilFormula.KFP.line_data_k hT hU hH hA hF hLO hLI R
  obtain ⟨q, hq0, hq⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.exists_poly_k hK hk
  have hω0 : ω ≠ 0 := by
    intro h; rw [h, norm_zero] at hω1; exact zero_ne_one hω1
  have hωi : ∀ j : ℕ, 0 < j → ω⁻¹ ^ j ≠ 1 := fun j hj h => hω j hj (by rw [inv_pow] at h; exact inv_eq_one.1 h)
  have hμ : (star χ)⁻¹ ≠ 0 := inv_ne_zero (star_ne_zero.2 hχ)
  obtain ⟨N, hN⟩ := poly_of_rot q hq0 (star χ)⁻¹ ω⁻¹ hμ (inv_ne_zero hω0) hωi
  have hinv : ∀ ξ z, actB (cA σ) k⁻¹ (vv ξ z) = vv ξ (ω⁻¹ * z) := fun ξ z => by
    have := congrArg (actB (cA σ) k⁻¹) (hrot ξ (ω⁻¹ * z))
    rwa [← _root_.PositivityTheory.SiegelWeilFormula.KFP.actB_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.KFP.actB_one_k, ← mul_assoc, mul_inv_cancel₀ hω0, one_mul, eq_comm] at this
  have hact : ∀ (i : ℕ) ξ z, actB (cA σ) (k⁻¹ ^ i) (vv ξ z) = vv ξ (ω⁻¹ ^ i * z) := by
    intro i
    induction i with
    | zero => intro ξ z; simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.actB_one_k]
    | succ i ih => intro ξ z; rw [pow_succ, _root_.PositivityTheory.SiegelWeilFormula.KFP.actB_mul_k, hinv, ih, pow_succ, mul_assoc]
  have hTΦ : d.T Φ ∈ d.schM := (hT.1 F E σ d).1 Φ hΦ
  refine _root_.PositivityTheory.SiegelWeilFormula.KFP.mem_fock_of_k R hνf hTΦ fun g hg' => ?_
  obtain ⟨Ω, hΩ, hTΩ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.exists_lift_k hT hF R hg'
  obtain ⟨h, hh⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_sch_k R hνf hTΦ hg'
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨P, -, hP⟩ := poly_gauss_of_lines (2 * Real.pi) hpi N h fun ξ => by
    set I : ℂ → ℂ := fun z => ∫ u, h u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) with hI
    set Eξ : ℂ → ℂ := fun z => Complex.exp (-(z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi))) * I z with hE
    have hdiff : Differentiable ℂ Eξ :=
      (Differentiable.cexp (by fun_prop)).mul (entire_laplace (2 * Real.pi) hpi h ξ)
    have hrel : ∀ z, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (star χ)⁻¹ ^ i * Eξ (ω⁻¹ ^ i * z) = 0 := by
      intro z
      have e0 := _root_.PositivityTheory.SiegelWeilFormula.KFP.B_rel_k hT hU hν hχ hΩ (heig g hg' Ω hΩ hTΩ) hΦ q hq (vv ξ z)
      simp only [hact, hB g hg' Ω hΩ hTΩ Φ hΦ, ← hh] at e0
      have hn : ∀ i : ℕ, ‖ω⁻¹ ^ i * z‖ = ‖z‖ := fun i => by
        rw [norm_mul, norm_pow, norm_inv, hω1, inv_one, one_pow, one_mul]
      simp only [hn] at e0
      have hc0 : (C * (Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) : ℂ)) ≠ 0 :=
        mul_ne_zero hC (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
      refine (mul_eq_zero.1 (?_ : (C * (Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) : ℂ)) *
        ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (star χ)⁻¹ ^ i * Eξ (ω⁻¹ ^ i * z) = 0)).resolve_left hc0
      rw [Finset.mul_sum, ← e0]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hE, hI]
      ring
    obtain ⟨p, hpN, hp⟩ := hN Eξ hdiff hrel
    refine ⟨p, hpN, fun z => ?_⟩
    have e1 := hp z
    simp only [hE] at e1
    have e2 : I z = Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi)) * p.eval z := by
      rw [← e1, ← mul_assoc, ← Complex.exp_add]
      simp
    have e3 : ((8 : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 16 * (Real.pi : ℂ) := by push_cast; ring
    rw [e3]
    simpa [hI] using e2
  exact ⟨P, fun u => by rw [← hh]; exact hP u⟩
end PositivityTheory.SiegelWeilFormula.KFP
end
end
