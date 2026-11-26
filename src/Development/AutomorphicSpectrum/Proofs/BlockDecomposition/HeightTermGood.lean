module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
noncomputable section

open MeasureTheory Filter Topology Metric
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
open scoped NNReal Real Pointwise

namespace GlobalTheory.CompanionTheory.RgEisHGood

theorem differentiable_of_pointwise {K : Type} [TopologicalSpace K] [CompactSpace K] (F : ℂ → C(K, ℂ))
    (hc : Continuous F) (hp : ∀ κ, Differentiable ℂ fun z => F z κ) : Differentiable ℂ F := by
  intro c
  have hint : CircleIntegrable F c ((1 : ℝ≥0) : ℝ) := hc.continuousOn.circleIntegrable'
  have hfp := hasFPowerSeriesOn_cauchy_integral hint one_pos
  simp only [NNReal.coe_one] at hfp
  have heq : ∀ w ∈ ball c (1 : ℝ), ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) = F w := by
    intro w hw
    ext κ
    have hcau := ((hp κ).diffContOnCl (s := ball c 1)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
    have hne : ∀ θ : ℝ, circleMap c 1 θ - w ≠ 0 := fun θ h => by
      have h1 : circleMap c 1 θ ∈ sphere c (1 : ℝ) := circleMap_mem_sphere c zero_le_one θ
      rw [sub_eq_zero.1 h] at h1
      exact (ne_of_lt (mem_ball.1 hw)) (mem_sphere.1 h1)
    have hcont : Continuous (fun θ : ℝ => deriv (circleMap c 1) θ • (circleMap c 1 θ - w)⁻¹ • F (circleMap c 1 θ)) := by
      have e : deriv (circleMap c 1) = fun θ => circleMap 0 1 θ * Complex.I := funext (deriv_circleMap c 1)
      rw [e]
      exact ((continuous_circleMap 0 1).mul continuous_const).smul
        ((((continuous_circleMap c 1).sub continuous_const).inv₀ hne).smul (hc.comp (continuous_circleMap c 1)))
    have hcomm : (∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ = ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z κ := by
      have e2 := (ContinuousMap.evalCLM ℂ κ : C(K, ℂ) →L[ℂ] ℂ).intervalIntegral_comp_comm
        (hcont.intervalIntegrable (μ := volume) 0 (2 * π))
      simp only [circleIntegral]
      refine e2.symm.trans ?_
      simp [ContinuousMap.evalCLM]
    have hfin : ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ
        = (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ := rfl
    rw [hfin, hcomm]
    exact hcau
  have han : AnalyticAt ℂ F c := by
    have h1 := hfp.analyticAt
    refine h1.congr ?_
    filter_upwards [ball_mem_nhds c (one_pos : (0:ℝ) < 1)] with w hw using heq w hw
  exact han.differentiableAt

theorem exists_integralCLM {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (μ : Measure K) [IsProbabilityMeasure μ]
    (r : K → E) (hr : Continuous r) : ∃ L : C(K, ℂ) →L[ℂ] E, ∀ f : C(K, ℂ), L f = ∫ κ, f κ • r κ ∂μ := by
  haveI : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • r κ) μ := fun f =>
    (f.continuous.smul hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let rc : C(K, E) := ⟨r, hr⟩
  let L₀ : C(K, ℂ) →ₗ[ℂ] E :=
    { toFun := fun f => ∫ κ, f κ • r κ ∂μ
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun a f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact integral_smul a _ }
  refine ⟨L₀.mkContinuous ‖rc‖ fun f => ?_, fun f => rfl⟩
  have hb : ∀ κ, ‖f κ • r κ‖ ≤ ‖rc‖ * ‖f‖ := fun κ => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (rc.norm_coe_le_norm κ) (f.norm_coe_le_norm κ) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hb)
  change ‖∫ κ, f κ • r κ ∂μ‖ ≤ _
  simpa using this

theorem gauss_bound (b a : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ a →
    ‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2 ≤ M := by
  set B : ℝ := |a| + |b| with hB
  have hB0 : 0 ≤ B := by positivity
  set c : ℝ := 3 + B with hc
  refine ⟨Real.exp (B ^ 2) * (6 * Real.exp c), by positivity, fun z h1 h2 => ?_⟩
  have hx : |z.re| ≤ B := by
    rw [abs_le]; constructor
    · have := neg_abs_le b; have := abs_nonneg a; linarith
    · have := le_abs_self a; have := abs_nonneg b; linarith
  set t : ℝ := |z.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hz : ‖z‖ ≤ B + t := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hexp : ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    rw [Complex.norm_exp]; congr 1
    simp [pow_two, Complex.mul_re]
  have h1z : ‖z - 1‖ ≤ 1 + ‖z‖ := by
    refine (norm_sub_le _ _).trans ?_
    simp [add_comm]
  have hs : 1 + ‖z‖ ≤ c + t ^ 2 - 1 := by nlinarith [sq_nonneg (t - 1)]
  have hn0 : 0 ≤ 1 + ‖z‖ := by positivity
  have hc0 : 0 ≤ c + t ^ 2 := by positivity
  have hcube : (1 + ‖z‖) ^ 3 ≤ 6 * Real.exp (c + t ^ 2) := by
    have h3 := Real.pow_div_factorial_le_exp (c + t ^ 2) hc0 3
    have h4 : (1 + ‖z‖) ^ 3 ≤ (c + t ^ 2) ^ 3 := pow_le_pow_left₀ hn0 (by linarith) 3
    have h5 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h5] at h3
    linarith [(div_le_iff₀ (by norm_num : (0:ℝ) < 6)).1 h3]
  have hre : z.re ^ 2 ≤ B ^ 2 := by
    have := sq_le_sq' (by linarith [(abs_le.1 hx).1]) (abs_le.1 hx).2
    exact this
  have him : z.im ^ 2 = t ^ 2 := by rw [ht, sq_abs]
  calc ‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2
      = Real.exp (z.re ^ 2 - z.im ^ 2) * (‖z - 1‖ * (1 + ‖z‖) ^ 2) := by
        rw [norm_mul, hexp]; ring
    _ ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * ((1 + ‖z‖) ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : (1 + ‖z‖) ^ 3 = (1 + ‖z‖) * (1 + ‖z‖) ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h1z (by positivity)
    _ ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * (6 * Real.exp (c + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hcube (Real.exp_pos _).le
    _ = Real.exp (z.re ^ 2) * (6 * Real.exp c) := by
        rw [him, Real.exp_add, Real.exp_sub, Real.exp_add]
        have := (Real.exp_pos (t ^ 2)).ne'
        field_simp
    _ ≤ Real.exp (B ^ 2) * (6 * Real.exp c) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hre) (by positivity)

theorem hGood : HGood := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hprob Φ hΦ
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨L, hL⟩ := exists_integralCLM μ (fun κ => ρ κ) hρ
  let Ψ₀ : C((ℂ × G) × K, ℂ) := ⟨fun p => Φ p.1.1 (p.1.2 * p.2),
    hΦ.cont.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)))⟩
  let Ψ : C(ℂ × G, C(K, ℂ)) := Ψ₀.curry
  have hA : ∀ (z : ℂ) (g : G), avg μ ρ (fun κ => Φ z (g * κ)) = L (Ψ (z, g)) := by
    intro z g
    rw [hL]
    rfl
  refine ⟨fun g => ?_, ?_, fun b a g => ?_⟩
  · simp only [hA]
    have hF : Differentiable ℂ fun z : ℂ => Ψ (z, g) :=
      differentiable_of_pointwise _ (Ψ.continuous.comp (by fun_prop)) fun κ => hΦ.ent (g * κ)
    exact ((Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul
      (differentiable_id.sub_const 1)).smul (L.differentiable.comp hF)
  · simp only [hA, Prod.mk.eta]
    exact (by fun_prop : Continuous fun y : ℂ × G => Complex.exp (y.1 ^ 2) * (y.1 - 1)).smul
      (L.continuous.comp Ψ.continuous)
  · obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds g
    obtain ⟨M, hM⟩ := hΦ.strip b a (U * (K : Set G)) (hUc.mul hK)
    obtain ⟨M2, hM2, hg⟩ := gauss_bound b a
    refine ⟨U, hU, ‖L‖ * |M| * M2, fun z h1 h2 g' hg' => ?_⟩
    rw [hA, norm_smul]
    have hΨ : ‖Ψ (z, g')‖ ≤ |M| * (1 + ‖z‖) ^ 2 := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun κ => ?_
      have h := hM z h1 h2 (g' * κ) (Set.mul_mem_mul hg' κ.2)
      exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
    calc ‖Complex.exp (z ^ 2) * (z - 1)‖ * ‖L (Ψ (z, g'))‖
        ≤ ‖Complex.exp (z ^ 2) * (z - 1)‖ * (‖L‖ * (|M| * (1 + ‖z‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left ((L.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hΨ (norm_nonneg _))) (norm_nonneg _)
      _ = ‖L‖ * |M| * (‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2) := by ring
      _ ≤ ‖L‖ * |M| * M2 := mul_le_mul_of_nonneg_left (hg z h1 h2) (by positivity)

end GlobalTheory.CompanionTheory.RgEisHGood
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGoodStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_term_good : HGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisHGood.hGood | exact GlobalTheory.CompanionTheory.RgEisHGood.hGood | (intros; apply GlobalTheory.CompanionTheory.RgEisHGood.hGood <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleOfFiniteEq
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped NumberField.AdeleRing nonZeroDivisors

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k]

theorem ideleModule_ofFinite_eq (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    (ideleModule k (ofFinite b) : ℝ) = finiteModule (ofFinite b) := by
  have h : infiniteModule (ofFinite b : IdeleGroup k) = 1 :=
    Finset.prod_eq_one fun w _ ↦ by
      rw [show ((ofFinite b : IdeleGroup k) : 𝔸[k]).1 w = 1 from rfl, norm_one, one_pow]
  rw [ideleModule_apply, h, one_mul]

theorem norm_le_one_of_mem_OH {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) (v : HeightOneSpectrum (𝓞 k)) :
    ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).1
      (mem_integralFiniteAdeles.1 hb v))

theorem finiteModule_le_one {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) : finiteModule (ofFinite b) ≤ 1 := by
  rw [finiteModule, finprod_eq_prod _ (finite_mulSupport_norm _)]
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦ norm_le_one_of_mem_OH hb v

theorem finiteModule_lt_one {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) (hu : b ∉ finiteIntegralUnits k) :
    finiteModule (ofFinite b) < 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 k), ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ < 1 := by
    by_contra hcon
    push_neg at hcon
    refine hu ((mem_finiteIntegralUnits k).2 fun v ↦ ⟨mem_integralFiniteAdeles.1 hb v, ?_⟩)
    have hv1 : ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ = 1 :=
      le_antisymm (norm_le_one_of_mem_OH hb v) (hcon v)
    have hmul : (b : FiniteAdeleRing (𝓞 k) k) v *
        ((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v = 1 :=
      congrArg (fun a : FiniteAdeleRing (𝓞 k) k ↦ a v) (Units.mul_inv b)
    have hn : ‖((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v‖ = 1 := by
      have := congrArg norm hmul
      rwa [norm_mul, hv1, one_mul, norm_one] at this
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).2
      ((Valued.toNormedField.norm_le_one_iff).1 hn.le)
  have hfin := finite_mulSupport_norm (ofFinite b : IdeleGroup k)
  have hvS : v ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
    exact hv.ne
  rw [finiteModule, finprod_eq_prod _ hfin, ← Finset.mul_prod_erase _ _ hvS]
  calc _ ≤ ‖((ofFinite b : IdeleGroup k) : 𝔸[k]).2 v‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun u _ ↦ norm_le_one_of_mem_OH hb u)
          (norm_nonneg _)
    _ < 1 := by rwa [mul_one]

def integrand (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k) (n : ℕ)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) : ℂ :=
  g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
    ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ (((n : ℝ) : ℝ) : ℂ)

theorem cpow_module_eq (b : (FiniteAdeleRing (𝓞 k) k)ˣ) (x : ℝ) :
    ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ (x : ℂ) = ((finiteModule (ofFinite b) ^ x : ℝ) : ℂ) := by
  rw [ideleModule_ofFinite_eq, Complex.ofReal_cpow (finiteModule_pos _).le]

theorem norm_integrand (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k) (n : ℕ)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    ‖integrand g ω n b‖ = ‖g fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)‖ *
      finiteModule (ofFinite b) ^ (n : ℝ) := by
  rw [integrand, cpow_module_eq, norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (finiteModule_pos _).le _)]

theorem continuous_integrand {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ}
    (hg : g ∈ GJMatrix.finiteSchwartzBruhatPi k) (ω : HeckeCharacter k) (n : ℕ) :
    Continuous (integrand g ω n) := by
  have h1 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦
      g fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k) :=
    ((GJMatrix.mem_finiteSchwartzBruhatPi k).1 hg).1.continuous.comp
      (continuous_pi fun _ ↦ Units.continuous_val)
  have h2 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ (ω.toIdele (ofFinite b) : ℂ) :=
    continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_ofFinite)
  have h3 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦
      ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      ((continuous_finiteModule.comp continuous_ofFinite).rpow_const
        fun b ↦ Or.inl (finiteModule_pos _).ne')
  have : integrand g ω n = fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) *
      (ω.toIdele (ofFinite b) : ℂ) * ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ) := by
    funext b
    rw [integrand, cpow_module_eq]
  rw [this]
  exact (h1.mul h2).mul h3

theorem norm_integrand_le {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ} (ω : HeckeCharacter k)
    (hb : ∀ t, ‖g fun _ ↦ t‖ ≤ 1 ∧ (g (fun _ ↦ t) ≠ 0 → t ∈ OH k)) {n : ℕ} (hn : 2 ≤ n)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    ‖integrand g ω n b‖ ≤ finiteZetaBound (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 2 b := by
  rw [norm_integrand]
  by_cases h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0
  · rw [h0, norm_zero, zero_mul]
    exact finiteZetaBound_nonneg _ _ _
  have hO := (hb _).2 h0
  have hL : (b : FiniteAdeleRing (𝓞 k) k) ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) := by
    rw [← SetLike.mem_coe, idealFiniteAdeles_one]
    exact hO
  rw [finiteZetaBound, if_pos hL]
  have hpow : finiteModule (ofFinite b) ^ (n : ℝ) ≤ finiteModule (ofFinite b) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (finiteModule_pos _) (finiteModule_le_one hO)
      (by exact_mod_cast hn)
  calc _ ≤ 1 * finiteModule (ofFinite b) ^ (n : ℝ) :=
        mul_le_mul_of_nonneg_right (hb _).1 (Real.rpow_nonneg (finiteModule_pos _).le _)
    _ ≤ _ := by rwa [one_mul]

theorem tendsto_integrand {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ} {ω : HeckeCharacter k}
    (hb : ∀ t, ‖g fun _ ↦ t‖ ≤ 1 ∧ (g (fun _ ↦ t) ≠ 0 → t ∈ OH k))
    (hu : ∀ u ∈ finiteIntegralUnits k,
      g (fun _ ↦ (u : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite u) : ℂ) = 1)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    Tendsto (fun n ↦ integrand g ω n b) atTop
      (𝓝 (((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
        Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b)) := by
  by_cases hW : b ∈ finiteIntegralUnits k
  · rw [Set.indicator_of_mem (SetLike.mem_coe.2 hW)]
    have hm : finiteModule (ofFinite b : IdeleGroup k) = 1 := finiteModule_eq_one_of_mem hW
    refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [integrand, cpow_module_eq, hu b hW, hm, Real.one_rpow, Complex.ofReal_one, one_mul]
  · rw [Set.indicator_of_notMem (fun h ↦ hW (SetLike.mem_coe.1 h))]
    by_cases h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0
    · refine tendsto_const_nhds.congr fun n ↦ ?_
      rw [integrand, h0, zero_mul, zero_mul]
    have hlt := finiteModule_lt_one ((hb _).2 h0) hW
    refine squeeze_zero_norm (a := fun n : ℕ ↦ finiteModule (ofFinite b) ^ n) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (finiteModule_pos _).le hlt)
    rw [norm_integrand, Real.rpow_natCast]
    calc _ ≤ 1 * finiteModule (ofFinite b) ^ n :=
          mul_le_mul_of_nonneg_right (hb _).1 (pow_nonneg (finiteModule_pos _).le _)
      _ = _ := one_mul _

theorem zFinLim : ZFinLim := by
  intro k _ _ g ω hg hb hu B
  have hlim : Tendsto (fun n : ℕ ↦ ∫ b, integrand g ω n b ∂finiteIdeleMeasure k) atTop
      (𝓝 (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
        Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k)) :=
    tendsto_integral_filter_of_dominated_convergence
      (finiteZetaBound (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 2)
      (Eventually.of_forall fun n ↦ (continuous_integrand hg ω n).aestronglyMeasurable)
      ((eventually_ge_atTop 2).mono fun n hn ↦ Eventually.of_forall (norm_integrand_le ω hb hn))
      (integrable_finiteZetaBound 1 (by norm_num))
      (Eventually.of_forall (tendsto_integrand hb hu))
  have hval : (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
      Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k) = 1 := by
    rw [integral_indicator_const _ (isOpen_finiteIntegralUnits k).measurableSet, Measure.real,
      finiteIdeleMeasure_finiteIntegralUnits]
    simp
  rw [hval] at hlim
  obtain ⟨n, hn, hB⟩ := ((hlim.eventually_ne one_ne_zero).and
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop B)).exists
  exact ⟨n, hB, hn⟩

end GlobalTheory.CompanionTheory.EisTF
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToIdeleMulSelf
set_option synthInstance.maxSize 1000

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RgEisAsm

open PositivityTheory.RgEis PositivityTheory.RgEis.TF
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem toIdele_mul_self {ω : HeckeCharacter k} (hω : ω * ω = 1) (x : IdeleGroup k) :
    ω.toIdele x * ω.toIdele x = 1 := by
  have h := congrArg (fun f : HeckeCharacter k => f (IdeleClassGroup.mk k x)) hω
  simpa [HeckeCharacter.toIdele_apply] using h

theorem tensor_eq (φ : 𝓢(ι → mixedSpace k, ℂ)) (g : (ι → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (x : ι → 𝔸[k]) :
    GJMatrix.schwartzBruhatTensorPi φ g x = rd φ (fun j => (x j).1) * g (fun j => (x j).2) := rfl

theorem norm_inv_units (a : (InfiniteAdeleRing k)ˣ) (ha : ∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1)
    (w : InfinitePlace k) : ‖((a⁻¹ : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) w‖ = 1 := by
  have h : (a : InfiniteAdeleRing k) w * ((a⁻¹ : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) w = 1 :=
    congrFun (Units.mul_inv a) w
  have h2 := congrArg norm h
  rw [norm_mul, ha w, one_mul, norm_one] at h2
  exact h2

theorem line_inv {ω : HeckeCharacter k} (hω : ω * ω = 1) (φ₁ : 𝓢(Unit → mixedSpace k, ℂ))
    (g₁ : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (hφ : ∀ a : (InfiniteAdeleRing k)ˣ, (∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) →
      rd φ₁ (fun _ => (a : InfiniteAdeleRing k)) = ω.toIdele (ofInfinite a))
    (hg : ∀ u ∈ finiteIntegralUnits k, g₁ (fun _ => (u : FiniteAdeleRing (𝓞 k) k)) =
      ω.toIdele (ofFinite u))
    (a : (InfiniteAdeleRing k)ˣ) (u : (FiniteAdeleRing (𝓞 k) k)ˣ)
    (ha : ∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) (hu : u ∈ finiteIntegralUnits k) :
    GJMatrix.schwartzBruhatTensorPi φ₁ g₁
        (fun _ => (((ofInfinite a * ofFinite u)⁻¹ : IdeleGroup k) : 𝔸[k])) =
      ω.toIdele (ofInfinite a * ofFinite u) := by
  have h1 : (((ofInfinite a * ofFinite u)⁻¹ : IdeleGroup k) : 𝔸[k]).1 =
      ((a⁻¹ : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) := by
    have : toInfinite k (ofInfinite a * ofFinite u)⁻¹ = a⁻¹ := by simp
    exact congrArg Units.val this
  have h2 : (((ofInfinite a * ofFinite u)⁻¹ : IdeleGroup k) : 𝔸[k]).2 =
      ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) := by
    have : toFinite k (ofInfinite a * ofFinite u)⁻¹ = u⁻¹ := by simp
    exact congrArg Units.val this
  rw [tensor_eq]
  simp only [h1, h2]
  rw [hφ _ (norm_inv_units a ha), hg _ (inv_mem hu), ← Circle.coe_mul, ← map_mul, map_inv, map_inv,
    ← mul_inv, map_inv]
  have h3 := toIdele_mul_self hω (ofInfinite a * ofFinite u)
  rw [inv_eq_of_mul_eq_one_left h3]

theorem near_one_nhds (hCol : ColLaw) (hTop : InMTop) (i₀ : ι) (M₀ : ℕ) (hM : M₀ ≠ 0)
    (U : Set ((adStd k).kGL ι)) (hU : U ∈ 𝓝 (1 : (adStd k).kGL ι)) :
    U ∩ {u : (adStd k).kGL ι | InM M₀ ((col i₀ u.1 i₀).2 - 1) ∧
      ∀ w, ‖(col i₀ u.1 i₀).1 w - 1‖ < 1} ∈ 𝓝 (1 : (adStd k).kGL ι) := by
  obtain ⟨-, hc, h1, -⟩ := hCol k ι i₀
  have hcc : Continuous fun u : (adStd k).kGL ι => col i₀ u.1 i₀ :=
    (continuous_apply i₀).comp (hc.comp continuous_subtype_val)
  refine inter_mem hU (IsOpen.mem_nhds ?_ ?_)
  · have o1 : IsOpen {u : (adStd k).kGL ι | InM M₀ ((col i₀ u.1 i₀).2 - 1)} :=
      ((hTop k).1 M₀ hM).1.preimage ((continuous_snd.comp hcc).sub continuous_const)
    have o2 : IsOpen {u : (adStd k).kGL ι | ∀ w, ‖(col i₀ u.1 i₀).1 w - 1‖ < 1} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_lt
        ((((continuous_apply w).comp (continuous_fst.comp hcc)).sub continuous_const).norm)
        continuous_const
    exact o1.inter o2
  · have e : col i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k]) i₀ = 1 := by
      have : col (k := k) i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k]) = Pi.single i₀ 1 := h1
      rw [this]; simp
    refine ⟨?_, fun w => ?_⟩
    · rw [e]
      exact ⟨0, (OH k).zero_mem, by
        show (1 : FiniteAdeleRing (𝓞 k) k) - 1 = _
        simp⟩
    · rw [e]
      simp

theorem asm : ColLaw → InMTop → Supp → ArchFun → FinFun → ZSplit → ZInf → ZFinPos → ZFinLim →
    StdGood → TestFun := by
  intro hCol hTop hSupp hArch hFin hZS hZI hZP hZL hStd k _ _ ι _ _ i₀ ω hω U hU
  obtain ⟨M₀, hM₀, hfin⟩ := hFin k ω
  have hU' := near_one_nhds hCol hTop i₀ M₀ hM₀ U hU
  obtain ⟨M, δ, hM, hdvd, hδ, hS⟩ := hSupp k ι i₀ ((hStd k).kcpt ι) _ hU' M₀ hM₀
  obtain ⟨g, g₁, hg, hg₁, hg1, hg₁u, hg₁b, hg₁p, hgV⟩ := hfin M hM hdvd ι i₀
  obtain ⟨φ, φ₁, hφ1, hφ₁u, hφ₁p, hφV⟩ := hArch k ι i₀ ω hω δ hδ
  obtain ⟨hcolK, hcc, hcol1, hcolP⟩ := hCol k ι i₀
  have hΨ := GJMatrix.schwartzBruhatTensorPi_mem φ hg
  have hΨ₁ := GJMatrix.schwartzBruhatTensorPi_mem φ₁ hg₁
  have hfac : ∀ (t : 𝔸[k]) (κ : (adStd k).kGL ι),
      GJMatrix.schwartzBruhatTensorPi φ g (t • col i₀ κ.1) =
        GJMatrix.schwartzBruhatTensorPi φ₁ g₁ (fun _ => t) *
          GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) := by
    intro t κ
    obtain ⟨hu, hp⟩ := hcolK κ.1 κ.2
    have a1 := (hφV _ hu).1 t.1
    have a2 := (hgV _ hp).1 t.2
    rw [tensor_eq, tensor_eq, tensor_eq]
    have e1 : (fun j => ((t • col i₀ κ.1) j).1) = t.1 • (fun j => (col i₀ κ.1 j).1) := rfl
    have e2 : (fun j => ((t • col i₀ κ.1) j).2) = t.2 • (fun j => (col i₀ κ.1 j).2) := rfl
    rw [e1, e2, a1, a2]
    ring
  have hequiv : ∀ p κ : (adStd k).kGL ι, p.1 ∈ stab 𝔸[k] {i₀} →
      GJMatrix.schwartzBruhatTensorPi φ g (col i₀ (p * κ).1) =
        ω.toIdele (bdet {i₀} p.1) * GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) := by
    intro p κ hp
    obtain ⟨hc, a, u, hb, ha, hu⟩ := hcolP p.1 p.2 hp
    have e : col i₀ (p * κ).1 = (((bdet {i₀} p.1)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) • col i₀ κ.1 := hc κ.1
    rw [e, hfac, hb, line_inv hω φ₁ g₁ hφ₁u hg₁u a u ha hu]
  have hone : rd φ₁ (fun _ => (1 : InfiniteAdeleRing k)) ≠ 0 := by
    have h := hφ₁u 1 (fun w => by
      rw [Units.val_one]
      exact norm_one (α := w.Completion))
    rw [Units.val_one] at h
    rw [h]
    simp
  have hunit : ∀ x : ℝ, 1 < x → zInf φ₁ ω x ≠ 0 := hZI k φ₁ ω hφ₁p hone
  refine ⟨GJMatrix.schwartzBruhatTensorPi φ g, GJMatrix.schwartzBruhatTensorPi φ₁ g₁,
    fun κ => GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1), hΨ, hΨ₁,
    (GJMatrix.continuous_of_mem_schwartzBruhatPi hΨ).comp (hcc.comp continuous_subtype_val),
    ?_, fun t κ => hfac t κ, ?_, fun p κ hp => hequiv p κ hp, ?_, ?_⟩
  · have e : col (k := k) i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k]) = Pi.single i₀ 1 := hcol1
    show GJMatrix.schwartzBruhatTensorPi φ g (col i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k])) = 1
    rw [e, tensor_eq]
    have e1 : (fun j => ((Pi.single i₀ (1 : 𝔸[k]) : ι → 𝔸[k]) j).1) = Pi.single i₀ 1 := by
      funext j
      by_cases h : j = i₀
      · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]; rfl
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]; rfl
    have e2 : (fun j => ((Pi.single i₀ (1 : 𝔸[k]) : ι → 𝔸[k]) j).2) = Pi.single i₀ 1 := by
      funext j
      by_cases h : j = i₀
      · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]; rfl
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]; rfl
    rw [e1, e2, hφ1, hg1, one_mul]
  · intro κ hne
    have hne' : GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) ≠ 0 := hne
    rw [tensor_eq] at hne'
    obtain ⟨n1, n2⟩ := mul_ne_zero_iff.1 hne'
    obtain ⟨hu, hpr⟩ := hcolK κ.1 κ.2
    obtain ⟨p, hp, u, huU, hκ⟩ := hS κ (fun j hj => (hgV _ hpr).2.1 n2 j hj) ((hφV _ hu).2.1 n1)
    refine ⟨p, hp, u, huU.1, hκ, ?_⟩
    obtain ⟨hu', hpr'⟩ := hcolK u.1 u.2
    have hreal : ∃ r : ℝ, 0 ≤ r ∧ GJMatrix.schwartzBruhatTensorPi φ g (col i₀ u.1) = r := by
      obtain ⟨r, hr, e⟩ := (hφV _ hu').2.2 huU.2.2
      rcases (hgV _ hpr').2.2 huU.2.1 with h | h
      · exact ⟨0, le_rfl, by rw [tensor_eq, h]; simp⟩
      · exact ⟨r, hr, by rw [tensor_eq, e, h, mul_one]⟩
    obtain ⟨r, hr, e⟩ := hreal
    have h1 : GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) = ω.toIdele (bdet {i₀} p.1) * r := by
      rw [hκ, hequiv p u hp, e]
    show GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) =
      ω.toIdele (bdet {i₀} p.1) * (‖GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1)‖ : ℂ)
    have h2 : ‖GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1)‖ = r := by
      rw [h1, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_of_nonneg hr]
    rw [h2, h1]
  · have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i₀⟩
    have hcard' : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
    obtain ⟨x, hx, hz⟩ := hZL k g₁ ω hg₁ hg₁b (fun u hu => by
      rw [hg₁u u hu, ← Circle.coe_mul, toIdele_mul_self hω, Circle.coe_one]) ((Fintype.card ι : ℝ) + 1)
    refine ⟨x, by simpa using hx, ?_⟩
    rw [hZS k φ₁ g₁ ω x hg₁]
    exact mul_ne_zero (hunit x (by linarith)) hz
  · rintro rfl x hx
    rw [hZS k φ₁ g₁ 1 x hg₁]
    refine mul_ne_zero (hunit x hx) (hZP k g₁ hg₁ (hg₁p rfl) ?_ x hx)
    have h := hg₁u 1 (one_mem _)
    rw [Units.val_one] at h
    rw [h]
    simp

end GlobalTheory.CompanionTheory.RgEisAsm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing Pointwise
open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

namespace GlobalTheory.CompanionTheory.EisTestK

theorem nhd_choice {K K₀ : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [Group K₀] [TopologicalSpace K₀] [IsTopologicalGroup K₀] [CompactSpace K₀] [T2Space K₀]
    (j : K →* K₀) (hj : Continuous j) (S : Subgroup K₀) (hS : IsClosed (S : Set K₀))
    (N₁ : Set K₀) (hN : N₁ ∈ 𝓝 (1 : K₀)) (V : Set K) (hV : V ∈ 𝓝 (1 : K)) :
    ∃ U ∈ 𝓝 (1 : K₀), ∀ (κ : K) (p u : K₀), p ∈ S → u ∈ U → j κ = p * u →
      ∃ r v : K, j r ∈ S ∧ v ∈ V ∧ κ = r * v ∧ ∀ u' ∈ U, j v * u'⁻¹ ∈ N₁ := by
  have hcont : Tendsto (fun x : K₀ × K₀ => x.1 * x.2⁻¹) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1) := by
    have h : Continuous (fun x : K₀ × K₀ => x.1 * x.2⁻¹) := by fun_prop
    have := h.tendsto ((1 : K₀), (1 : K₀))
    simpa [nhds_prod_eq] using this
  obtain ⟨W, hW, hWN⟩ := Filter.mem_prod_self_iff.1 (hcont hN)
  have hjW : j ⁻¹' W ∈ 𝓝 (1 : K) := hj.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨V₀, hV₀sub, hV₀o, h1⟩ := mem_nhds_iff.1 (Filter.inter_mem hV hjW)
  let Q : Subgroup K := S.comap j
  let A : Set K := (Q : Set K) * V₀
  have hAo : IsOpen A := hV₀o.mul_left
  have hC : IsCompact (j '' Aᶜ) := (hAo.isClosed_compl.isCompact).image hj
  have hScpt : IsCompact (S : Set K₀) := hS.isCompact
  let T : Set K₀ := (S : Set K₀) * (j '' Aᶜ)
  have hT : IsCompact T := hScpt.mul hC
  have h1T : (1 : K₀) ∉ T := by
    rintro ⟨p, hp, c, ⟨x, hx, rfl⟩, hpc⟩
    apply hx
    have hjx : j x ∈ S := by
      have : j x = p⁻¹ := eq_inv_of_mul_eq_one_right hpc
      rw [this]; exact S.inv_mem hp
    exact ⟨x, hjx, 1, h1, by simp⟩
  refine ⟨W ∩ Tᶜ, Filter.inter_mem hW (hT.isClosed.isOpen_compl.mem_nhds h1T), ?_⟩
  intro κ p u hp hu hκ
  by_cases hκA : κ ∈ A
  · obtain ⟨r, hr, v, hv, rfl⟩ := hκA
    refine ⟨r, v, hr, (hV₀sub hv).1, rfl, fun u' hu' => ?_⟩
    exact hWN (Set.mk_mem_prod (hV₀sub hv).2 hu'.1)
  · exfalso
    apply hu.2
    refine ⟨p⁻¹, S.inv_mem hp, j κ, ⟨κ, hκA, rfl⟩, ?_⟩
    simp [hκ]

section Concrete

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]

theorem dgl_mem_stab (d : ι → IdeleGroup k) (i : ι) : dgl d ∈ stab 𝔸[k] ({i} : Set ι) := by
  intro r hr c hc
  have hrc : r ≠ c := fun h => hr (h ▸ hc)
  exact ⟨Matrix.diagonal_apply_ne _ hrc, Matrix.diagonal_apply_ne _ hrc⟩

theorem kap_mem_stab_iff (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    kap π d g ∈ stab 𝔸[k] ({i} : Set ι) ↔ π g ∈ stab 𝔸[k] ({i} : Set ι) := by
  have hD := dgl_mem_stab d i
  constructor
  · intro h
    have e : π g = dgl d * kap π d g * (dgl d)⁻¹ := by simp [kap, mul_assoc]
    rw [e]
    exact mul_mem (mul_mem hD h) (inv_mem hD)
  · intro h
    exact mul_mem (mul_mem (inv_mem hD) h) hD

theorem bdet_congr {R : Type} [CommRing R] {s : Set ι} {g g' : GL ι R}
    (h : (g : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      (g' : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) : bdet s g = bdet s g' := by
  unfold bdet
  split_ifs with h1 h2 h2
  · exact Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h])
  · exact absurd (by rwa [h] at h1) h2
  · exact absurd (by rwa [← h] at h2) h1
  · rfl

theorem bdet_kap (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    bdet ({i} : Set ι) (kap π d g) = bdet ({i} : Set ι) (π g) := by
  apply bdet_congr
  ext ⟨a, ha⟩ ⟨b, hb⟩
  obtain rfl : a = i := ha
  obtain rfl : b = a := hb
  have e : (((dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) =
      Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) := rfl
  have e' : ((dgl d : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = Matrix.diagonal fun i => (d i : 𝔸[k]) := rfl
  simp only [Matrix.submatrix_apply, kap, Units.val_mul, e, e', Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [mul_right_comm, Units.inv_mul, one_mul]

end Concrete

theorem testK : StdGood → BdetLaw → TestFun → TestK := by
  intro hStd hB hT G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hSide V hV
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : CompactSpace ((adStd k).kGL ι) := isCompact_iff_compactSpace.1 ((hStd k).kcpt ι)
  obtain ⟨hcl, hmul, hcb, -, -, -⟩ := hB k 𝔸[k] (adStd k) (hStd k) ι ({i} : Set ι)
  let j : K →* (adStd k).kGL ι :=
    { toFun := fun κ => ⟨kap π d κ, hSide.piK κ κ.2⟩
      map_one' := by apply Subtype.ext; simp [kap]
      map_mul' := fun a b => by apply Subtype.ext; simp [kap, mul_assoc] }
  have hj : Continuous j := by
    refine Continuous.subtype_mk ?_ _
    unfold kap
    exact (continuous_const.mul (hSide.cont.comp continuous_subtype_val)).mul continuous_const
  let S : Subgroup ((adStd k).kGL ι) := (stab 𝔸[k] ({i} : Set ι)).comap ((adStd k).kGL ι).subtype
  have hS : IsClosed (S : Set ((adStd k).kGL ι)) := hcl.preimage continuous_subtype_val
  have hb1 : bdet ({i} : Set ι) (1 : GL ι 𝔸[k]) = 1 := by
    have := hmul 1 (one_mem _) 1 (one_mem _)
    simpa using this
  let f : (adStd k).kGL ι → ℂ := fun p => (ω.toIdele (bdet ({i} : Set ι) p.1) : ℂ)
  have hf1 : f 1 = 1 := by
    show (ω.toIdele (bdet ({i} : Set ι) (1 : GL ι 𝔸[k])) : ℂ) = 1
    rw [hb1]
    simp [HeckeCharacter.toIdele_apply]
  have hfc : ContinuousOn f (S : Set ((adStd k).kGL ι)) := by
    have h1 : ContinuousOn (fun p : (adStd k).kGL ι => bdet ({i} : Set ι) p.1) (S : Set ((adStd k).kGL ι)) :=
      hcb.comp continuous_subtype_val.continuousOn fun p hp => hp
    exact continuous_subtype_val.comp_continuousOn (ω.continuous_toIdele.comp_continuousOn h1)
  obtain ⟨N₁, hN₁, hNf⟩ : ∃ N₁ ∈ 𝓝 (1 : (adStd k).kGL ι), ∀ p ∈ S, p ∈ N₁ → ‖f p - 1‖ ≤ 1 / 4 := by
    have h := hfc 1 (one_mem S)
    have hm : f ⁻¹' Metric.closedBall 1 (1 / 4) ∈ 𝓝[(S : Set ((adStd k).kGL ι))] (1 : (adStd k).kGL ι) :=
      h (by rw [hf1]; exact Metric.closedBall_mem_nhds _ (by norm_num))
    obtain ⟨u, huo, hu1, hus⟩ := mem_nhdsWithin.1 hm
    refine ⟨u, huo.mem_nhds hu1, fun p hp hpu => ?_⟩
    have := hus ⟨hpu, hp⟩
    simpa [dist_eq_norm] using this
  obtain ⟨U, hU, hUmain⟩ := nhd_choice j hj S hS N₁ hN₁ V hV
  obtain ⟨Ψ, Ψ₁, ψ, hΨ, hΨ₁, hψc, hψ1, hfac, hsupp, hlaw, hz, hone⟩ := hT k ι i ω hSide.sq U hU
  refine ⟨Ψ, Ψ₁, ψ ∘ j, hΨ, hΨ₁, hψc.comp hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hψ1
  · intro r κ hr
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := (kap_mem_stab_iff π d i r).2 ((hSide.mem _).1 hr)
    show ψ (j (r * κ)) = c r * ψ (j κ)
    rw [map_mul, hlaw _ _ hrS, (hSide.val _ hr).1]
    rw [show (j r).1 = kap π d r from rfl, bdet_kap]
  · intro κ hκ
    obtain ⟨p, hp, u, hu, hκe, -⟩ := hsupp (j κ) hκ
    obtain ⟨r, v, hr, hv, rfl, hvN⟩ := hUmain κ p u hp hu hκe
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := hr
    have hrP : (r : G) ∈ P := (hSide.mem _).2 ((kap_mem_stab_iff π d i r).1 hr)
    refine ⟨r, v, hrP, hv, rfl, ?_⟩
    have hl := hlaw (j r) (j v) hrS
    have hφv : ψ (j v) ≠ 0 := fun h => hκ (by
      show ψ (j (r * v)) = 0
      rw [map_mul, hl, h, mul_zero])
    obtain ⟨p', hp', u', hu', hve, hval⟩ := hsupp (j v) hφv
    have hpN : p' ∈ N₁ := by
      have := hvN u' hu'
      rwa [hve, mul_inv_cancel_right] at this
    have hb : ‖f p' - 1‖ ≤ 1 / 4 := hNf p' hp' hpN
    show ‖ψ (j v) - (‖ψ (j v)‖ : ℂ)‖ ≤ ‖ψ (j v)‖ / 4
    generalize ψ (j v) = a at hval
    have e : a - (‖a‖ : ℂ) = (f p' - 1) * (‖a‖ : ℂ) := by
      rw [sub_mul, one_mul]
      exact congrArg (· - (‖a‖ : ℂ)) hval
    rw [e, norm_mul, Complex.norm_real, norm_norm]
    nlinarith [norm_nonneg a]
  · intro s κ
    show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) ω s = globalZeta (fun t => Ψ₁ fun _ => t) ω s * ψ (j κ)
    have hfun : (fun t => Ψ (t • vec (kap π d κ) i)) = fun t => (Ψ₁ fun _ => t) * ψ (j κ) :=
      funext fun t => hfac t (j κ)
    rw [hfun]
    unfold globalZeta
    rw [← integral_mul_const]
    congr 1
    ext x
    ring
  · obtain ⟨z, hz1, hz2⟩ := hz
    exact ⟨z, by linarith, hz2⟩
  · exact hone

end GlobalTheory.CompanionTheory.EisTestK
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalKStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_spherical_K : StdGood → BdetLaw → TestFun → TestK := by
  first | exact @GlobalTheory.CompanionTheory.EisTestK.testK | exact GlobalTheory.CompanionTheory.EisTestK.testK | (intros; apply GlobalTheory.CompanionTheory.EisTestK.testK <;> assumption)
end
end
