module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekind
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffPolynomialConjugationDerivMemShapeSpan
open MvPolynomial
open scoped ContDiff
open GlobalTheory.PsCo.Pc1

noncomputable section

namespace GlobalTheory.PsCo.Pc1.B

theorem sb_derivcut (H : ℝ → ℝ) (hH : IsCutFn H) : IsCutFn (deriv H) := by
  obtain ⟨hc, R, hR⟩ := hH
  refine ⟨(contDiff_infty_iff_deriv.1 hc).2, R + 1, fun x hx => ?_⟩
  have h : H =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds (show R < x by linarith)] with y hy
    exact hR y (le_of_lt hy)
  rw [h.deriv_eq]
  simp

theorem sb_evrp {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rP, rM, map_sum, map_mul, ev, eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem sb_degmono {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (s : _) (a : ℂ) :
    (dZ ε Z (monomial s a)).totalDegree ≤ (monomial s a).totalDegree := by
  refine induction_on_monomial (motive := fun p => (dZ ε Z p).totalDegree ≤ p.totalDegree) ?_ ?_ s a
  · intro a
    have : dZ ε Z (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact (dZ ε Z).map_algebraMap a
    rw [this]; simp
  · intro p v ih
    by_cases hp : p = 0
    · simp [hp]
    rw [Derivation.leibniz, totalDegree_mul_of_isDomain hp (X_ne_zero v), totalDegree_X, smul_eq_mul, smul_eq_mul]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans (add_le_add le_rfl ?_)
      simp only [dZ, mkDerivation_X]
      cases v with
      | inl x =>
        simp only [Sum.elim_inl]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
      | inr x =>
        simp only [Sum.elim_inr]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega

theorem sb_degdz {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (P : Poly n) :
    (dZ ε Z P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (sb_degmono ε Z m _).trans ?_
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hm)

theorem sb_degrp {n : ℕ} (ε : Fin n → Bool) : (rP ε : Poly n).totalDegree ≤ 2 := by
  unfold rP
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp

theorem sb_evderiv {σ : Type} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (γ : ℝ → σ → ℂ) (s : ℝ)
    (hγ : ∀ v, HasDerivAt (fun u => γ u v) (MvPolynomial.eval (γ s) (D (MvPolynomial.X v))) s) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun u => MvPolynomial.eval (γ u) P) (MvPolynomial.eval (γ s) (D P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : D (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact D.map_algebraMap a
    simp only [this, eval_C, map_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p v hp =>
    have h := hp.fun_mul (hγ v)
    simp only [map_mul, eval_X]
    refine h.congr_deriv ?_
    rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, eval_X]
    ring

theorem sb_curve {n : ℕ} (Z g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (a b : Fin n) :
    HasDerivAt (fun u : ℝ => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) a b)
      (((NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) * Z -
        Z * (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) a b) s := by
  let : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Z))) (NormedSpace.exp (s • (-Z)) * (-Z)) s :=
    hasDerivAt_exp_smul_const _ _
  have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Z)) (NormedSpace.exp (s • Z) * Z) s :=
    hasDerivAt_exp_smul_const _ _
  have h3 := (h1.mul_const g).mul h2
  have hc : Commute Z (NormedSpace.exp (s • Z)) := ((Commute.refl Z).smul_right s).exp_right
  have hc' : Commute (-Z) (NormedSpace.exp (s • (-Z))) := ((Commute.refl (-Z)).smul_right s).exp_right
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  have h4 := L.hasFDerivAt.comp_hasDerivAt s h3
  simp only [Function.comp_def] at h4
  have e : ∀ u : ℝ, (u : ℂ) • Z = u • Z := fun u => by simp
  simp only [e, smul_neg] at *
  refine HasDerivAt.congr_deriv (f := fun u : ℝ => (NormedSpace.exp (-(u • Z)) * g * NormedSpace.exp (u • Z)) a b) h4 ?_
  show (NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z)) a b = _
  have hm : NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z) =
      NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z) * Z -
        Z * (NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z)) := by
    rw [← hc'.eq]; noncomm_ring
  rw [hm]

theorem sb_evcurve {n : ℕ} (ε : Fin n → Bool) (Z g : Mat n) (s : ℝ) (P : Poly n) (hZ : LieU ε Z) :
    HasDerivAt (fun u : ℝ => ev (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) P) (ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z P)) s := by
  refine sb_evderiv (dZ ε Z)
    (fun u : ℝ => Sum.elim (fun x : Fin n × Fin n => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2) (fun x => star ((NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2))) s ?_ P
  have hZ' : ∀ a b, barM ε Z a b = (starRingEnd ℂ) (Z a b) := fun a b => (hZ a b).symm
  rintro (x | x)
  · refine (sb_curve Z g s x.1 x.2).congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib]
  · refine (sb_curve Z g s x.1 x.2).star.congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib, hZ', star_sum, star_mul']

theorem cutoffPolynomial_conjugation_deriv_mem_shapeSpan : StBasDeriv := by
  intro n ε Z H P hZ hH
  refine ⟨?_, fun g s => ?_⟩
  · have h1 : bas ε (deriv H) (dZ ε Z (rP ε) * P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨deriv H, _, sb_derivcut H hH, ?_, rfl⟩
      have := (sb_degdz ε Z (rP ε)).trans (sb_degrp ε)
      exact (totalDegree_mul _ _).trans (by omega)
    have h2 : bas ε H (dZ ε Z P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨H, _, hH, ?_, rfl⟩
      exact (sb_degdz ε Z P).trans (by omega)
    have e : adBas ε Z H P = bas ε (deriv H) (dZ ε Z (rP ε) * P) + bas ε H (dZ ε Z P) := rfl
    rw [e]
    exact Submodule.add_mem _ h1 h2
  · have hE := sb_evcurve ε Z g s (rP ε) hZ
    simp only [sb_evrp] at hE
    obtain ⟨c, hc⟩ : ∃ c, c = ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z (rP ε)) := ⟨_, rfl⟩
    rw [← hc] at hE
    have hre : HasDerivAt (fun u : ℝ => rM ε (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z))) c.re s := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hE
      simpa [Function.comp_def] using this
    have him : c.im = 0 := by
      have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hE
      simp [Function.comp_def] at h1
      exact h1.unique (hasDerivAt_const _ _)
    have hcre : ((c.re : ℝ) : ℂ) = c := Complex.ext (by simp) (by simp [him])
    have hHd : HasDerivAt H (deriv H (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)))) (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) :=
      ((hH.1.differentiable (by simp)) _).hasDerivAt
    have hcomp := (hHd.comp s hre).ofReal_comp
    have hP := sb_evcurve ε Z g s P hZ
    have htot := hcomp.fun_mul hP
    refine htot.congr_deriv ?_
    simp only [adBas, bas, map_mul, ← hc, Function.comp_apply]
    rw [← hcre]
    simp only [Complex.ofReal_re, Complex.ofReal_mul]
    ring

end GlobalTheory.PsCo.Pc1.B
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzGaussWidth
open FourierTransform MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_schwartz_gauss_width (c : ℝ) (hc : 0 < c) :
    ∃ g : SchwartzMap E ℂ, ∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  set t : ℝ := Real.sqrt (c / Real.pi) with ht_def
  have ht : t ≠ 0 := (Real.sqrt_pos.2 (div_pos hc Real.pi_pos)).ne'
  have ht2 : t ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc Real.pi_pos).le
  let e : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (GroundTheory.Global.gaussianSchwartz E), fun y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
  congr 1
  have hey : e y = t • y := rfl
  rw [hey, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ht2]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

theorem mem_of_smul {M : Submodule ℂ (SchwartzMap E ℂ)} (c : ℝ) (K : ℂ) (hK : K ≠ 0)
    (u : SchwartzMap E ℂ) (hu : ∀ y, u y = K * Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)))
    (huM : u ∈ M) :
    ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro g hg
  have : g = K⁻¹ • u := by
    ext y
    rw [SchwartzMap.smul_apply, hu, hg, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  rw [this]
  exact M.smul_mem _ huM

variable [MeasurableSpace E] [BorelSpace E]

theorem integral_gauss_mul_gauss (s c : ℝ) (hs : 0 < s) (hc : 0 < c) (y : E) :
    ∫ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (-(((s * c / (s + c)) * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  have hsc : 0 < s + c := by linarith
  have key : ∀ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((s + c : ℝ) : ℂ) * (‖a‖ : ℂ) ^ 2 + ((2 * c : ℝ) : ℂ) * ((inner ℝ y a : ℝ) : ℂ)) *
        Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [norm_sub_sq_real]
    push_cast
    ring
  simp_rw [key]
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (by simpa using hsc) _ y, mul_assoc, ← Complex.exp_add]
  congr 2
  have h1 : ((s + c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  push_cast at h1 ⊢
  field_simp
  ring

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def HasWidth (M : Submodule ℂ (SchwartzMap E ℂ)) (c : ℝ) : Prop :=
  ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M

def ConvStable (M : Submodule ℂ (SchwartzMap E ℂ)) : Prop :=
  ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
        Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) → u ∈ M

theorem cpow_ne_zero_of_pos (r : ℝ) (hr : 0 < r) (z : ℂ) : ((r : ℂ)) ^ z ≠ 0 := by
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  exact (Complex.ofReal_ne_zero.2 hr.ne') h.1

theorem hasWidth_of_lt {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) (c' : ℝ) (hc' : 0 < c') (hlt : c' < c) : HasWidth M c' := by
  set s : ℝ := c * c' / (c - c') with hs_def
  have hcc : 0 < c - c' := by linarith
  have hs : 0 < s := div_pos (mul_pos hc hc') hcc
  have hsc : s * c / (s + c) = c' := by
    rw [hs_def]; field_simp; ring
  obtain ⟨h, hh⟩ := exists_schwartz_gauss_width (E := E) (s / 2) (by linarith)
  obtain ⟨g', hg'⟩ := exists_schwartz_gauss_width (E := E) c' hc'
  set K : ℂ := ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / ((s + c : ℝ) : ℂ) = ((Real.pi / (s + c) : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos (by linarith)) _
  have huM : K • g' ∈ M := hconv (s / 2) c (by linarith) hc hP h (K • g') (fun y => by
    rw [SchwartzMap.smul_apply, smul_eq_mul, hg', ← hsc, ← integral_gauss_mul_gauss s c hs hc y]
    congr 1
    funext a
    rw [hh]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring)
  exact mem_of_smul c' K hK (K • g') (fun y => by rw [SchwartzMap.smul_apply, smul_eq_mul, hg']) huM

theorem hasWidth_fourier {M : Submodule ℂ (SchwartzMap E ℂ)} (hF : ∀ f ∈ M, 𝓕 f ∈ M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) : HasWidth M (Real.pi ^ 2 / c) := by
  obtain ⟨g, hg⟩ := exists_schwartz_gauss_width (E := E) c hc
  set K : ℂ := ((Real.pi : ℂ) / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / (c : ℂ) = ((Real.pi / c : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos hc) _
  refine mem_of_smul (Real.pi ^ 2 / c) K hK (𝓕 g) (fun w => ?_) (hF g (hP g hg))
  have hfun : (g : E → ℂ) = fun v => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v; rw [hg]; push_cast; ring_nf
  rw [SchwartzMap.fourier_coe, hfun, fourier_gaussian_innerProductSpace (by simpa using hc)]
  congr 2
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

theorem hasWidth_all {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M)
    (hF : ∀ f ∈ M, 𝓕 f ∈ M) (hπ : HasWidth M Real.pi) (c : ℝ) (hc : 0 < c) : HasWidth M c := by
  rcases lt_trichotomy c Real.pi with hlt | heq | hgt
  · exact hasWidth_of_lt hconv Real.pi Real.pi_pos hπ c hc hlt
  · exact heq ▸ hπ
  · have hc' : 0 < Real.pi ^ 2 / c := by positivity
    have hlt : Real.pi ^ 2 / c < Real.pi := by
      rw [div_lt_iff₀ hc]; nlinarith [Real.pi_pos]
    have h1 := hasWidth_fourier hF _ hc' (hasWidth_of_lt hconv Real.pi Real.pi_pos hπ _ hc' hlt)
    have : Real.pi ^ 2 / (Real.pi ^ 2 / c) = c := by
      have := Real.pi_pos.ne'; field_simp
    rwa [this] at h1

theorem hasWidth_pi {M : Submodule ℂ (SchwartzMap E ℂ)} (G : SchwartzMap E ℂ)
    (hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) (hGM : G ∈ M) :
    HasWidth M Real.pi := by
  intro g hg
  have : g = G := by ext y; rw [hg, hG]
  rwa [this]

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

theorem all_widths_of_conv
    (hconvAll : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
      ∀ (b c : ℝ), 0 < b → 0 < c →
      (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
      ∀ (h u : SchwartzMap E ℂ),
        (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
          Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
        u ∈ M) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro E _ _ _ _ _ M hM hℓ hF G hG hGM c hc g hg
  exact hasWidth_all (fun b c' hb hc' hP h u hu => hconvAll E M hM hℓ b c' hb hc' hP h u hu) hF
    (hasWidth_pi G hG hGM) c hc g hg

end GlobalTheory.GaussWidths
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportStabilizerWeightedPairTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportStabilizerWeightedPairTerm
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

namespace GlobalTheory.OrbitUnfold

theorem finite_support_pairTerm :
    ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ),
      (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) →
      (∀ y : Y, (Function.support (F y)).Finite) →
      {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite →
      (Function.support (fun o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ) =>
        pairTerm F (Quotient.out o))).Finite := by
  intro Γ Y _ _ F hF hfin hS
  refine (hS.biUnion (t := fun o' =>
      (fun γ : Γ => (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of γ))) ''
        Function.support (F (Quotient.out o'))) (fun o' _ => (hfin _).image _)).subset ?_
  intro o ho
  have hne : F (Quotient.out o).1 (val (Quotient.out o).2) ≠ 0 := by
    intro h
    apply ho
    simp [pairTerm, h]
  set p := Quotient.out o with hp
  set o' : MulAction.orbitRel.Quotient Γ Y := Quotient.mk (MulAction.orbitRel Γ Y) p.1 with ho'
  obtain ⟨η, hη⟩ := Quotient.exact (Quotient.out_eq o')
  change η • p.1 = Quotient.out o' at hη
  have hval : F (Quotient.out o') (η * val p.2 * η⁻¹) ≠ 0 := by
    rw [← hη, hF]; exact hne
  refine Set.mem_biUnion (x := o') ⟨_, hval⟩ ⟨η * val p.2 * η⁻¹, hval, ?_⟩
  have hsm : (η • p : Y × ConjSelf Γ) = (Quotient.out o', of (η * val p.2 * η⁻¹)) := by
    rw [Prod.smul_def, hη]; rfl
  show Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of (η * val p.2 * η⁻¹)) = o
  rw [← hsm]
  calc Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (η • p)
      = Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p :=
        Quotient.sound ⟨η, rfl⟩
    _ = o := by rw [hp]; exact Quotient.out_eq o

end GlobalTheory.OrbitUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportStabilizerWeightedPairTermStatement
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_stabilizerWeightedPairTerm : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → (Function.support (fun o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ) => pairTerm F (Quotient.out o))).Finite := by
  first | exact @GlobalTheory.OrbitUnfold.finite_support_pairTerm | exact GlobalTheory.OrbitUnfold.finite_support_pairTerm | (intros; apply GlobalTheory.OrbitUnfold.finite_support_pairTerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitRelFibredEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitRelFibredEquivariant
namespace GlobalTheory

open MulAction

theorem finsum_orbitRel_fibred : ∀ {H X B E : Type} [Group H] [MulAction H X] [MulAction H B] [MulAction H E] (π : X → B), (∀ (h : H) (x : X), π (h • x) = h • π x) → ∀ (S : B → Subgroup H), (∀ b : B, MulAction.stabilizer H b ≤ S b) → ∀ (j : B → E → X), (∀ b : B, Function.Injective (j b)) → (∀ (b : B) (e : E), π (j b e) = b) → (∀ (b : B) (x : X), π x = b → ∃ e : E, j b e = x) → (∀ (b : B), ∀ h ∈ S b, ∀ e : E, j b (h • e) = h • j b e) → ∀ (s : MulAction.orbitRel.Quotient H B → B), (∀ q, Quotient.mk (MulAction.orbitRel H B) (s q) = q) → ∀ (g : MulAction.orbitRel.Quotient H X → ℂ), (Function.support g).Finite → ∑ᶠ o, g o = ∑ᶠ q, ∑ᶠ o' : MulAction.orbitRel.Quotient (S (s q)) E, g (Quotient.mk (MulAction.orbitRel H X) (j (s q) (Quotient.out o'))) := by
  intro H X B E _ _ _ _ π hπ S hS j hinj hjπ hjsurj hjeq s hs g hg
  let ρ : orbitRel.Quotient H X → orbitRel.Quotient H B :=
    Quotient.map π (fun x y hxy => by
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hxy)
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨h, by rw [← hπ, hh]⟩))
  have hρ : ∀ x, ρ (Quotient.mk _ x) = Quotient.mk _ (π x) := fun x => rfl
  rw [GlobalTheory.finsum_fiberwise_of_finite_support ρ g hg]
  refine finsum_congr (fun q => ?_)
  set b := s q with hb

  have key : ∀ e e' : E, (orbitRel (S b) E) e e' →
      Quotient.mk (orbitRel H X) (j b e) = Quotient.mk (orbitRel H X) (j b e') := by
    intro e e' hee
    obtain ⟨k, hk⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hee)
    apply Quotient.sound
    refine orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨(k : H), ?_⟩)
    rw [← hjeq b k k.2 e', ← hk]
    rfl
  let φ : orbitRel.Quotient (S b) E → {o // ρ o = q} := fun o' =>
    ⟨Quotient.mk _ (j b (Quotient.out o')), by rw [hρ, hjπ, hb, hs]⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro o₁ o₂ h12
      have h12' : Quotient.mk (orbitRel H X) (j b (Quotient.out o₁))
          = Quotient.mk (orbitRel H X) (j b (Quotient.out o₂)) := congrArg Subtype.val h12
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact h12'))
      have hbh : h • b = b := by
        have := congrArg π hh
        rwa [hπ, hjπ, hjπ] at this
      have hmem : h ∈ S b := hS b (mem_stabilizer_iff.mpr hbh)
      have he : h • Quotient.out o₂ = Quotient.out o₁ := by
        apply hinj b
        rw [hjeq b h hmem, hh]
      rw [← Quotient.out_eq o₁, ← Quotient.out_eq o₂]
      apply Quotient.sound
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨⟨h, hmem⟩, he⟩)
    · rintro ⟨o, ho⟩
      have hx : Quotient.mk (orbitRel H B) (π (Quotient.out o)) = Quotient.mk (orbitRel H B) b := by
        rw [← hρ, Quotient.out_eq, ho, hb, hs]
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact hx))
      obtain ⟨e, he⟩ := hjsurj b (h⁻¹ • Quotient.out o) (by rw [hπ, ← hh, inv_smul_smul])
      refine ⟨Quotient.mk _ e, Subtype.ext ?_⟩
      show Quotient.mk (orbitRel H X) (j b (Quotient.out (Quotient.mk (orbitRel (S b) E) e))) = o
      rw [key _ e (Quotient.exact (Quotient.out_eq _)), he]
      conv_rhs => rw [← Quotient.out_eq o]
      apply Quotient.sound
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨h⁻¹, rfl⟩)
  exact (finsum_comp_equiv (Equiv.ofBijective φ hφ) (f := fun o : {o // ρ o = q} => g o.1)).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitRelFibredEquivariantStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_orbitRel_fibred_equivariant : ∀ {H X B E : Type} [Group H] [MulAction H X] [MulAction H B] [MulAction H E] (π : X → B), (∀ (h : H) (x : X), π (h • x) = h • π x) → ∀ (S : B → Subgroup H), (∀ b : B, MulAction.stabilizer H b ≤ S b) → ∀ (j : B → E → X), (∀ b : B, Function.Injective (j b)) → (∀ (b : B) (e : E), π (j b e) = b) → (∀ (b : B) (x : X), π x = b → ∃ e : E, j b e = x) → (∀ (b : B), ∀ h ∈ S b, ∀ e : E, j b (h • e) = h • j b e) → ∀ (s : MulAction.orbitRel.Quotient H B → B), (∀ q, Quotient.mk (MulAction.orbitRel H B) (s q) = q) → ∀ (g : MulAction.orbitRel.Quotient H X → ℂ), (Function.support g).Finite → ∑ᶠ o, g o = ∑ᶠ q, ∑ᶠ o' : MulAction.orbitRel.Quotient (S (s q)) E, g (Quotient.mk (MulAction.orbitRel H X) (j (s q) (Quotient.out o'))) := by
  first | exact @GlobalTheory.finsum_orbitRel_fibred | exact GlobalTheory.finsum_orbitRel_fibred | (intros; apply GlobalTheory.finsum_orbitRel_fibred <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMuEqExtDerivation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OptionEquivLeftRenameSomeComplexEqC
open MvPolynomial

namespace GlobalTheory

theorem optionEquivLeft_rename_some_complex_eq_C {τ : Type} (c : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.rename some c) = Polynomial.C c := by
  induction c using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, MvPolynomial.optionEquivLeft_C, Polynomial.C_eq_algebraMap]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, Polynomial.C_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, MvPolynomial.rename_X, MvPolynomial.optionEquivLeft_X_some, Polynomial.C_mul]

theorem coeff_optionEquivLeft_extDerivation {τ : Type}
    (E : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ)) (k : ℕ) (s : MvPolynomial (Option τ) ℂ) :
    (MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.mkDerivation ℂ (fun w : Option τ => match w with
      | none => (0 : MvPolynomial (Option τ) ℂ)
      | some v => MvPolynomial.rename some (E (MvPolynomial.X v))) s)).coeff k
      = E ((MvPolynomial.optionEquivLeft ℂ τ (s)).coeff k) := by
  induction s using MvPolynomial.induction_on generalizing k with
  | C a =>
    have h1 : (MvPolynomial.C a : MvPolynomial (Option τ) ℂ) = algebraMap ℂ _ a := rfl
    have h2 : (MvPolynomial.C a : MvPolynomial τ ℂ) = algebraMap ℂ _ a := rfl
    rw [h1, Derivation.map_algebraMap, ← h1, MvPolynomial.optionEquivLeft_C, Polynomial.coeff_C]
    split_ifs <;> simp [h2, Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p n hp =>
    rw [Derivation.leibniz, MvPolynomial.mkDerivation_X]
    rcases n with _ | v
    · simp only [smul_zero, zero_add, smul_eq_mul, mul_zero, map_mul, MvPolynomial.optionEquivLeft_X_none]
      rcases k with _ | k
      · simp [Polynomial.coeff_mul_X_zero, mul_comm (Polynomial.X) _]
      · rw [mul_comm Polynomial.X, Polynomial.coeff_mul_X, Polynomial.coeff_mul_X, hp]
    · simp only [smul_eq_mul, map_add (f := _), map_mul, MvPolynomial.optionEquivLeft_X_some, optionEquivLeft_rename_some_complex_eq_C,
        Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, hp, Derivation.leibniz]

end GlobalTheory
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem coefM_apply_eq_coeff {n L : ℕ} (k : ℕ) (s : PolyM n L) :
    coefM n L k s = (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) s).coeff k := by
  simp only [coefM, LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply,
    Polynomial.lcoeff_apply]

theorem dMu_eq_extDerivation {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) :
    dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := by
  unfold dMu
  refine congrArg _ (funext fun w => ?_)
  cases w with
  | none => rfl
  | some v => simp only [inM]

theorem coefM_dMu : T_coefM_dMu := by
  intro n L ε x k s
  have h := GlobalTheory.coeff_optionEquivLeft_extDerivation (dL L ε x) k s
  rw [coefM_apply_eq_coeff, coefM_apply_eq_coeff, ← h]
  have e : dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := dMu_eq_extDerivation ε x
  refine congrArg (fun D : Derivation ℂ (PolyM n L) (PolyM n L) => (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) (D s)).coeff k) (e.trans ?_)
  refine congrArg _ (funext fun w => ?_)
  cases w <;> rfl

end GlobalTheory.PsCo.Cw2a
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaCoeffCommutesModeDerivation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesSumAlgEquivMkDerivation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesSumAlgEquivMkDerivation
open MvPolynomial

namespace GlobalTheory

theorem sumAlgEquiv_rename_inr_eq_C {σ : Type} {L : ℕ} (q : MvPolynomial σ ℂ) :
    MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.rename Sum.inr q) = MvPolynomial.C q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, rename_X, sumAlgEquiv_X_inr]

theorem coeff_sumAlgEquiv_mkDerivation_gen {σ : Type} {L : ℕ}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (b : MvPolynomial (Fin L ⊕ σ) ℂ) (m : Fin L →₀ ℕ) :
    AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ
      (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ))
        (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) m =
      D (AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ b) m) := by
  induction b using MvPolynomial.induction_on generalizing m with
  | C a =>
    have h1 : (MvPolynomial.C a : MvPolynomial (Fin L ⊕ σ) ℂ) = algebraMap ℂ _ a := rfl
    rw [h1, Derivation.map_algebraMap, map_zero, AddMonoidAlgebra.coeff_zero, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C]
    split_ifs
    · exact (D.map_algebraMap a).symm
    · simp
  | add p q hp hq => simp only [map_add (f := _), MvPolynomial.coeff_add, hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, map_mul, MvPolynomial.coeff_add]
    rcases i with j | v
    · simp only [mkDerivation_X, Sum.elim_inl, map_zero, mul_zero, AddMonoidAlgebra.coeff_zero,
        sumAlgEquiv_X_inl]
      rw [mul_comm (X j), coeff_mul_X', coeff_mul_X']
      simp only [Finsupp.zero_apply, zero_add]
      split_ifs
      · exact hp _
      · exact (D.map_zero).symm
    · simp only [mkDerivation_X, Sum.elim_inr, sumAlgEquiv_X_inr, sumAlgEquiv_rename_inr_eq_C,
        coeff_C_mul, hp]
      rw [mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (D (X v))),
        mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (X v)), coeff_C_mul, coeff_C_mul,
        Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring

theorem coeff_allOnes_sumAlgEquiv_mkDerivation :
    ∀ {σ : Type} {L : ℕ} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (b : MvPolynomial (Fin L ⊕ σ) ℂ), AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ)) (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) = D (AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ))) :=
  fun D b => coeff_sumAlgEquiv_mkDerivation_gen D b _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesSumAlgEquivMkDerivationStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_allOnes_sumAlgEquiv_derivation_eq : ∀ {σ : Type} {L : ℕ} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (b : MvPolynomial (Fin L ⊕ σ) ℂ), AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ)) (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) = D (AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ))) := by
  first | exact @GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation | exact GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation | (intros; apply GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation <;> assumption)
end
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem exL_dL_holds : GlobalTheory.PsCo.Cw2a.T_exL_dL := by
  intro n L ε x b
  have h := GlobalTheory.T.coeff_allOnes_sumAlgEquiv_derivation_eq (σ := EntIdx n) (L := L) (dM ε x) b
  simpa [exL, dL, inL, allOnes] using h

end GlobalTheory.PsCo.Cw2a
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedAverageApproxOfSubgroupFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedAverageApproxOfSubgroupFixed
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory


open MeasureTheory in
open scoped ContDiff in
theorem _root_.GlobalTheory.exists_average_fixed_approx_of_fixed :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (H U : Subgroup G), IsOpen (U : Set G) → (∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H) → ∀ v : K, (∀ k ∈ H, ρ k v = v) → ∀ ε : ℝ, 0 < ε → ∃ η : G → ℂ, Continuous η ∧ HasCompactSupport η ∧ (∀ k ∈ H, ρ k (∫ y, η y • ρ y v ∂μ) = ∫ y, η y • ρ y v ∂μ) ∧ ‖v - ∫ y, η y • ρ y v ∂μ‖ < ε := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ρ _ hcont H U hU hconj v hv ε hε
  set W : Set G := (U : Set G) ∩ {y | ‖ρ y v - v‖ < ε / 2} with hW
  have hWo : IsOpen W :=
    hU.inter (isOpen_lt ((hcont v).sub continuous_const).norm continuous_const)
  have h1W : (1 : G) ∈ W := ⟨U.one_mem, by simp [half_pos hε]⟩
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hWo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1W)
  have hf1' : f 1 = 1 := by simpa using hf1 (Set.mem_singleton (1 : G))
  have hfpos : 0 < ∫ y, f y ∂μ :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc (fun x => (hfI x).1)
      (x := 1) (by rw [hf1']; norm_num)
  set c := ∫ y, f y ∂μ with hc
  set η : G → ℂ := fun y => ((c⁻¹ * f y : ℝ) : ℂ) with hηdef
  have hηc : Continuous η :=
    Complex.continuous_ofReal.comp (continuous_const.mul f.continuous)
  have hηs : HasCompactSupport η :=
    hfc.comp_left (g := fun r : ℝ => ((c⁻¹ * r : ℝ) : ℂ)) (by simp)
  have hηW : ∀ y, η y ≠ 0 → y ∈ W := by
    intro y hy
    by_contra hyW
    exact hy (by simp [hηdef, hf0 hyW])
  have hηI : Integrable η μ := hηc.integrable_of_hasCompactSupport hηs
  have hint : Integrable (fun y => η y • ρ y v) μ :=
    (hηc.smul (hcont v)).integrable_of_hasCompactSupport hηs.smul_right
  have hnormη : (fun y => ‖η y‖) = fun y => c⁻¹ * f y := by
    funext y
    simp only [hηdef, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (inv_nonneg.2 hfpos.le) (hfI y).1)
  have hη1 : ∫ y, η y ∂μ = 1 := by
    simp only [hηdef]
    rw [integral_complex_ofReal, integral_const_mul, inv_mul_cancel₀ hfpos.ne', Complex.ofReal_one]
  refine ⟨η, hηc, hηs, ?_, ?_⟩
  · intro k hk
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [map_smul]
    by_cases hy : η y = 0
    · simp [hy]
    have hyU : y ∈ U := (hηW y hy).1
    congr 1
    have hky : k * y = y * (y⁻¹ * k * y) := by group
    calc ρ k (ρ y v) = ρ (k * y) v := by rw [map_mul]; rfl
      _ = ρ (y * (y⁻¹ * k * y)) v := by rw [hky]
      _ = ρ y (ρ (y⁻¹ * k * y) v) := by rw [map_mul]; rfl
      _ = ρ y v := by rw [hv _ (hconj y hyU k hk)]
  · have hsplit : v - ∫ y, η y • ρ y v ∂μ = ∫ y, η y • (v - ρ y v) ∂μ := by
      simp_rw [smul_sub]
      rw [integral_sub (hηI.smul_const v) hint, integral_smul_const, hη1, one_smul]
    rw [hsplit]
    calc ‖∫ y, η y • (v - ρ y v) ∂μ‖ ≤ ∫ y, ‖η y‖ * (ε / 2) ∂μ := by
          refine norm_integral_le_of_norm_le (hηI.norm.mul_const _)
            (Filter.Eventually.of_forall fun y => ?_)
          rw [norm_smul]
          by_cases hy : η y = 0
          · simp [hy]
          exact mul_le_mul_of_nonneg_left
            (by rw [norm_sub_rev]; exact (hηW y hy).2.le) (norm_nonneg _)
      _ = ε / 2 := by
          rw [integral_mul_const, hnormη, integral_const_mul, inv_mul_cancel₀ hfpos.ne', one_mul]
      _ < ε := half_lt_self hε

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedAverageApproxOfSubgroupFixedStatement
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_average_approx_of_subgroup_fixed : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (H U : Subgroup G), IsOpen (U : Set G) → (∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H) → ∀ v : K, (∀ k ∈ H, ρ k v = v) → ∀ ε : ℝ, 0 < ε → ∃ η : G → ℂ, Continuous η ∧ HasCompactSupport η ∧ (∀ k ∈ H, ρ k (∫ y, η y • ρ y v ∂μ) = ∫ y, η y • ρ y v ∂μ) ∧ ‖v - ∫ y, η y • ρ y v ∂μ‖ < ε := by
  first | exact @GlobalTheory.exists_average_fixed_approx_of_fixed | exact GlobalTheory.exists_average_fixed_approx_of_fixed | (intros; apply GlobalTheory.exists_average_fixed_approx_of_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseDerivativePowerSeriesMulSubstLeibniz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseDerivativePowerSeriesMulSubstLeibniz
open Polynomial

namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

theorem hasse_coe (l : ℕ) (f : R[X]) :
    hasse l (f : PowerSeries R) = ((hasseDeriv l f : R[X]) : PowerSeries R) := by
  ext n
  rw [coeff_hasse, Polynomial.coeff_coe, Polynomial.coeff_coe, hasseDeriv_coeff]

theorem coeff_hasse_congr {l n : ℕ} {φ φ' : PowerSeries R}
    (h : ∀ m ≤ n + l, PowerSeries.coeff m φ = PowerSeries.coeff m φ') :
    PowerSeries.coeff n (hasse l φ) = PowerSeries.coeff n (hasse l φ') := by
  rw [coeff_hasse, coeff_hasse, h _ le_rfl]

theorem coeff_mul_congr {n : ℕ} {φ φ' ψ ψ' : PowerSeries R}
    (h₁ : ∀ m ≤ n, PowerSeries.coeff m φ = PowerSeries.coeff m φ')
    (h₂ : ∀ m ≤ n, PowerSeries.coeff m ψ = PowerSeries.coeff m ψ') :
    PowerSeries.coeff n (φ * ψ) = PowerSeries.coeff n (φ' * ψ') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [h₁ _ (by omega), h₂ _ (by omega)]

theorem hasse_mul (l : ℕ) (φ ψ : PowerSeries R) :
    hasse l (φ * ψ) = ∑ p ∈ Finset.range (l + 1), hasse p φ * hasse (l - p) ψ := by
  ext n
  set M := n + l + 1 with hM
  set f : R[X] := PowerSeries.trunc M φ
  set g : R[X] := PowerSeries.trunc M ψ
  have hf : ∀ m < M, PowerSeries.coeff m φ = PowerSeries.coeff m (f : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hg : ∀ m < M, PowerSeries.coeff m ψ = PowerSeries.coeff m (g : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hpoly : hasse l ((f : PowerSeries R) * (g : PowerSeries R)) =
      ∑ p ∈ Finset.range (l + 1), hasse p (f : PowerSeries R) * hasse (l - p) (g : PowerSeries R) := by
    rw [← Polynomial.coe_mul, hasse_coe, hasseDeriv_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => hasseDeriv i f * hasseDeriv j g) l]
    simp only [hasse_coe]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_hasse_congr (φ' := (f : PowerSeries R) * (g : PowerSeries R)), hpoly, map_sum, map_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpl : p ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    apply coeff_mul_congr
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hf m' (by omega)).symm
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hg m' (by omega)).symm
  · intro m hm
    exact coeff_mul_congr (fun m' hm' => hf m' (by omega)) (fun m' hm' => hg m' (by omega))

end GlobalTheory.PicDiv

namespace GlobalTheory

theorem hasse_mul_subst :
    ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 →
      ((GlobalTheory.PicDiv.hasse l (φ * ψ)).subst a : PowerSeries k) =
        ∑ p ∈ Finset.range (l + 1),
          ((GlobalTheory.PicDiv.hasse p φ).subst a : PowerSeries k) * (GlobalTheory.PicDiv.hasse (l - p) ψ).subst a := by
  intro k _ a φ ψ l ha
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.PicDiv.hasse_mul, ← PowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseDerivativePowerSeriesMulSubstLeibnizStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasseDerivativePowerSeries_mul_subst_leibniz : ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 → ((GlobalTheory.PicDiv.hasse l (φ * ψ)).subst a : PowerSeries k) = ∑ p ∈ Finset.range (l + 1), ((GlobalTheory.PicDiv.hasse p φ).subst a : PowerSeries k) * (GlobalTheory.PicDiv.hasse (l - p) ψ).subst a := by
  first | exact @GlobalTheory.hasse_mul_subst | exact GlobalTheory.hasse_mul_subst | (intros; apply GlobalTheory.hasse_mul_subst <;> assumption)
end
end
