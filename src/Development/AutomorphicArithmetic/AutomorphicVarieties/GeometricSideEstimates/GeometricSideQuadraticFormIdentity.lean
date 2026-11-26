module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem quad_eq (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Fin a → Cinf E) :
    quad p x = ∑ w : InfinitePlace E, ∑ j, ∑ i, (x i w * p i j w * star (x j w)).re := by
  simp only [quad, dotProduct, vecMul, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, Complex.re_sum, Finset.sum_mul]

private theorem qf_eq (x : Fin a → Cinf E) :
    qf x = ∑ w : InfinitePlace E, ((x ⬝ᵥ star x) w).re := by
  rw [qf, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dotProduct, Finset.sum_apply, Pi.mul_apply, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem UpperTheory.geometric_side_quadraticForm_identity :
    QfFacts := by
  intro E _ _ a
  refine ⟨fun x => ?_, fun p p' c x => ⟨?_, ?_⟩, fun h x => ?_, fun c x => ?_, fun p x => ?_, fun x => ⟨?_, ?_⟩⟩
  · rw [qf_eq, quad, vecMul_one]
  · simp only [quad_eq, Matrix.add_apply, Pi.add_apply, mul_add, add_mul, Complex.add_re, Finset.sum_add_distrib]
  · simp only [quad_eq, Matrix.smul_apply, Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, Complex.smul_re, smul_eq_mul]
  · rw [qf_eq, quad, star_vecMul, dotProduct_mulVec, vecMul_vecMul]
    rfl
  · simp only [qf, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  · have hp : ∀ i j w, ‖p i j w‖ ≤ ‖toL p‖ := fun i j w =>
      ((norm_le_pi_norm (toL p i j) w).trans (norm_le_pi_norm (toL p i) j)).trans (norm_le_pi_norm (toL p) i)
    have key : ∀ w j i, |(x i w * p i j w * star (x j w)).re| ≤ ‖toL p‖ / 2 * (‖x i w‖ ^ 2 + ‖x j w‖ ^ 2) := by
      intro w j i
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, norm_star]
      have h1 := hp i j w
      have h2 := norm_nonneg (p i j w)
      have h3 := mul_nonneg (norm_nonneg (x i w)) (norm_nonneg (x j w))
      have h4 := mul_le_mul_of_nonneg_left h1 h3
      have h5 := mul_nonneg (h2.trans h1) (sq_nonneg (‖x i w‖ - ‖x j w‖))
      nlinarith
    rw [quad_eq, qf, Finset.sum_comm (f := fun i w => ‖x i w‖ ^ 2), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    calc _ ≤ ∑ j, ∑ i, ‖toL p‖ / 2 * (‖x i w‖ ^ 2 + ‖x j w‖ ^ 2) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => key w j i))
      _ = _ := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  · have h0 := qf_nonneg x
    have h : ‖x‖ ≤ √(qf x) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => Real.le_sqrt_of_sq_le ?_
      calc ‖x i w‖ ^ 2 ≤ ∑ w, ‖x i w‖ ^ 2 :=
            Finset.single_le_sum (f := fun w => ‖x i w‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w)
        _ ≤ qf x := Finset.single_le_sum (f := fun i => ∑ w, ‖x i w‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖x‖ ^ 2 ≤ √(qf x) ^ 2 := by gcongr
      _ = qf x := Real.sq_sqrt h0
  · calc qf x ≤ ∑ _i : Fin a, ∑ _w : InfinitePlace E, ‖x‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun w _ => ?_
          have := (norm_le_pi_norm (x i) w).trans (norm_le_pi_norm x i)
          gcongr
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments
open UpperTheory.V.Lit.Geo

private theorem moment_pt (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ k * Real.exp (-Real.pi * x) ≤
      (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * x)) := by
  have h1 : (1 + x) ^ k / (k.factorial : ℝ) ≤ Real.exp (1 + x) :=
    Real.pow_div_factorial_le_exp (1 + x) (by linarith) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h2 : (1 + x) ^ k ≤ k.factorial * Real.exp (1 + x) := by
    rw [div_le_iff₀ hf] at h1
    linarith
  calc (1 + x) ^ k * Real.exp (-Real.pi * x)
      ≤ k.factorial * Real.exp (1 + x) * Real.exp (-Real.pi * x) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (k.factorial * Real.exp 1) * Real.exp (x + -Real.pi * x) := by
        rw [Real.exp_add, Real.exp_add]
        ring
    _ ≤ (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.2
        nlinarith [Real.pi_gt_three]

theorem UpperTheory.moment_bound_of_pointwise_moments :
    Moment := by
  intro N k
  refine ⟨k.factorial * Real.exp 1 * 2 ^ N, by positivity, fun ι q hq => ?_⟩
  obtain ⟨hs1, hle⟩ := hq.2 (1 / 2) 1 (by norm_num) (by norm_num)
  have hnn : ∀ i, 0 ≤ (1 + q i) ^ k * Real.exp (-Real.pi * q i) := fun i => by
    have := hq.1 i
    positivity
  have hpt : ∀ i, (1 + q i) ^ k * Real.exp (-Real.pi * q i) ≤
      (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * q i)) := fun i => moment_pt k (q i) (hq.1 i)
  have hsum : Summable fun i => (1 + q i) ^ k * Real.exp (-Real.pi * q i) :=
    Summable.of_nonneg_of_le hnn hpt (hs1.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' i, (1 + q i) ^ k * Real.exp (-Real.pi * q i)
      ≤ ∑' i, (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * q i)) :=
        hsum.tsum_le_tsum hpt (hs1.mul_left _)
    _ = (k.factorial * Real.exp 1) * ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) := tsum_mul_left
    _ ≤ (k.factorial * Real.exp 1) * ((1 / (1 / 2)) ^ N * ∑' i, Real.exp (-Real.pi * (1 * q i))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = k.factorial * Real.exp 1 * 2 ^ N * ∑' i, Real.exp (-Real.pi * q i) := by
        rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num]
        simp only [one_mul]
        ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RationalPointRetractionExistsCmDatum
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem hom_one {G : Type} [Group G] [TopologicalSpace G] (U : Subgroup G) (hU : IsCompact (U : Set G))
    (φ : G →* {r : ℝ // 0 < r}) (hc : Continuous φ) : ∀ u ∈ U, φ u = 1 := by
  obtain ⟨m, hmU, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hc.continuousOn
  have hle : ∀ u ∈ U, φ u ≤ 1 := fun u hu => by
    have h : φ (u * m) ≤ φ m := hmax (U.mul_mem hu hmU)
    rw [map_mul, mul_comm] at h
    exact (mul_le_iff_le_one_right' _).1 h
  intro u hu
  have h2 := hle _ (U.inv_mem hu)
  rw [map_inv, inv_le_one'] at h2
  exact le_antisymm (hle u hu) h2

private theorem ptF_rat (γ : GL (Fin a) E) (g : GA E a) (v : Fin a → E) :
    ptF (ratGL E a γ * g) v = ptF g (v ᵥ* γ.val) := by
  have h : vFin (v ᵥ* γ.val) = vFin v ᵥ* (GeneralLinearGroup.map (pFin E) (ratGL E a γ)).val :=
    funext fun j => RingHom.map_vecMul (algebraMap E (Af E)) γ.val v j
  change vFin v ᵥ* _ = vFin (v ᵥ* γ.val) ᵥ* _
  rw [h, map_mul, Units.val_mul, Matrix.vecMul_vecMul]

variable [_root_.NumberField.IsTotallyComplex E]

private theorem pt_rat (γ : GL (Fin a) E) (g : GA E a) (v : Fin a → E) :
    pt (ratGL E a γ * g) v = pt g (v ᵥ* γ.val) := by
  have h : vInf (v ᵥ* γ.val) = vInf v ᵥ* (GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val :=
    funext fun j => RingHom.map_vecMul ((pInf E).comp (algebraMap E (Ad E))) γ.val v j
  change vInf v ᵥ* _ = vInf (v ᵥ* γ.val) ᵥ* _
  rw [h, map_mul, Units.val_mul, Matrix.vecMul_vecMul]

private theorem rt_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    rt (ratGL E a γ * splitCentre E a t * g) = ratGL E a γ * rt g := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem retract_rt (g : GA E a) : retractOne (rt g) = retractOne g := retractOne_coe _

private theorem ptF_rt (g : GA E a) : ptF (rt g) = ptF g := by
  have h : GeneralLinearGroup.map (pFin E) (rt g) = GeneralLinearGroup.map (pFin E) g := finPart_retract g
  refine AddMonoidHom.ext fun v => ?_
  change vFin v ᵥ* _ = vFin v ᵥ* _
  rw [h]

private theorem rt_fin (U : Subgroup (GL (Fin a) (Af E))) (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    (u : GL (Fin a) (Af E)) (hu : u ∈ U) (g : GA E a) : rt (g * finGL E a u) = rt g * finGL E a u := by
  have h1 : Reduction.detModule E a (finGL E a u) = 1 := by
    rw [← Fb.finEmb_eq]
    exact hom_one U hU ((Reduction.detModule E a).comp (finEmb E a))
      (Reduction.continuous_detModule.comp continuous_finEmb) u hu
  unfold Lit.Geo.rt
  rw [coe_retractOne, coe_retractOne, map_mul, h1, mul_one, mul_assoc, ← centralSection_inv_mul_comm, ← mul_assoc]

end

theorem UpperTheory.rationalPoint_retraction_exists_cmDatum :
    RtFacts := by
  intro E _ _ _ a _
  refine ⟨rt_left, fun g => ⟨congrArg Subtype.val (retract_rt g), ?_, ptF_rt g⟩,
    fun γ g v => ⟨ptF_rat γ g v, pt_rat γ g v⟩, rt_fin⟩
  unfold qht
  rw [retract_rt]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.DerivSimilitudeCharAtOneEqTrace
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped ContDiff

private theorem der_det {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun r : ℂ => (1 + r • M).det) M.trace 0 := by
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ r : ℂ, (1 + r • M).det = 1 + M.trace * r + p.eval r * r ^ 2 :=
    ⟨_, fun r => Matrix.det_one_add_smul r M⟩
  have h1 := (((hasDerivAt_id (0 : ℂ)).const_mul M.trace).const_add 1).add
    ((p.hasDerivAt 0).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
  rw [funext hp]
  exact HasDerivAt.congr_deriv h1 (by simp)

private theorem der_log {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => Real.log ‖(1 + (t : ℂ) • M).det‖) M.trace.re 0 := by
  have h1 := (der_det M).clog (by simp)
  have h2 : HasDerivAt (fun r : ℂ => Complex.log (1 + r • M).det) M.trace ((0 : ℝ) : ℂ) := by
    simpa using h1
  have h3 := h2.real_of_complex
  simpa only [Complex.log_re] using h3

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem det_ne {y : Matrix (Fin a) (Fin a) (Cinf E)} (hy : IsUnit y) (w : InfinitePlace E) : y.det w ≠ 0 :=
  (((Matrix.isUnit_iff_isUnit_det y).1 hy).map (Pi.evalMonoidHom (fun _ : InfinitePlace E => ℂ) w)).ne_zero

private theorem sm_at {y : Lie E a} (hy : IsUnit (Matrix.of y)) :
    ContDiffAt ℝ ∞ (fun y : Lie E a => sc (Matrix.of y)) y := by
  unfold sc
  refine ((ContDiffAt.sum fun w _ => ?_).div_const _).neg.exp
  have h : ContDiff ℝ ∞ fun x : Lie E a => (Matrix.of x).det w :=
    (contDiff_apply ℝ (fun _ => ℂ) w).comp GlobalTheory.CuspRep.contDiff_det
  exact (h.contDiffAt.norm ℝ (det_ne hy w)).log (norm_ne_zero_iff.2 (det_ne hy w))

private theorem det_line (X : Lie E a) (t : ℝ) (w : InfinitePlace E) :
    (Matrix.of (oneL E a + t • X)).det w = (1 + (t : ℂ) • Matrix.of fun i j => X i j w).det := by
  have h := (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).map_det (Matrix.of (oneL E a + t • X))
  refine h.trans (congrArg _ ?_)
  ext i j
  by_cases hij : i = j <;> simp [oneL, toL, Matrix.one_apply, hij]

private theorem der_sc (X : Lie E a) :
    HasDerivAt (fun t : ℝ => sc (Matrix.of (oneL E a + t • X))) (-ell E a X) 0 := by
  unfold sc
  simp only [det_line]
  have h := ((HasDerivAt.fun_sum (u := Finset.univ) fun (w : InfinitePlace E) _ =>
    der_log (Matrix.of fun i j => X i j w)).div_const ((a : ℝ) * Fintype.card (InfinitePlace E))).neg.exp
  exact HasDerivAt.congr_deriv h (by simp [ell, Matrix.trace])

private theorem sc_mul_star {y : Matrix (Fin a) (Fin a) (Cinf E)} : sc (y * star y) = sc y ^ 2 := by
  unfold sc
  rw [← Real.exp_nat_mul]
  congr 1
  have h : ∀ w, Real.log ‖(y * star y).det w‖ = 2 * Real.log ‖y.det w‖ := fun w => by
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Pi.mul_apply, Pi.star_apply,
      norm_mul, norm_star, ← sq, Real.log_pow]
    norm_num
  simp only [h, ← Finset.mul_sum]
  push_cast
  ring

private theorem sc_one : sc (1 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 := by
  simp [sc]

theorem UpperTheory.deriv_similitudeChar_at_one_eq_trace :
    ScSm := by
  intro E _ _ a
  refine ⟨fun y hy => (sm_at hy).contDiffWithinAt, sc_one, fun X => ?_, fun h => sc_mul_star, fun k => ?_⟩
  · have h1 : IsUnit (Matrix.of (oneL E a)) := isUnit_one
    have hd := ((sm_at h1).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a)
    have h2 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd hl (by simp)
    exact h2.unique (der_sc X)
  · have h : sc k.1 ^ 2 = 1 := by
      rw [← sc_mul_star, Matrix.mem_unitaryGroup_iff.1 k.2, sc_one]
    have hp : 0 < sc k.1 := Real.exp_pos _
    exact (pow_eq_one_iff_of_nonneg hp.le two_ne_zero).1 h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HeightBoundOfQuasiHeightLe
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem ratio_bound {m : ℕ} {f : Fin (m + 1) → ℝ} {c u : ℝ} (hf : ∀ i, 0 < f i) (hc : 0 ≤ c)
    (hu : ∀ i, f i ≤ u) (h1 : 1 ≤ c * ∏ i, f i) (i j : Fin (m + 1)) : f i / f j ≤ c * u ^ (m + 1) := by
  rw [Fin.prod_univ_succAbove _ j] at h1
  have h2 : ∏ k, f (j.succAbove k) ≤ u ^ m := by
    calc ∏ k, f (j.succAbove k) ≤ ∏ _k : Fin m, u := Finset.prod_le_prod₀ (fun k _ => (hf _).le) fun k _ => hu _
      _ = u ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hu0 : 0 < u := (hf i).trans_le (hu i)
  have h3 : 1 ≤ c * (f j * u ^ m) :=
    h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (hf j).le) hc)
  rw [div_le_iff₀ (hf j)]
  calc f i ≤ u * 1 := by rw [mul_one]; exact hu i
    _ ≤ u * (c * (f j * u ^ m)) := mul_le_mul_of_nonneg_left h3 hu0.le
    _ = c * u ^ (m + 1) * f j := by ring

private theorem chain_first {m : ℕ} {r : Fin (m + 1) → ℝ} {t s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hst : s ≤ t) (hr : ∀ i, 0 < r i) (h : ∀ i j : Fin (m + 1), (j : ℕ) = i + 1 → t * r j ≤ r i)
    (i : Fin (m + 1)) : s ^ m * r i ≤ r 0 := by
  have h1 := Reduction.pow_mul_le_of_chain (r := fun j => (r j.rev)⁻¹) hs0 hs1 hst (fun j => inv_pos.2 (hr _))
    (fun p q hpq => by
      have h2 := h q.rev p.rev (by have := q.2; simp only [Fin.val_rev]; omega)
      rw [← div_eq_mul_inv, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ (hr _)]
      exact h2) i.rev
  simp only [Fin.rev_last, Fin.rev_rev] at h1
  rw [← div_eq_mul_inv, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ (hr _)] at h1
  exact h1

private theorem le_of_pow_le {x c : ℝ} {d : ℕ} (hd : d ≠ 0) (hc : 1 ≤ c) (h : x ^ d ≤ c) : x ≤ c := by
  rcases le_or_gt x 1 with h1 | h1
  · exact h1.trans hc
  · exact (le_self_pow₀ h1.le hd).trans h

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem qht_le_height (g : KernelIndexFullLattice.G1 E a) (γ : GL (Fin a) E) :
    qht (E := E) (a := a) g.1 ≤ height (AdelicGLn.diagonal E a γ * g.1) := by
  have h1 := ciInf_le (f := fun γ : GL (Fin a) E =>
    height (K := E) (ratGL E a γ * (retractOne g.1 : KernelIndexFullLattice.G1 E a).1))
    ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩ γ
  rw [retractOne_coe] at h1
  unfold qht
  rw [retractOne_coe]
  exact h1

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem prod_bound {ω : Set (AdelicGLn.AdelicGL E a)} (hω : IsCompact ω) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL E a)),
      b * Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) * kk ∈ Reduction.normOneGL (K := E) (n := a) →
      ∏ i, ρ i ≤ c ∧ (∏ i, ρ i)⁻¹ ≤ c := by
  have hdc : Continuous fun g : AdelicGLn.AdelicGL E a => (Reduction.detModule E a g : ℝ) :=
    continuous_subtype_val.comp Reduction.continuous_detModule
  obtain ⟨M₁, hM₁⟩ := hω.bddAbove_image hdc.continuousOn
  obtain ⟨M₂, hM₂⟩ := hω.bddAbove_image (hdc.inv₀ fun g => (Reduction.detModule E a g).2.ne').continuousOn
  refine ⟨max 1 (max M₁ M₂), le_max_left _ _, fun b hb ρ hρ kk hkk hx => ?_⟩
  have hd : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  have h1 := Reduction.mem_normOneGL_iff_detModule.1 hx
  rw [map_mul, map_mul, Reduction.mem_normOneGL_iff_detModule.1 (Reduction.maxCompact_le_normOneGL hkk),
    mul_one] at h1
  have h2 := congrArg Subtype.val h1
  rw [Positive.val_mul, detModule_diagUnits_posIdele, Positive.val_one] at h2
  have h3 := eq_inv_of_mul_eq_one_right h2
  constructor
  · refine le_of_pow_le hd (le_max_left _ _) ?_
    rw [h3]
    exact (hM₂ ⟨b, hb, rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))
  · refine le_of_pow_le hd (le_max_left _ _) ?_
    rw [inv_pow, h3, inv_inv]
    exact (hM₁ ⟨b, hb, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))

end

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.height_bound_of_quasiHeight_le :
    SiegelHt := by
  intro E _ _ _ a
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) a
  rcases a with _ | m
  · refine ⟨ω, 0, 0, hω, hωB, fun g => ?_⟩
    obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
    exact ⟨γ, b, kk, ρ, hρ, hb, hkk, hxe, fun i => i.elim0⟩
  obtain ⟨Ch, hCh0, hCh⟩ := exists_height_le_normOne (K := E) (n := m + 1) hω
  obtain ⟨c, hc, hcb⟩ := prod_bound hω
  have hc0 : 0 < c := one_pos.trans_le hc
  have hs0 : 0 < min t 1 := lt_min ht one_pos
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = (min t 1) ^ m := ⟨_, rfl⟩
  have hσ0 : 0 < σ := hσ ▸ pow_pos hs0 m
  obtain ⟨e, he⟩ : ∃ e, e = Fintype.card (InfinitePlace E) := ⟨_, rfl⟩
  rw [← he] at hCh
  refine ⟨ω, Ch * c ^ (2 * e) * σ⁻¹ ^ (2 * ((m + 1) * e)), (m + 1) * e, hω, hωB, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγx : AdelicGLn.diagonal E (m + 1) γ * g.1 ∈ Reduction.normOneGL (K := E) (n := (m + 1)) :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) g.2
  obtain ⟨hP1, hP2⟩ := hcb b hb ρ hρ kk hkk (hxe ▸ hγx)
  have hP : 0 < ∏ i, ρ i := Finset.prod_pos fun i _ => hρ i
  have key : ∀ v : ℝ, (∀ i j, ρ i / ρ j ≤ c * (σ⁻¹ * v) ^ (m + 1)) →
      qht (E := E) (a := m + 1) g.1 ≤ Ch * c ^ (2 * e) * σ⁻¹ ^ (2 * ((m + 1) * e)) * v ^ (2 * ((m + 1) * e)) := by
    intro v hv
    have h1 : 1 ≤ c * (σ⁻¹ * v) ^ (m + 1) := by
      have := hv 0 0
      rwa [div_self (hρ 0).ne'] at this
    refine (qht_le_height g γ).trans ((hCh b hb ρ hρ kk hkk _ hγx hxe _ h1 hv).trans_eq ?_)
    simp only [mul_pow, ← pow_mul]
    rw [show (m + 1) * (2 * e) = 2 * ((m + 1) * e) by ring]
    ring
  refine ⟨γ, b, kk, ρ, hρ, hb, hkk, hxe, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl : i = Fin.last m := Fin.ext (by simpa using hi)
    have h := key (ρ (Fin.last m))⁻¹ fun p q => by
      have h1 := ratio_bound (f := fun j => (ρ j)⁻¹) (u := σ⁻¹ * (ρ (Fin.last m))⁻¹) (fun j => inv_pos.2 (hρ j)) hc0.le
        (fun j => by
          rw [← mul_inv]
          refine inv_anti₀ (mul_pos hσ0 (hρ _)) ?_
          rw [hσ]
          exact Reduction.pow_mul_le_of_chain hs0.le (min_le_right _ _) (min_le_left _ _) hρ hs j)
        (by rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, one_le_div hP]; exact hP1) q p
      rwa [inv_div_inv] at h1
    rwa [inv_pow (ρ _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos (hρ _) _)] at h
  · obtain rfl : i = 0 := Fin.ext hi
    refine key (ρ 0) fun p q => ratio_bound hρ hc0.le (fun j => ?_) ?_ p q
    · rw [le_inv_mul_iff₀ hσ0, hσ]
      exact chain_first hs0.le (min_le_right _ _) (min_le_left _ _) hρ hs j
    · rwa [inv_le_iff_one_le_mul₀ hP] at hP2
end
