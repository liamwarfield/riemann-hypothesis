module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralLeOfDisjointTranslates
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaSupBall

open MeasureTheory Filter Set
open scoped Pointwise

theorem integral_le_of_disjoint_translates {ι : Type} [Fintype ι]
    (A : AddSubgroup (EuclideanSpace ℂ ι)) [Countable A]
    (D t : Set (EuclideanSpace ℂ ι)) (hD : IsAddFundamentalDomain A D volume)
    (ht : MeasurableSet t)
    (hd : ∀ y₁ y₂ : A, y₁ ≠ y₂ → Disjoint (y₁ +ᵥ t) (y₂ +ᵥ t))
    (f : EuclideanSpace ℂ ι → ℝ) (hf0 : ∀ u, 0 ≤ f u) (hfc : Continuous f)
    (hf : ∀ (y : A) u, f (y +ᵥ u) = f u) (hi : IntegrableOn f D) :
    ∫ u in t, f u ≤ ∫ u in D, f u := by
  haveI : VAddInvariantMeasure A (EuclideanSpace ℂ ι) volume :=
    ⟨fun g s _ => measure_preimage_add volume (g : EuclideanSpace ℂ ι) s⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable]
  refine ENNReal.toReal_mono (Integrable.lintegral_lt_top hi).ne ?_
  calc ∫⁻ u in t, ENNReal.ofReal (f u)
      = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f (-y +ᵥ u)) :=
        hD.setLIntegral_eq_tsum' (fun u => ENNReal.ofReal (f u)) t
    _ = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by simp_rw [hf]
    _ = ∫⁻ u in ⋃ y : A, (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by
        refine (lintegral_iUnion₀ (fun y => ?_) ?_ _).symm
        · exact (ht.const_vadd y).nullMeasurableSet.inter hD.nullMeasurableSet
        · intro y₁ y₂ h
          exact (((hd y₁ y₂ h).inf_left _).inf_right _).aedisjoint
    _ ≤ ∫⁻ u in D, ENNReal.ofReal (f u) :=
        lintegral_mono_set (iUnion_subset fun _ => inter_subset_right)

theorem factorial_div_le (g : ℕ) {v r : ℝ} (hv : 1 ≤ v) (hr : r ^ 2 = 1 / (4 * v)) :
    (g.factorial : ℝ) / (Real.pi ^ g * r ^ (2 * g)) ≤ (2 * (g : ℝ) * v + 1) ^ g := by
  have hv0 : 0 < v := by linarith
  have hpi := Real.pi_gt_three
  rw [pow_mul, hr, ← mul_pow]
  have h1 : (g.factorial : ℝ) ≤ (g : ℝ) ^ g := by exact_mod_cast Nat.factorial_le_pow g
  calc (g.factorial : ℝ) / (Real.pi * (1 / (4 * v))) ^ g
      ≤ (g : ℝ) ^ g / (Real.pi * (1 / (4 * v))) ^ g := by gcongr
    _ = ((g : ℝ) / (Real.pi * (1 / (4 * v)))) ^ g := by rw [div_pow]
    _ ≤ _ := by
        refine pow_le_pow_left₀ (by positivity) ?_ g
        rw [div_le_iff₀ (by positivity)]
        have h2 : (2 * (g : ℝ) * v + 1) * (Real.pi * (1 / (4 * v)))
            = Real.pi / 2 * g + Real.pi / (4 * v) := by field_simp; ring
        rw [h2]
        have h3 : 0 ≤ Real.pi / (4 * v) := by positivity
        have h4 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
        nlinarith

theorem sup_le_mean_square : ∀ (ι : Type) [Fintype ι] (A : AddSubgroup (EuclideanSpace ℂ ι)) (v : ℝ) (Fd : Set (EuclideanSpace ℂ ι)) (G : EuclideanSpace ℂ ι → ℂ), 1 ≤ v → (∀ x ∈ A, x ≠ 0 → 1 / v ≤ ‖x‖ ^ 2) → MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume → MeasureTheory.volume Fd = 1 → Differentiable ℂ G → (∀ x ∈ A, ∀ z, ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2) = ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) → MeasureTheory.IntegrableOn (fun z => ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) Fd → ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * ∫ w in Fd, ‖G w‖ ^ 2 * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  intro ι _ A v Fd G hv hA hD _ hG hinv hint z
  have hv0 : 0 < v := by linarith
  set r : ℝ := Real.sqrt (1 / (4 * v)) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 1 / (4 * v) := Real.sq_sqrt (by positivity)
  set N : EuclideanSpace ℂ ι → ℝ := fun u => ‖G u‖ ^ 2 * Real.exp (-Real.pi * ‖u‖ ^ 2) with hN
  have hN0 : ∀ u, 0 ≤ N u := fun u => by positivity
  have hGc := hG.continuous
  have hNc : Continuous N := by simp only [hN]; fun_prop
  have hdisj : ∀ y₁ y₂ : A, y₁ ≠ y₂ →
      Disjoint (y₁ +ᵥ Metric.ball z r) (y₂ +ᵥ Metric.ball z r) := by
    intro y₁ y₂ hne
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    have hpq' : (y₂ : EuclideanSpace ℂ ι) + q = (y₁ : EuclideanSpace ℂ ι) + p := hpq
    have hy : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) = q - p := by
      rw [AddSubgroup.coe_sub, sub_eq_sub_iff_add_eq_add, ← hpq', add_comm]
    have hne' : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) ≠ 0 := fun h0 =>
      hne (sub_eq_zero.mp (Subtype.ext h0))
    have h1 := hA _ (y₁ - y₂ : A).2 hne'
    rw [hy] at h1
    have h2 : ‖q - p‖ < 2 * r := by
      have hp' : dist p z < r := hp
      have hq' : dist q z < r := hq
      rw [← dist_eq_norm]
      calc dist q p ≤ dist q z + dist z p := dist_triangle _ _ _
        _ < 2 * r := by rw [dist_comm z p]; linarith
    have h3 : ‖q - p‖ ^ 2 < (2 * r) ^ 2 := by gcongr
    have h4 : (2 * r) ^ 2 = 1 / v := by rw [mul_pow, hr2]; field_simp; norm_num
    linarith
  haveI : Countable A := by
    rw [← Set.countable_univ_iff]
    refine Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun y : A => y +ᵥ Metric.ball z r) (fun a _ b _ h => hdisj a b h) ?_ ?_
    · intro y _
      exact Metric.isOpen_ball.vadd (y : EuclideanSpace ℂ ι)
    · intro y _
      exact ⟨y +ᵥ z, z, Metric.mem_ball_self hr0, rfl⟩
  have hpk : ∫ u in Metric.ball z r, N u ≤ ∫ u in Fd, N u := by
    refine integral_le_of_disjoint_translates A Fd _ hD measurableSet_ball hdisj N hN0 hNc ?_ hint
    intro y u
    have e : y +ᵥ u = u + (y : EuclideanSpace ℂ ι) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    rw [e]
    exact hinv y y.2 u
  set φ : EuclideanSpace ℂ ι → ℂ :=
    fun u => G u * Complex.exp (-(Real.pi : ℂ) * innerSL ℂ z (u - z)) with hφ
  have hφd : Differentiable ℂ φ := by
    refine hG.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
    exact (innerSL ℂ z).differentiable.comp (differentiable_id.sub_const z)
  have hφi : IntegrableOn (fun u => ‖φ u‖ ^ 2) (Metric.ball z r) :=
    GlobalTheory.integrableOn_norm_pow_ball volume hφd.continuous.continuousOn 2
  have hsub := GlobalTheory.norm_pow_le_factorial_div_mul_integral_ball hr0 hφd.differentiableOn 2 hφi
  rw [finrank_euclideanSpace] at hsub
  have hφz : φ z = G z := by simp [hφ]
  rw [hφz] at hsub
  have hpt : ∀ u ∈ Metric.ball z r,
      ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * N u := by
    intro u hu
    have hu' : ‖u - z‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hu
    have h1 : ‖u - z‖ ^ 2 ≤ 1 / 4 := by
      have : ‖u - z‖ ^ 2 ≤ r ^ 2 := by gcongr
      refine this.trans ?_
      rw [hr2]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : ‖u‖ ^ 2 = ‖z‖ ^ 2 + 2 * (inner ℂ z (u - z)).re + ‖u - z‖ ^ 2 := by
      have := norm_add_sq (𝕜 := ℂ) z (u - z)
      rwa [add_sub_cancel] at this
    have h3 : Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ 3 := by
      have hpi := Real.pi_le_four
      have hpi0 := Real.pi_pos
      calc Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖u - z‖])
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have h4 : ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
        = Real.exp (Real.pi * ‖u - z‖ ^ 2) * N u := by
      simp only [hφ, hN]
      rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add,
        mul_left_comm, ← Real.exp_add, h2]
      congr 2
      simp only [innerSL_apply_apply, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
      push_cast
      ring
    rw [h4]
    exact mul_le_mul_of_nonneg_right h3 (hN0 u)
  have hNi : IntegrableOn N (Metric.ball z r) :=
    (hNc.continuousOn.integrableOn_compact (isCompact_closedBall z r)).mono_set
      Metric.ball_subset_closedBall
  have hb : (∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ 3 * ∫ u in Metric.ball z r, N u := by
    rw [← integral_mul_const, ← integral_const_mul]
    exact setIntegral_mono_on (hφi.mul_const _) (hNi.const_mul _) measurableSet_ball hpt
  have hnum := factorial_div_le (Fintype.card ι) hv hr2
  have hI0 : 0 ≤ ∫ u in Fd, N u := integral_nonneg hN0
  set c : ℝ := ((Fintype.card ι).factorial : ℝ) /
    (Real.pi ^ Fintype.card ι * r ^ (2 * Fintype.card ι)) with hc
  have hc0 : 0 ≤ c := by positivity
  calc ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ (c * ∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hsub (Real.exp_pos _).le
    _ ≤ c * (3 * ∫ u in Metric.ball z r, N u) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hc0
    _ ≤ c * (3 * ∫ u in Fd, N u) := by gcongr
    _ ≤ (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * (3 * ∫ u in Fd, N u) := by gcongr
    _ = _ := by ring

end GlobalTheory.ThetaSupBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstMulLogEqNSer
section -- merged from Development.AbelianVarietyTheory.Definitions.ThetaMetrics.InvariantDifferentialMulEqDerivX
noncomputable section

open Formalism.L2.Th1.A ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

universe u v

namespace GlobalTheory.WeierstrassFormal

section Series

open PowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

theorem w_eq : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
    + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 := (wSerSpec R W).1.2

theorem w_eq_X_pow_mul : wSer W = X ^ 3 * wU W ∧ constantCoeff (wU W) = 1 :=
  ⟨(wSerFactor R W).1, (wSerFactor R W).2.1⟩

theorem wU_eq : wU W = 1 + C W.a₁ * X * wU W + C W.a₂ * X ^ 2 * wU W + C W.a₃ * X ^ 3 * wU W ^ 2
    + C W.a₄ * X ^ 4 * wU W ^ 2 + C W.a₆ * X ^ 6 * wU W ^ 3 := by
  have h := w_eq W
  rw [(w_eq_X_pow_mul W).1] at h
  refine X_pow_mul_cancel (k := 3) ?_
  linear_combination h

theorem coeff_one_wU : coeff 1 (wU W) = W.a₁ := by
  have h : wU W = 1 + X * (C W.a₁ * wU W + X * (C W.a₂ * wU W + C W.a₃ * X * wU W ^ 2
      + C W.a₄ * X ^ 2 * wU W ^ 2 + C W.a₆ * X ^ 4 * wU W ^ 3)) := by
    linear_combination wU_eq W
  rw [h, map_add (f := _), coeff_succ_X_mul]
  simp [(w_eq_X_pow_mul W).2, coeff_one]

variable (φ : R →+* S)

end Series

section Group

open MvPowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

def formalGroup : FormalGroup R where
  toPowerSeries := fgl W
  zero_constantCoeff := (fglChord R W).2.2.2.2.1
  lin_coeff_X := (fglChord R W).2.2.2.2.2.1
  lin_coeff_Y := (fglChord R W).2.2.2.2.2.2
  assoc := by
    obtain ⟨F, hF, -⟩ := fglGroup R W
    rw [← hF]
    exact F.assoc

@[simp] theorem formalGroup_toPowerSeries : (formalGroup W).toPowerSeries = fgl W := rfl

theorem chord (i : Fin 2) : (wSer W).subst (X i : MvPowerSeries (Fin 2) R) = lam W * X i + nu W := by
  have := Fgl2.nu_eq W i
  change _ = (wSer W).subst (X i : MvPowerSeries (Fin 2) R) - _ at this
  linear_combination -this

theorem third_point : constantCoeff (uThird W) = 0 ∧
    (wSer W).subst (uThird W) = lam W * uThird W + nu W ∧
    cThree W * (X 0 + X 1 + uThird W) + cTwo W = 0 ∧
    (formalGroup W).toPowerSeries = (iSer W).subst (uThird W) :=
  ⟨(fglChord R W).2.1, (fglChord R W).2.2.1.symm, Fgl2.third_rel W 0 1 (by decide),
    (fglChord R W).2.2.2.1⟩

variable {σ : Type*}

theorem map_zsmul (φ : R →+* S) (n : ℤ) : PowerSeries.map φ (zSer W n) = zSer (W.map φ) n :=
  zSerMap R S φ W n

end Group

section Law

open MvPowerSeries

variable {R S : Type} [CommRing R] [CommRing S]

variable (W : WeierstrassCurve R)

end Law

section Points

open MvPowerSeries WeierstrassCurve WeierstrassCurve.Projective GlobalTheory.AddLaw

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) {σ : Type*}

abbrev seriesCurve (σ : Type*) : WeierstrassCurve.Projective (MvPowerSeries σ R) :=
  W.map (C : R →+* MvPowerSeries σ R)

def point (s : MvPowerSeries σ R) : Fin 3 → MvPowerSeries σ R := ![s, -1, (wSer W).subst s]

theorem equation_point {s : MvPowerSeries σ R} (hs : PowerSeries.HasSubst s) :
    (seriesCurve W σ).Equation (point W s) := by
  have h := congrArg (PowerSeries.substAlgHom (R := R) hs) (w_eq W)
  simp only [map_add (f := _), map_mul, map_pow, PowerSeries.substAlgHom_X] at h
  simp only [PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
  rw [equation_iff]
  simp only [point, fin3_def_ext, WeierstrassCurve.map]
  linear_combination h

variable {K : Type v} [Field K] (φ : MvPowerSeries σ R →+* K)

end Points

section Examples

open MvPowerSeries

variable {R : Type u} [CommRing R]

theorem formalGroup_singular (a : R) :
    (formalGroup (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve R)).toPowerSeries =
      X 0 + X 1 - C a * X 0 * X 1 := by
  set W : WeierstrassCurve R := ⟨a, 0, 0, 0, 0⟩ with hW
  have hw : ∀ i : Fin 2, (lam W * X i + nu W) * (1 - C a * X i) = X i ^ 3 := fun i => by
    have h := (WeierstrassCurve.Projective.equation_iff _).mp
      (equation_point W (s := (X i : MvPowerSeries (Fin 2) R)) (.of_constantCoeff_zero (by simp)))
    simp only [point, WeierstrassCurve.Projective.fin3_def_ext, WeierstrassCurve.map, chord W i] at h
    simp only [hW, map_zero] at h ⊢
    linear_combination h
  have hl : lam W * ((1 - C a * X 0) * (1 - C a * X 1)) =
      X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 - C a * X 0 * X 1 * (X 0 + X 1) :=
    sub_eq_zero.mp (Fgl1.sub_cancel (by
      linear_combination (1 - C a * X 1) * hw 0 - (1 - C a * X 0) * hw 1))
  have h3 : X 0 + X 1 + uThird W + C a * lam W = 0 := by
    simpa [cThree, cTwo, hW] using (third_point W).2.2.1
  have hd : Fgl1.dd W * invOfUnit (Fgl1.dd W) (-1) = 1 :=
    mul_invOfUnit _ _ (by
      have hc := (third_point W).1
      simp only [hW] at hc ⊢
      simp [Fgl1.dd, hc])
  have hd' : Fgl1.dd W = -1 + C a * uThird W := by simp [Fgl1.dd, hW]
  have key : uThird W = (X 0 + X 1 - C a * X 0 * X 1) * Fgl1.dd W := by
    rw [hd']
    linear_combination (1 - C a * X 0) * (1 - C a * X 1) * h3 - C a * hl
  change uThird W * invOfUnit (Fgl1.dd W) (-1) = _
  linear_combination invOfUnit (Fgl1.dd W) (-1) * key + (X 0 + X 1 - C a * X 0 * X 1) * hd

end Examples

end GlobalTheory.WeierstrassFormal
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.IntDLog

open PowerSeries Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime]

def intModel (g : G1 p) (h : Formalism.L2.Th1.A.IntModel g.W) :
    WeierstrassCurve (Formalism.G.unitBall ℂ_[p]) :=
  ⟨⟨g.W.a₁, h.1⟩, ⟨g.W.a₂, h.2.1⟩, ⟨g.W.a₃, h.2.2.1⟩, ⟨g.W.a₄, h.2.2.2.1⟩, ⟨g.W.a₆, h.2.2.2.2⟩⟩

theorem intModel_map (g : G1 p) (h : Formalism.L2.Th1.A.IntModel g.W) :
    (intModel g h).map (Formalism.G.unitBall ℂ_[p]).subtype = g.W := by
  ext <;> rfl

theorem subst_mul_log_eq_nSer (g : G1 p) (hOk : g.Ok) (N : ℕ) :
    (PowerSeries.subst (PowerSeries.C (N : ℂ_[p]) * g.l) g.ex : PowerSeries ℂ_[p]) =
      Formalism.L2.Th1.A.nSer g.W N := by
  have hl : g.l = Formalism.L2.Th1.A.logSer g.W :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  obtain ⟨hl0, -, -, -⟩ := Formalism.L2.Th1.A.logSpec ℂ_[p] g.W
  obtain ⟨he0, -, hLE, -, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] g.W
  induction N with
  | zero =>
    simp only [Nat.cast_zero, map_zero, zero_mul]
    rw [he]
    exact PowerSeries.subst_zero_of_constantCoeff_zero he0
  | succ N ih =>
    have hcN : PowerSeries.constantCoeff (Formalism.L2.Th1.A.nSer g.W N) = 0 :=
      Formalism.L2.Th1.A.ZSer.nSer_cc g.W N
    have hadd := Formalism.L2.KerInert.Dict.formal_addition_agree p g hOk Unit
      (PowerSeries.X : MvPowerSeries Unit ℂ_[p]) (Formalism.L2.Th1.A.nSer g.W N) (MvPowerSeries.constantCoeff_X _) hcN
    have hN : PowerSeries.subst (Formalism.L2.Th1.A.nSer g.W N) g.l = PowerSeries.C (N : ℂ_[p]) * g.l := by
      have hb : HasSubst (PowerSeries.C (N : ℂ_[p]) * g.l) :=
        HasSubst.of_constantCoeff_zero' (by rw [map_mul, hl, hl0, mul_zero])
      have hex : HasSubst g.ex := HasSubst.of_constantCoeff_zero' (by rw [he]; exact he0)
      have hLE' : PowerSeries.subst g.ex g.l = PowerSeries.X := by rw [he, hl]; exact hLE
      rw [← ih, ← PowerSeries.subst_comp_subst_apply hex hb g.l, hLE', PowerSeries.subst_X hb]
    show _ = MvPowerSeries.subst (![PowerSeries.X, Formalism.L2.Th1.A.nSer g.W N] : Fin 2 → PowerSeries ℂ_[p])
      (Formalism.L2.Th1.A.fgl g.W)
    rw [← hadd]
    show _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.l +
      PowerSeries.subst (Formalism.L2.Th1.A.nSer g.W N) g.l) g.ex
    rw [hN, PowerSeries.X_subst]
    congr 1
    push_cast
    rw [map_add (f := _), map_one]
    ring

theorem int_dlog : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → (∀ (f : PowerSeries ℂ_[p]), (∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) → ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n (PowerSeries.subst g.ex f : PowerSeries ℂ_[p])‖ ≤ 1) ∧ (PowerSeries.subst g.l g.ex : PowerSeries ℂ_[p]) = PowerSeries.X ∧ ∀ N : ℕ, ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst (PowerSeries.C (N : ℂ_[p]) * g.l) g.ex : PowerSeries ℂ_[p])‖ ≤ 1 := by
  intro p _ g hOk
  have hl : g.l = Formalism.L2.Th1.A.logSer g.W :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  have hM := Formalism.L2.KerInert.Dict.intModel_of_ok hOk
  obtain ⟨-, -, -, hEL, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] g.W
  refine ⟨?_, ?_, ?_⟩
  · intro f hf n
    have hJ := (Formalism.L2.Th1.A.jetMem ℂ_[p] g.W (Formalism.G.unitBall ℂ_[p]) hM.1 hM.2.1 hM.2.2.1
      hM.2.2.2.1 hM.2.2.2.2).2.1 f hf n
    rw [he]
    exact hJ
  · rw [hl, he]
    exact hEL
  · intro N n
    rw [subst_mul_log_eq_nSer g hOk N, ← intModel_map g hM]
    have hz := GlobalTheory.WeierstrassFormal.map_zsmul (intModel g hM) (Formalism.G.unitBall ℂ_[p]).subtype (N : ℤ)
    change PowerSeries.map _ (Formalism.L2.Th1.A.nSer _ N) = Formalism.L2.Th1.A.nSer _ N at hz
    rw [← hz, PowerSeries.coeff_map]
    exact (PowerSeries.coeff n (Formalism.L2.Th1.A.nSer (intModel g hM) N)).2

end GlobalTheory.IntDLog

end
end
