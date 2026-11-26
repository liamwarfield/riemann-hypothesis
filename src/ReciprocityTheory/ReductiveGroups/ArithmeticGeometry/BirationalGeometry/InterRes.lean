module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def SameOrbit (z z' : (Σ k, ι k) → ℂ) : Prop :=
  ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = fun p => c p.1 * z' p

def affCoord (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => z q / z ⟨q.1, p q.1⟩

structure AnLogRes (P J : Ideal (MRing ι)) (e : ℕ) where

  homog : IsMultiHomogIdeal J

  nondeg : ¬ J ≤ P

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  U : X → Set X
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x

  lift : X → X → (Σ k, ι k) → ℂ
  holo : ∀ x p, A.HoloOn (U x) (fun y => lift x y p)
  mem : ∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P

  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)

  surj : ∀ z ∈ mcPts P, z ∉ mcPts J → ∃ x, SameOrbit (lift x x) z

  inj : ∀ x x', lift x x ∉ mcPts J → SameOrbit (lift x x) (lift x' x') → x = x'

  immersion : ∀ x, lift x x ∉ mcPts J → ∀ p : (k : K) → ι k, (∀ k, lift x x ⟨k, p k⟩ ≠ 0) →
    ∀ j, x ∈ (A.chart j).source →
      (fderiv ℂ (fun y => affCoord p (lift x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

  snc : ∀ (f : MRing ι) (a : K → ℕ), f ∉ P → IsMultiHomog f a →
    (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 → z ∈ mcPts J) →
    ∃ (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set X),
      IsSNC A ⟨U, isOpen_U, mem_U, fun _ _ => 0⟩
        (fun x y => eval (lift x y) (map (Int.castRingHom ℂ) f)) m W

  null : ∀ j, MeasureTheory.volume
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | lift x x ∈ mcPts J}) = 0

attribute [instance] AnLogRes.top AnLogRes.compact AnLogRes.t2

def potOf {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (L : HermLine ι) : LocPot R.X where
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  φ x y := Real.log (L.h (R.lift x y))

def ResExistsStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ P →
    ∃ J' : Ideal (MRing ι), J' ≤ J ∧ IsMultiHomogIdeal J' ∧ ¬ J' ≤ P ∧ Nonempty (AnLogRes P J' e)

def ResBridgeStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    ptsIntegralAt P Ψ (pot L) (logNorm A s) =
      mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x))

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeN
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology Real

private theorem log_max_norm_le_circleAverage_of_analyticOnNhd {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    Real.log (max ‖h 0‖ 1) ≤ Real.circleAverage (fun ζ => Real.log (max ‖h ζ‖ 1)) 0 1 := by
  have hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1 := by rw [abs_one]; exact sphere_subset_closedBall
  have hI : CircleIntegrable (fun ζ => Real.log (max ‖h ζ‖ 1)) 0 1 :=
    ContinuousOn.circleIntegrable' (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm (hh.continuousOn.mono hs)) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne'))
  rcases le_or_gt ‖h 0‖ 1 with h0 | h0
  · rw [max_eq_right h0, Real.log_one]
    have := Real.circleAverage_mono (circleIntegrable_const (0 : ℝ) 0 1) hI
      (fun x _ => Real.log_nonneg (le_max_right _ _))
    rwa [Real.circleAverage_const] at this
  · have hne : h 0 ≠ 0 := by intro e; rw [e, norm_zero] at h0; linarith
    have hh' : AnalyticOnNhd ℂ h (closedBall 0 |1|) := by rwa [abs_one]
    rw [max_eq_left h0.le]
    have hJ := AnalyticOnNhd.circleAverage_log_norm (c := 0) (R := 1) hh' hne
    have hdn := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh'
    have hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor h (closedBall 0 |1|)) u : ℝ) *
        Real.log (1 * ‖0 - u‖⁻¹) := by
      apply finsum_nonneg
      intro u
      by_cases hu : u ∈ closedBall (0 : ℂ) |1|
      · apply mul_nonneg
        · exact_mod_cast hdn u
        · rw [one_mul, zero_sub, norm_neg, Real.log_inv]
          rw [abs_one, mem_closedBall, dist_zero_right] at hu
          exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg u) hu)
      · have hz : (MeromorphicOn.divisor h (closedBall 0 |1|)) u = 0 := by
          by_contra hz
          exact hu ((MeromorphicOn.divisor h _).supportWithinDomain hz)
        rw [hz]; simp
    have hlog : CircleIntegrable (fun ζ => Real.log ‖h ζ‖) 0 1 :=
      MeromorphicOn.circleIntegrable_log_norm (fun x hx => (hh x (hs hx)).meromorphicAt)
    calc Real.log ‖h 0‖ ≤ Real.circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 := by
          rw [hJ]; linarith
      _ ≤ _ := Real.circleAverage_mono hlog hI (fun x _ => by
          by_cases hx0 : h x = 0
          · simp [hx0]
          · exact Real.log_le_log (norm_pos_iff.2 hx0) (le_max_left _ _))

theorem isPsh_logmax {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {f : (Fin D → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ReciprocityTheory.AnForm.A.IsPsh U (fun z => Real.log (max ‖f z‖ ε)) := by
  refine ⟨?_, fun z w hdisc => ?_⟩
  · exact ContinuousOn.upperSemicontinuousOn (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm hf.continuousOn) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right hε).ne'))
  set g : ℂ → ℂ := fun ζ => (ε : ℂ)⁻¹ * f (z + ζ • w) with hg
  have hga : AnalyticOnNhd ℂ g (closedBall 0 1) := by
    intro ζ hζ
    have hz : z + ζ • w ∈ U := hdisc ζ (by simpa using hζ)
    have hφ : AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have hc : AnalyticAt ℂ (fun ζ : ℂ => f (z + ζ • w)) ζ :=
      AnalyticAt.comp (g := f) (f := fun ζ : ℂ => z + ζ • w) (hf _ hz) hφ
    exact analyticAt_const.mul hc
  have hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1 := by rw [abs_one]; exact sphere_subset_closedBall
  have hI2 : CircleIntegrable (fun ζ => Real.log (max ‖g ζ‖ 1)) 0 1 :=
    ContinuousOn.circleIntegrable' (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm (hga.continuousOn.mono hs)) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne'))
  have hkey : ∀ ζ : ℂ, Real.log (max ‖f (z + ζ • w)‖ ε) = Real.log ε + Real.log (max ‖g ζ‖ 1) := by
    intro ζ
    have hnorm : ‖g ζ‖ = ‖f (z + ζ • w)‖ / ε := by
      simp only [hg, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      rw [div_eq_inv_mul]
    rw [hnorm, ← Real.log_mul hε.ne' (lt_max_of_lt_right one_pos).ne', mul_max_of_nonneg _ _ hε.le,
      show ε * (‖f (z + ζ • w)‖ / ε) = ‖f (z + ζ • w)‖ by field_simp, mul_one]
  have hfun : (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) =
      fun ζ => Real.log ε + Real.log (max ‖g ζ‖ 1) := funext hkey
  refine ⟨?_, ?_⟩
  · show CircleIntegrable (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1
    rw [hfun]
    exact (circleIntegrable_const _ _ _).add hI2
  · show Real.log (max ‖f z‖ ε) ≤ Real.circleAverage (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1
    rw [hfun, Real.circleAverage_fun_add (circleIntegrable_const _ _ _) hI2, Real.circleAverage_const]
    have h0 := hkey 0
    simp only [zero_smul, add_zero] at h0
    rw [h0]
    linarith [log_max_norm_le_circleAverage_of_analyticOnNhd hga]

theorem integrableOn_log_norm_closedBall {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {f : (Fin D → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U) {z0 : Fin D → ℂ} {t : ℝ} (ht : 0 < t)
    (hS2 : ball z0 (2 * t) ⊆ U) (hz0 : f z0 ≠ 0) :
    IntegrableOn (fun z => Real.log ‖f z‖) (closedBall z0 t) := by
  set B := closedBall z0 t with hBdef
  have hBU : B ⊆ U := fun x hx =>
    hS2 (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (by linarith)))
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBfin : volume B < ⊤ := measure_closedBall_lt_top
  have hfc : ContinuousOn f B := hf.continuousOn.mono hBU
  set c : ℝ := min ‖f z0‖ 1 with hc
  have hc0 : 0 < c := lt_min (norm_pos_iff.2 hz0) one_pos
  set ε : ℕ → ℝ := fun n => c / ((n : ℝ) + 1) with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n => div_pos hc0 (by positivity)
  have hεc : ∀ n, ε n ≤ c := fun n =>
    div_le_self hc0.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hε1 : ∀ n, ε n ≤ 1 := fun n => (hεc n).trans (min_le_right _ _)
  have hεanti : ∀ m n : ℕ, m ≤ n → ε n ≤ ε m := fun m n hmn =>
    div_le_div_of_nonneg_left hc0.le (by positivity)
      (by have := (Nat.cast_le (α := ℝ)).2 hmn; linarith)
  set φ : ℕ → (Fin D → ℂ) → ℝ := fun n x => Real.log (max ‖f x‖ (ε n)) with hφdef
  set φ1 : (Fin D → ℂ) → ℝ := fun x => Real.log (max ‖f x‖ 1) with hφ1def
  have hsub : ∀ n, IntegrableOn (φ n) B ∧ φ n z0 ≤ ⨍ x in B, φ n x := fun n =>
    ReciprocityTheory.AnForm.A.subMeanPolydisc_thm D U (φ n) z0 t hU (isPsh_logmax hU hf (hε0 n)) ht hBU
  have hφc : ∀ n, ContinuousOn (φ n) B := fun n =>
    ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right (hε0 n)).ne')
  have hφ1c : ContinuousOn φ1 B :=
    ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne')
  have hφ1i : IntegrableOn φ1 B := ContinuousOn.integrableOn_compact (isCompact_closedBall z0 t) hφ1c
  have hφz0 : ∀ n, φ n z0 = Real.log ‖f z0‖ := fun n => by
    simp only [hφdef]
    rw [max_eq_left ((hεc n).trans (min_le_left _ _))]
  have hφle : ∀ n x, φ n x ≤ φ1 x := fun n x =>
    Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hε1 n))
  have hφanti : ∀ m n : ℕ, m ≤ n → ∀ x, φ n x ≤ φ m x := fun m n hmn x =>
    Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hεanti m n hmn))
  set V := (volume B).toReal with hVdef
  have hV : 0 < V := ENNReal.toReal_pos (measure_closedBall_pos volume z0 ht).ne' hBfin.ne
  have hlow : ∀ n, V * Real.log ‖f z0‖ ≤ ∫ x in B, φ n x := by
    intro n
    have h1 : Real.log ‖f z0‖ ≤ V⁻¹ * ∫ x in B, φ n x := by
      have h2 := (hsub n).2
      rw [setAverage_eq, smul_eq_mul] at h2
      exact (hφz0 n).symm.le.trans h2
    have h3 := mul_le_mul_of_nonneg_left h1 hV.le
    rwa [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul] at h3
  set G : (Fin D → ℂ) → ℝ := fun x => φ1 x - Real.log ‖f x‖ with hGdef
  have hG0 : ∀ x, 0 ≤ G x := by
    intro x
    simp only [hGdef, hφ1def, sub_nonneg]
    by_cases hx : f x = 0
    · simp [hx]
    · exact Real.log_le_log (norm_pos_iff.2 hx) (le_max_left _ _)
  have hpt : ∀ x, ENNReal.ofReal (G x) ≤ ⨆ n, ENNReal.ofReal (φ1 x - φ n x) := by
    intro x
    by_cases hx : f x = 0
    · have : G x = 0 := by simp [hGdef, hφ1def, hx]
      rw [this, ENNReal.ofReal_zero]; exact zero_le
    · have hpos : 0 < ‖f x‖ := norm_pos_iff.2 hx
      obtain ⟨n, hn⟩ := exists_nat_gt (c / ‖f x‖)
      have hn' : ε n ≤ ‖f x‖ := by
        rw [div_lt_iff₀ hpos] at hn
        show c / ((n : ℝ) + 1) ≤ ‖f x‖
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      refine le_iSup_of_le n (le_of_eq ?_)
      congr 1
      simp only [hGdef, hφdef, max_eq_left hn']
  have hmeasn : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ1 x - φ n x)) (volume.restrict B) :=
    fun n => ((hφ1c.sub (hφc n)).aemeasurable hBm).ennreal_ofReal
  have hsup : ∫⁻ x in B, ⨆ n, ENNReal.ofReal (φ1 x - φ n x) =
      ⨆ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x) :=
    lintegral_iSup' hmeasn (Filter.Eventually.of_forall fun x m n hmn =>
      ENNReal.ofReal_le_ofReal (sub_le_sub_left (hφanti m n hmn x) _))
  have hbound : ∀ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x) ≤
      ENNReal.ofReal ((∫ x in B, φ1 x) - V * Real.log ‖f z0‖) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => φ1 x - φ n x) (hφ1i.sub (hsub n).1)
      (Filter.Eventually.of_forall fun x => sub_nonneg.2 (hφle n x))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub hφ1i (hsub n).1]
    linarith [hlow n]
  have hfin : ∫⁻ x in B, ENNReal.ofReal (G x) < ⊤ :=
    lt_of_le_of_lt ((lintegral_mono hpt).trans (hsup.le.trans (iSup_le hbound))) ENNReal.ofReal_lt_top
  have hlogm : AEStronglyMeasurable (fun x => Real.log ‖f x‖) (volume.restrict B) :=
    (Real.measurable_log.comp_aemeasurable ((ContinuousOn.norm hfc).aemeasurable hBm)).aestronglyMeasurable
  have hGi : IntegrableOn G B :=
    ⟨(hφ1c.aestronglyMeasurable hBm).sub hlogm,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)).2 hfin⟩
  refine (hφ1i.sub hGi).congr_fun (fun x _ => ?_) hBm
  simp [hGdef]

theorem logAbsLocInt' (D : ℕ) (U : Set (Fin D → ℂ)) (f : (Fin D → ℂ) → ℂ) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) : LocallyIntegrableOn (fun z => Real.log ‖f z‖) U volume := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
  by_cases h : ∃ z0 ∈ ball z (r / 5), f z0 ≠ 0
  · obtain ⟨z0, hz0, hfz0⟩ := h
    refine ⟨closedBall z0 (2 * (r / 5)), ?_,
      integrableOn_log_norm_closedBall hU hf (by positivity) ?_ hfz0⟩
    · apply mem_nhdsWithin_of_mem_nhds
      refine Filter.mem_of_superset (ball_mem_nhds z (by positivity : (0 : ℝ) < r / 5)) ?_
      intro x hx
      rw [mem_closedBall]
      rw [mem_ball] at hx hz0
      calc dist x z0 ≤ dist x z + dist z z0 := dist_triangle _ _ _
        _ ≤ 2 * (r / 5) := by rw [dist_comm z z0]; linarith
    · intro x hx
      apply hball
      rw [mem_ball] at hx hz0 ⊢
      calc dist x z ≤ dist x z0 + dist z0 z := dist_triangle _ _ _
        _ < r := by linarith
  · push_neg at h
    refine ⟨ball z (r / 5), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (by positivity)), ?_⟩
    exact IntegrableOn.congr_fun integrableOn_zero (fun x hx => by simp [h x hx]) measurableSet_ball

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

def secSet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (B : Set (Fin e → ℂ)) : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) :=
  {G | (∀ y ∉ B, G y = 0) ∧ DifferentiableOn ℂ G B ∧ ∀ y ∈ B, G y ∈ fibre P Ψ y}

theorem coincide_null (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {c : Fin e → ℂ} {r : ℝ}
    {G G' : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} (hG : G ∈ secSet P Ψ (ball c r))
    (hG' : G' ∈ secSet P Ψ (ball c r)) (hne : G ≠ G') :
    volume {y | y ∈ ball c r ∧ G y = G' y} = 0 := by
  obtain ⟨y0, hy0⟩ : ∃ y0, G y0 ≠ G' y0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  have hy0b : y0 ∈ ball c r := by
    by_contra hb
    exact hy0 (by rw [hG.1 y0 hb, hG'.1 y0 hb])
  obtain ⟨i, hi⟩ : ∃ i, G y0 i ≠ G' y0 i := by
    by_contra hcon
    push_neg at hcon
    exact hy0 (funext hcon)
  set f : (Fin e → ℂ) → ℂ := fun y => G y i - G' y i with hf
  have hdiff : DifferentiableOn ℂ f (ball c r) := by
    have h1 : DifferentiableOn ℂ (fun y => G y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG.2.1 y hy)) i
    have h2 : DifferentiableOn ℂ (fun y => G' y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG'.2.1 y hy)) i
    exact h1.sub h2
  have han : AnalyticOnNhd ℂ f (ball c r) := hA e (ball c r) f isOpen_ball hdiff
  have hnull := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball (convex_ball c r).isPreconnected han
    ⟨y0, hy0b, sub_ne_zero.2 hi⟩
  refine measure_mono_null ?_ hnull
  intro y hy
  exact ⟨hy.1, by simp [f, hy.2]⟩

theorem secSet_finite (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite)
    (c : Fin e → ℂ) {r : ℝ} (hr : 0 < r) : (secSet P Ψ (ball c r)).Finite := by
  by_contra hinf
  have hS : (secSet P Ψ (ball c r)).Infinite := hinf
  have key : ∀ m : ℕ, volume {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} = 0 := by
    intro m
    obtain ⟨F, hFS, hFc⟩ := hS.exists_subset_card_eq m
    have hnull : volume (⋃ G ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)), ⋃ G' ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)),
        {y | G ≠ G' ∧ y ∈ ball c r ∧ G y = G' y}) = 0 := by
      refine (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G hG =>
        (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA (hFS hG) (hFS hG') h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    refine measure_mono_null (fun y hy => ?_) hnull
    obtain ⟨hyb, hlt⟩ := hy
    by_contra hnot
    have hinj : Set.InjOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) := fun G hG G' hG' heq => by
      by_contra hne
      exact hnot (Set.mem_iUnion₂.2 ⟨G, hG, Set.mem_iUnion₂.2 ⟨G', hG', ⟨hne, hyb, heq⟩⟩⟩)
    have hmaps : Set.MapsTo (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) (fibre P Ψ y) := fun G hG => (hFS hG).2.2 y hyb
    have hle := Set.ncard_le_ncard_of_injOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) hmaps hinj (hfin y)
    rw [Set.ncard_coe_finset, hFc] at hle
    omega
  have hcover : ball c r ⊆ ⋃ m : ℕ, {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} := fun y hy =>
    Set.mem_iUnion.2 ⟨(fibre P Ψ y).ncard + 1, hy, Nat.lt_succ_self _⟩
  have h0 : volume (ball c r) = 0 := measure_mono_null hcover (measure_iUnion_null key)
  exact (Metric.measure_ball_pos volume c hr).ne' h0

def badSet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set (Fin e → ℂ) :=
  {y | ∃ w γ γ', IsSheet P Ψ y w γ ∧ IsSheet P Ψ y w γ' ∧
    ¬ ((fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y'))}

theorem segre_differentiableAt {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : DifferentiableAt ℂ γ y) : DifferentiableAt ℂ (fun y' => segre (γ y')) y := by
  rw [differentiableAt_pi]
  intro i
  simp only [segre]
  classical
  have key : ∀ s : Finset K, DifferentiableAt ℂ (fun x => ∏ k ∈ s, γ x ⟨k, i k⟩) y := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact ((differentiableAt_pi.1 hγ) ⟨a, i a⟩).mul ih
  exact key Finset.univ

theorem mem_secSet_of_sheet {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {B : Set (Fin e → ℂ)}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : ∀ y' ∈ B, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y') :
    B.indicator (fun y' => segre (γ y')) ∈ secSet P Ψ B := by
  refine ⟨fun y hy => Set.indicator_of_notMem hy _, ?_, fun y hy => ?_⟩
  · have hd : DifferentiableOn ℂ (fun y' => segre (γ y')) B := fun y' hy' =>
      (segre_differentiableAt (h y' hy').1).differentiableWithinAt
    exact hd.congr (fun y' hy' => Set.indicator_of_mem hy' _)
  · rw [Set.indicator_of_mem hy]
    exact ⟨γ y, (h y hy).2.1, rfl, (h y hy).2.2⟩

theorem badSet_null (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite) :
    volume (badSet P Ψ) = 0 := by
  obtain ⟨Dc, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  let S : (Fin e → ℂ) → ℚ → Set (Fin e → ℂ) := fun d q =>
    ⋃ G ∈ secSet P Ψ (ball d q), ⋃ G' ∈ secSet P Ψ (ball d q), {y | G ≠ G' ∧ y ∈ ball d (q : ℝ) ∧ G y = G' y}
  have hS : ∀ d q, volume (S d q) = 0 := by
    intro d q
    by_cases hq : (0 : ℝ) < q
    · have hfinS := secSet_finite hA hfin d hq
      refine (measure_biUnion_null_iff hfinS.countable).2 fun G hG =>
        (measure_biUnion_null_iff hfinS.countable).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA hG hG' h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    · have hempty : ball d (q : ℝ) = ∅ := Metric.ball_eq_empty.2 (not_lt.1 hq)
      refine measure_mono_null ?_ measure_empty
      intro y hy
      simp only [S, Set.mem_iUnion] at hy
      obtain ⟨G, _, G', _, _, hyb, _⟩ := hy
      rw [hempty] at hyb
      exact hyb
  have hcount : volume (⋃ d ∈ Dc, ⋃ q : ℚ, S d q) = 0 :=
    (measure_biUnion_null_iff hDc).2 fun d _ => measure_iUnion_null fun q => hS d q
  refine measure_mono_null ?_ hcount
  intro y hy
  obtain ⟨w, γ, γ', ⟨hγw, hγev⟩, ⟨hγ'w, hγ'ev⟩, hne⟩ := hy
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hγev.and hγ'ev)
  obtain ⟨q, hq0, hqε⟩ : ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < ε / 2 := by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (half_pos hε)
    exact ⟨q, h1, h2⟩
  obtain ⟨d, hdD, hd⟩ := hDd.exists_mem_open isOpen_ball ⟨y, mem_ball_self hq0⟩
  have hdy : dist y d < q := by
    rw [dist_comm]
    exact hd
  have hyB : y ∈ ball d (q : ℝ) := by
    rw [mem_ball]
    exact hdy
  have hBsub : ball d (q : ℝ) ⊆ ball y ε := by
    intro y' hy'
    rw [mem_ball] at hy' ⊢
    calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
      _ < q + q := by
        rw [dist_comm d y]
        exact add_lt_add hy' hdy
      _ < ε := by linarith
  have hG : (ball d (q : ℝ)).indicator (fun y' => segre (γ y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).1)
  have hG' : (ball d (q : ℝ)).indicator (fun y' => segre (γ' y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).2)
  refine Set.mem_iUnion₂.2 ⟨d, hdD, Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨_, hG,
    Set.mem_iUnion₂.2 ⟨_, hG', ?_, hyB, ?_⟩⟩⟩⟩
  · intro heq
    apply hne
    filter_upwards [isOpen_ball.mem_nhds hyB] with y' hy'
    have h1 := congrFun heq y'
    simpa [Set.indicator_of_mem hy'] using h1
  · simp [Set.indicator_of_mem hyB, hγw, hγ'w]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter Topology

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def bsmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => c p.1 * z p

theorem eval_bsmul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (bsmul c z) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∈ s.support := support_map_subset _ _ hm
  have hblk := hs m hm'
  simp only [bsmul, mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
    rw [← hblk k, Finset.prod_pow_eq_pow_sum]
  rw [hc]
  ring

theorem logNorm_bsmul (A : HermLine ι) {s : MRing ι} {a : K → ℕ} (hA : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNorm A s (bsmul c z) = logNorm A s z := by
  unfold logNorm
  rw [eval_bsmul_of_isMultiHomog hs]
  have hh : A.h (bsmul c z) = (∏ k, ‖c k‖ ^ (a k)) * A.h z := by
    rw [show bsmul c z = fun p => c p.1 * z p from rfl, A.smul c z hc]
    simp [hA, zpow_natCast]
  rw [hh, norm_mul, norm_prod]
  simp only [norm_pow]
  rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))]

theorem prod_update_eq [DecidableEq K] (z : (Σ k, ι k) → ℂ) (i0 : (k : K) → ι k) (k : K) (i : ι k) :
    ∏ k', z ⟨k', Function.update i0 k i k'⟩ = z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k' hk' => ?_
    simp [Finset.ne_of_mem_erase hk']

theorem eq_bsmul_of_segre_eq {z z' : (Σ k, ι k) → ℂ} (i0 : (k : K) → ι k)
    (h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0) (hs : segre z = segre z') :
    (∀ k, z' ⟨k, i0 k⟩ ≠ 0) ∧ z' = bsmul (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z := by
  classical
  have hseg : ∀ i : (k : K) → ι k, ∏ k, z ⟨k, i k⟩ = ∏ k, z' ⟨k, i k⟩ := fun i => congrFun hs i
  have hP0 : ∏ k, z ⟨k, i0 k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => h0 k
  have h0' : ∀ k, z' ⟨k, i0 k⟩ ≠ 0 := by
    intro k
    have h1 : ∏ k, z' ⟨k, i0 k⟩ ≠ 0 := by rw [← hseg i0]; exact hP0
    exact Finset.prod_ne_zero_iff.1 h1 k (Finset.mem_univ _)
  refine ⟨h0', ?_⟩
  funext ⟨k, i⟩
  simp only [bsmul]
  have hA' : z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k i, ← prod_update_eq z' i0 k i]
    exact hseg _
  have hB' : z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k (i0 k), ← prod_update_eq z' i0 k (i0 k)]
    exact hseg _
  have hP' : ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => h0' k'
  rw [div_mul_eq_mul_div, eq_div_iff (h0 k)]
  apply mul_right_cancel₀ hP'
  linear_combination (-(z ⟨k, i0 k⟩)) * hA' + z ⟨k, i⟩ * hB'

end Alg

section Hess

variable {e : ℕ}

theorem fderiv_re_apply {h : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hh : DifferentiableAt ℂ h y)
    (v : Fin e → ℂ) : fderiv ℝ (fun y' => (h y').re) y v = (fderiv ℂ h y v).re := by
  have hd : HasFDerivAt (fun y' => (h y').re)
      (Complex.reCLM.comp ((fderiv ℂ h y).restrictScalars ℝ)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hh.hasFDerivAt.restrictScalars ℝ)
  rw [hd.fderiv]
  rfl

theorem hess_re {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hG : AnalyticAt ℂ G y) (v w : Fin e → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y v w = (fderiv ℂ (fderiv ℂ G) y v w).re := by
  let Φ : ((Fin e → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin e → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin e → ℂ) ℂ ℝ ℝ)
  have hΦ : ∀ L : (Fin e → ℂ) →L[ℂ] ℂ, ∀ u, Φ L u = (L u).re := fun L u => rfl
  have heq : fderiv ℝ (fun y' => (G y').re) =ᶠ[𝓝 y] fun y' => Φ (fderiv ℂ G y') := by
    filter_upwards [hG.eventually_analyticAt] with y' hy'
    ext u
    rw [fderiv_re_apply hy'.differentiableAt u, hΦ]
  have hD : HasFDerivAt (fderiv ℂ G) (fderiv ℂ (fderiv ℂ G) y) y :=
    hG.fderiv.differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun y' => Φ (fderiv ℂ G y'))
      (Φ.comp ((fderiv ℂ (fderiv ℂ G) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hD.restrictScalars ℝ)
  rw [heq.fderiv_eq, h2.fderiv]
  rfl

theorem cxHessian_add_re {φ : (Fin e → ℂ) → ℝ} {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (C : ℝ)
    (hφ : ContDiffAt ℝ 2 φ y) (hG : AnalyticAt ℂ G y) :
    cxHessian (fun y' => φ y' + (G y').re + C) y = cxHessian φ y := by
  have hre2 : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hG.contDiffAt.restrict_scalars ℝ)
  have hφev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ φ y' :=
    (hφ.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have hreev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ (fun y' => (G y').re) y' :=
    (hre2.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => φ y' + (G y').re + C) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ φ y' + fderiv ℝ (fun y' => (G y').re) y' := by
    filter_upwards [hφev, hreev] with y' h1 h2
    rw [fderiv_add_const]
    exact (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdre : DifferentiableAt ℝ (fderiv ℝ (fun y' => (G y').re)) y :=
    (hre2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsum : fderiv ℝ (fderiv ℝ (fun y' => φ y' + (G y').re + C)) y =
      fderiv ℝ (fderiv ℝ φ) y + fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y := by
    rw [heq.fderiv_eq]
    exact (hdφ.hasFDerivAt.add hdre.hasFDerivAt).fderiv
  have hH := hess_re hG
  have k1 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) (Complex.I • v) =
      - fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u v := by
    intro u v
    rw [hH, hH]
    simp [map_smul, ← mul_assoc]
  have k2 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u (Complex.I • v) =
      fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) v := by
    intro u v
    rw [hH, hH]
    simp [map_smul]
  ext i j
  simp only [cxHessian, hsum, ContinuousLinearMap.add_apply, k1, k2]
  push_cast
  ring

theorem cxHessian_congr {f g : (Fin e → ℂ) → ℝ} {y : Fin e → ℂ} (h : f =ᶠ[𝓝 y] g) :
    cxHessian f y = cxHessian g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := h.fderiv.fderiv_eq
  unfold cxHessian
  rw [h2]

end Hess

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter NumberField

section Host

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def LiesOver {F : Type*} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (sg : F →+* ℂ)
    (z : (Σ k, ι k) → ℂ) : Prop :=
  ∀ (d : K → ℕ) (g h : MRing ι) (θ : F), IsMultiHomog g d → IsMultiHomog h d →
    aeval y g = algebraMap F Ω θ * aeval y h →
    eval z (map (Int.castRingHom ℂ) g) = sg θ * eval z (map (Int.castRingHom ℂ) h)

end Host

def ArithmeticHilbertSamuelUpperBoundNumberField : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (Λ : (F →+* ℂ) → ℝ) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    IsConjInvariantH A → (∀ sg, 0 < Λ sg) → (∀ sg, Λ (ComplexEmbedding.conjugate sg) = Λ sg) →
    ∑ sg, Real.log (Λ sg) ≤ 0 →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      ∀ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ Λ sg * A.h z) →
    limsup (fun τ : ℕ =>
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ /
          ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A)

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
