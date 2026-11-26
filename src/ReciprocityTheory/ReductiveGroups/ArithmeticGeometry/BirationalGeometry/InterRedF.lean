module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem maDens_congr_fderiv {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ i, fderiv ℝ (φ i) =ᶠ[𝓝 z] fderiv ℝ (ψ i)) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have h2 : ∀ i, fderiv ℝ (fderiv ℝ (φ i)) z = fderiv ℝ (fderiv ℝ (ψ i)) z :=
    fun i => (h i).fderiv_eq
  unfold ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.hessC
  simp only [h2]

theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := by
  unfold IsSmoothHerm at *
  exact hA.mul hB

theorem isSectionOn_one {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι} (hB : B.a = 0) :
    IsSectionOn P B 1 := by
  refine ⟨0, fun k => by simp [hB], ?_, ?_⟩
  · intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  · exact fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)

def oneLine : HermLine ι := HermLine.ofWeight (fun _ => 1) (fun _ _ _ => rfl)

theorem logNorm_oneLine (z : (Σ k, ι k) → ℂ) : logNorm (oneLine (ι := ι)) 1 z = 1 := by
  simp [logNorm, oneLine, HermLine.ofWeight, Real.exp_neg]

theorem isSmoothHerm_oneLine : IsSmoothHerm (oneLine (ι := ι)) := by
  simp only [IsSmoothHerm, oneLine, HermLine.ofWeight]
  exact contDiffOn_const

def HermLine.sqMetric (b : K → ℕ) : HermLine ι where
  a k := b k
  h z := ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ b k
  pos z hz := Finset.prod_pos fun k _ => by
    obtain ⟨i, hi⟩ := hz k
    refine pow_pos (Real.sqrt_pos.mpr ?_) _
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i))
  smul c z hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : ∑ i, ‖c k * z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
      simp [mul_pow, Finset.mul_sum]
    simp only
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _), mul_pow, zpow_natCast]

theorem isSmoothHerm_sqMetric (b : K → ℕ) : IsSmoothHerm (HermLine.sqMetric (ι := ι) b) := by
  unfold IsSmoothHerm
  have hs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι k) → ℂ => ∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
    intro k
    apply ContDiff.sum
    intro i _
    exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))
  show ContDiffOn ℝ _ (fun z : (Σ k, ι k) → ℂ => ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ b k) _
  apply contDiffOn_prod
  intro k _
  apply ContDiffOn.pow
  apply ContDiffOn.sqrt (hs k).contDiffOn
  intro z hz
  obtain ⟨i, hi⟩ := hz k
  have hpos : 0 < ‖z ⟨k, i⟩‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  exact (lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ i))).ne'

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem germ_of_eqOn (R : AnLogRes P J e) {Q Q' : LocPot R.X}
    (h : ∀ x, ∀ y ∈ R.U x, Q.φ x y = Q'.φ x y) (j : Fin R.A.n) (y : Fin e → ℂ)
    (hy : y ∈ (R.A.chart j).target) :
    (fun y' => Q.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => Q'.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y') := by
  have hc : ContinuousAt (R.A.chart j).symm y := (R.A.chart j).continuousAt_symm hy
  have hU : R.U ((R.A.chart j).symm y) ∈ 𝓝 ((R.A.chart j).symm y) :=
    (R.isOpen_U _).mem_nhds (R.mem_U _)
  filter_upwards [hc hU] with y' hy'
  exact h _ _ hy'

theorem locDens_congr_of_eqOn (R : AnLogRes P J e) {Φ Φ' : Fin e → LocPot R.X}
    (h : ∀ i x, ∀ y ∈ R.U x, (Φ i).φ x y = (Φ' i).φ x y) :
    ∀ j, ∀ y ∈ (R.A.chart j).target, locDens R.A Φ j y = locDens R.A Φ' j y := by
  intro j y hy
  unfold locDens
  apply maDens_congr_fderiv
  intro i
  exact (germ_of_eqOn R (h i) j y hy).fderiv

theorem potOf_cons {n : ℕ} (R : AnLogRes P J e) (C : HermLine ι) (L : Fin n → HermLine ι) :
    (fun j => potOf R ((Fin.cons C L : Fin (n + 1) → HermLine ι) j)) =
      Fin.cons (potOf R C) (fun j => potOf R (L j)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
  · simp only [Fin.cons_succ]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

theorem ptsIntegral_one_eq_mInt (hE : ResExistsStatement) (hB : ResBridgeStatement) {e : ℕ}
    (R : AnLogRes P J e) {L : Fin e → HermLine ι} (hP : IsArithVar P (e + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (pot L) (fun _ => 1) = mInt R.A (fun j => potOf R (L j)) (fun _ => 1) := by
  have h1 : (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) = logNorm oneLine 1 :=
    funext fun z => (logNorm_oneLine z).symm
  rw [h1, ptsIntegral_eq_mInt' hE hB R hP hL isSmoothHerm_oneLine (isSectionOn_one hP.2.1.1 rfl)]
  exact mInt_congr _ (fun _ _ _ => rfl) fun x => logNorm_oneLine _

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

def projCoord {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {e n : ℕ} (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) :
    Fin n → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeM
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)

theorem ram_null' (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_U x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r,
      Ψ (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu).1.2 Ψ
    rw [hμeq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_brQ R Ψ _ j ((R.A.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.A.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat R Ψ hP hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_brQ_chart R Ψ (j := j) ((R.A.chart j).map_target hwt) hk hw0
    rw [(R.A.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) w :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem volume_projection_zeroSet_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0 with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (R.mem x0 x0 (R.mem_U x0))
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (R.lift x0 x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin e := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (R.lift x0 x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O,
        Ψ' (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu.1).2 Ψ'
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) O := by
      intro u hu
      have := analyticAt_brQ R Ψ' _ j ((R.A.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.A.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (brQ R Ψ' ∘ (R.A.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, brQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu.1).2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m)
          (0 : (Fin e → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact not_flat R Ψ' hP hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO
  · rintro w ⟨⟨hwt, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hwb).2 Ψ
    have := congrFun hμeq 0
    rw [Pi.smul_apply, smul_eq_mul] at this
    have hw0' : Ψ (segre (R.lift ((R.A.chart j).symm w) ((R.A.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hμ

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
