module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.DifferentiableAtAffCoord
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights.LowerBoundFree (torusSmul)
open ReciprocityTheory.AnForm

namespace RootFieldNumerics.Levi

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem tangent_decomp (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, γ t' ∈ mcPts (mCoordIdeal y))
    (himm : ∀ u c, fderiv ℂ γ t u = torusSmul c (γ t) → u = 0) (v : (Σ k, J k) → ℂ)
    (hv : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) v) :
    ∃ (u : Fin e → ℂ) (c : K → ℂ), v = fderiv ℂ γ t u + torusSmul c (γ t) := by
  classical
  have hz := hpts.self_of_nhds
  have hdim := finrank_tanSub_pC_le Ω y _ hP hsm hz
  have hzI : ∀ f ∈ pC (mCoordIdeal y), eval (γ t) f = 0 := by
    have h := hz
    rw [mcPts_eq_pC] at h
    exact h.2
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  have hcone : ∀ x, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) x →
      x ∈ tanSub (pC (mCoordIdeal y)) (γ t) := by
    intro x hx f hf
    have hle : pC (mCoordIdeal y) ≤ tanIdeal (γ t) x := by
      rw [pC, Ideal.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨hz.2 g hg, hx g hg⟩
    exact (hle hf).2
  let L₁ : (Fin e → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ := (fderiv ℂ γ t).toLinearMap
  let L₂ : (K → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ :=
    { toFun := fun c => torusSmul c (γ t)
      map_add' := fun c c' => by funext q; simp only [torusSmul, Pi.add_apply]; ring
      map_smul' := fun r c => by
        funext q; simp only [torusSmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let L := L₁.coprod L₂
  have hL : ∀ u c, L (u, c) = fderiv ℂ γ t u + torusSmul c (γ t) := fun _ _ => rfl
  have hrange : LinearMap.range L ≤ tanSub (pC (mCoordIdeal y)) (γ t) := by
    rintro _ ⟨⟨u, c⟩, rfl⟩
    rw [hL]
    refine Submodule.add_mem _ (hcone _ ?_) fun f hf => (le_tanIdeal_torusSmul hPh hzI c hf).2
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.G1.isConeTangent_of_sheet le_rfl hγ hpts u
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨u, c⟩ h
    rw [hL] at h
    have hu : u = 0 := himm u (fun k => -c k) (by
      funext q
      have h1 := congrFun h q
      simp only [torusSmul, Pi.add_apply, Pi.zero_apply] at h1 ⊢
      linear_combination h1)
    subst hu
    have h2 : torusSmul c (γ t) = 0 := by simpa using h
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := hz.1 k
      have h3 : c k * γ t ⟨k, i⟩ = 0 := congrFun h2 ⟨k, i⟩
      exact (mul_eq_zero.mp h3).resolve_right hi
    rw [hc]
    rfl
  have hfr : Module.finrank ℂ (LinearMap.range L) = e + Fintype.card K := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have heq := Submodule.eq_of_le_of_finrank_le hrange (by rw [hfr]; exact hdim)
  have hvr : v ∈ LinearMap.range L := heq ▸ hcone v hv
  obtain ⟨⟨u, c⟩, huc⟩ := hvr
  exact ⟨u, c, huc.symm⟩

theorem differentiableAt_affCoord (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    DifferentiableAt ℂ (affCoord p) z := by
  refine differentiableAt_pi.2 fun q => ?_
  have h1 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v q) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) q).analyticAt z
  have h2 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v ⟨q.1, p q.1⟩) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨q.1, p q.1⟩).analyticAt z
  exact (h1.div h2 (hp q.1)).differentiableAt

theorem affCoord_torus (p : (k : K) → J k) (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    affCoord p (torusSmul c z) = affCoord p z := by
  funext q
  simp only [affCoord, torusSmul]
  exact mul_div_mul_left _ _ (hc q.1)

theorem fderiv_affCoord_torus (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) (b : K → ℂ) :
    fderiv ℂ (affCoord p) z (torusSmul b z) = 0 := by
  have h1 : HasDerivAt (fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) (torusSmul b z) 0 := by
    refine hasDerivAt_pi.2 fun q => ?_
    have := (((hasDerivAt_id (0 : ℂ)).mul_const (b q.1)).cexp).mul_const (z q)
    simpa [torusSmul] using this
  have h0 : torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z = z := by
    funext q; simp [torusSmul]
  have h2 : HasFDerivAt (affCoord p) (fderiv ℂ (affCoord p) z)
      (torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z) := by
    rw [h0]; exact (differentiableAt_affCoord p z hp).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℂ) h1
  have h4 : (affCoord p ∘ fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) = fun _ => affCoord p z := by
    funext s
    exact affCoord_torus p _ (fun k => Complex.exp_ne_zero _) z
  rw [h4] at h3
  exact h3.unique (hasDerivAt_const _ _)

theorem levi_torus {e : ℕ} (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, ∀ k, ∃ i, γ t' ⟨k, i⟩ ≠ 0) (hφ : ContDiffAt ℝ 2 φ (γ t)) (u : Fin e → ℂ) (b : K → ℂ) :
    levi φ (γ t) (fderiv ℂ γ t u + torusSmul b (γ t)) = levi (φ ∘ γ) t u := by
  let ℓ : (Unit → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj ()
  let lin : (Unit → ℂ) → Fin e → ℂ := fun s => t + ℓ s • u
  have hlin : HasFDerivAt lin (ℓ.smulRight u) 0 := by
    have := (ℓ.smulRight u).hasFDerivAt (x := 0)
    exact this.const_add t
  have hlinA : AnalyticAt ℂ lin 0 := analyticAt_const.add ((ℓ.smulRight u).analyticAt 0)
  have hl0 : lin 0 = t := by simp [lin]
  have hγ' : AnalyticAt ℂ γ (lin 0) := by rw [hl0]; exact hγ
  let Γ : (Unit → ℂ) → (Σ k, J k) → ℂ := fun s => torusSmul (fun k => Complex.exp (ℓ s * b k)) (γ (lin s))
  have hΓ0 : Γ 0 = γ t := by
    funext q; simp [Γ, torusSmul, hl0]
  have hγl : AnalyticAt ℂ (γ ∘ lin) 0 := hγ'.comp hlinA
  have hΓA : AnalyticAt ℂ Γ 0 := by
    refine analyticAt_pi_iff.2 fun q => ?_
    exact (((ℓ.analyticAt 0).mul analyticAt_const).cexp').mul (analyticAt_pi_iff.1 hγl q)
  have hΓd : fderiv ℂ Γ 0 (fun _ => 1) = fderiv ℂ γ t u + torusSmul b (γ t) := by
    have hg : HasFDerivAt (γ ∘ lin) ((fderiv ℂ γ t).comp (ℓ.smulRight u)) 0 := by
      have h1 : HasFDerivAt γ (fderiv ℂ γ t) (lin 0) := by rw [hl0]; exact hγ.differentiableAt.hasFDerivAt
      exact h1.comp 0 hlin
    funext q
    have h1 := (hasFDerivAt_pi'.1 hΓA.differentiableAt.hasFDerivAt q)
    have h2 := (((ℓ.hasFDerivAt (x := 0)).mul_const (b q.1)).cexp).mul (hasFDerivAt_pi'.1 hg q)
    have h3 := congrArg (fun L => L (fun _ => 1)) (h1.unique h2)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply] at h3
    rw [h3]
    simp [ℓ, hl0, torusSmul]
    ring
  have hφγ : ContDiffAt ℝ 2 (φ ∘ γ) t := hφ.comp t (hγ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have e1 := levi_comp (φ := φ) (τ := Γ) (z := 0) (fun _ => 1) hΓA (by rw [hΓ0]; exact hφ)
  rw [hΓ0, hΓd] at e1
  have e2 := levi_comp (φ := φ ∘ γ) (τ := lin) (z := 0) (fun _ => 1) hlinA (by rw [hl0]; exact hφγ)
  rw [hl0, hlin.fderiv] at e2
  have e3 : (ℓ.smulRight u) (fun _ => 1) = u := by simp [ℓ]
  rw [e3] at e2
  rw [← e1, ← e2]
  let G : (Unit → ℂ) → ℂ := fun s => ∑ k, (d k : ℂ) * (ℓ s * b k)
  have hG : AnalyticAt ℂ G 0 :=
    Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ((ℓ.analyticAt 0).mul analyticAt_const)
  have hev : φ ∘ Γ =ᶠ[𝓝 0] fun s => ((φ ∘ γ) ∘ lin) s + 1 * (G s).re := by
    have ht : Tendsto lin (𝓝 0) (𝓝 t) := by rw [← hl0]; exact hlinA.continuousAt
    filter_upwards [ht.eventually hpts] with s hs
    simp only [Function.comp_apply, Γ]
    rw [hhom _ _ (fun k => Complex.exp_ne_zero _) hs, add_comm, one_mul]
    congr 1
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.norm_exp, Real.log_exp]
  have hc1 : ContDiffAt ℝ 2 ((φ ∘ γ) ∘ lin) 0 :=
    ContDiffAt.comp 0 (by rw [hl0]; exact hφγ) (hlinA.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hc2 : ContDiffAt ℝ 2 (fun s => (G s).re) 0 :=
    Complex.reCLM.contDiff.contDiffAt.comp 0 (hG.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hG]
  simp

theorem levi_nonneg (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y) {B : Ideal (MRing J)} (hB : B = ⊤)
    (R : AnLogRes (mCoordIdeal y) B e) (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (hφ : ∀ z : (Σ k, J k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 φ z)
    (hpsh : ∀ x j, x ∈ (R.A.chart j).source → ∀ u,
      0 ≤ levi (fun t => φ (R.lift x ((R.A.chart j).symm t))) (R.A.chart j x) u)
    (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal y)) (w : (Σ k, J k) → ℂ)
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) z w) : 0 ≤ leviForm φ z w := by
  classical
  have hno : ∀ z : (Σ k, J k) → ℂ, z ∉ mcPts B := fun z hz => by
    subst hB
    simpa using hz.2 1 Submodule.mem_top
  obtain ⟨x, c, hc, hx⟩ := R.surj z hz (hno z)
  obtain ⟨j, hj⟩ := R.A.cover x
  let γ₀ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => R.lift x ((R.A.chart j).symm t)
  let γ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => torusSmul (fun k => (c k)⁻¹) (γ₀ t)
  have hci : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have hsx : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmemO : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsx]; exact R.mem_U x⟩
  have hO := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hmemO
  have hγ₀A : AnalyticAt ℂ γ₀ (R.A.chart j x) := analyticAt_pi_iff.2 fun q => R.holo x q j _ hmemO
  have hγA : AnalyticAt ℂ γ (R.A.chart j x) :=
    analyticAt_pi_iff.2 fun q => analyticAt_const.mul (analyticAt_pi_iff.1 hγ₀A q)
  have hγz : γ (R.A.chart j x) = z := by
    funext q
    simp only [γ, γ₀, torusSmul, hsx, hx]
    rw [← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have h0pts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ₀ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hO] with t ht using R.mem x _ ht.2
  have hpts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [h0pts] with t ht
    exact mcPts_smul hP.2.1.2.1 _ hci ht
  choose p hp using hz.1
  have himm : ∀ u b, fderiv ℂ γ (R.A.chart j x) u = torusSmul b (γ (R.A.chart j x)) → u = 0 := by
    intro u b hub
    have hp' : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0 := fun k => by
      rw [hx]; exact mul_ne_zero (hc k) (hp k)
    have hk := R.immersion x (hno _) p hp' j hj
    have hfun : (fun t => affCoord p (R.lift x ((R.A.chart j).symm t))) = affCoord p ∘ γ := by
      funext t
      exact (affCoord_torus p _ hci _).symm
    rw [hfun, fderiv_comp _ (by rw [hγz]; exact differentiableAt_affCoord p z hp) hγA.differentiableAt] at hk
    have : u ∈ (⊥ : Submodule ℂ (Fin e → ℂ)) := by
      rw [← hk]
      show fderiv ℂ (affCoord p) (γ (R.A.chart j x)) (fderiv ℂ γ (R.A.chart j x) u) = 0
      rw [hub, hγz]
      exact fderiv_affCoord_torus p z hp b
    exact this
  obtain ⟨u, b, hub⟩ := tangent_decomp Ω y e hP hsm γ _ hγA hpts himm w (by rw [hγz]; exact hw)
  have h1 := levi_torus φ d hhom γ _ hγA (hpts.mono fun t ht => ht.1) (by rw [hγz]; exact hφ z hz.1) u b
  rw [← hub, hγz] at h1
  show 0 ≤ levi φ z w
  rw [h1]
  have hev : φ ∘ γ =ᶠ[𝓝 (R.A.chart j x)] fun t => φ (γ₀ t) +
      1 * ((fun _ : Fin e → ℂ => ((∑ k, d k * Real.log ‖(c k)⁻¹‖ : ℝ) : ℂ)) t).re := by
    filter_upwards [h0pts] with t ht
    simp only [Function.comp_apply, γ]
    rw [hhom _ _ hci ht.1, Complex.ofReal_re, one_mul, add_comm]
  have hc1 : ContDiffAt ℝ 2 (fun t => φ (γ₀ t)) (R.A.chart j x) :=
    (hφ _ h0pts.self_of_nhds.1).comp _ (hγ₀A.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 contDiffAt_const, levi_re_analytic analyticAt_const]
  simpa using hpsh x j hj u

end RootFieldNumerics.Levi
end
end

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.LowerBoundFree (torusSmul)

namespace RootFieldNumerics.Levi

theorem telescope (g : ℕ → ℝ) (k n : ℕ) (h : k ≤ n) :
    ∑ i ∈ Finset.range n, (if k ≤ i then g i - g (i + 1) else 0) = g k - g n := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [sub_self]
    refine Finset.sum_eq_zero fun i hi => if_neg ?_
    have := Finset.mem_range.1 hi
    omega
  | succ n hn ih => rw [Finset.sum_range_succ, ih, if_pos hn]; ring

private theorem sum_gap_of_le_eq {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (ψ : Ψ) (j : Fin N) :
    ∑ k : Fin N, (if j ≤ k then PB.gap lam (ψ, k) else 0) = lam (ψ, j) := by
  set g : ℕ → ℝ := fun i => if h : i < N then lam (ψ, ⟨i, h⟩) else 0 with hgdef
  have hg : ∀ k : Fin N, PB.gap lam (ψ, k) = g k - g (k + 1) := by
    intro k
    simp only [PB.gap, PB.gapX, map_sub, eval_X, hgdef, dif_pos k.2]
    split_ifs with h
    · simp
    · simp
  calc ∑ k : Fin N, (if j ≤ k then PB.gap lam (ψ, k) else 0)
      = ∑ k : Fin N, (fun i : ℕ => if (j : ℕ) ≤ i then g i - g (i + 1) else 0) k := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [Fin.le_iff_val_le_val, hg]
    _ = ∑ i ∈ Finset.range N, (if (j : ℕ) ≤ i then g i - g (i + 1) else 0) :=
        Fin.sum_univ_eq_sum_range (fun i : ℕ => if (j : ℕ) ≤ i then g i - g (i + 1) else 0) N
    _ = g j - g N := telescope g j N j.2.le
    _ = lam (ψ, j) := by simp [hgdef]

theorem sum_gap_mul {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam f : Ψ × Fin N → ℝ) :
    ∑ p, PB.gap lam p * ∑ k ∈ Finset.Iic p.2, f (p.1, k) = ∑ p, lam p * f p := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ψ _
  have hI : ∀ k : Fin N, ∑ j ∈ Finset.Iic k, f (ψ, j) = ∑ j : Fin N, if j ≤ k then f (ψ, j) else 0 := by
    intro k
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext j
      simp
    · intro j _
      rfl
  simp only [hI, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← sum_gap_of_le_eq lam ψ j, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_torus (L : HermLine ι) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (L.h (torusSmul c z)) = ∑ k, (L.a k : ℝ) * Real.log ‖c k‖ + Real.log (L.h z) := by
  have hsm : L.h (torusSmul c z) = (∏ k, ‖c k‖ ^ L.a k) * L.h z := L.smul c z hc
  have hpos : 0 < L.h z := L.pos z hz
  have hprod : ∀ k ∈ (Finset.univ : Finset K), ‖c k‖ ^ L.a k ≠ 0 := by
    intro k _
    exact zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hprod) hpos.ne', Real.log_prod hprod]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.log_zpow]

theorem contDiffAt_log_h {L : HermLine ι} (hL : IsSmoothHerm L) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun z => Real.log (L.h z)) z := by
  have hopen : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have hset : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} =
        ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext w
      simp
    rw [hset]
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iUnion
    intro i
    exact isOpen_ne_fun (continuous_apply _) continuous_const
  have hh : ContDiffAt ℝ 2 L.h z := by
    have h1 := hL.contDiffAt (hopen.mem_nhds hz)
    exact h1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact hh.log (L.pos z hz).ne'

theorem log_line_lift {D : ℕ} {σ : Type} {S : PB.AnSys D σ} {P : Ideal (MRing ι)} (Re : PB.Realis S P) (a : σ) (t : ℝ)
    (ht : 0 < t) (ht' : t ≤ S.t₀) (x y : Re.R.X) (hy : y ∈ Re.R.U x) :
    Real.log ((Re.line a t).h (Re.R.lift x y)) = Real.log ((Re.ref a).h (Re.R.lift x y)) + S.phT a t (Re.π y) := by
  obtain ⟨c, hc, h⟩ := Re.R.compat x y y ⟨hy, Re.R.mem_U y⟩
  have hz := (Re.R.mem y y (Re.R.mem_U y)).1
  change Re.R.lift x y = torusSmul c _ at h
  rw [h, log_h_torus _ c _ hc hz, log_h_torus _ c _ hc hz, Re.line_eq a t ht ht', Re.line_deg]
  ring

theorem levi_chart_nonneg {D : ℕ} {σ : Type} [Fintype σ] {S : PB.AnSys D σ} {P : Ideal (MRing ι)} (Re : PB.Realis S P)
    (t : ℝ) (ht : 0 < t) (ht' : t ≤ S.t₀) (c : σ → ℝ) (hpsh : IsPsh S.A (PB.sumPot c fun a => S.potT a t))
    (x : Re.R.X) (F : Re.R.X → ℝ)
    (hF : ∀ y ∈ Re.R.U x, F y = ∑ a, c a * (Real.log ((Re.ref a).h (Re.R.lift x y)) + S.phT a t (Re.π y)))
    (j : Fin Re.R.A.n) (hj : x ∈ (Re.R.A.chart j).source) (u : Fin D → ℂ) :
    0 ≤ levi (fun v => F ((Re.R.A.chart j).symm v)) (Re.R.A.chart j x) u := by
  set χ := Re.R.A.chart j with hχ
  have hv0 : χ x ∈ χ.target := χ.map_source hj
  have hχx : χ.symm (χ x) = x := χ.left_inv hj
  obtain ⟨k, hk⟩ := S.A.cover (Re.π x)
  set ψ := S.A.chart k with hψ
  set Φ : S.X → ℝ := (PB.sumPot c fun a => S.potT a t).φ (Re.π x) with hΦd
  have hΦ : ∀ w, Φ w = ∑ a, c a * ((S.th a).φ (Re.π x) w + S.phT a t w) := fun w => rfl
  set τ : (Fin D → ℂ) → (Fin D → ℂ) := fun v => ψ (Re.π (χ.symm v)) with hτd
  have hτv0 : τ (χ x) = ψ (Re.π x) := by simp only [hτd, hχx]
  have hτ : AnalyticAt ℂ τ (χ x) := by
    apply Re.holo.2 j k
    refine ⟨hv0, ?_⟩
    show Re.π (χ.symm (χ x)) ∈ ψ.source
    rw [hχx]
    exact hk
  have hψx : ψ (Re.π x) ∈ ψ.target := ψ.map_source hk
  have hψxl : ψ.symm (ψ (Re.π x)) = Re.π x := ψ.left_inv hk
  have hΦsm : ContDiffAt ℝ 2 (Φ ∘ ψ.symm) (ψ (Re.π x)) := by
    have hfun : Φ ∘ ψ.symm = fun v => ∑ a, c a * ((S.th a).φ (Re.π x) (ψ.symm v) + S.phT a t (ψ.symm v)) := by
      funext v
      exact hΦ _
    rw [hfun]
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.add
    · have h1 := (S.sing a).1.1 (Re.π x) k
      have hmem : ψ.target ∩ ψ.symm ⁻¹' (S.th a).U (Re.π x) ∈ 𝓝 (ψ (Re.π x)) := by
        apply (ψ.isOpen_inter_preimage_symm ((S.th a).isOpen_U _)).mem_nhds
        refine ⟨hψx, ?_⟩
        rw [Set.mem_preimage, hψxl]
        exact (S.th a).mem_U _
      exact (h1.contDiffAt hmem).of_le (WithTop.coe_le_coe.mpr le_top)
    · have h1 := ((S.reg a).2.2 t ht ht').1 k
      have hmem : ψ.target ∩ ψ.symm ⁻¹' Set.univ ∈ 𝓝 (ψ (Re.π x)) := by
        rw [Set.preimage_univ, Set.inter_univ]
        exact ψ.open_target.mem_nhds hψx
      exact (h1.contDiffAt hmem).of_le (WithTop.coe_le_coe.mpr le_top)
  choose V hVo hxV G hG hGeq using fun a => Re.ref_pot a x (Set.mem_univ _)
  set Gs : Re.R.X → ℂ := fun y => ∑ a, (c a : ℂ) * G a y with hGsum
  have hGsan : AnalyticAt ℂ (Gs ∘ χ.symm) (χ x) := by
    have hfun : Gs ∘ χ.symm = fun v => ∑ a, (c a : ℂ) * (G a ∘ χ.symm) v := by
      funext v
      rfl
    have hfun2 : (fun v => ∑ a, (c a : ℂ) * (G a ∘ χ.symm) v) =
        ∑ a, (fun v => (c a : ℂ) * (G a ∘ χ.symm) v) := by
      funext v
      simp [Finset.sum_apply]
    rw [hfun, hfun2]
    apply Finset.analyticAt_sum
    intro a _
    apply analyticAt_const.mul
    apply hG a j
    refine ⟨hv0, ?_⟩
    show χ.symm (χ x) ∈ V a
    rw [hχx]
    exact hxV a
  have hcont : ContinuousAt χ.symm (χ x) := χ.continuousAt_symm hv0
  have hev1 : ∀ᶠ v in 𝓝 (χ x), χ.symm v ∈ Re.R.U x := by
    apply hcont.preimage_mem_nhds
    rw [hχx]
    exact (Re.R.isOpen_U x).mem_nhds (Re.R.mem_U x)
  have hev2 : ∀ᶠ v in 𝓝 (χ x), ∀ a, χ.symm v ∈ V a := by
    rw [Filter.eventually_all]
    intro a
    apply hcont.preimage_mem_nhds
    rw [hχx]
    exact (hVo a).mem_nhds (hxV a)
  have hev3 : ∀ᶠ v in 𝓝 (χ x), Re.π (χ.symm v) ∈ ψ.source := by
    apply (Re.holo.1.continuousAt.comp hcont).preimage_mem_nhds
    show ψ.source ∈ 𝓝 (Re.π (χ.symm (χ x)))
    rw [hχx]
    exact ψ.open_source.mem_nhds hk
  have heq : (fun v => F (χ.symm v)) =ᶠ[𝓝 (χ x)]
      (fun v => ((Φ ∘ ψ.symm) ∘ τ) v + 1 * ((Gs ∘ χ.symm) v).re) := by
    filter_upwards [hev1, hev2, hev3] with v h1 h2 h3
    have hl : ψ.symm (ψ (Re.π (χ.symm v))) = Re.π (χ.symm v) := ψ.left_inv h3
    simp only [Function.comp_apply, hτd, hl, hΦ, hGsum, one_mul, Complex.re_sum, Complex.re_ofReal_mul]
    rw [hF _ h1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have h := hGeq a (χ.symm v) (h2 a)
    have h' : Real.log ((Re.ref a).h (Re.R.lift x (χ.symm v))) - (S.th a).φ (Re.π x) (Re.π (χ.symm v)) =
        (G a (χ.symm v)).re := h
    rw [show Real.log ((Re.ref a).h (Re.R.lift x (χ.symm v))) =
        (S.th a).φ (Re.π x) (Re.π (χ.symm v)) + (G a (χ.symm v)).re by linarith]
    ring
  have hC1 : ContDiffAt ℝ 2 ((Φ ∘ ψ.symm) ∘ τ) (χ x) := by
    apply ContDiffAt.comp (χ x) (by rw [hτv0]; exact hΦsm)
    exact hτ.contDiffAt.restrict_scalars ℝ
  have hC2 : ContDiffAt ℝ 2 (fun v => ((Gs ∘ χ.symm) v).re) (χ x) :=
    Complex.reCLM.contDiff.contDiffAt.comp (χ x) (hGsan.contDiffAt.restrict_scalars ℝ)
  have hmemP : ψ (Re.π x) ∈ ψ.target ∩ ψ.symm ⁻¹' (PB.sumPot c fun a => S.potT a t).U (Re.π x) := by
    refine ⟨hψx, ?_⟩
    rw [Set.mem_preimage, hψxl]
    exact (PB.sumPot c fun a => S.potT a t).mem_U _
  have hnn := hpsh (Re.π x) k (ψ (Re.π x)) hmemP ((fderiv ℂ τ (χ x)) u)
  rw [levi_congr heq u, levi_add_smul 1 hC1 hC2 u, levi_comp u hτ (by rw [hτv0]; exact hΦsm),
    levi_re_analytic hGsan u, hτv0]
  simpa using hnn

end RootFieldNumerics.Levi
