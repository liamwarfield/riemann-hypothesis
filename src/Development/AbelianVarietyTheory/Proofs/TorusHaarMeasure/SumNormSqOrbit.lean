module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsCompactOfLeSumPnormSq
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

namespace CuspCompact

theorem exists_sum_exp_lt {N : ℕ} (C c : Fin N → ℝ) (hc : ∀ k, 0 < c k) (c0 : ℝ) (h0 : 0 < c0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ∑ k, C k * Real.exp (-2 * Real.pi * c k / s) < c0 := by
  have ht : Filter.Tendsto (fun s : ℝ => ∑ k, C k * Real.exp (-2 * Real.pi * c k / s))
      (𝓝[>] 0) (𝓝 (∑ k : Fin N, C k * 0)) := by
    refine tendsto_finsetSum _ fun k _ => Filter.Tendsto.const_mul _ ?_
    refine Real.tendsto_exp_atBot.comp ?_
    have hneg : -2 * Real.pi * c k < 0 := by
      have := mul_pos Real.pi_pos (hc k)
      linarith
    exact (Filter.Tendsto.const_mul_atTop_of_neg hneg (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))).congr
      fun s => (div_eq_mul_inv _ _).symm
  simp only [mul_zero, Finset.sum_const_zero] at ht
  have hev := ht.eventually (gt_mem_nhds h0)
  obtain ⟨δ, hδ, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  exact ⟨δ, hδ, fun s hs hsδ => hsub ⟨hs, hsδ⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_compact_of_le_sum_pnorm_sq :
    LineBundleFirstBoundGlobalGeneration (E := E) → MahlerCompactnessCriterion (E := E) →
    ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (c0 : ℝ), 0 < c0 →
    ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom,
      c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 →
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C := by
  intro hLa hM2 r X Xa c0 h0
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨X.dom, Set.subsingleton_of_subsingleton.isCompact, subset_rfl, fun x hx _ => ?_⟩
    refine ⟨1, X.Γ.one_mem, x, fun τ => ⟨by simp, fun a => a.elim0⟩, ?_⟩
    rwa [Subsingleton.elim (lact 1 (rmul x x)) x]
  have hpos := (hLa r X hr).2.2
  choose c hc hcw using fun k => spectralGap_holds r X Xa.L (Xa.w k) (Xa.w_van k).1
  choose C hC using fun k => cuspidalDecay_holds r X Xa.L (Xa.w k) (c k) (hc k).le (hcw k)
  obtain ⟨δ, hδ, hlt⟩ := exists_sum_exp_lt C c hc c0 h0
  obtain ⟨K, hK, hKd, hKx⟩ := hM2 r X (Real.sqrt δ) (Real.sqrt_pos.2 hδ)
  refine ⟨K, hK, hKd, fun x hx hle => hKx x hx ?_⟩
  have hs : 0 < X.firstMinimumSq x := Real.sqrt_pos.1 (hpos x hx)
  refine Real.sqrt_le_sqrt (not_lt.1 fun h => ?_)
  have h1 := hlt _ hs h
  have h2 : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤
      ∑ k, C k * Real.exp (-2 * Real.pi * c k / X.firstMinimumSq x) :=
    Finset.sum_le_sum fun k _ => hC k x hx
  linarith

end CuspCompact

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallySplit
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FiniteZeroOrbits

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cpt_origin {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : cpt X x 0 = x := by
  have : nmat X 0 = ExtFPf.oneF X := by
    funext τ a b
    simp only [nmat, ExtFPf.oneF, Matrix.one_apply]
    split_ifs with h1 h2 h3
    · exact absurd h2 (ne_of_gt h1)
    · rfl
    · rfl
    · rfl
  rw [cpt, this, ExtFPf.rmul_oneF]

theorem eventually_split {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∃ z ∈ Metric.closedBall (0 : V (nd X)) δ, ∃ b ∈ Bor X.Ψ r,
      y = rmul (cpt X x z) b := by
  have hu : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.mpr (hx τ).1
  have hM : ∀ τ, LUPf.Mx X x x τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hu τ)
  have hΔ : LUPf.DeltaF X x x ≠ 0 := by
    have : LUPf.DeltaF X x x = 1 := by
      unfold LUPf.DeltaF
      refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
      rw [hM]
      exact LUPf.lminor_one k
    rw [this]; exact one_ne_zero
  have hL : LUPf.Lm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    refine (LUPf.Lm_unique 1 1 (fun k => by rw [LUPf.lminor_one]; exact one_ne_zero)
      (fun i k h => Matrix.one_apply_ne (ne_of_lt h)) (fun i => Matrix.one_apply_eq i) fun i j h => ?_).symm
    rw [Matrix.one_mul]; exact Matrix.one_apply_ne (ne_of_gt h)
  have hz0 : LUPf.zF X x x = 0 := by
    ext k
    set p := (Fintype.equivFin (Ent X)).symm k with hp
    show ((LUPf.Lm (LUPf.Mx X x x p.1))⁻¹ : Matrix (Fin r) (Fin r) ℂ) p.2.1.1 p.2.1.2 = 0
    rw [hM, hL, inv_one]
    exact Matrix.one_apply_ne (ne_of_gt p.2.2)
  have hopen : IsOpen {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (LUPf.Delta_diff (X := X) (x0 := x)).continuous continuous_const)
  have hn := hopen.mem_nhds (show x ∈ {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} from ⟨hx, hΔ⟩)
  have hc : ContinuousAt (LUPf.zF X x) x :=
    (LUPf.zF_diffOn (X := X) (x0 := x)).continuousOn.continuousAt hn
  have hb : ∀ᶠ y in 𝓝 x, LUPf.zF X x y ∈ Metric.closedBall (0 : V (nd X)) δ :=
    hc.preimage_mem_nhds (by rw [hz0]; exact Metric.closedBall_mem_nhds _ hδ)
  filter_upwards [hn, hb] with y hy hyb
  refine ⟨hy.1, _, hyb, _, LUPf.bF_mem hy.1 hy.2, ?_⟩
  funext τ
  show y τ = (mat x τ * mat (nmat X (LUPf.zF X x y)) τ *
    (LUPf.Lm (LUPf.Mx X x y τ) * LUPf.Mx X x y τ) : Matrix (Fin r) (Fin r) ℂ)
  rw [LUPf.nmat_zF]
  show y τ = (mat x τ * (LUPf.Lm (LUPf.Mx X x y τ))⁻¹ * (LUPf.Lm (LUPf.Mx X x y τ) * ((mat x τ)⁻¹ * mat y τ)) :
    Matrix (Fin r) (Fin r) ℂ)
  have hL' : IsUnit (LUPf.Lm (LUPf.Mx X x y τ)).det := by rw [LUPf.Lm_det]; exact isUnit_one
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (LUPf.Lm (LUPf.Mx X x y τ))⁻¹, Matrix.nonsing_inv_mul _ hL',
    Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  rfl

theorem isolated_of_det {n : ℕ} {f : V n → V n} (hdet : (fderiv ℂ f 0).det ≠ 0) (h0 : f 0 = 0) :
    ∃ δ > 0, ∀ y ∈ Metric.closedBall (0 : V n) δ, f y = 0 → y = 0 := by
  by_cases hd : DifferentiableAt ℂ f 0
  · exact HE.iso_zero hd.hasFDerivAt hdet h0
  · refine ⟨1, one_pos, fun y _ _ => ?_⟩
    have hk := HE.ker_bot_of_det hdet
    rw [fderiv_zero_of_not_differentiableAt hd] at hk
    have : y ∈ LinearMap.ker ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) := by simp
    rw [hk] at this
    exact (Submodule.mem_bot ℂ).1 this

def orbitSetoid {r : ℕ} (X : Data E r) : Setoid (Frame X.Ψ r) where
  r x y := ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)
  iseqv := by
    refine ⟨fun x => ⟨1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, ?_⟩, ?_, ?_⟩
    · rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]
    · rintro x y ⟨γ, hγ, b, hb, rfl⟩
      refine ⟨γ⁻¹, X.Γ.inv_mem hγ, ExtFPf.invF X b, ExtFPf.invF_mem X hb, ?_⟩
      rw [← FundSetPf.lact_rmul, FundSetPf.lact_inv, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
        ExtFPf.rmul_oneF]
    · rintro x y z ⟨γ, hγ, b, hb, rfl⟩ ⟨γ', hγ', b', hb', rfl⟩
      refine ⟨γ' * γ, X.Γ.mul_mem hγ' hγ, rmul b b', ExtFPf.mul_mem X hb hb', ?_⟩
      rw [FundSetPf.lact_mul, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc]

theorem finite_orbits : ∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ),
    X.IsSec L w0 → (∀ k, X.IsSec L (s k)) →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → w0 x ≠ 0 ∧ (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X x z) / w0 (cpt X x z) : V (nd X))) 0).det ≠ 0) →
    ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) →
    ∃ (δ : ℕ) (xs : Fin δ → Frame X.Ψ r), (∀ j, xs j ∈ X.dom) ∧
      (∀ x ∈ X.dom, (∀ k, s k x = 0) ↔ ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)) ∧
      ∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j' := by
  classical
  intro r X L w0 s _ hs hsimp C hC hCd hmeet
  set S := orbitSetoid X with hS

  have hstab : ∀ x y, S.r x y → (x ∈ X.dom ∧ ∀ k, s k x = 0) → (y ∈ X.dom ∧ ∀ k, s k y = 0) := by
    rintro x y ⟨γ, hγ, b, hb, rfl⟩ ⟨hx, h0⟩
    have hxb := OntoS.dom_rmul X hx hb
    refine ⟨OntoS.dom_lact X hγ hxb, fun k => ?_⟩
    rw [(hs k).2.2 γ hγ _ hxb, (hs k).2.1 x hx b hb, h0 k, mul_zero, mul_zero]

  have hloc : ∀ x ∈ X.dom, (∀ k, s k x = 0) → ∀ᶠ y in 𝓝 x, (∀ k, s k y = 0) → S.r x y := by
    intro x hx h0
    obtain ⟨δ, hδ, hiso⟩ := isolated_of_det (hsimp x hx h0).2 (by
      ext k
      simp [cpt_origin, h0 k])
    filter_upwards [eventually_split X hx hδ] with y ⟨hy, z, hz, b, hb, he⟩ hy0
    have hR : S.r (cpt X x z) y := ⟨1, X.Γ.one_mem, b, hb, by rw [FundSetPf.lact_one]; exact he⟩
    have h1 := (hstab _ _ (S.iseqv.symm hR) ⟨hy, hy0⟩).2
    have hz0 : z = 0 := hiso z hz (by
      ext k
      simp [h1 k])
    rwa [hz0, cpt_origin] at hR
  have hK : IsCompact (C ∩ {x | ∀ k, s k x = 0}) := by
    have hcont : ContinuousOn (fun x k => s k x) C :=
      continuousOn_pi.2 fun k => (hs k).1.continuousOn.mono hCd
    have hcl := hcont.preimage_isClosed_of_isClosed hC.isClosed (isClosed_singleton (x := 0))
    have he : C ∩ {x | ∀ k, s k x = 0} = C ∩ (fun x k => s k x) ⁻¹' {0} := by
      ext x; simp [funext_iff]
    rw [he]
    exact hC.of_isClosed_subset hcl Set.inter_subset_left
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | (∀ k, s k y = 0) → S.r x y})
    (fun x hx => hloc x (hCd hx.1) hx.2)
  set T : Finset (Quotient S) := t.image (Quotient.mk S) with hT
  have hout : ∀ q ∈ T, q.out ∈ X.dom ∧ ∀ k, s k q.out = 0 := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    exact hstab x _ (S.iseqv.symm (Quotient.mk_out x)) ⟨hCd (htK x hx).1, (htK x hx).2⟩
  refine ⟨T.card, fun j => (T.equivFin.symm j).1.out, fun j => (hout _ (T.equivFin.symm j).2).1,
    fun x hx => ⟨fun h0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨γ, hγ, b, hb, hc⟩ := hmeet x hx h0
    have hR : S.r x (lact γ (rmul x b)) := ⟨γ, hγ, b, hb, rfl⟩
    have h1 := (hstab _ _ hR ⟨hx, h0⟩).2
    obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hcov ⟨hc, h1⟩)
    refine ⟨T.equivFin ⟨Quotient.mk S u, Finset.mem_image_of_mem _ hu⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact S.iseqv.trans (Quotient.mk_out u) (S.iseqv.trans (hy h1) (S.iseqv.symm hR))
  · rintro ⟨j, hj⟩
    exact (hstab _ x hj (hout _ (T.equivFin.symm j).2)).2
  · intro j j' γ hγ b hb h
    have hR : S.r (T.equivFin.symm j).1.out (T.equivFin.symm j').1.out := ⟨γ, hγ, b, hb, h⟩
    have := Quotient.sound (s := S) hR
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact T.equivFin.symm.injective (Subtype.ext this)

end GlobalTheory.FiniteZeroOrbits
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FlatPoints

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_comb_sq_le {N : ℕ} (t a : Fin N → ℂ) :
    ‖∑ j, t j * a j‖ ^ 2 ≤ (∑ j, ‖t j‖ ^ 2) * ∑ j, ‖a j‖ ^ 2 := by
  have h1 : ‖∑ j, t j * a j‖ ≤ ∑ j, ‖t j‖ * ‖a j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

theorem pnorm_sq_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x ^ 2 = ‖P x‖ ^ 2 * X.nfac la x ^ 2 := by
  have e : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  rw [e, mul_pow]

theorem sum_pnorm_sq_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (P : Fin N → Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) :
    ∑ k, X.pnorm la (P k) x ^ 2 = (∑ k, ‖P k x‖ ^ 2) * X.nfac la x ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => pnorm_sq_eq X la _ x

theorem comb_mem {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (c : ℝ) {N : ℕ} (t : Fin N → ℂ)
    (w : Fin N → Frame X.Ψ r → ℂ) (hw : ∀ k, w k ∈ X.SSgt la c) :
    (fun x => ∑ j, t j * w j x) ∈ X.SSgt la c := by
  classical
  obtain ⟨-, -, ⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X la la c
  have hmem : ∀ s : Finset (Fin N), ∑ j ∈ s, t j • w j ∈ X.SSgt la c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ (hsmul _ _ (hw a)) _ ih
  have e : (fun x => ∑ j, t j * w j x) = ∑ j, t j • w j := by
    funext x; simp [Finset.sum_apply]
  rw [e]; exact hmem _

theorem sum_norm_sq_orbit {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {N : ℕ}
    (P : Fin N → Frame X.Ψ r → ℂ) (hP : ∀ k, X.IsSec la (P k)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    ∑ k, ‖P k (lact γ (rmul x b))‖ ^ 2 = ‖bchar la b‖ ^ 2 * ∑ k, ‖P k x‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hP k).2.2 γ hγ _ (OntoS.dom_rmul X hx hb), (hP k).2.1 x hx b hb, norm_mul, norm_mul,
    OntoE.chi_norm X la hγ, one_mul, mul_pow]

theorem exists_flat : LineBundleFirstBoundGlobalGeneration (E := E) → MahlerCompactnessCriterion (E := E) → ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (t : Fin (nd X + 1) → Fin Xa.N → ℂ),
    let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t i j * Xa.w j x
    (∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ K * ∑ i, ‖sf i x‖ ^ 2) →
    (∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < ε * ‖sf 0 x‖ ^ 2 →
      c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) →
    (∀ x ∈ X.dom, (∀ k : Fin (nd X), sf k.succ x = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      sf k.succ (cpt X x z) / sf 0 (cpt X x z) : V (nd X))) 0).det ≠ 0) →
    ∃ Fl : FlatM X Xa, Fl.w0 = sf 0 ∧ Fl.s = fun k => sf k.succ := by
  intro hLa hM2 r X Xa t sf ⟨K, hK⟩ ⟨ε, c0, hε, hc0, hsm⟩ hdet
  have hvan : ∀ i, sf i ∈ X.SSgt Xa.L 0 := fun i => comb_mem X _ 0 (t i) Xa.w Xa.w_van
  have hsec : ∀ i, X.IsSec Xa.L (sf i) := fun i => (hvan i).1.1.1
  have hwsec : ∀ k, X.IsSec Xa.L (Xa.w k) := fun k => (Xa.w_van k).1.1.1
  have hcs : ∀ i x, ‖sf i x‖ ^ 2 ≤ (∑ j, ‖t i j‖ ^ 2) * ∑ j, ‖Xa.w j x‖ ^ 2 :=
    fun i x => norm_comb_sq_le (t i) fun j => Xa.w j x
  have hK' : ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤
      K * (‖sf 0 x‖ ^ 2 + ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) := fun x hx => by
    have := hK x hx
    rwa [Fin.sum_univ_succ] at this
  have hw0 : ∀ x ∈ X.dom, (∀ k : Fin (nd X), sf k.succ x = 0) → sf 0 x ≠ 0 := by
    intro x hx h0 h00
    have h1 := hK' x hx
    simp only [h0, h00, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, add_zero, mul_zero] at h1
    obtain ⟨k, hk⟩ := Xa.w_nz x hx
    have : 0 < ∑ k, ‖Xa.w k x‖ ^ 2 := Finset.sum_pos' (fun j _ => by positivity)
      ⟨k, Finset.mem_univ k, pow_pos (norm_pos_iff.2 hk) 2⟩
    linarith
  obtain ⟨C, hC, hCd, hCx⟩ :=
    GlobalTheory.CuspCompact.exists_compact_of_le_sum_pnorm_sq hLa hM2 r X Xa c0 hc0
  obtain ⟨δ, xs, hxs, hS, hinj⟩ := GlobalTheory.FiniteZeroOrbits.finite_orbits r X Xa.L (sf 0)
    (fun k => sf k.succ) (hsec 0) (fun k => hsec _) (fun x hx h0 => ⟨hw0 x hx h0, hdet x hx h0⟩)
    C hC hCd (fun x hx h0 => hCx x hx (hsm x hx (by
      have := pow_pos (norm_pos_iff.2 (hw0 x hx h0)) 2
      have h0' : ∀ k : Fin (nd X), sf k.succ x = 0 := h0
      simp only [h0', norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero]
      positivity)))
  have hxs0 : ∀ j, ∀ k : Fin (nd X), sf k.succ (xs j) = 0 := fun j =>
    (hS _ (hxs j)).2 ⟨j, (GlobalTheory.FiniteZeroOrbits.orbitSetoid X).iseqv.refl (xs j)⟩
  refine ⟨⟨sf 0, fun k => sf k.succ, hvan 0, fun k => hvan _, δ, xs, hxs, hS, hinj,
    fun j => hw0 _ (hxs j) (hxs0 j), fun j => hdet _ (hxs j) (hxs0 j), ⟨K, fun x hx => ?_⟩,
    ⟨∑ j, ‖t 0 j‖ ^ 2, fun x hx => ?_⟩,
    ⟨∑ i : Fin (nd X), ∑ j, ‖t i.succ j‖ ^ 2, fun x hx => ?_⟩, fun U hU hxU hsat => ?_⟩, rfl, rfl⟩
  · rw [sum_pnorm_sq_eq, sum_pnorm_sq_eq, pnorm_sq_eq, ← add_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hK' x hx) (sq_nonneg _)
  · rw [sum_pnorm_sq_eq, pnorm_sq_eq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hcs 0 x) (sq_nonneg _)
  · rw [sum_pnorm_sq_eq, sum_pnorm_sq_eq, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hcs _ x
  · have hpos : ∀ x ∈ X.dom, x ∉ U → 0 < ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 := by
      intro x hx hxU'
      by_contra hle
      have hz : ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 = 0 :=
        le_antisymm (not_lt.1 hle) (Finset.sum_nonneg fun i _ => by positivity)
      have h0 : ∀ k : Fin (nd X), sf k.succ x = 0 := fun k => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hz k (Finset.mem_univ k)
        simpa using this
      obtain ⟨j, γ, hγ, b, hb, he⟩ := (hS x hx).1 h0
      exact hxU' (he ▸ hsat _ (hxU j) γ hγ b hb)
    have hCU : IsCompact (C \ U) := hC.diff hU
    have hcont : ContinuousOn
        (fun x => (∑ k, ‖Xa.w k x‖ ^ 2) / ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) (C \ U) := by
      refine ContinuousOn.div ?_ ?_ fun x hx => (hpos x (hCd hx.1) hx.2).ne'
      · exact continuousOn_finsetSum _ fun k _ =>
          (((hwsec k).1.continuousOn.mono fun x (hx : x ∈ C \ U) => hCd hx.1).norm.pow 2)
      · exact continuousOn_finsetSum _ fun k _ =>
          (((hsec k.succ).1.continuousOn.mono fun x (hx : x ∈ C \ U) => hCd hx.1).norm.pow 2)
    obtain ⟨M, hM⟩ := (hCU.image_of_continuousOn hcont).bddAbove
    refine ⟨max M (|K| * (ε⁻¹ + 1)), fun x hx hxU' => ?_⟩
    rw [sum_pnorm_sq_eq, sum_pnorm_sq_eq, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hp := hpos x hx hxU'
    rcases lt_or_ge (∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) (ε * ‖sf 0 x‖ ^ 2) with h | h
    · obtain ⟨γ, hγ, b, hb, hy⟩ := hCx x hx (hsm x hx h)
      have hyU : lact γ (rmul x b) ∉ U := by
        intro hU'
        obtain ⟨γ', hγ', b', hb', he⟩ := (GlobalTheory.FiniteZeroOrbits.orbitSetoid X).iseqv.symm
          (show (GlobalTheory.FiniteZeroOrbits.orbitSetoid X).r x (lact γ (rmul x b)) from ⟨γ, hγ, b, hb, rfl⟩)
        exact hxU' (he ▸ hsat _ hU' γ' hγ' b' hb')
      have h1 := hM ⟨_, ⟨hy, hyU⟩, rfl⟩
      have hb0 : ‖bchar Xa.L b‖ ^ 2 ≠ 0 := (pow_pos (norm_pos_iff.2 (OntoE.bchar_ne X _ hb)) 2).ne'
      simp only at h1
      rw [sum_norm_sq_orbit X Xa.L Xa.w hwsec hγ hx hb,
        sum_norm_sq_orbit X Xa.L (fun k : Fin (nd X) => sf k.succ) (fun k => hsec _) hγ hx hb,
        mul_div_mul_left _ _ hb0, div_le_iff₀ hp] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le)
      have h2 : ‖sf 0 x‖ ^ 2 ≤ ε⁻¹ * ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 := by
        rw [le_inv_mul_iff₀ hε]; exact h
      calc _ ≤ K * (‖sf 0 x‖ ^ 2 + ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) := hK' x hx
        _ ≤ |K| * (‖sf 0 x‖ ^ 2 + ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
        _ ≤ |K| * (ε⁻¹ * ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 + ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
        _ = _ := by ring

end GlobalTheory.FlatPoints
