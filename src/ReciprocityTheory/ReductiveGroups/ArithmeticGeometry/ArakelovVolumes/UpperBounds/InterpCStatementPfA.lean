module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModelNefness
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace IC

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨k, hk, h⟩ := X.χ_fin la
  intro h0
  have h1 := h γ hγ
  rw [h0, zero_pow hk.ne'] at h1
  exact zero_ne_one h1

theorem poin_single {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    {γ0 : GL (Fin r) E} (h0 : γ0 ∈ X.Γ) (hz : ∀ γ ∈ X.Γ, γ ≠ γ0 → P (lact γ x) = 0) :
    poin X la P x = (X.χ la γ0)⁻¹ * P (lact γ0 x) := by
  unfold poin
  refine (tsum_eq_single ⟨γ0, h0⟩ fun γ hγ => ?_).trans rfl
  rw [hz γ.1 γ.2 (fun h => hγ (Subtype.ext h)), mul_zero]

theorem poin_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hz : ∀ γ ∈ X.Γ, P (lact γ x) = 0) : poin X la P x = 0 := by
  unfold poin
  have h1 : ∀ γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x) = 0 := fun γ => by
    rw [hz γ.1 γ.2, mul_zero]
  simp only [h1, tsum_zero]

theorem norm_sgn (p0 a : ℕ) : ‖((sgn p0 a : ℝ) : ℂ)‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem norm_dmin_orth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ)
    (i : Fin (r + 1)) : ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  exact Finset.prod_eq_one fun a _ => norm_sgn _ _

theorem pnorm_orth {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : X.pnorm la P x = ‖P x‖ := by
  simp [Data.pnorm, norm_div, norm_dmin_orth X hx]

theorem cfwM_smul {r : ℕ} (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : cfwM X ps a) {t : ℝ}
    (ht : 0 < t) : cfwM X (fun x => t * ps x) (t * a) := by
  obtain ⟨⟨C, A', h1⟩, h2⟩ := h
  refine ⟨⟨t * C, t * A', fun x hx => ?_⟩, fun η hη hη' => ?_⟩
  · show t * ps x ≤ _
    exact (mul_le_mul_of_nonneg_left (h1 x hx) ht.le).trans_eq (by ring)
  · obtain ⟨C, A', h3⟩ := h2 η hη hη'
    refine ⟨t * C, t * A', fun x hx ξ hξ hτ => ?_⟩
    show t * ps x ≤ _
    exact (mul_le_mul_of_nonneg_left (h3 x hx ξ hξ hτ) ht.le).trans_eq (by ring)

theorem half_le {w : ℝ≥0∞} {p ψ : ℝ} (hw : ENNReal.ofReal (Real.exp (-(p + ψ))) ≤ w) :
    (ENNReal.ofReal (Real.exp (-p)) / w) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.exp (ψ / 2)) := by
  have h1 : ENNReal.ofReal (Real.exp (-p)) / w ≤ ENNReal.ofReal (Real.exp ψ) := by
    calc ENNReal.ofReal (Real.exp (-p)) / w
        ≤ ENNReal.ofReal (Real.exp (-p)) / ENNReal.ofReal (Real.exp (-(p + ψ))) :=
          ENNReal.div_le_div_left hw _
      _ = ENNReal.ofReal (Real.exp (-p) / Real.exp (-(p + ψ))) :=
          (ENNReal.ofReal_div_of_pos (Real.exp_pos _)).symm
      _ = ENNReal.ofReal (Real.exp ψ) := by
          rw [← Real.exp_sub, show -p - -(p + ψ) = ψ by ring]
  calc (ENNReal.ofReal (Real.exp (-p)) / w) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (Real.exp ψ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = ENNReal.ofReal (Real.exp ψ ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num)
    _ = ENNReal.ofReal (Real.exp (ψ / 2)) := by
        rw [← Real.exp_mul, mul_one_div]

theorem orth_mem_dom {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) : x0 ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq]
  intro τ
  have hs : ∀ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) ≠ 0 := by
    intro a
    unfold sgn
    split_ifs <;> norm_num
  refine ⟨?_, fun i => ?_⟩
  · intro h0
    have hg : gram τ.1 X.Gm (mat x0 τ) =
        (mat x0 τ)ᵀ * X.Gm.map τ.1 * (mat x0 τ).map (starRingEnd ℂ) := by
      ext a b
      simp only [gram, hermC, col, mat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply, Finset.sum_mul]
      exact Finset.sum_comm
    have h1 := congrArg Matrix.det hg
    rw [ho τ, Matrix.det_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0,
      zero_mul, zero_mul] at h1
    exact (Finset.prod_ne_zero_iff.mpr fun a _ => hs a) h1
  · have hd : dmin X.Gm x0 τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
      unfold dmin lminor
      rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
      simp [psgn, ← Fin.prod_univ_eq_prod_range]
    have hne : psgn X.p0 i ≠ 0 := by
      unfold psgn
      refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
      unfold sgn
      split_ifs <;> norm_num
    rw [hd, Complex.ofReal_re]
    exact mul_self_pos.mpr hne

private lemma leviO_fderiv_lemma {m : ℕ} (c : ℝ) (f : V m → ℂ) (y : V m) :
    fderiv ℝ (fun w => (c : ℂ) * f w) y = (c : ℂ) • fderiv ℝ f y := by
  by_cases hf : DifferentiableAt ℝ f y
  · exact fderiv_const_mul hf _
  · by_cases hc : c = 0
    · subst hc
      simp
    · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      have h2 : ¬ DifferentiableAt ℝ (fun w => (c : ℂ) * f w) y := by
        intro h
        apply hf
        refine (h.const_mul ((c : ℂ)⁻¹)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
        show f w = (c : ℂ)⁻¹ * ((c : ℂ) * f w)
        rw [← mul_assoc, inv_mul_cancel₀ hc', one_mul]
      rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt h2, smul_zero]

theorem leviO_smul {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (g : Frame X.Ψ r → ℝ) (t : ℝ)
    {z : V (nd X)} (hg : ContDiffAt ℝ 2 (fun w => g (cpt X x0 w)) z) (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (fun x => t * g x) z ξ = t * leviO X x0 g z ξ := by
  show (leviV (nd X) (fun w => (((t * g (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re =
    t * (leviV (nd X) (fun w => ((g (cpt X x0 w) : ℝ) : ℂ)) z ξ).re
  have hf : (fun w => (((t * g (cpt X x0 w)) : ℝ) : ℂ)) =
      fun w => (t : ℂ) * ((g (cpt X x0 w) : ℝ) : ℂ) := funext fun w => Complex.ofReal_mul _ _
  have hwdb : ∀ (k : Fin (nd X)) (f : V (nd X) → ℂ),
      wdb (nd X) k (fun w => (t : ℂ) * f w) = fun y => (t : ℂ) * wdb (nd X) k f y := by
    intro k f
    funext y
    simp only [wdb, leviO_fderiv_lemma, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hwd : ∀ (j : Fin (nd X)) (f : V (nd X) → ℂ) (y : V (nd X)),
      wd (nd X) j (fun w => (t : ℂ) * f w) y = (t : ℂ) * wd (nd X) j f y := by
    intro j f y
    simp only [wd, leviO_fderiv_lemma, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hf]
  simp only [leviV, hwdb, hwd, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]

end IC

theorem interpC_of (hP : PoinStatement (E := E)) (hK : KronHolPsiStatement (E := E))
    (hη : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 →
      ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ +
          leviO X x0 (fun x => (1 + Xa.c1 / Xa.a1) * Xa.ps0 x) z ξ) :
    InterpCStatement (E := E) := by
  intro r X Xa Fl hPD hmar hL hps hcusp hMH v
  obtain ⟨bb, m, hbb, hbm, hm⟩ := hmar
  obtain ⟨Cp, hCp⟩ := hps
  set t : ℝ := 1 + Xa.c1 / Xa.a1 with ht_def
  have ht : 0 < t := by have := Xa.frame_theta_const_pos; have := Xa.frame_theta_weight_pos; positivity
  have hta : Xa.c1 < t * Xa.a1 := by
    have ha := Xa.frame_theta_weight_pos
    rw [ht_def, add_mul, one_mul, div_mul_cancel₀ _ ha.ne']
    linarith
  set ψ : Frame X.Ψ r → ℝ := fun x => t * Xa.ps0 x with hψ
  have hψinv : IsInvFn X ψ := fun γ hγ x hx b hb => by simp only [hψ, Xa.potential_invariant γ hγ x hx b hb]
  have hsm : ∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => Xa.ps0 (cpt X x0 z)) (OmF X x0) :=
    fun x0 ho => Xa.potential_smooth x0 (IC.orth_mem_dom X ho)
  have hψsm : ∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0) :=
    fun x0 ho => contDiffOn_const.mul (hsm x0 ho)
  have hψb : ∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C :=
    ⟨t * Cp, fun x hx => mul_le_mul_of_nonneg_left (hCp x hx) ht.le⟩
  have hmψ : ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 ψ z ξ := by
    refine ⟨bb, m, hbb, hbm, fun x0 ho z hz ξ => ?_⟩
    have hca : ContDiffAt ℝ 2 (fun w => Xa.ps0 (cpt X x0 w)) z :=
      ((hsm x0 ho).contDiffAt ((ExF.isOpen_OmF X x0).mem_nhds hz)).of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from WithTop.coe_le_coe.2 le_top)
    rw [show leviO X x0 ψ z ξ = t * leviO X x0 Xa.ps0 z ξ from IC.leviO_smul X x0 Xa.ps0 t hca ξ]
    exact hm x0 ho z hz ξ
  have hQ : ∀ j, ∃ Q ∈ X.SSgt Xa.Fp Xa.c1, Q (Fl.xs j) ≠ 0 ∧ ∀ j', j' ≠ j → Q (Fl.xs j') = 0 := by
    intro j
    obtain ⟨x0, W, bb', F, P, γ0, ho, hW, hWl, hWψ, hbb', hF, hA, hBE, hPF, h0, hne, hz⟩ :=
      hK r X Xa Fl hPD ψ hψinv hψsm hψb hmψ (hη r X Xa) hL j
    obtain ⟨-, hbdd, -, hball, -⟩ := hP r X x0 ho hPD Xa.Fp W bb' hW hWl hbb' F P hF hA hBE hPF
    have hmode := hMH Xa.Fp (poin X Xa.Fp P) ψ (t * Xa.a1) hbdd.1 (IC.cfwM_smul X Xa.base_psi_weighted_cf ht)
      (by have := Xa.frame_theta_weight_pos; positivity) (fun ρ hρ hρ1 => by
        obtain ⟨C', hC'⟩ := hball ρ hρ hρ1
        refine ⟨C', fun x hx hox => ?_⟩
        rw [IC.pnorm_orth X Xa.Fp _ hox]
        refine (hC' x hx hox).trans (mul_le_mul' le_rfl ?_)
        exact iSup_mono fun z => iSup_mono fun _ => iSup_mono fun hzd => IC.half_le (hWψ _ hzd))
    refine ⟨poin X Xa.Fp P, ⟨⟨hbdd, fun ξ hξ x hx => hmode ξ hξ 0 ?_ x hx⟩,
      fun ξ hξ ν hν x hx => hmode ξ hξ ν (lt_of_le_of_lt hν hta) x hx⟩, ?_, fun j' hj' => ?_⟩
    · simp only [Pi.zero_apply, Finset.sum_const_zero]
      have := Xa.frame_theta_weight_pos; positivity
    · rw [IC.poin_single X Xa.Fp P _ h0 fun γ hγ hne' => hz γ hγ j (Or.inl hne')]
      exact mul_ne_zero (inv_ne_zero (IC.chi_ne_zero X Xa.Fp h0)) hne
    · exact IC.poin_zero X Xa.Fp P _ fun γ hγ => hz γ hγ j' (Or.inr hj')
  classical
  choose Q hQs hQne hQz using hQ
  obtain ⟨-, -, ⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X Xa.Fp Xa.Fp Xa.c1
  set G : Fin Fl.δ → Frame X.Ψ r → ℂ := fun j => (Q j (Fl.xs j))⁻¹ • Q j with hG
  have hGs : ∀ j, G j ∈ X.SSgt Xa.Fp Xa.c1 := fun j => hsmul _ _ (hQs j)
  have hGv : ∀ j j', G j (Fl.xs j') = if j' = j then 1 else 0 := by
    intro j j'
    by_cases h : j' = j
    · subst h; simp [hG, hQne]
    · simp [hG, h, hQz j j' h]
  have hmem : ∀ s : Finset (Fin Fl.δ), ∑ j ∈ s, v j • G j ∈ X.SSgt Xa.Fp Xa.c1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ (hsmul _ _ (hGs a)) _ ih
  refine ⟨∑ j, v j • G j, hmem _, fun j => ?_⟩
  simp [Finset.sum_apply, hGv]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace BigB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem S_pos (X : Data E r) (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  obtain ⟨k, hk⟩ := Xa.w_nz x hx
  have hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have hne : ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hd' τ).2 i
    rw [h0] at h1
    simp at h1
  have hp : 0 < X.pnorm Xa.L (Xa.w k) x := by
    unfold Data.pnorm
    apply mul_pos (norm_pos_iff.mpr hk)
    apply Finset.prod_pos
    intro τ _
    apply Finset.prod_pos
    intro i _
    apply Real.rpow_pos_of_pos
    exact norm_pos_iff.mpr (div_ne_zero (hne τ i.succ) (hne τ i.castSucc))
  calc (0 : ℝ) < X.pnorm Xa.L (Xa.w k) x ^ 2 := by positivity
    _ ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
      Finset.single_le_sum (f := fun k => X.pnorm Xa.L (Xa.w k) x ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)

theorem pnorm_contOn (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    apply Continuous.matrix_det
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    simp only [Matrix.submatrix_apply, gram, hermC, Matrix.of_apply, mat, col]
    fun_prop
  have hne : ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro x hx τ i h0
    have hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
    have h1 := (hd' τ).2 i
    rw [h0] at h1
    simp at h1
  unfold Data.pnorm
  apply ContinuousOn.mul
  · exact continuous_norm.comp_continuousOn hP.1.continuousOn
  · apply continuousOn_finsetProd
    intro τ _
    apply continuousOn_finsetProd
    intro i _
    apply ContinuousOn.rpow_const
    · exact (((hd τ i.succ).continuousOn).div (hd τ i.castSucc).continuousOn
        (fun x hx => hne x hx τ i.castSucc)).norm
    · intro x hx
      left
      exact norm_ne_zero_iff.mpr (div_ne_zero (hne x hx τ i.succ) (hne x hx τ i.castSucc))

theorem r_pos (X : Data E r) (Xa : ArchInM X) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    have h := Xa.n_ge
    have h0 : nd X = 0 := by
      unfold nd
      rw [Fintype.card_eq_zero_iff]
      constructor
      rintro ⟨_, ⟨⟨a, _⟩, _⟩⟩
      exact a.elim0
    omega
  · exact hr

theorem lam_ne (X : Data E r) (Xa : ArchInM X) : ∃ v ∈ X.Λ, v ≠ 0 := by
  have hr := r_pos X Xa
  by_contra h
  push_neg at h
  have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥ := by
    rw [Submodule.span_le]
    intro v hv
    simp [h v hv]
  rw [X.Λ_span, top_le_iff] at h1
  have hm : (fun _ => (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E)) := Submodule.mem_top
  rw [← h1, Submodule.mem_bot] at hm
  exact one_ne_zero (congrFun hm ⟨0, hr⟩)

end BigB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ss_sub_ssgt0 {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SS la) : P ∈ X.SSgt la 0 := by
  refine ⟨hP, ?_⟩
  intro ξ hξ ν hν x hx
  by_contra hne
  have hpos : ∀ τ, 0 ≤ ν τ := BoundedSectionAlgebra.sign_of_bdd (X := X) moderateCoefficientPositivity_holds hP.1 hξ ν hx hne
  have hsum : ∑ τ, ν τ = 0 := le_antisymm hν (Finset.sum_nonneg fun τ _ => hpos τ)
  have hz : ν = 0 := by
    funext τ
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => hpos τ)).1 hsum τ (Finset.mem_univ τ)
  subst hz
  exact hne (hP.2 ξ hξ x hx)

theorem interp_of_kron {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {δ : ℕ} (xs : Fin δ → Frame X.Ψ r)
    (h : ∀ j, ∃ F ∈ X.SSgt la 0, ∀ j', F (xs j') = if j' = j then 1 else 0) :
    ∀ v : Fin δ → ℂ, ∃ F ∈ X.SSgt la 0, ∀ j, F (xs j) = v j := by
  intro v
  choose F hF hval using h
  obtain ⟨h0, hadd, hsmul⟩ := (siegelSpaceAlgebra_holds (E := E) r X la la 0).2.2.1
  refine ⟨∑ j, v j • F j, ?_, ?_⟩
  · exact Finset.sum_induction (fun j => v j • F j) (· ∈ X.SSgt la 0)
      (fun a b ha hb => hadd a ha b hb) h0 (fun j _ => hsmul (v j) (F j) (hF j))
  · intro j
    simp [Finset.sum_apply, hval]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Hyp (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) : Prop :=
  IsOrth X x0 ∧ PropDisc X ∧ IsMetricW X la W ∧ WLower X la W ∧
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧
    IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

def supR (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (ρ : ℝ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
    (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)

def LocStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ x ∈ X.dom, ∃ ε > 0, ∃ u : X.Γ → ℝ, Summable u ∧
      ∀ γ : X.Γ, ∀ y ∈ Metric.ball x ε, ‖P (lact γ.1 y)‖ ≤ u γ

def BallStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ ≤ ENNReal.ofReal C * supR X la W ρ x

def FFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)

theorem differentiable_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Differentiable ℂ (lact (Ψ := Ψ) γ) := by
  unfold lact mat
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem enorm_poin_le (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    ENNReal.ofReal ‖poin X la P x‖ ≤ ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ := by
  unfold poin
  have hχ : ∀ γ : X.Γ, ‖X.χ la γ.1‖ = 1 := fun γ => by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1
      (by rw [← norm_pow, h γ.1 γ.2, norm_one])
  have hn : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ = ‖P (lact γ.1 x)‖ := fun γ => by
    rw [norm_mul, norm_inv, hχ γ, inv_one, one_mul]
  by_cases hs : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖
  · calc ENNReal.ofReal ‖∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖
        ≤ ENNReal.ofReal (∑' γ : X.Γ, ‖P (lact γ.1 x)‖) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hn))
          exact hs.congr fun γ => (hn γ).symm
      _ = ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
          simp only [ofReal_norm_eq_enorm]
  · have htop : ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ = ⊤ := by
      by_contra h
      apply hs
      have h2 : Summable fun γ : X.Γ => ‖P (lact γ.1 x)‖₊ := by
        rw [← ENNReal.tsum_coe_ne_top_iff_summable]
        simpa only [enorm_eq_nnnorm] using h
      exact NNReal.summable_coe.2 h2
    rw [htop]
    exact le_top

theorem supR_le (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) {c : ℝ} (hc : 0 < c)
    (hW : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x) (ρ : ℝ) (x : Frame X.Ψ r) :
    supR X la W ρ x ≤ ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) := by
  unfold supR
  refine iSup₂_le fun z _ => iSup_le fun hz => ENNReal.rpow_le_rpow ?_ (by norm_num)
  have he : 0 < Real.exp (-phla X la (cpt X x z)) := Real.exp_pos _
  calc ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)
      ≤ ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) /
          ENNReal.ofReal (c * Real.exp (-phla X la (cpt X x z))) := ENNReal.div_le_div_left (hW _ hz) _
    _ = ENNReal.ofReal (1 / c) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_sgn' (p0 a : ℕ) : ‖((sgn p0 a : ℝ) : ℂ)‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem norm_dmin_orth' (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ)
    (i : Fin (r + 1)) : ‖dmin X.Gm x τ i‖ = 1 := by
  unfold IsOrth at hx
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  exact Finset.prod_eq_one fun a _ => norm_sgn' _ _

theorem pnorm_orth' (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  simp [norm_div, norm_dmin_orth' X hx]

theorem poin_of (hL : LocStatement (E := E)) (hB : BallStatement (E := E)) (hF : FFStatement (E := E)) :
    PoinStatement (E := E) := by
  intro r X x0 hx0 hPD la W bb hW hWl hbb F P hFd hA hP hPF
  have H : Hyp X x0 la W bb F P := ⟨hx0, hPD, hW, hWl, hbb, hFd, hA, hP, hPF⟩
  obtain ⟨c, hc, hcW⟩ := hWl
  have hterm : ∀ (γ : X.Γ) y, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ := by
    intro γ y; rw [norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]
  obtain ⟨C1, hC1⟩ := hB r X x0 la W bb F P H 1 one_pos le_rfl
  have horth : ∀ y ∈ X.dom, IsOrth X y → ‖poin X la P y‖ ≤ max C1 0 * (1 / c) ^ (1 / 2 : ℝ) := by
    intro y hy hyo
    have h1 := (enorm_poin_le X la P y).trans ((hC1 y hy hyo).trans
      (mul_le_mul_of_nonneg_left (supR_le X la W hc hcW 1 y) (zero_le)))
    have h2 : ENNReal.ofReal C1 * ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (max C1 0 * (1 / c) ^ (1 / 2 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ENNReal.ofReal_mul (le_max_right _ _)]
      gcongr
      exact le_max_left _ _
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans h2)
  refine ⟨?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hF r X x0 la W bb F P H, ?_, ?_⟩
  · intro x hx
    obtain ⟨ε, hε, u, hu, hub⟩ := hL r X x0 la W bb F P H x hx
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun γ => (hterm γ x).le.trans (hub γ x (Metric.mem_ball_self hε))) hu
  · unfold poin
    refine differentiableOn_tsum_loc (isOpenDom X) _ (fun γ => ?_) (fun x hx => ?_)
    · exact (differentiableOn_const _).mul
        (hP.1.comp (differentiable_lact γ.1).differentiableOn fun y hy => lactDom X γ.2 hy)
    · obtain ⟨ε, hε, u, hu, hub⟩ := hL r X x0 la W bb F P H x hx
      exact ⟨ε, hε, u, hu, fun γ y hy => (hterm γ y).le.trans (hub γ y hy)⟩
  · intro x hx b hb
    exact poin_rmul X la P hP.2 hx hb
  · intro γ hγ x _
    exact poin_lact X la P hγ x
  · refine ⟨max C1 0 * (1 / c) ^ (1 / 2 : ℝ), fun x hx => ?_⟩
    have hb := FrameDegreeData.bOf_mem X hx
    have ho : IsOrth X (rmul x (FrameDegreeData.bOf X x)) := FrameDegreeData.ortho_bOf X hx
    have hxb : rmul x (FrameDegreeData.bOf X x) ∈ X.dom := rmulDom X hb hx
    rw [← FrameDegreeData.pnorm_rmul X la _ (fun y hy b hb => poin_rmul X la P hP.2 hy hb) x hx _ hb,
      pnorm_orth' X la _ ho]
    exact horth _ hxb ho
  · intro ρ hρ hρ1
    obtain ⟨C, hC⟩ := hB r X x0 la W bb F P H ρ hρ hρ1
    exact ⟨C, fun x hx hxo => (enorm_poin_le X la P x).trans (hC x hx hxo)⟩
  · intro la' g hg x hx
    exact poin_mul X la la' P g hg x hx

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem countable_Γ (X : Data E r) : Countable X.Γ := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Function.Injective.countable (f := (Units.val : GL (Fin r) E → Matrix (Fin r) (Fin r) E)) (fun _ _ h => Units.ext h)
  infer_instance

def Hg (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (bb : ℝ) (φ : Frame X.Ψ r → ℝ≥0∞)
    (γ : GL (Fin r) E) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  (lact γ⁻¹ ⁻¹' Sset X x0 FF).indicator (fun y => ENNReal.ofReal (kap X x0 bb y) * φ y) x

theorem meas_Hg (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : MeasurableSet FF) (bb : ℝ) {φ : Frame X.Ψ r → ℝ≥0∞} (hφ : Measurable φ) (γ : GL (Fin r) E) :
    Measurable (Hg X x0 FF bb φ γ) :=
  ((meas_kap X x0 bb).ennreal_ofReal.mul hφ).indicator ((cont_lact X γ⁻¹).measurable (meas_S X ho hFF))

theorem Hg_rmul (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (bb : ℝ) {φ : Frame X.Ψ r → ℝ≥0∞}
    (hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) (γ : GL (Fin r) E) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    Hg X x0 FF bb φ γ (rmul x b) = Hg X x0 FF bb φ γ x := by
  classical
  simp only [Hg, Set.indicator_apply, Set.mem_preimage, lact_rmul', rmul_mem_S X hb,
    kap_rmul X x0 x bb hb, hφB x hx b hb]

private lemma lact_inv_lact_self {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ⁻¹ (lact γ x) = x := by
  funext τ
  have h : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (γ : Matrix (Fin r) (Fin r) E) = 1 := by
    simp
  show ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * Matrix.of (x τ)) = x τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero τ.1) (map_one τ.1),
    Matrix.one_mul]
  rfl

theorem Hg_lact_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (FF : Set (V (nd X))) (bb : ℝ)
    {φ : Frame X.Ψ r → ℝ≥0∞} (hφΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Hg X x0 FF bb φ γ (lact γ (cpt X x0 z)) =
      FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ (cpt X x0 z))) * φ (cpt X x0 z)) z := by
  classical
  rw [Hg, Set.indicator_apply, Set.mem_preimage, lact_lact, inv_mul_cancel, lact_one, cpt_mem_S X ho,
    hφΓ γ hγ _ hz, Set.indicator_apply]

theorem cover (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} (hFF : IsFundSet X x0 FF) :
    ∀ᵐ z ∂muF X x0, ∃ γ ∈ X.Γ, lact γ⁻¹ (cpt X x0 z) ∈ Sset X x0 FF := by
  obtain ⟨-, -, -, h⟩ := hFF
  filter_upwards [h] with z hz
  obtain ⟨z', hz', γ, hγ, b, hb, he⟩ := hz
  exact ⟨γ, hγ, ⟨(z', b), ⟨hz', hb⟩, by rw [he, lact_inv_lact_self]⟩⟩

theorem kaUnfold_of (hMI : MeasInvStatement (E := E)) (hSB : SumBoundStatement) :
    KaUnfoldStatement (E := E) := by
  intro r X x0 ho hPD FF hFF bb hbb
  obtain ⟨C, hC, hCb⟩ := sum_bound hSB X ho hPD bb hbb
  have := countable_Γ X
  refine ⟨C, hC, fun φ hφ hφB hφΓ => ?_⟩
  have hae : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := ExtFPf.ae_OmF (X := X) (x0 := x0)
  have hT := (cont_cpt X x0).measurable
  have hI : ∀ γ : X.Γ, Measurable fun z => FF.indicator
      (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) * φ (cpt X x0 z)) z := fun γ =>
    ((meas_kap X x0 bb).comp ((cont_lact X γ.1).comp (cont_cpt X x0)).measurable).ennreal_ofReal.mul
      (hφ.comp hT) |>.indicator hFF.1
  have step1 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 ≤
      ∫⁻ z, ∑' γ : X.Γ, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 := by
    refine lintegral_mono_ae ((hae.and (cover X hFF)).mono fun z ⟨hz, γ, hγ, hS⟩ => ?_)
    rw [kaF_eq X ho bb hz]
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : X.Γ))
    rw [Hg, Set.indicator_of_mem (show cpt X x0 z ∈ lact γ⁻¹ ⁻¹' Sset X x0 FF from hS)]
  have step2 : ∫⁻ z, ∑' γ : X.Γ, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 =
      ∑' γ : X.Γ, ∫⁻ z, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 :=
    lintegral_tsum fun γ => ((meas_Hg X ho hFF.1 bb hφ γ.1).comp hT).aemeasurable
  have step3 : ∀ γ : X.Γ, ∫⁻ z, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) *
        φ (cpt X x0 z)) z ∂muF X x0 := by
    intro γ
    rw [hMI r X x0 (lact γ.1 x0) ho (isOrth_lact X γ.2 ho) (Hg X x0 FF bb φ γ.1)
      (meas_Hg X ho hFF.1 bb hφ γ.1) (fun x hx b hb => Hg_rmul X x0 FF bb hφB γ.1 hx hb),
      muF_lact X γ.2]
    refine lintegral_congr_ae (hae.mono fun z hz => ?_)
    show Hg X x0 FF bb φ γ.1 (cpt X (lact γ.1 x0) z) = _
    rw [cpt_lact, Hg_lact_cpt X ho FF bb hφΓ γ.2 hz]
  have step4 : ∑' γ : X.Γ, ∫⁻ z, FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) *
        φ (cpt X x0 z)) z ∂muF X x0 ≤ ∫⁻ z in FF, C * φ (cpt X x0 z) ∂muF X x0 := by
    rw [← lintegral_tsum fun γ => (hI γ).aemeasurable, ← lintegral_indicator hFF.1]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ FF
    · simp only [Set.indicator_of_mem hz]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul_left (hCb z (hFF.2.1 hz)) _
    · simp [Set.indicator_of_notMem hz]
  calc ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0
      ≤ ∑' γ : X.Γ, ∫⁻ z, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 := step1.trans_eq step2
    _ = ∑' γ : X.Γ, ∫⁻ z, FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) *
        φ (cpt X x0 z)) z ∂muF X x0 := tsum_congr step3
    _ ≤ ∫⁻ z in FF, C * φ (cpt X x0 z) ∂muF X x0 := step4
    _ = C * ∫⁻ z in FF, φ (cpt X x0 z) ∂muF X x0 := lintegral_const_mul C (hφ.comp hT)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem kaUnfold_of (hMI : MeasInvStatement (E := E)) (hSB : SumBoundStatement) :
    KaUnfoldStatement (E := E) := KU.kaUnfold_of hMI hSB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
