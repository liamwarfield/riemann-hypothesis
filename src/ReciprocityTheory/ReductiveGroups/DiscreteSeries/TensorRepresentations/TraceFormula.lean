module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Decomp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaH
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaM
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaL
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaI
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_ph_inj (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {y : D} (hyG : y ∈ genSub E V) (hy0 : (y : H) ≠ 0) {g0 : Fin n → D} (hg0m : g0 ∈ tensSub (genSub E V))
    (h0 : tfPh dual ε σ (y : H) (fun i => ((g0 i : D) : H)) = 0) : g0 = 0 := by
  have hyC : (y : H) ∈ closGen E V := Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩
  have hcoeC : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c : Fin n, ((f c : D) : H) ∈ closGen E V :=
    fun f hf c => Submodule.le_topologicalClosure _ ⟨f c, (tset_mem.1 hf) c, rfl⟩
  set f2 : Fin n → D := fun c => tfSgn ε c • g0 c with hf2
  have hf2m : f2 ∈ tensSub (genSub E V) := by
    rw [tset_mem]; intro c; exact Submodule.smul_mem _ _ ((tset_mem.1 hg0m) c)
  have hT2b := tensor_functor_separation dual hσ hD hgap hV hc hVK hd hyC (hcoeC _ hf2m) (hcoeC _ hg0m)
    (tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hf2m) (tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hg0m)
  rw [h0, map_zero, inner_zero_right] at hT2b
  have hform : tfFormBH ε (fun i => ((f2 i : D) : H)) (fun i => ((g0 i : D) : H)) =
      ((∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) : ℂ) := by
    unfold tfFormBH
    push_cast
    refine sum_congr rfl fun c _ => ?_
    rw [hf2]
    simp only [Submodule.coe_smul, inner_smul_left, ← mul_assoc, inner_self_eq_norm_sq_to_K]
    rw [show (starRingEnd ℂ) (tfSgn ε c) = tfSgn ε c from tf_star_sgn ε c, tfSgn_mul_self, one_mul]
    rfl
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  have hN0 : inner ℂ (y : H) (y : H) ≠ 0 := inner_self_ne_zero.2 hy0
  rw [hform] at hT2b
  have hs0 : (∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) = 0 := by
    have h1 : ((∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) : ℂ) = 0 := by
      have h2 := hT2b.symm
      rw [mul_div_assoc] at h2
      exact (mul_eq_zero.1 h2).resolve_right (div_ne_zero hN0 hd0)
    exact_mod_cast h1
  funext c
  have h1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖((g0 i : D) : H)‖)).1 hs0 c (mem_univ _)
  have h2 : ((g0 c : D) : H) = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  exact Subtype.ext h2

theorem tf_trace_core (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c0 : ℂ} (hc0 : ∀ x ∈ genSub E V, ptr P x = c0 • x) {y : D} (hyV : y ∈ V) (hy0 : (y : H) ≠ 0) :
    ∃ r : ℝ, 0 ≤ r ∧ c0 = r ∧ (c0 = 0 → ∀ b, P (Pi.single b y) = 0) := by
  obtain ⟨d, hd⟩ := tfClRep_fdeg hgap hσ hD hV hc hVK (tf_sqInt_of_hW hσ hD hgap hV hc hVK hW)
  obtain ⟨HP, w, -, hHPeq, -, hrep, hc0eq⟩ :=
    tf_trace_data dual hσ hD hsm hgap hV hc hVK hW hP hPP hPB hEP hc0 hyV hy0 hd
  have hdpos : 0 < d := hd.1
  refine ⟨(∑ c, ‖w c‖ ^ 2) / d, div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) hdpos.le, hc0eq, fun h0 b => ?_⟩
  have hT0 : ∑ c, ‖w c‖ ^ 2 = 0 := by
    rw [h0] at hc0eq
    have h1 : (∑ c, ‖w c‖ ^ 2) / d = 0 := by exact_mod_cast hc0eq.symm
    exact (div_eq_zero_iff.1 h1).resolve_right hdpos.ne'
  have hw0 : ∀ c, w c = 0 := by
    intro c
    have h1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖w i‖)).1 hT0 c (mem_univ _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  have hHP0 : ∀ v ∈ HP, v = 0 := by
    intro v hv
    refine vectorL2_ext fun c => ?_
    have h1 := hrep v hv c
    simp only [hw0, inner_zero_left] at h1
    exact Lp.ext (h1.trans (Lp.coeFn_zero ℂ 2 (Formalism.REAL.muG ε)).symm)
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  have hsing : (Pi.single b y : Fin n → D) ∈ tensSub (genSub E V) := by
    simpa using tf_single_smul_mem b (1 : ℂ) hyG
  have hmemHP : tfPh dual ε σ (y : H) (fun i => ((P (Pi.single b y) i : D) : H)) ∈ HP := by
    rw [hHPeq]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, hsing, rfl⟩)
  exact tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hyG hy0 (hP.1 _ hsing) (hHP0 _ hmemHP)

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaJ
noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

theorem tf_ge_abstract {n : ℕ} {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (HP H' : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))) (hH'c : IsClosed (H' : Set (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))))
    (hH'P : H' ≤ HP) (hH'st : ∀ g, ∀ v ∈ H', ρ g v ∈ H') (hH'0 : H' ≠ ⊥)
    (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (hrep : ∀ v ∈ HP, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v))
    {d' : ℝ} (hd' : 0 < d')
    (hschur : ∀ x ∈ H', ∀ v ∈ H', ∫ g, ‖inner ℂ x (ρ g v)‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖v‖ ^ 2 / d') :
    d' ≤ ∑ c, ‖w c‖ ^ 2 ∧ (∑ c, ‖w c‖ ^ 2 = d' → HP ≤ H') := by
  have : CompleteSpace H' := hH'c.completeSpace_coe
  set Pw : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) := fun c => H'.starProjection (w c) with hPw
  have hPwm : ∀ c, Pw c ∈ H' := fun c => H'.starProjection_apply_mem (w c)
  have horth : ∀ c, ∀ y ∈ H', inner ℂ (w c - Pw c) y = 0 := fun c y hy =>
    H'.starProjection_inner_eq_zero (w c) y hy
  have hinnerP : ∀ c, ∀ y ∈ H', inner ℂ (w c) y = inner ℂ (Pw c) y := fun c y hy => by
    have := horth c y hy
    rwa [inner_sub_left, sub_eq_zero] at this
  have hpyth : ∀ c, ‖w c‖ ^ 2 = ‖Pw c‖ ^ 2 + ‖w c - Pw c‖ ^ 2 := fun c => by
    have h0 : inner ℂ (Pw c) (w c - Pw c) = 0 := by
      rw [← inner_conj_symm, horth c _ (hPwm c), map_zero]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Pw c) (w c - Pw c) h0
    rw [add_sub_cancel] at this
    simp only [sq]; linarith
  have hL2 : ∀ f : Lp ℂ 2 μ, ‖f‖ ^ 2 = ∫ g, ‖(f : G → ℂ) g‖ ^ 2 ∂μ := fun f => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def,
      ← integral_re (MeasureTheory.L2.integrable_inner f f)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ((f : G → ℂ) g)
  have hcomp : ∀ v ∈ H', ∀ c, ‖v c‖ ^ 2 = ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := fun v hv c => by
    rw [hL2, ← hschur (Pw c) (hPwm c) v hv]
    refine integral_congr_ae ?_
    filter_upwards [hrep v (hH'P hv) c] with g hg
    rw [hg, hinnerP c _ (hH'st g v hv)]
  have hkey : ∀ v ∈ H', ‖v‖ ^ 2 = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := fun v hv => by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Lp ℂ 2 μ) v
    calc ‖v‖ ^ 2 = ∑ c, ‖v c‖ ^ 2 := h
      _ = ∑ c, ‖Pw c‖ ^ 2 * ‖v‖ ^ 2 / d' := Finset.sum_congr rfl fun c _ => hcomp v hv c
      _ = (∑ c, ‖Pw c‖ ^ 2) * ‖v‖ ^ 2 / d' := by rw [Finset.sum_mul, Finset.sum_div]
  obtain ⟨v0, hv0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH'0
  have hsum : ∑ c, ‖Pw c‖ ^ 2 = d' := by
    have h := hkey v0 hv0
    have hn : ‖v0‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
    field_simp at h
    nlinarith [h, hn, sq_nonneg ‖v0‖]
  refine ⟨hsum ▸ Finset.sum_le_sum fun c _ => by rw [hpyth c]; nlinarith [sq_nonneg ‖w c - Pw c‖], fun heq => ?_⟩
  have hwc : ∀ c, w c ∈ H' := by
    have h0 : ∑ c, ‖w c - Pw c‖ ^ 2 = 0 := by
      have := congrArg (fun t => t - d') heq
      simp only [sub_self] at this
      rw [← this, ← hsum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [hpyth c]; ring
    intro c
    have := (Finset.sum_eq_zero_iff_of_nonneg fun c _ => sq_nonneg ‖w c - Pw c‖).mp h0 c (Finset.mem_univ c)
    have h1 : w c - Pw c = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    rw [sub_eq_zero.mp h1]; exact hPwm c
  have hadj : ∀ g (a b : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), inner ℂ a (ρ g b) = inner ℂ (ρ g⁻¹ a) b := fun g a b => by
    let L : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗᵢ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) :=
      ⟨(ρ g : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)), hiso g⟩
    have e : ρ g (ρ g⁻¹ a) = a := by
      rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
    conv_lhs => rw [← e]
    exact L.inner_map_map _ _
  intro v hv
  set u := v - H'.starProjection v with hu
  have huP : u ∈ HP := HP.sub_mem hv (hH'P (H'.starProjection_apply_mem v))
  have hu0 : ∀ c, ((u c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] 0 := fun c => by
    filter_upwards [hrep u huP c] with g hg
    rw [hg, hadj, Pi.zero_apply]
    have := H'.starProjection_inner_eq_zero v _ (hH'st g⁻¹ _ (hwc c))
    rw [← inner_conj_symm, this, map_zero]
  have hu' : u = 0 := by
    refine (WithLp.ofLp_injective 2).eq_iff.mp ?_
    funext c
    exact Lp.eq_zero_iff_ae_eq_zero.mpr (hu0 c)
  have : v = H'.starProjection v := sub_eq_zero.mp hu'
  rw [this]; exact H'.starProjection_apply_mem v

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaK
noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

theorem tf_schur_transfer {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
    (S₁ : Submodule ℂ H₁) [S₁.HasOrthogonalProjection] (S₂ : Submodule ℂ H₂) (U : S₁ ≃ₗᵢ[ℂ] S₂)
    (hU : ∀ g ∈ UJset ε, ∀ x y : S₁, (x : H₁) = σ₁ g (y : H₁) → ((U x : S₂) : H₂) = σ₂ g ((U y : S₂) : H₂))
    (hS₁ : ∀ g ∈ UJset ε, ∀ x ∈ S₁, σ₁ g x ∈ S₁) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ₁ S₁) d) :
    ∀ x ∈ S₂, ∀ v ∈ S₂, ∫ g : Formalism.REAL.UJ ε, ‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 ∂(Formalism.REAL.muG ε) =
      ‖x‖ ^ 2 * ‖v‖ ^ 2 / d := by
  intro x hx v hv
  set x1 : S₁ := U.symm ⟨x, hx⟩ with hx1
  set v1 : S₁ := U.symm ⟨v, hv⟩ with hv1
  have ex : ((U x1 : S₂) : H₂) = x := by rw [hx1, LinearIsometryEquiv.apply_symm_apply]
  have ev : ((U v1 : S₂) : H₂) = v := by rw [hv1, LinearIsometryEquiv.apply_symm_apply]
  have hcoef : ∀ g : Formalism.REAL.UJ ε, inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g := by
    intro g
    have hg := umat_mem_UJset ε g
    set y : S₁ := ⟨σ₁ (Formalism.MainNotions.S.umat g) (v1 : H₁), hS₁ _ hg _ v1.2⟩ with hy
    have h1 := hU _ hg y v1 rfl
    rw [← ex, ← ev, ← h1, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    show inner ℂ x1 y = inner ℂ x1 (tfClRep σ₁ S₁ (Formalism.MainNotions.S.umat g) v1)
    congr 1
    exact Subtype.ext (tfClRep_coe σ₁ S₁ (hS₁ _ hg) v1).symm
  obtain ⟨-, hint, hval⟩ := hd.1, (hd.2 v1 x1 v1 x1).1, (hd.2 v1 x1 v1 x1).2
  have hnx : ‖x‖ = ‖x1‖ := by rw [← ex]; exact U.norm_map x1
  have hnv : ‖v‖ = ‖v1‖ := by rw [← ev]; exact U.norm_map v1
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ g : Formalism.REAL.UJ ε, ((‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 : ℝ) : ℂ) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g * star (Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g) := by
    intro g
    rw [hcoef, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  have h1 : inner ℂ v1 v1 = ((‖v1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h2 : inner ℂ x1 x1 = ((‖x1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hval, h1, h2, hnx, hnv]
  push_cast
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tf_kstable_fin (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V0 : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V0) (hVK : IsKStableSub ε E V0) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {v : D} (hv : v ∈ V0) : σ k (v : H) ∈ V0.map D.subtype := by
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hk
  have hE := hD.glRep
  have hv0 : v ∈ layer ε E V0 0 := hv
  obtain ⟨C, _, hC⟩ := exists_norm_actM_pow_le_of_inK hE hVK hVf hZ 0
  have hs : Summable fun m : ℕ => C ^ m * ‖v‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_right ‖v‖
    refine this.congr fun m => ?_
    simp only [sub_zero, abs_one, one_pow, mul_one]
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖) (fun m => hC v hv0 m) 0 1 hs
  rw [exp_zero_smul, hσ.1.1] at hsum
  simp only [Complex.ofReal_one, one_smul, one_apply_eq_self] at hsum
  have : FiniteDimensional ℂ (V0.map D.subtype) := Module.Finite.map _ _
  have hcl : IsClosed ((V0.map D.subtype : Submodule ℂ H) : Set H) := Submodule.isClosed_of_finiteDimensional _
  refine hcl.mem_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  exact Submodule.mem_map_of_mem (actM_pow_mem_layer_of_inK hE hVK hZ hv0 m)

theorem tf_tensGrp_kDiag (dual : Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ k f = kDiag dual σ k f := by
  have hu : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hu
  funext c
  simp only [tensGrp, kDiag, hinv, Matrix.conjTranspose_apply]

theorem tf_kirr_map {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    {E₁ : Fin n → Fin n → Module.End ℂ M} {E₂ : Fin n → Fin n → Module.End ℂ M'} {Λ : Fin n → ℝ}
    {V : Submodule ℂ M} (hV : IsKIrrHW ε E₁ Λ V) (Ψ : M →ₗ[ℂ] M')
    (hΨ : ∀ a b, ∀ x ∈ V, Ψ (E₁ a b x) = E₂ a b (Ψ x)) (hinj : ∀ x ∈ V, Ψ x = 0 → x = 0) :
    IsKIrrHW ε E₂ Λ (V.map Ψ) := by
  have := hV.1
  refine ⟨Module.Finite.map _ _, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨x, hx, rfl⟩
    exact ⟨E₁ a b x, hV.2.1 a b hab x hx, hΨ a b x hx⟩
  · intro S' hS' hst
    have hT : IsKStableSub ε E₁ (S'.comap Ψ ⊓ V) := by
      rintro a b hab x ⟨hx1, hx2⟩
      refine ⟨?_, hV.2.1 a b hab x hx2⟩
      show Ψ (E₁ a b x) ∈ S'
      rw [hΨ a b x hx2]
      exact hst a b hab _ hx1
    rcases hV.2.2.1 _ inf_le_right hT with h | h
    · left
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨x, hx, rfl⟩ := hS' hs
      have hx0 : x ∈ S'.comap Ψ ⊓ V := ⟨hs, hx⟩
      rw [h, Submodule.mem_bot] at hx0
      rw [hx0, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ S'.comap Ψ ⊓ V := by rw [h]; exact hx
      exact hx'.1
  · obtain ⟨w, hwV, hw0, hw1, hw2⟩ := hV.2.2.2
    refine ⟨Ψ w, ⟨w, hwV, rfl⟩, fun h => hw0 (hinj w hwV h), fun a => ?_, fun a b hab h => ?_⟩
    · rw [← hΨ a a w hwV, hw1 a, map_smul]
    · rw [← hΨ a b w hwV, hw2 a b hab h, map_zero]

theorem tf_kfin_tens (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) :
    ∃ W : Submodule ℂ (Fin n → D), FiniteDimensional ℂ W ∧ f ∈ W ∧ W ≤ tensSub (genSub E V) ∧
      ∀ k ∈ Kset ε, ∀ w ∈ W, ∃ w' ∈ W,
        (fun c => ((w' c : D) : H)) = kDiag dual σ k (fun c => ((w c : D) : H)) := by
  have hE := hD.glRep
  have hmono : Monotone (layer ε E V) := fun k l hkl => layer_mono hkl
  have hlay : ∀ c, ∃ m, f c ∈ layer ε E V m := fun c => by
    have h1 := (tset_mem.1 hf) c
    rw [genSub_eq_iSup_layer hE hVk] at h1
    exact (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 h1
  choose m hm using hlay
  set M := Finset.univ.sup m with hM
  have hfM : ∀ c, f c ∈ layer ε E V M := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hLf : FiniteDimensional ℂ (layer ε E V M) := finiteDimensional_layer hVf M
  have hLk : IsKStableSub ε E (layer ε E V M) := layer_kStable hE hVk M
  refine ⟨tensSub (layer ε E V M), ?_, tset_mem.2 hfM,
    fun w hw => tset_mem.2 fun c => layer_le_genSub M ((tset_mem.1 hw) c), ?_⟩
  · exact Module.Finite.of_injective (LinearMap.pi fun c => LinearMap.codRestrict (layer ε E V M)
      ((LinearMap.proj c : (Fin n → D) →ₗ[ℂ] D) ∘ₗ (tensSub (layer ε E V M)).subtype) fun f => tset_mem.mp f.2 c)
      (fun f f' h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  · intro k hk w hw
    have hu : ∀ d, ∃ u ∈ layer ε E V M, (u : H) = σ k ((w d : D) : H) := fun d => by
      obtain ⟨u, hu, e⟩ := tf_kstable_fin hσ hD hLf hLk hk ((tset_mem.1 hw) d)
      exact ⟨u, hu, e⟩
    choose u hu hue using hu
    refine ⟨fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • u d,
      tset_mem.2 fun c => Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hu d), ?_⟩
    funext c
    simp only [kDiag, Submodule.coe_sum, Submodule.coe_smul, hue]

section Datum

variable [CompleteSpace H]

theorem tf_phi (dual : Bool) {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {y : D} (hy : y ∈ genSub E V) :
    ∃ Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε),
      (∀ f, ((Φ f : smD ε (tfRdiag ε)) : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H))) ∧
      ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Φ f) =
        Φ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := by
  have hce := fun c f hf => coef_embed dual hσ hD hsm hgap hV hc hVK hW _
    (tf_single_smul_mem c (tfSgn ε c) hy) f hf
  simp only [tf_coe_single] at hce
  let Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε) :=
    { toFun := fun f => ⟨tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H)),
        tfRdiag_smooth fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1⟩
      map_add' := fun f f' => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_add_smooth ε ((hce c f.1 f.2).1.2 []) ((hce c f'.1 f'.2).1.2 []))
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, sum_add_distrib])
      map_smul' := fun a f => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_smul_smooth ε a _)
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        cases dual <;> simp [coefMap, tensGrp, ← smul_comm a, ← Finset.smul_sum, mul_sum]) }
  refine ⟨Φ, fun f => rfl, fun a b f => Subtype.ext (vectorL2_ext fun c => ?_)⟩
  refine (tfRdiag_smE (fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1) a b c).trans ?_
  refine (rightDerivative_toL2 (hce c f.1 f.2).1 a b).trans (toL2_congr_of_eq_on_UJset fun g hg => ?_)
  exact (hce c f.1 f.2).2.1 a b g hg

end Datum

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tf_datum2 (dual : Bool) {lam lam' : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) {y : D} (hy : y ∈ genSub E V)
    (hy0 : (y : H) ≠ 0) {V' : Submodule ℂ D} (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι) :
    ∃ V₂ : Submodule ℂ (smD ε (tfRdiag ε)), IsKIrrHW ε (smE ε (tfRdiag ε)) (lowK ε lam') V₂ ∧
      (∀ v ∈ V₂, casimir (smE ε (tfRdiag ε)) v = (casVal lam' : ℂ) • v) ∧
      (∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : tfL2n ε) = tfRdiag ε k v) ∧ V₂ ≠ ⊥ ∧
      (∀ v ∈ genSub (smE ε (tfRdiag ε)) V₂, ∃ x ∈ genSub E V',
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H))) ∧
      (∀ x ∈ genSub E V', ∃ v ∈ genSub (smE ε (tfRdiag ε)) V₂,
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H))) := by
  obtain ⟨Φ, hΦ, hΦE⟩ := tf_phi dual hσ hD hsm hgap hV hc hVK hW hy
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (tensSub (n := n) (genSub E V))
  let π := Submodule.projectionOnto _ q hq
  let Ψ : D →ₗ[ℂ] smD ε (tfRdiag ε) := Φ ∘ₗ π ∘ₗ ι
  have hΨ : ∀ x (hx : x ∈ genSub E V'), Ψ x = Φ ⟨ι x, hι.1 x hx⟩ := by
    intro x hx
    show Φ (π (ι x)) = _
    congr 1
    exact Submodule.projectionOnto_apply_left hq ⟨ι x, hι.1 x hx⟩
  have hΨc : ∀ x ∈ genSub E V', (Ψ x : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)) :=
    fun x hx => by rw [hΨ x hx, hΦ]
  have hΨE : ∀ a b, ∀ x ∈ genSub E V', Ψ (E a b x) = smE ε (tfRdiag ε) a b (Ψ x) := by
    intro a b x hx
    rw [hΨ _ (tset_genSub_E E V' a b hx), hΨ x hx, hΦE]
    congr 1
    exact Subtype.ext (hι.2.2.1 a b x hx)
  have hV'le : V' ≤ genSub E V' := fun x hx => Submodule.mem_sInf.mpr fun _ hT => hT.1 hx
  have hinj : ∀ x ∈ genSub E V', Ψ x = 0 → x = 0 := by
    intro x hx h
    have h1 : tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)) = 0 := by
      rw [← hΨc x hx, h]; rfl
    exact hι.2.1 x hx (tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hy hy0 (hι.1 x hx) h1)
  have hK2 := tf_kirr_map hV' Ψ (fun a b x hx => hΨE a b x (hV'le hx)) (fun x hx => hinj x (hV'le hx))
  refine ⟨V'.map Ψ, hK2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxG := hV'le hx
    have e : casimir (smE ε (tfRdiag ε)) (Ψ x) = Ψ (casimir E x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hΨE a b _ (tset_genSub_E E V' b a hxG), hΨE b a x hxG]
    rw [e, hc' x hx, map_smul]
  · rintro k hk _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hxx'⟩ := hVK' k hk x hx
    refine ⟨Ψ x', ⟨x', hx', rfl⟩, ?_⟩
    have hk' : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
    rw [hΨc x' (hV'le hx'), hΨc x (hV'le hx), tfRdiag_tfPh dual hσ hk', tf_tensGrp_kDiag dual hk,
      ← hι.2.2.2 k hk x (hV'le hx) x' (hV'le hx') hxx']
  · intro h
    obtain ⟨w, hw, hw0, -⟩ := hK2.2.2.2
    apply hw0
    have hwb : w ∈ (⊥ : Submodule ℂ (smD ε (tfRdiag ε))) := h ▸ hw
    exact (Submodule.mem_bot ℂ).1 hwb
  · intro v hv
    have hle : genSub (smE ε (tfRdiag ε)) (V'.map Ψ) ≤ (genSub E V').map Ψ := by
      refine sInf_le ⟨Submodule.map_mono hV'le, ?_⟩
      rintro a b _ ⟨x, hx, rfl⟩
      exact ⟨E a b x, tset_genSub_E E V' a b hx, hΨE a b x hx⟩
    obtain ⟨x, hx, rfl⟩ := hle hv
    exact ⟨x, hx, hΨc x hx⟩
  · intro x hx
    have hle : genSub E V' ≤ (genSub (smE ε (tfRdiag ε)) (V'.map Ψ)).comap Ψ ⊓ genSub E V' := by
      refine sInf_le ⟨fun z hz => ⟨Submodule.mem_sInf.mpr fun _ hT => hT.1 ⟨z, hz, rfl⟩, hV'le hz⟩, ?_⟩
      rintro a b z ⟨hz1, hz2⟩
      refine ⟨?_, tset_genSub_E E V' a b hz2⟩
      show Ψ (E a b z) ∈ genSub (smE ε (tfRdiag ε)) (V'.map Ψ)
      rw [hΨE a b z hz2]
      exact tset_genSub_E _ _ a b hz1
    exact ⟨Ψ x, (hle hx).1, hΨc x hx⟩

theorem tf_eq_case (dual : Bool) {lam lam' : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) {y : D} (hy : y ∈ genSub E V)
    (hy0 : (y : H) ≠ 0) {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)} (hι : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hgap' : StdGap ε lam') {V₂ : Submodule ℂ (smD ε (tfRdiag ε))}
    (hV₂ : IsKIrrHW ε (smE ε (tfRdiag ε)) (lowK ε lam') V₂)
    (hc₂ : ∀ v ∈ V₂, casimir (smE ε (tfRdiag ε)) v = (casVal lam' : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : tfL2n ε) = tfRdiag ε k v)
    (hgen : ∀ v ∈ genSub (smE ε (tfRdiag ε)) V₂, ∃ x ∈ genSub E V',
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)))
    (hin : ∀ f ∈ tensSub (genSub E V),
      tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H)) ∈ closGen (smE ε (tfRdiag ε)) V₂) :
    ∀ f ∈ tensSub (genSub E V), ∃ x ∈ genSub E V', P f = ι x := by
  obtain ⟨Φ, hΦ, -⟩ := tf_phi dual hσ hD hsm hgap hV hc hVK hW hy
  intro f hf
  obtain ⟨W, hWf, hfW, hWle, hWK⟩ := tf_kfin_tens dual hσ hD hV.1 hV.2.1 hf
  let P' : Module.End ℂ (tensSub (n := n) (genSub E V)) := P.restrict hP.1
  let W' : Submodule ℂ (tensSub (n := n) (genSub E V)) := W.comap (tensSub (genSub E V)).subtype
  have hW'f : FiniteDimensional ℂ W' := Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hWle).symm
  let S0 : Submodule ℂ (tfL2n ε) := W'.map ((smD ε (tfRdiag ε)).subtype ∘ₗ Φ ∘ₗ P')
  have hS0v : ∀ w : tensSub (n := n) (genSub E V),
      ((smD ε (tfRdiag ε)).subtype ∘ₗ Φ ∘ₗ P') w = tfPh dual ε σ (y : H) (fun c => ((P w.1 c : D) : H)) :=
    fun w => hΦ (P' w)
  have hS0 : S0 ≤ closGen (smE ε (tfRdiag ε)) V₂ := by
    rintro _ ⟨w, -, rfl⟩
    rw [hS0v]
    exact hin w.1 w.2
  have hS0f : FiniteDimensional ℂ S0 := Module.Finite.map _ _
  have hS0K : ∀ k ∈ Kset ε, ∀ x ∈ S0, tfRdiag ε k x ∈ S0 := by
    rintro k hk _ ⟨w, hw, rfl⟩
    obtain ⟨w', hw', hww'⟩ := hWK k hk w.1 hw
    refine ⟨⟨w', hWle hw'⟩, hw', ?_⟩
    rw [hS0v, hS0v, tfRdiag_tfPh dual hσ (closure_inUJ_of_mem_Kset hk), tf_tensGrp_kDiag dual hk,
      hP.2.2 k hk w.1 w.2 w' (hWle hw') hww']
  have hkf := data_kfin_le hgap' (tfRdiag_isURepOn ε) (isDerivedOn_smE (tfRdiag_isURepOn ε)) hV₂ hc₂ hVK₂
    S0 hS0 hS0f hS0K
  have hfS0 : tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H)) ∈ S0 :=
    ⟨⟨f, hf⟩, hfW, hS0v ⟨f, hf⟩⟩
  obtain ⟨v, hv, hve⟩ := hkf hfS0
  obtain ⟨x, hx, hxe⟩ := hgen v hv
  refine ⟨x, hx, ?_⟩
  have hd0 : (P f - ι x) ∈ tensSub (genSub E V) := Submodule.sub_mem _ (hP.1 f hf) (hι x hx)
  have e1 : Φ ⟨P f - ι x, hd0⟩ = Φ ⟨P f, hP.1 f hf⟩ - Φ ⟨ι x, hι x hx⟩ := by
    rw [← map_sub]; rfl
  have h0 : tfPh dual ε σ (y : H) (fun c => (((P f - ι x) c : D) : H)) = 0 := by
    calc tfPh dual ε σ (y : H) (fun c => (((P f - ι x) c : D) : H))
        = ((Φ ⟨P f - ι x, hd0⟩ : smD ε (tfRdiag ε)) : tfL2n ε) := (hΦ ⟨P f - ι x, hd0⟩).symm
      _ = ((Φ ⟨P f, hP.1 f hf⟩ : smD ε (tfRdiag ε)) : tfL2n ε) -
          ((Φ ⟨ι x, hι x hx⟩ : smD ε (tfRdiag ε)) : tfL2n ε) := by rw [e1, Submodule.coe_sub]
      _ = 0 := by
        rw [sub_eq_zero]
        exact ((hΦ ⟨P f, hP.1 f hf⟩).trans hve.symm).trans (hxe.trans (hΦ ⟨ι x, hι x hx⟩).symm)
  exact sub_eq_zero.1 (tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hy hy0 hd0 h0)

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

instance closGen_completeSpace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) : CompleteSpace (closGen E V) := by
  unfold closGen; infer_instance

def formB {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H} (ε : Fin n → Bool)
    (f g : Fin n → D) : ℂ :=
  ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((f c : D) : H) ((g c : D) : H)

theorem tfa_sign (ε : Fin n → Bool) (r s : Fin n) :
    (if ε s then (1 : ℂ) else -1) * adjSign ε r s = if ε r then (1 : ℂ) else -1 := by
  unfold adjSign
  rcases Bool.eq_false_or_eq_true (ε r) with h | h <;> rcases Bool.eq_false_or_eq_true (ε s) with h' | h' <;>
    simp [h, h']

theorem tfa_sign' (ε : Fin n → Bool) (r s : Fin n) :
    (if ε s then (1 : ℂ) else -1) * adjSign ε s r = if ε r then (1 : ℂ) else -1 := by
  unfold adjSign
  rcases Bool.eq_false_or_eq_true (ε r) with h | h <;> rcases Bool.eq_false_or_eq_true (ε s) with h' | h' <;>
    simp [h, h']

theorem tfa_inner_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    (x : Fin n → D) (y : D) : inner ℂ (((∑ r, x r : D)) : H) (y : H) = ∑ r, inner ℂ ((x r : D) : H) (y : H) := by
  rw [Submodule.coe_sum, sum_inner]

theorem tfa_inner_sum' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    (x : Fin n → D) (y : D) : inner ℂ (y : H) (((∑ r, x r : D)) : H) = ∑ r, inner ℂ (y : H) ((x r : D) : H) := by
  rw [Submodule.coe_sum, inner_sum]

section FormB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H} {ε : Fin n → Bool}

theorem formB_conj (f g : Fin n → D) : starRingEnd ℂ (formB ε f g) = formB ε g f := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [formB, map_sum, map_mul, inner_conj_symm]
  refine sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem formB_add_right (f g g' : Fin n → D) : formB ε f (g + g') = formB ε f g + formB ε f g' := by
  simp only [formB, Pi.add_apply, Submodule.coe_add, inner_add_right, mul_add, sum_add_distrib]

theorem formB_smul_right (f g : Fin n → D) (a : ℂ) : formB ε f (a • g) = a * formB ε f g := by
  simp only [formB, Pi.smul_apply, Submodule.coe_smul, inner_smul_right, mul_sum]
  refine sum_congr rfl fun c _ => by ring

theorem formB_smul_left (f g : Fin n → D) (a : ℂ) : formB ε (a • f) g = starRingEnd ℂ a * formB ε f g := by
  simp only [formB, Pi.smul_apply, Submodule.coe_smul, inner_smul_left, mul_sum]
  refine sum_congr rfl fun c _ => by ring

theorem formB_zero_right (f : Fin n → D) : formB ε f 0 = 0 := by
  simp [formB]

theorem formB_zero_left (f : Fin n → D) : formB ε 0 f = 0 := by
  simp [formB]

theorem formB_sub_right (f g g' : Fin n → D) : formB ε f (g - g') = formB ε f g - formB ε f g' := by
  simp only [formB, Pi.sub_apply, Submodule.coe_sub, inner_sub_right, mul_sub, sum_sub_distrib]

theorem formB_sum_right {ι : Type*} (s : Finset ι) (f : Fin n → D) (g : ι → Fin n → D) :
    formB ε f (∑ i ∈ s, g i) = ∑ i ∈ s, formB ε f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [formB_zero_right]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, formB_add_right, ih]

end FormB

def closRep {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (g : Matrix (Fin n) (Fin n) ℂ) : S →L[ℂ] S :=
  S.orthogonalProjectionOnto ∘L σ g ∘L S.subtypeL

theorem trace_nonneg (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c : ℂ} (hc : ∀ x ∈ genSub E V, ptr P x = c • x) :
    c.im = 0 ∧ 0 ≤ c.re ∧ (c = 0 → ∀ f ∈ tensSub (genSub E V), P f = 0) := by
  rename_i hcas
  have hPB' : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)) := hPB
  have hcore : ∀ y ∈ V, (y : H) ≠ 0 → ∃ r : ℝ, 0 ≤ r ∧ c = r ∧ (c = 0 → ∀ b, P (Pi.single b y) = 0) :=
    fun y hy hy0 => tf_trace_core dual hσ hD hsm hgap hV hcas hVK hW hP hPP hPB' hEP hc hy hy0
  obtain ⟨y0, hy0V, hy00, -⟩ := hV.2.2.2
  have hy0H : (y0 : H) ≠ 0 := fun h => hy00 (Subtype.ext h)
  obtain ⟨r, hr, hcr, -⟩ := hcore y0 hy0V hy0H
  refine ⟨by rw [hcr, Complex.ofReal_im], by rw [hcr, Complex.ofReal_re]; exact hr, fun h0 => ?_⟩
  have hV0 : ∀ y ∈ V, ∀ b, P (Pi.single b y) = 0 := by
    intro y hy b
    by_cases hyz : (y : H) = 0
    · have hy' : y = 0 := Subtype.ext hyz
      rw [hy', Pi.single_zero, map_zero]
    · obtain ⟨-, -, -, h⟩ := hcore y hy hyz
      exact h h0 b
  have hVt : ∀ f ∈ tensSub V, P f = 0 := by
    intro f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single f, map_sum]
    exact sum_eq_zero fun b _ => hV0 _ ((tset_mem.1 hf) b) b
  have hle : tensSub (genSub E V) ≤ tensSub (genSub E V) ⊓ LinearMap.ker P := by
    refine tfg_gen dual E V _ (fun f hf => ⟨tset_mem.2 fun b => rorth_le_genSub ((tset_mem.1 hf) b), hVt f hf⟩) ?_
    intro a b f hf
    refine ⟨tensSub_stable dual a b f hf.1, ?_⟩
    show P (tensF dual E a b f) = 0
    rw [hP.2.1 a b f hf.1, show P f = 0 from hf.2, map_zero]
  intro f hf
  exact (hle hf).2

theorem trace_ge (dual : Bool) {lam lam' : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {V' : Submodule ℂ D} (hgap' : StdGap ε lam') (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    (hSq : Formalism.MainNotions.S.IsSqIntOn ε (closRep σ (closGen E V)))
    (hSq' : Formalism.MainNotions.S.IsSqIntOn ε (closRep σ (closGen E V')))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c : ℂ} (hc : ∀ x ∈ genSub E V, ptr P x = c • x)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι)
    (hιP : ∀ x ∈ genSub E V', P (ι x) = ι x) {w : closGen E V} (hw : w ≠ 0) {w' : closGen E V'} (hw' : w' ≠ 0) :
    Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V')) w' /
              Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V)) w ≤ c.re ∧
      (c.re = Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V')) w' /
          Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V)) w →
        ∀ f ∈ tensSub (genSub E V), ∃ x ∈ genSub E V', P f = ι x) := by
  rename_i hcas
  have hPB' : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)) := hPB
  obtain ⟨d, hd⟩ := tfClRep_fdeg hgap hσ hD hV hcas hVK hSq
  obtain ⟨d', hd'⟩ := tfClRep_fdeg hgap' hσ hD hV' hc' hVK' hSq'
  have hfd : Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V)) w = d :=
    fdegOf_of_isFdeg' hd hw
  have hfd' : Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V')) w' = d' :=
    fdegOf_of_isFdeg' hd' hw'
  rw [hfd, hfd']
  obtain ⟨y0, hy0V, hy00, -⟩ := hV.2.2.2
  have hy0H : (y0 : H) ≠ 0 := fun h => hy00 (Subtype.ext h)
  have hy0G : y0 ∈ genSub E V := rorth_le_genSub hy0V
  obtain ⟨HP, wv, hHPc, hHPeq, hst, hrep, hc0eq⟩ :=
    tf_trace_data dual hσ hD hsm hgap hV hcas hVK hW hP hPP hPB' hEP hc hy0V hy0H hd
  obtain ⟨V₂, hV₂, hc₂, hVK₂, hV₂0, hgen1, -⟩ :=
    tf_datum2 dual hσ hD hsm hgap hV hcas hVK hW hd hy0G hy0H hV' hc' hVK' hι
  have hV'0 : V' ≠ ⊥ := by
    obtain ⟨u, hu, hu0, -⟩ := hV'.2.2.2
    intro h
    apply hu0
    have hub : u ∈ (⊥ : Submodule ℂ D) := h ▸ hu
    exact (Submodule.mem_bot ℂ).1 hub
  have hR := tfRdiag_isURepOn ε
  have hDR := isDerivedOn_smE hR
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap' hσ hD hV' hc' hVK' hV'0 hR hDR hV₂ hc₂ hVK₂ hV₂0
  have hschur := tf_schur_transfer (closGen E V') (closGen (smE ε (tfRdiag ε)) V₂) U hU
    (closGen_stable hgap' hσ hD hV' hc' hVK') hd'
  have hH'c : IsClosed ((closGen (smE ε (tfRdiag ε)) V₂ : Submodule ℂ (tfL2n ε)) : Set (tfL2n ε)) :=
    Submodule.isClosed_topologicalClosure _
  have hst2 := closGen_stable hgap' hR hDR hV₂ hc₂ hVK₂
  have hH'P : closGen (smE ε (tfRdiag ε)) V₂ ≤ HP := by
    refine Submodule.topologicalClosure_minimal _ ?_ hHPc
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hgen1 v hv
    rw [hHPeq]
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ι x, hι.1 x hx, ?_⟩)
    show (v : tfL2n ε) = _
    rw [hxe, hιP x hx]
  have hH'0 : closGen (smE ε (tfRdiag ε)) V₂ ≠ ⊥ := by
    obtain ⟨u, hu, hu0, -⟩ := hV₂.2.2.2
    intro h
    apply hu0
    have h1 : ((u : smD ε (tfRdiag ε)) : tfL2n ε) ∈ closGen (smE ε (tfRdiag ε)) V₂ :=
      Submodule.le_topologicalClosure _ ⟨u, Submodule.mem_sInf.mpr fun _ hT => hT.1 hu, rfl⟩
    have h2 : ((u : smD ε (tfRdiag ε)) : tfL2n ε) ∈ (⊥ : Submodule ℂ (tfL2n ε)) := h ▸ h1
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 h2)
  have hone : tfRdiag ε (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := hR.1.1
  have hmul : ∀ a b : Formalism.REAL.UJ ε, tfRdiag ε (Formalism.MainNotions.S.umat (a * b)) =
      (tfRdiag ε (Formalism.MainNotions.S.umat a)).comp (tfRdiag ε (Formalism.MainNotions.S.umat b)) := fun a b =>
    hR.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ (g : Formalism.REAL.UJ ε) v, ‖tfRdiag ε (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ := fun g v =>
    hR.2.1 _ (umat_mem_UJset ε g) v
  obtain ⟨hge, heq⟩ := tf_ge_abstract (μ := Formalism.REAL.muG ε) (fun g => tfRdiag ε (Formalism.MainNotions.S.umat g)) hone hmul hiso
    HP _ hH'c hH'P (fun g v hv => hst2 _ (umat_mem_UJset ε g) v hv) hH'0 wv hrep hd'.1 hschur
  have hdpos : 0 < d := hd.1
  have hre : c.re = (∑ i, ‖wv i‖ ^ 2) / d := by rw [hc0eq, Complex.ofReal_re]
  refine ⟨by rw [hre]; exact div_le_div_of_nonneg_right hge hdpos.le, fun h => ?_⟩
  have hT : ∑ i, ‖wv i‖ ^ 2 = d' := by
    rwa [hre, div_left_inj₀ hdpos.ne'] at h
  have hle := heq hT
  refine tf_eq_case dual hσ hD hsm hgap hV hcas hVK hW hd hy0G hy0H hP hι.1 hgap' hV₂ hc₂ hVK₂ hgen1 ?_
  intro f hf
  apply hle
  rw [hHPeq]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)

theorem eeF_formB_symm (dual : Bool) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (f g : Fin n → D) :
    formB ε (eeF dual E f) g = formB ε f (eeF dual E g) := by
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hU' : ∀ a b (x y : D), inner ℂ ((E a b x : D) : H) (y : H) = adjSign ε a b * inner ℂ (x : H) ((E b a y : D) : H) := by
    intro a b x y
    have := hU a b x y
    simpa only [Submodule.coe_inner] using this
  cases dual
  · simp only [formB, eeF, cond_false, eeV_coord, tfa_inner_sum, tfa_inner_sum', mul_sum, hU']
    rw [sum_comm]
    refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, tfa_sign]
  · simp only [formB, eeF, cond_true, eeVd_coord, Submodule.coe_neg, inner_neg_left, inner_neg_right,
      tfa_inner_sum, tfa_inner_sum', mul_neg, mul_sum, hU', sum_neg_distrib]
    rw [sum_comm]
    refine congrArg _ (sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_)
    rw [← mul_assoc, tfa_sign']

theorem eigenProj_formB (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (z : ℂ) {P : Module.End ℂ (Fin n → D)}
    (hPM : ∀ f ∈ tensSub (genSub E V), P f ∈ tensSub (genSub E V)) (hPz : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    (hP1 : ∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → P f = f)
    (hP0 : ∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → P f = 0) :
    ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g) := by
  obtain ⟨Bs, hdec, hreal⟩ := ee_decomp dual hσ hD hgap hV hc hVK hW
  have horth : ∀ x y : Fin n → D, ∀ a b : ℂ, a.im = 0 → eeF dual E x = a • x → eeF dual E y = b • y → a ≠ b →
      formB ε x y = 0 := by
    intro x y a b ha hx hy hab
    have h := eeF_formB_symm dual hσ hD (ε := ε) x y
    rw [hx, hy, formB_smul_left, formB_smul_right] at h
    have hca : starRingEnd ℂ a = a := Complex.conj_eq_iff_im.mpr ha
    rw [hca] at h
    have h2 : (a - b) * formB ε x y = 0 := by rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hab
    · exact h3
  have hL : ∀ f ∈ tensSub (genSub E V), ∀ h ∈ tensSub (genSub E V), formB ε (P f) (h - P h) = 0 := by
    intro f hf h hh
    obtain ⟨hb, hbe, rfl⟩ := hdec h hh
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← sum_sub_distrib, formB_sum_right]
    refine sum_eq_zero fun b _ => ?_
    by_cases hbz : ((b : ℝ) : ℂ) = z
    · rw [hP1 _ (hbe b).1 (by rw [(hbe b).2, hbz]), sub_self, formB_zero_right]
    · rw [hP0 _ (hbe b).1 _ hbz (hbe b).2, sub_zero]
      by_cases hPf : P f = 0
      · rw [hPf, formB_zero_left]
      · obtain ⟨b0, _, hb0⟩ := hreal z (P f) (hPM f hf) hPf (hPz f hf)
        exact horth _ _ z _ (by rw [hb0]; simp) (hPz f hf) (hbe b).2 (Ne.symm hbz)
  intro f hf g hg
  have e1 : formB ε (P f) g = formB ε (P f) (P g) := by
    have := hL f hf g hg
    rw [formB_sub_right, sub_eq_zero] at this
    exact this
  have e2 : formB ε f (P g) = formB ε (P f) (P g) := by
    have := hL g hg f hf
    rw [formB_sub_right, sub_eq_zero] at this
    rw [← formB_conj, this, formB_conj]
  rw [e1, e2]

end ReciprocityTheory.ChartRestriction.DS
