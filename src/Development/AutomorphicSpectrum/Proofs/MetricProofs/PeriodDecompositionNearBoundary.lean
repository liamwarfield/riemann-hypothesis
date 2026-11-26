module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerFromAffineChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentSpanRelIndexCriterion
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjChartSetEqSetChartSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQHermitianAndRealPairing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsKerProjStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartWSaturatedAndContinuousSection
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartWSaturatedAndContinuousSection
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.NoMonodromy

variable {a g : ℕ}

theorem map_mulVec_real (M : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    M.map (fun x : ℤ => (x : ℝ)) *ᵥ (fun k => (v k : ℝ)) = fun k => ((M *ᵥ v) k : ℝ) := by
  funext k
  simp [mulVec, dotProduct]

theorem ker_each (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ)
    (hv : (∑ j, B j) *ᵥ v = 0) (j : Fin a) : B j *ᵥ v = 0 := by
  set r : Fin g → ℝ := fun k => (v k : ℝ) with hr
  have hsum : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have h1 : (∑ j, (B j).map (fun x : ℤ => (x : ℝ))) *ᵥ r = 0 := by
    rw [← hsum, hr, map_mulVec_real, hv]
    funext k
    simp
  have h0 : r ⬝ᵥ ((∑ j, (B j).map (fun x : ℤ => (x : ℝ))) *ᵥ r) = 0 := by
    rw [h1]; simp
  rw [Matrix.sum_mulVec, dotProduct_sum] at h0
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ r ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ r) := by
    intro i _
    simpa using (hB i).dotProduct_mulVec_nonneg r
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
  have h3 : (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ r = 0 :=
    ((hB j).dotProduct_mulVec_zero_iff).1 (by simpa using h2)
  rw [hr, map_mulVec_real] at h3
  funext k
  have := congrFun h3 k
  simpa using this

theorem vec_eq_sum (t : Fin g → ℂ) : t = ∑ i, t i • cst (Pi.single i 1 : Fin g → ℤ) := by
  funext k
  simp [cst, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.NoMonodromy

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NoMonodromy

theorem noMonodromy_lattice : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (k : ℤ), k ≠ 0 → k • x ∈ chartW bas B → x ∈ chartW bas B) ∧ (∀ x ∈ chartW bas B, ContinuousAt (chartS bas A T0 x) 0 ∧ ∀ w ∈ logCover L.a_le, chartS bas A T0 x (expCover a w) = L.P w x) ∧ Function.Injective (chartPer bas A T0 B) ∧ Submodule.span ℂ (Set.range (chartPer bas A T0 B)) = ⊤ := by
  intro n a g Λ _ L bas A T0 B c ρ h
  have hmem : ∀ x, x ∈ chartW bas B ↔ (∑ j, B j) *ᵥ vCo bas x = 0 := fun x => by
    rw [chartW, LinearMap.mem_ker]
    rfl
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hA0 : ContinuousAt A 0 := h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hT0 : ContinuousAt T0 0 := h.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hunit : IsUnit ((A 0)ᵀ).det := Ne.isUnit (by rw [det_transpose]; exact h.A_det)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x k hk hx
    rw [hmem] at hx ⊢
    rw [map_zsmul, Matrix.mulVec_smul] at hx
    exact (smul_eq_zero.1 hx).resolve_left hk
  · intro x hx
    have hxv := (hmem x).1 hx
    refine ⟨?_, fun w hw => ?_⟩
    · have hcts : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
          p.1ᵀ *ᵥ (cst (uCo bas x) + p.2 *ᵥ cst (vCo bas x))) :=
        (continuous_fst.matrix_transpose).matrix_mulVec
          (continuous_const.add (continuous_snd.matrix_mulVec continuous_const))
      exact ContinuousAt.comp (f := fun z => (A z, T0 z)) hcts.continuousAt (hA0.prodMk hT0)
    · rw [h.per w hw x]
      simp only [chartS, tauAt]
      have hz : (∑ j, (w (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
          (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ cst (vCo bas x) = 0 := by
        rw [Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Matrix.smul_mulVec, cst_mulVec, ker_each B h.B_psd _ hxv j, cst_zero, smul_zero]
      rw [Matrix.add_mulVec, hz, add_zero]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hxv := (hmem _).1 x.2
    set u := uCo bas (x : Λ) with hu
    set v := vCo bas (x : Λ) with hv
    have hS : (A 0)ᵀ *ᵥ (cst u + T0 0 *ᵥ cst v) = 0 := hx
    have hy : cst u + T0 0 *ᵥ cst v = 0 := by
      have := congrArg (fun y => ((A 0)ᵀ)⁻¹ *ᵥ y) hS
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit] using this
    set r : Fin g → ℝ := fun k => (v k : ℝ) with hr
    have him : ((T0 0).map Complex.im) *ᵥ r = 0 := by
      funext i
      have h1 := congrArg Complex.im (congrFun hy i)
      simpa [cst, mulVec, dotProduct, hr] using h1
    have hlow := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
      Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball h.ρ_le)) h.B_psd h.c_pos h.im_lower 0
      (Metric.mem_ball_self h.ρ_pos) 0 (fun j hj => absurd rfl hj) (fun _ _ => rfl) r
      (fun j _ => by
        rw [hr, map_mulVec_real, ker_each B h.B_psd _ hxv j]
        funext k
        simp)
    simp only [Pi.zero_apply, zero_div, zero_smul, Finset.sum_const_zero, add_zero] at hlow
    rw [him, dotProduct_zero] at hlow
    have hrr : r ⬝ᵥ r ≤ 0 := by
      by_contra hcon
      exact absurd hlow (not_le.2 (mul_pos h.c_pos (not_le.1 hcon)))
    have hr0 : r = 0 := by
      refine dotProduct_self_eq_zero.1 (le_antisymm hrr ?_)
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hv0 : v = 0 := by
      funext k
      have := congrFun hr0 k
      simpa [hr] using this
    have hu0 : u = 0 := by
      rw [hv0, cst_zero, mulVec_zero, add_zero] at hy
      funext k
      have := congrFun hy k
      simpa [cst] using this
    refine Subtype.ext (eq_of_coords bas ?_ ?_)
    · rw [← hu, hu0]; simp
    · rw [← hv, hv0]; simp
  · rw [eq_top_iff]
    intro y _
    set t : Fin g → ℂ := ((A 0)ᵀ)⁻¹ *ᵥ y with ht
    have hyt : y = (A 0)ᵀ *ᵥ t := by
      rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    have hper : ∀ i, (A 0)ᵀ *ᵥ cst (Pi.single i 1 : Fin g → ℤ) ∈
        Submodule.span ℂ (Set.range (chartPer bas A T0 B)) := by
      intro i
      refine Submodule.subset_span ⟨⟨mk bas (Pi.single i 1) 0, ?_⟩, ?_⟩
      · rw [hmem, vCo_mk]; simp
      · change chartS bas A T0 (mk bas (Pi.single i 1) 0) 0 = _
        simp only [chartS, uCo_mk, vCo_mk, cst_zero, mulVec_zero, add_zero]
    rw [hyt, vec_eq_sum t, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (hper i)

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartWSaturatedAndContinuousSectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartW_saturated_and_continuous_section : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (k : ℤ), k ≠ 0 → k • x ∈ chartW bas B → x ∈ chartW bas B) ∧ (∀ x ∈ chartW bas B, ContinuousAt (chartS bas A T0 x) 0 ∧ ∀ w ∈ logCover L.a_le, chartS bas A T0 x (expCover a w) = L.P w x) ∧ Function.Injective (chartPer bas A T0 B) ∧ Submodule.span ℂ (Set.range (chartPer bas A T0 B)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.noMonodromy_lattice | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.noMonodromy_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.noMonodromy_lattice <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetMulNormSqDet
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetMulNormSqDet
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange

theorem gram_eq' {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) :
    R.gram u = (Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * (Matrix.of u)ᵀ := by
  have hg : ∀ a b, R.gram u a b = u b ⬝ᵥ R.Hm *ᵥ star (u a) := fun _ _ => rfl
  ext a b
  rw [hg]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_det_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u f : Fin m → Fin g → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ i, f i = ∑ j, T j i • u j) → (R.gram f).det = ((‖T.det‖ ^ 2 : ℝ) : ℂ) * (R.gram u).det := by
  intro E _ _ _ g Λ _ _ R m u f T hf
  have hfT : Matrix.of f = Tᵀ * Matrix.of u := by
    ext i k
    simp [hf, Matrix.mul_apply, Finset.sum_apply]
  have hc : (Tᵀ.map (starRingEnd ℂ)).det = starRingEnd ℂ T.det := by
    rw [Matrix.transpose_map, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  have hn : ((‖T.det‖ ^ 2 : ℝ) : ℂ) = T.det * starRingEnd ℂ T.det := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_eq', GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_eq',
    hfT, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [show Tᵀ.map (starRingEnd ℂ) * (Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * ((Matrix.of u)ᵀ * T) =
      Tᵀ.map (starRingEnd ℂ) * ((Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * (Matrix.of u)ᵀ) * T by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.det_mul, Matrix.det_mul, hc, hn]
  ring

end GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetMulNormSqDetStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_mul_normSq_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u f : Fin m → Fin g → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ i, f i = ∑ j, T j i • u j) → (R.gram f).det = ((‖T.det‖ ^ 2 : ℝ) : ℂ) * (R.gram u).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_det_change | exact GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_det_change | (intros; apply GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_det_change <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFamilyInIdealOfIsOFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFamilyInIdealOfIsOFamily
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem oFamily_of_image : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (W I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (r : ℕ) (v : Fin r → Fin g → ℂ), I ≤ W → Function.Injective per → (∀ (c : 𝓞 E) (x : W), per (c • x) = ρ c (per x)) → IsOFamily ρ (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) v → ∃ y : Fin r → W, (∀ a, (y a : Λ) ∈ I) ∧ (∀ a, per (y a) = v a) ∧ LinearIndependent (𝓞 E) (fun a => (y a : Λ)) ∧ (oSpan ρ v).relIndex (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) = (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup.relIndex I.toAddSubgroup := by
  intro E _ _ g Λ _ _ W I per ρ r v hIW hinj hact hO
  classical
  set J : Submodule (𝓞 E) W := I.comap W.subtype with hJ
  have hS : AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x} = J.toAddSubgroup.map per := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro p ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro p ⟨x, hx, rfl⟩
      exact AddSubgroup.subset_closure ⟨x, hx, rfl⟩
  rw [hS] at hO ⊢
  obtain ⟨hmem, hind, hfin⟩ := hO
  choose y hyJ hyv using fun a => (hmem a)
  have hyI : ∀ a, ((y a : W) : Λ) ∈ I := fun a => hyJ a
  have hsum : ∀ c : Fin r → 𝓞 E, per (∑ i, c i • y i) = ∑ i, ρ (c i) (v i) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hact, hyv]
  refine ⟨y, hyI, hyv, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ∑ i, c i • y i = 0 := by
      apply Subtype.ext
      simpa using hc
    have := hind c (by rw [← hsum, h0, map_zero])
    exact congrFun this i
  · set P : Submodule (𝓞 E) W := Submodule.span (𝓞 E) (Set.range y) with hP
    have hspan : oSpan ρ v = P.toAddSubgroup.map per := by
      apply le_antisymm
      · rw [oSpan, AddSubgroup.closure_le]
        rintro p ⟨a, i, rfl⟩
        refine ⟨a • y i, ?_, ?_⟩
        · exact P.smul_mem a (Submodule.subset_span ⟨i, rfl⟩)
        · simp only [hact, hyv]
      · rintro p ⟨x, hx, rfl⟩
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hx
        show per _ ∈ _
        rw [hsum]
        exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, i, rfl⟩
    have hPΛ : (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup
        = P.toAddSubgroup.map W.subtype.toAddMonoidHom := by
      have : Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ)) = P.map W.subtype := by
        rw [hP, Submodule.map_span, ← Set.range_comp]
        rfl
      rw [this]
      ext x
      simp
    have hIΛ : I.toAddSubgroup = J.toAddSubgroup.map W.subtype.toAddMonoidHom := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨x, hIW hx⟩, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz
    rw [hspan, hPΛ, hIΛ, AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
      AddSubgroup.relIndex_map_map_of_injective _ _ W.injective_subtype]

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFamilyInIdealOfIsOFamilyStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_in_ideal_of_isOFamily : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (W I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (r : ℕ) (v : Fin r → Fin g → ℂ), I ≤ W → Function.Injective per → (∀ (c : 𝓞 E) (x : W), per (c • x) = ρ c (per x)) → IsOFamily ρ (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) v → ∃ y : Fin r → W, (∀ a, (y a : Λ) ∈ I) ∧ (∀ a, per (y a) = v a) ∧ LinearIndependent (𝓞 E) (fun a => (y a : Λ)) ∧ (oSpan ρ v).relIndex (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) = (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup.relIndex I.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.oFamily_of_image | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.oFamily_of_image | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.oFamily_of_image <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetImEqZero
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetImEqZero
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GramReal

theorem gram_det_im_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ) :
    (R.gram u).det.im = 0 := by
  have hg : ∀ a b, R.gram u a b = u b ⬝ᵥ R.Hm *ᵥ star (u a) := fun _ _ => rfl
  have hHm : ∀ i j, star (R.Hm i j) = R.Hm j i := fun i j => R.10.apply j i
  have hH : (R.gram u)ᴴ = R.gram u := by
    ext a b
    rw [Matrix.conjTranspose_apply, hg, hg]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hHm]
    ring
  have hd : star (R.gram u).det = (R.gram u).det := by
    rw [← Matrix.det_conjTranspose, hH]
  exact Complex.conj_eq_iff_im.mp hd

end GlobalTheory.CompanionTheory.Ar.Cusp.GramReal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetImEqZeroStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_im_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (R.gram u).det.im = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousChangeOfFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousChangeOfFrame
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.SolveCoeff

private def colMat {g m : ℕ} (v : Fin m → Fin g → ℂ) : Matrix (Fin g) (Fin m) ℂ :=
  Matrix.of fun a i => v i a

private lemma colMat_eq_mul {g m : ℕ} (M f : Fin m → Fin g → ℂ) (C : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ i, f i = ∑ j, C j i • M j) : colMat f = colMat M * C := by
  ext a i
  simp only [colMat, Matrix.of_apply, Matrix.mul_apply]
  rw [h i]
  simp [Finset.sum_apply, mul_comm]

private lemma solve_eq {g m : ℕ} (A : Matrix (Fin g) (Fin m) ℂ) (C : Matrix (Fin m) (Fin m) ℂ)
    (hd : (Aᴴ * A).det ≠ 0) : (Aᴴ * A)⁻¹ * Aᴴ * (A * C) = C := by
  have hu : IsUnit (Aᴴ * A).det := isUnit_iff_ne_zero.mpr hd
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

open scoped ComplexOrder in
private lemma gram_det_ne {g m : ℕ} (M : Fin m → Fin g → ℂ) (h : LinearIndependent ℂ M) :
    ((colMat M)ᴴ * colMat M).det ≠ 0 := by
  have hinj : Function.Injective (colMat M).mulVec := by
    intro x y hxy
    have hz : ∑ i, (x - y) i • M i = 0 := by
      funext a
      have h1 : (colMat M *ᵥ (x - y)) a = 0 := by
        rw [Matrix.mulVec_sub, hxy, sub_self]; rfl
      simpa [Matrix.mulVec, dotProduct, colMat, mul_comm, Finset.sum_apply] using h1
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 h _ hz i)
  have hinj2 : Function.Injective ((colMat M)ᴴ * colMat M).mulVec := by
    intro x y hxy
    apply hinj
    have h0 : ((colMat M)ᴴ * colMat M) *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 := (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).1 h0
    rw [Matrix.mulVec_sub] at h1
    exact sub_eq_zero.1 h1
  have := (Matrix.mulVec_injective_iff_isUnit).1 hinj2
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

private lemma cat_mul {X : Type} [TopologicalSpace X] {x : X} {l k r : ℕ}
    {A : X → Matrix (Fin l) (Fin k) ℂ} {B : X → Matrix (Fin k) (Fin r) ℂ}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) : ContinuousAt (fun z => A z * B z) x := by
  have c : Continuous (fun p : Matrix (Fin l) (Fin k) ℂ × Matrix (Fin k) (Fin r) ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact c.continuousAt.comp (hA.prodMk hB)

private lemma cat_conj {X : Type} [TopologicalSpace X] {x : X} {l k : ℕ}
    {A : X → Matrix (Fin l) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z)ᴴ) x := by
  have c : Continuous (fun N : Matrix (Fin l) (Fin k) ℂ => Nᴴ) :=
    continuous_id.matrix_conjTranspose
  exact c.continuousAt.comp hA

private lemma cat_det {X : Type} [TopologicalSpace X] {x : X} {k : ℕ}
    {A : X → Matrix (Fin k) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z).det) x := by
  have c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.det) := continuous_id.matrix_det
  exact c.continuousAt.comp hA

private lemma cat_adj {X : Type} [TopologicalSpace X] {x : X} {k : ℕ}
    {A : X → Matrix (Fin k) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z).adjugate) x := by
  have c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.adjugate) :=
    continuous_id.matrix_adjugate
  exact c.continuousAt.comp hA

private lemma colMat_continuousAt {n g m : ℕ} (M : (Fin n → ℂ) → Fin m → Fin g → ℂ)
    (h : ∀ i, ContinuousAt (fun z => M z i) 0) : ContinuousAt (fun z => colMat (M z)) 0 := by
  refine continuousAt_pi.2 fun a => continuousAt_pi.2 fun i => ?_
  exact (continuous_apply a).continuousAt.comp (h i)

theorem coeff_continuous (n g m : ℕ) (M f : (Fin n → ℂ) → Fin m → Fin g → ℂ)
    (T₀ : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i, ContinuousAt (fun z => M z i) 0)
    (hf : ∀ i, ContinuousAt (fun z => f z i) 0) (hli : LinearIndependent ℂ (M 0))
    (h0 : ∀ i, f 0 i = ∑ j, T₀ j i • M 0 j)
    (hspan : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i ∈ Submodule.span ℂ (Set.range (M z))) :
    ∃ T : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ, ContinuousAt T 0 ∧ T 0 = T₀ ∧
      ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i = ∑ j, T z j i • M z j := by
  have hA : ContinuousAt (fun z => colMat (M z)) 0 := colMat_continuousAt M hM
  have hF : ContinuousAt (fun z => colMat (f z)) 0 := colMat_continuousAt f hf
  have hG : ContinuousAt (fun z => (colMat (M z))ᴴ * colMat (M z)) 0 :=
    cat_mul (cat_conj hA) hA
  have hdet : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z)).det) 0 := cat_det hG
  have hd0 := gram_det_ne (M 0) hli
  have hinv : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹) 0 := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hdet.inv₀ hd0).smul (cat_adj hG)
  refine ⟨fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z),
    cat_mul (cat_mul hinv (cat_conj hA)) hF, ?_, ?_⟩
  · show ((colMat (M 0))ᴴ * colMat (M 0))⁻¹ * (colMat (M 0))ᴴ * colMat (f 0) = T₀
    rw [colMat_eq_mul (M 0) (f 0) T₀ h0]
    exact solve_eq _ _ hd0
  · filter_upwards [hspan, hdet.eventually_ne hd0] with z hz hdz i
    have hc : ∀ i, ∃ c : Fin m → ℂ, ∑ j, c j • M z j = f z i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hz i)
    choose c hc using hc
    have hcol : colMat (f z) = colMat (M z) * Matrix.of (fun j i => c i j) :=
      colMat_eq_mul (M z) (f z) _ (fun i => by simpa using (hc i).symm)
    have hT : ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z)
        = Matrix.of (fun j i => c i j) := by
      rw [hcol]; exact solve_eq _ _ hdz
    simp only [hT, Matrix.of_apply]
    exact (hc i).symm

end GlobalTheory.CompanionTheory.Ar.SolveCoeff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousChangeOfFrameStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_change_of_frame : ∀ (n g m : ℕ) (M f : (Fin n → ℂ) → Fin m → Fin g → ℂ) (T₀ : Matrix (Fin m) (Fin m) ℂ), (∀ i, ContinuousAt (fun z => M z i) 0) → (∀ i, ContinuousAt (fun z => f z i) 0) → LinearIndependent ℂ (M 0) → (∀ i, f 0 i = ∑ j, T₀ j i • M 0 j) → (∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i ∈ Submodule.span ℂ (Set.range (M z))) → ∃ T : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ, ContinuousAt T 0 ∧ T 0 = T₀ ∧ ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i = ∑ j, T z j i • M z j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous | exact GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous | (intros; apply GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosOfSemidefiniteTransversal
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosOfSemidefiniteTransversal
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef

open scoped ComplexOrder

theorem star_form_eq {g : ℕ} {Hb : Matrix (Fin g) (Fin g) ℂ} (hH : Hb.IsHermitian)
    (x y : Fin g → ℂ) :
    star (x ⬝ᵥ Hb *ᵥ star y) = y ⬝ᵥ Hb *ᵥ star x := by
  have h1 : ∀ w : Fin g → ℂ, star (x ⬝ᵥ w) = star w ⬝ᵥ star x := by
    intro w
    simp [dotProduct, mul_comm]
  rw [h1, star_mulVec, star_star, hH.eq, dotProduct_mulVec]

theorem gram_form_eq {g k : ℕ} (Hb : Matrix (Fin g) (Fin g) ℂ) (q : Fin k → Fin g → ℂ)
    (l : Fin k → ℂ) :
    star l ⬝ᵥ (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)) *ᵥ l =
      (∑ c, l c • q c) ⬝ᵥ Hb *ᵥ star (∑ c, l c • q c) := by
  rw [star_sum, mulVec_sum, sum_dotProduct]
  simp only [dotProduct_sum, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  simp only [dotProduct, mulVec, of_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem gram_posDef {g k : ℕ} {Hb : Matrix (Fin g) (Fin g) ℂ}
    {U : Submodule ℂ (Fin g → ℂ)} {q : Fin k → Fin g → ℂ} (hH : Hb.IsHermitian)
    (hpos : ∀ v : Fin g → ℂ,
      0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U))
    (hind : ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) :
    (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext c c'
    simp only [conjTranspose_apply, of_apply]
    exact star_form_eq hH (q c) (q c')
  · intro l hl
    rw [gram_form_eq]
    set v : Fin g → ℂ := ∑ c, l c • q c with hv
    have hre : 0 < (v ⬝ᵥ Hb *ᵥ star v).re := by
      refine lt_of_le_of_ne (hpos v).1 fun h0 => hl (hind l ?_)
      exact (hpos v).2 h0.symm
    have him : (v ⬝ᵥ Hb *ᵥ star v).im = 0 :=
      Complex.conj_eq_iff_im.mp (star_form_eq hH v v)
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem gram_det_re_pos (g : ℕ) (Hb : Matrix (Fin g) (Fin g) ℂ)
    (U : Submodule ℂ (Fin g → ℂ)) (k : ℕ) (q : Fin k → Fin g → ℂ) (hH : Hb.IsHermitian)
    (hpos : ∀ v : Fin g → ℂ,
      0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U))
    (hind : ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) :
    0 < (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).det.re :=
  (Complex.lt_def.mp (gram_posDef hH hpos hind).det_pos).1

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosOfSemidefiniteTransversalStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_pos_of_semidefinite_transversal : ∀ (g : ℕ) (Hb : Matrix (Fin g) (Fin g) ℂ) (U : Submodule ℂ (Fin g → ℂ)) (k : ℕ) (q : Fin k → Fin g → ℂ), Hb.IsHermitian → (∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U)) → (∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) → 0 < (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodDecompositionNearBoundary
namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit

theorem contAt_act {E : Type} [Field E] [NumberField E] [IsCMField E] {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (L : ActPeriods E n a g Λ) (c' : 𝓞 E) (t : (Fin n → ℂ) → Fin g → ℂ) (ht : ContinuousAt t 0) :
    ContinuousAt (fun z => L.B z c' (t z)) 0 := by
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have e : (fun z => L.B z c' (t z)) = fun z => ∑ i, t z i • L.B z c' (Pi.single i 1) := by
    funext z
    conv_lhs => rw [pi_eq_sum_univ' (t z)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e]
  refine tendsto_finsetSum _ fun i _ => ?_
  have h1 : ContinuousAt (fun z => L.B z c' (Pi.single i 1)) 0 :=
    (L.B_hol c' _).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  exact ((continuous_apply i).continuousAt.comp ht).smul h1

theorem li_of_det {g m : ℕ} (u f : Fin m → Fin g → ℂ) (T : Matrix (Fin m) (Fin m) ℂ) (hu : LinearIndependent ℂ u)
    (hf : ∀ i, f i = ∑ j, T j i • u j) (hd : T.det ≠ 0) : LinearIndependent ℂ f := by
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro l hl i
  have h1 : ∑ j, (T *ᵥ l) j • u j = 0 := by
    rw [← hl]
    simp only [hf, Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have h2 : T *ᵥ l = 0 := funext (hu _ h1)
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hd h2) i

theorem contAt_form {n g : ℕ} (u u' : (Fin n → ℂ) → Fin g → ℂ) (Q : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (hu : ContinuousAt u 0) (hu' : ContinuousAt u' 0) (hQ : ContinuousAt Q 0) :
    ContinuousAt (fun z => u z ⬝ᵥ Q z *ᵥ star (u' z)) 0 := by
  have hc : Continuous (fun t : (Fin g → ℂ) × Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
      t.1 ⬝ᵥ t.2.1 *ᵥ star t.2.2) :=
    continuous_fst.dotProduct ((continuous_fst.comp continuous_snd).matrix_mulVec
      (continuous_star.comp (continuous_snd.comp continuous_snd)))
  exact ContinuousAt.comp (f := fun z => (u z, Q z, u' z)) hc.continuousAt (hu.prodMk (hQ.prodMk hu'))

theorem limit_of_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ) (W I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (s : W → (Fin n → ℂ) → Fin g → ℂ) (Hb : Matrix (Fin g) (Fin g) ℂ) (Qm : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ : ℝ), IsCMFam σ → IsEigFrames (Metric.ball 0 1) L.B σ b → I ≤ W → (∀ x ∈ I, ∀ y ∈ I, L.toLogPeriods.E x y = 0) → Function.Injective per → (∀ (c : 𝓞 E) (x : W), per (c • x) = L.B 0 c (per x)) → (∀ x : W, ContinuousAt (s x) 0 ∧ s x 0 = per x ∧ ∀ w ∈ logCover L.a_le, s x (expCover a w) = L.P w x) → Hb.IsHermitian → (∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x})) → ContinuousAt Qm 0 → Qm 0 = Hb → 0 < ρ → (∀ w ∈ logCover L.a_le, ‖expCover a w‖ < ρ → ∀ y : Fin g → ℂ, ∃ p : Fin g → ℂ, p - y ∈ Submodule.span ℂ (L.P w '' (I : Set Λ)) ∧ (∀ x ∈ I, p ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w x) = 0) ∧ ∀ y' : Fin g → ℂ, y' ⬝ᵥ L.H (expCover a w) *ᵥ star p = y' ⬝ᵥ Qm (expCover a w) *ᵥ star y) → ∀ ν : ℝ, PhiNormSq (L.B 0) (fun x y => y ⬝ᵥ Hb *ᵥ star x) (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) 1 σ (fun τ i => b τ i 0) ν → 0 < ν ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ → |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) - Real.log ν| < ε := by
  intro E _ _ _ n a g Λ _ _ Ψ _ L σ m b W I per s Hb Qm ρ hσ hb hIW hiso hinj hact hs hHerm hpos hQc hQ0 hρ hrep ν hν
  classical
  obtain ⟨r, k, rfl, v, q, T, hfam, hq, hT, hdet, hνeq⟩ := hν
  simp only [Fin.cast_eq_self] at hT
  obtain ⟨y, hyI, hyv, hyli, hidx⟩ := GlobalTheory.T.exists_family_in_ideal_of_isOFamily E g Λ W I per (L.B 0) r v hIW hinj hact hfam
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  choose cf hcf using fun τ => GlobalTheory.T.exists_eigenComponent_polynomial E (σ τ)
  let f : Ψ → (Fin n → ℂ) → Fin r → Fin g → ℂ := fun τ z a => eigComp (L.B z) (σ τ) (s (y a) z)
  let qt : Ψ → (Fin n → ℂ) → Fin k → Fin g → ℂ := fun τ z c => ∑ j, T τ j (Fin.natAdd r c) • b τ j z
  let F : Ψ → (Fin n → ℂ) → Fin (r + k) → Fin g → ℂ := fun τ z => Fin.append (f τ z) (qt τ z)
  have hbc : ∀ τ j, ContinuousAt (b τ j) 0 := fun τ j =>
    (hb.1 τ j).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hfc : ∀ τ a, ContinuousAt (fun z => f τ z a) 0 := by
    intro τ a'
    have e : (fun z => f τ z a') = fun z => ∑ e ∈ (cf τ).support, cf τ e • L.B z e (s (y a') z) := by
      funext z
      exact ((hcf τ) (Fin g → ℂ) (L.B z)).1 _
    rw [e]
    refine tendsto_finsetSum _ fun e _ => ?_
    exact (contAt_act L e _ (hs (y a')).1).tendsto.const_smul _
  have hqc : ∀ τ c, ContinuousAt (fun z => qt τ z c) 0 := fun τ c =>
    tendsto_finsetSum _ fun j _ => (hbc τ j).tendsto.const_smul _
  have hFc : ∀ τ i, ContinuousAt (fun z => F τ z i) 0 := by
    intro τ i
    refine Fin.addCases (fun a' => ?_) (fun c => ?_) i
    · simpa only [F, Fin.append_left] using hfc τ a'
    · simpa only [F, Fin.append_right] using hqc τ c
  have hf0 : ∀ τ a', f τ 0 a' = eigComp (L.B 0) (σ τ) (v a') := by
    intro τ a'
    simp only [f, (hs (y a')).2.1, hyv]
  have hqt0 : ∀ τ c, qt τ 0 c = q τ c := by
    intro τ c
    have := hT τ (Fin.natAdd r c)
    rw [Fin.append_right] at this
    exact this.symm
  have hF0 : ∀ τ, F τ 0 = Fin.append (fun a' => eigComp (L.B 0) (σ τ) (v a')) (q τ) := by
    intro τ
    simp only [F]
    congr 1
    · exact funext (hf0 τ)
    · exact funext (hqt0 τ)
  have hsol := fun τ => GlobalTheory.T.exists_continuous_change_of_frame n g (r + k) (fun z i => b τ i z) (F τ) (T τ) (fun i => hbc τ i) (hFc τ)
    ((hb.2 0 h0ball τ).1) (fun i => by rw [hF0 τ]; exact hT τ i) (by
      filter_upwards [Metric.isOpen_ball.mem_nhds h0ball] with z hz i
      rw [(hb.2 z hz τ).2]
      refine Fin.addCases (fun a' => ?_) (fun c => ?_) i
      · simp only [F, Fin.append_left]
        exact ((hcf τ) (Fin g → ℂ) (L.B z)).2.1 _
      · simp only [F, Fin.append_right]
        rw [← (hb.2 z hz τ).2]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  choose Tt hTc hT0 hTe using hsol
  let Qd : Ψ → (Fin n → ℂ) → ℂ := fun τ z => (Matrix.of fun c c' => qt τ z c' ⬝ᵥ Qm z *ᵥ star (qt τ z c)).det
  have hQdc : ∀ τ, ContinuousAt (Qd τ) 0 := by
    intro τ
    have hM : ContinuousAt (fun z => (Matrix.of fun c c' => qt τ z c' ⬝ᵥ Qm z *ᵥ star (qt τ z c) :
        Matrix (Fin k) (Fin k) ℂ)) 0 := by
      refine continuousAt_pi.2 fun c => continuousAt_pi.2 fun c' => ?_
      exact contAt_form _ _ _ (continuousAt_pi.2 fun i => ((continuous_apply i).continuousAt.comp (hqc τ c')))
        (continuousAt_pi.2 fun i => ((continuous_apply i).continuousAt.comp (hqc τ c))) hQc
    have hdc : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.det) := continuous_id.matrix_det
    exact hdc.continuousAt.comp hM
  have hQd0 : ∀ τ, Qd τ 0 = (Matrix.of fun c c' => q τ c' ⬝ᵥ Hb *ᵥ star (q τ c)).det := by
    intro τ
    simp only [Qd, hqt0, hQ0]
  have hstable : ∀ (c : 𝓞 E), ∀ x ∈ AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x},
      L.B 0 c x ∈ AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x} := by
    intro c x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨c • x, I.smul_mem c hx, (hact c x).symm⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (L.B 0 c)]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have hQpos : ∀ τ, 0 < (Qd τ 0).re := by
    intro τ
    rw [hQd0 τ]
    refine GlobalTheory.T.gram_det_pos_of_semidefinite_transversal g Hb (Submodule.span ℂ {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) k (q τ) hHerm hpos fun l hl => ?_
    refine GlobalTheory.T.eigenComponent_append_independent_span E (Fin g → ℂ) (L.B 0) (σ τ) _ r k v (q τ) hfam hstable (hq τ) ?_ l ?_
    · have := li_of_det (fun i => b τ i 0) (F τ 0) (T τ) (hb.2 0 h0ball τ).1
        (fun i => by rw [hF0 τ]; exact hT τ i) (hdet τ)
      rwa [hF0 τ] at this
    · refine Submodule.span_mono ?_ hl
      exact AddSubgroup.subset_closure
  have hTne : ∀ τ, 0 < ‖(Tt τ 0).det‖ ^ 2 := fun τ => by
    rw [hT0 τ]
    have := norm_pos_iff.2 (hdet τ)
    positivity
  have hdetc : ∀ τ, ContinuousAt (fun z => ‖(Tt τ z).det‖ ^ 2) 0 := by
    intro τ
    have hdc : Continuous (fun N : Matrix (Fin (r + k)) (Fin (r + k)) ℂ => ‖N.det‖ ^ 2) :=
      (continuous_id.matrix_det.norm).pow 2
    exact hdc.continuousAt.comp (hTc τ)
  have hQre : ∀ τ, ContinuousAt (fun z => (Qd τ z).re) 0 := fun τ =>
    Complex.continuous_re.continuousAt.comp (hQdc τ)
  let Φ : (Fin n → ℂ) → ℝ := fun z => ∑ τ, (Real.log (Qd τ z).re - Real.log (‖(Tt τ z).det‖ ^ 2))
  have hΦc : ContinuousAt Φ 0 := by
    refine tendsto_finsetSum _ fun τ _ => ?_
    exact ((hQre τ).log (hQpos τ).ne').sub ((hdetc τ).log (hTne τ).ne')
  set idx : ℕ := (Submodule.span (𝓞 E) (Set.range fun a' => (y a' : Λ))).toAddSubgroup.relIndex I.toAddSubgroup with hidxdef
  have hidx0 : idx ≠ 0 := by
    rw [← hidx]
    exact hfam.2.2
  have hidxpos : (0 : ℝ) < idx := Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx0)
  have hνe : ν = (idx : ℝ) * ∏ τ, ((Qd τ 0).re / ‖(Tt τ 0).det‖ ^ 2) := by
    rw [hνeq, hidx]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hQd0 τ, hT0 τ, one_pow, one_mul]
  have hνpos : 0 < ν := by
    rw [hνe]
    exact mul_pos hidxpos (Finset.prod_pos fun τ _ => div_pos (hQpos τ) (hTne τ))
  have hlogν : Real.log ν = Real.log idx + Φ 0 := by
    rw [hνe, Real.log_mul hidxpos.ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (div_pos (hQpos τ) (hTne τ)).ne'),
      Real.log_prod (fun τ _ => (div_pos (hQpos τ) (hTne τ)).ne')]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => Real.log_div (hQpos τ).ne' (hTne τ).ne'
  refine ⟨hνpos, fun ε hε => ?_⟩
  have hev : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ τ, ∀ i, F τ z i = ∑ j, Tt τ z j i • b τ j z) ∧
      (∀ τ, 0 < (Qd τ z).re) ∧ (∀ τ, 0 < ‖(Tt τ z).det‖ ^ 2) ∧ |Φ z - Φ 0| < ε := by
    refine (eventually_all.2 hTe).and ((eventually_all.2 fun τ =>
      (hQre τ).eventually (lt_mem_nhds (hQpos τ))).and ((eventually_all.2 fun τ =>
      (hdetc τ).eventually (lt_mem_nhds (hTne τ))).and ?_))
    have := (hΦc.eventually (Metric.ball_mem_nhds (Φ 0) hε))
    filter_upwards [this] with z hz
    simpa [Real.dist_eq] using hz
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨min δ₀ ρ, lt_min hδ₀ hρ, fun w hw hwδ => ?_⟩
  set z := expCover a w with hz
  have hzball : z ∈ Metric.ball (0 : Fin n → ℂ) δ₀ := by
    rw [mem_ball_zero_iff]
    exact hwδ.trans_le (min_le_left _ _)
  obtain ⟨h1, h2, h3, h4⟩ := hball z hzball
  have hwρ : ‖z‖ < ρ := hwδ.trans_le (min_le_right _ _)
  set R := L.riem w hw with hR
  have hfz : ∀ τ, (fun a' => eigComp R.B (σ τ) (R.P (y a' : Λ))) = f τ z := by
    intro τ
    funext a'
    simp only [f]
    rw [(hs (y a')).2.2 w hw]
    rfl
  have hGQ : ∀ τ, (R.gram (F τ z)).det = (R.gram (f τ z)).det * Qd τ z := by
    intro τ
    have hp := fun c => hrep w hw hwρ (qt τ z c)
    choose p hp1 hp2 hp3 using hp
    have hS := GlobalTheory.T.eigenComponent_span_relIndex_criterion E g Λ R I (σ τ) r k (fun a' => (y a' : Λ)) (qt τ z) p hyI (by rw [← hidxdef]; exact hidx0)
      (fun c => ?_) hp1 hp2
    · rw [hfz τ] at hS
      refine hS.trans ?_
      congr 2
      ext c c'
      exact hp3 c (qt τ z c')
    · have hzb : z ∈ Metric.ball (0 : Fin n → ℂ) 1 := expCover_mem_ball L.a_le hw
      have h5 : qt τ z c ∈ Submodule.span ℂ (Set.range fun i => b τ i z) :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      rw [(hb.2 z hzb τ).2] at h5
      exact h5
  have hDG : ∀ τ, ‖(Tt τ z).det‖ ^ 2 * (R.gram fun i => b τ i z).det.re = (R.gram (f τ z)).det.re * (Qd τ z).re := by
    intro τ
    have e1 := GlobalTheory.T.gram_det_mul_normSq_det E g Λ R (r + k) (fun i => b τ i z) (F τ z) (Tt τ z) (h1 τ)
    rw [hGQ τ] at e1
    have e2 := congrArg Complex.re e1
    rw [Complex.mul_re, GlobalTheory.T.gram_det_im_eq_zero E g Λ R r (f τ z), zero_mul, sub_zero, Complex.re_ofReal_mul] at e2
    exact e2.symm
  have hnz_data : R.nz σ I = R.nzOf σ I (fun a' => (y a' : Λ)) ∧ 0 < R.nz σ I := by
    by_cases hbot : I = ⊥
    · subst I
      have hr : r = 0 := by
        by_contra h
        let i : Fin r := ⟨0, Nat.pos_of_ne_zero h⟩
        exact hyli.ne_zero i (by simpa using hyI i)
      subst r
      have hno : ¬ ∃ k v, IsNzFamily (⊥ : Submodule (𝓞 E) Λ) k v := by
        rintro ⟨k, v, hk, hv, hli, -⟩
        exact hli.ne_zero ⟨0, hk⟩ (by simpa using hv ⟨0, hk⟩)
      simp [RiemLat.nz, hno, RiemLat.nzOf, Set.range_eq_empty]
    · have hr : 1 ≤ r := by
        by_contra h
        have hr0 : r = 0 := by omega
        subst r
        have hs : Submodule.span (𝓞 E) (Set.range fun a' => (y a' : Λ)) = ⊥ := by
          simp [Set.range_eq_empty]
        have hfinite : Nat.card I.toAddSubgroup ≠ 0 := by
          simpa only [hidxdef, hs, Submodule.bot_toAddSubgroup, AddSubgroup.relIndex_bot_left] using hidx0
        have : Finite I.toAddSubgroup := Nat.finite_of_card_ne_zero hfinite
        have := R.free
        obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
        obtain ⟨d, hd, hdx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
          (isOfFinAddOrder_of_finite (⟨x, hx⟩ : I.toAddSubgroup))
        have hzx : (d : ℤ) • x = 0 := by
          rw [natCast_zsmul]
          exact congrArg Subtype.val hdx
        exact hx0 ((smul_eq_zero.1 hzx).resolve_left (by exact_mod_cast hd.ne'))
      have hyfam : IsNzFamily I r (fun a' => (y a' : Λ)) := ⟨hr, hyI, hyli, hidx0⟩
      obtain ⟨heq, hpos, _⟩ := (GlobalTheory.CompanionTheory.Relay.isotropic_sublattice_covolume_positive
        E g Λ Ψ R σ I hσ hiso hbot).2 r _ hyfam
      exact ⟨heq, hpos⟩
  obtain ⟨hnz, hnzpos⟩ := hnz_data
  have hnz2 : R.nz σ I = (∏ τ, (R.gram (f τ z)).det.re) / (idx : ℝ) := by
    rw [hnz, RiemLat.nzOf]
    simp only [hfz]
    rfl
  have hPne : (∏ τ, (R.gram (f τ z)).det.re) ≠ 0 := by
    intro h0
    rw [hnz2, h0, zero_div] at hnzpos
    exact lt_irrefl _ hnzpos
  have hGne : ∀ τ, (R.gram (f τ z)).det.re ≠ 0 := fun τ => (Finset.prod_ne_zero_iff.1 hPne) τ (Finset.mem_univ τ)
  have hlogD : ∀ τ, Real.log (R.gram fun i => b τ i z).det.re =
      Real.log (R.gram (f τ z)).det.re + (Real.log (Qd τ z).re - Real.log (‖(Tt τ z).det‖ ^ 2)) := by
    intro τ
    have e : (R.gram fun i => b τ i z).det.re = (R.gram (f τ z)).det.re * (Qd τ z).re / ‖(Tt τ z).det‖ ^ 2 := by
      rw [← hDG τ, mul_div_cancel_left₀ _ (h3 τ).ne']
    rw [e, Real.log_div (mul_ne_zero (hGne τ) (h2 τ).ne') (h3 τ).ne', Real.log_mul (hGne τ) (h2 τ).ne']
    ring
  have hmain : R.logDet (fun τ i => b τ i z) - Real.log (R.nz σ I) - Real.log ν = Φ z - Φ 0 := by
    rw [hnz2, hlogν, Real.log_div hPne hidxpos.ne', Real.log_prod (fun τ _ => hGne τ), RiemLat.logDet]
    simp only [hlogD, Finset.sum_add_distrib]
    ring
  rw [hmain]
  exact h4

theorem limit_at_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsCMFam σ → IsEigFrames (Metric.ball 0 1) L.B σ b → ∃ (W : Submodule (𝓞 E) Λ) (I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (s : W → (Fin n → ℂ) → Fin g → ℂ) (Hb : Matrix (Fin g) (Fin g) ℂ), (∀ x, x ∈ I ↔ x ∈ W ∧ ∀ y ∈ W, L.toLogPeriods.E x y = 0) ∧ IsSaturated I ∧ Function.Injective per ∧ (∀ x : W, ContinuousAt (s x) 0 ∧ s x 0 = per x ∧ ∀ w ∈ logCover L.a_le, s x (expCover a w) = L.P w x) ∧ (∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀) ∧ Submodule.span ℂ (Set.range per) = ⊤ ∧ Hb.IsHermitian ∧ (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.toLogPeriods.E x x') ∧ (∀ x : W, (x : Λ) ∈ I → Hb *ᵥ star (per x) = 0) ∧ ∀ ν : ℝ, PhiNormSq (L.B 0) (fun x y => y ⬝ᵥ Hb *ᵥ star x) (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) 1 σ (fun τ i => b τ i 0) ν → 0 < ν ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ → |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) - Real.log ν| < ε := by
  intro E _ _ _ n a g Λ _ _ Ψ _ L σ m b hσ hb
  classical
  obtain ⟨bas, A, T0, B, c, ρ, h⟩ := exists_isChart L.toLogPeriods
  obtain ⟨Pr, hPr⟩ := GlobalTheory.T.exists_isKerProj' g (∑ j, B j)
  obtain ⟨hsat, hs, hinj, hspan⟩ := GlobalTheory.T.chartW_saturated_and_continuous_section n a g Λ L.toLogPeriods bas A T0 B c ρ h
  obtain ⟨hext, hlim⟩ := GlobalTheory.T.mem_chartW_of_continuous_period n a g Λ L.toLogPeriods bas A T0 B c ρ h
  obtain ⟨hHerm, hIm, hKill, hPos⟩ := GlobalTheory.T.chartQ_hermitian_and_real_pairing n a g Λ L.toLogPeriods bas A T0 B c ρ Pr h hPr
  obtain ⟨hQc, ρ', hρ', hrep⟩ := GlobalTheory.T.chartQ_continuousAt_and_local_solution n a g Λ L.toLogPeriods bas A T0 B c ρ Pr h hPr
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos

  have hBc : ∀ (c' : 𝓞 E) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 →
      ContinuousAt (fun z => L.B z c' (t z)) 0 := fun c' t ht => contAt_act L c' t ht
  have hstab : ∀ (c' : 𝓞 E) (x : Λ), x ∈ chartW bas B → c' • x ∈ chartW bas B := by
    intro c' x hx
    refine hext (c' • x) (fun z => L.B z c' (chartS bas A T0 x z)) (hBc c' _ (hs x hx).1) fun w hw => ?_
    rw [L.act w hw, (hs x hx).2 w hw]
  have hconj : ∀ c' : 𝓞 E, ∃ c'' : 𝓞 E, (c'' : E) = IsCMField.complexConj E (c' : E) := by
    intro c'
    refine ⟨⟨IsCMField.complexConj E (c' : E), ?_⟩, rfl⟩
    exact (NumberField.RingOfIntegers.isIntegral_coe c').map (IsCMField.complexConj E)
  let W : Submodule (𝓞 E) Λ :=
    { carrier := chartW bas B
      add_mem' := fun hx hy => (chartW bas B).add_mem hx hy
      zero_mem' := (chartW bas B).zero_mem
      smul_mem' := fun c' x hx => hstab c' x hx }
  have hW : ∀ x, x ∈ W ↔ x ∈ chartW bas B := fun x => Iff.rfl
  let I : Submodule (𝓞 E) Λ :=
    { carrier := {x | x ∈ chartW bas B ∧ ∀ y ∈ chartW bas B, L.toLogPeriods.E x y = 0}
      add_mem' := fun {x y} hx hy => ⟨(chartW bas B).add_mem hx.1 hy.1, fun u hu => by
        rw [map_add (f := _), LinearMap.add_apply, hx.2 u hu, hy.2 u hu, add_zero]⟩
      zero_mem' := ⟨(chartW bas B).zero_mem, fun u _ => by simp⟩
      smul_mem' := fun c' x hx => ⟨hstab c' x hx.1, fun u hu => by
        obtain ⟨c'', hc⟩ := hconj c'
        rw [L.adj c' c'' hc]
        exact hx.2 _ (hstab c'' u hu)⟩ }
  have hI : ∀ x, x ∈ I ↔ x ∈ W ∧ ∀ y ∈ W, L.toLogPeriods.E x y = 0 := fun x => Iff.rfl
  let toZ : W →+ chartW bas B := AddMonoidHom.mk' (fun x => ⟨x.1, x.2⟩) (fun _ _ => rfl)
  have hrad : ∀ x : chartW bas B, (∀ x' : chartW bas B, L.toLogPeriods.E x x' = 0) ↔ (x : Λ) ∈ I :=
    fun x => ⟨fun hx => ⟨x.2, fun y hy => hx ⟨y, hy⟩⟩, fun hx x' => hx.2 _ x'.2⟩
  let per : W →+ (Fin g → ℂ) := (chartPer bas A T0 B).comp toZ
  have hper : ∀ x : W, per x = chartS bas A T0 (x : Λ) 0 := fun _ => rfl
  let s : W → (Fin n → ℂ) → Fin g → ℂ := fun x => chartS bas A T0 (x : Λ)
  have hs' : ∀ x : W, ContinuousAt (s x) 0 ∧ s x 0 = per x ∧ ∀ w ∈ logCover L.a_le, s x (expCover a w) = L.P w x :=
    fun x => ⟨(hs x.1 x.2).1, rfl, (hs x.1 x.2).2⟩
  have hinj' : Function.Injective per := fun x y hxy => Subtype.ext (congrArg Subtype.val (hinj hxy))
  have hseq : ∃ ws : ℕ → Fin n → ℂ, (∀ m, ws m ∈ logCover L.a_le) ∧
      Tendsto (fun m => expCover a (ws m)) atTop (𝓝 0) := by
    refine ⟨fun m k => if k.val < a then -(((m : ℝ) + 1 : ℝ) : ℂ) else 0, fun m => ⟨fun i => ?_, fun k hk => ?_⟩, ?_⟩
    · have hi : (Fin.castLE L.a_le i).val < a := i.2
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [hi, ite_true, Complex.neg_re, Complex.ofReal_re]
      linarith
    · have hk' : ¬ k.val < a := not_lt.2 hk
      simp [hk']
    · rw [tendsto_pi_nhds]
      intro k
      by_cases hk : k.val < a
      · simp only [expCover, hk, ite_true, Pi.zero_apply]
        have h1 : Tendsto (fun m : ℕ => Real.exp (-((m : ℝ) + 1))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
            (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_exp, Complex.ofReal_neg] using h2
      · simp [expCover, hk]
  have hact : ∀ (c' : 𝓞 E) (x : W), per (c' • x) = L.B 0 c' (per x) := by
    intro c' x
    obtain ⟨ws, hws, hlim0⟩ := hseq
    have h1 : Tendsto (fun m => chartS bas A T0 ((c' • x : W) : Λ) (expCover a (ws m))) atTop
        (𝓝 (per (c' • x))) := (hs' (c' • x)).1.tendsto.comp hlim0 |>.congr fun _ => rfl
    have h2 : Tendsto (fun m => L.B (expCover a (ws m)) c' (chartS bas A T0 (x : Λ) (expCover a (ws m)))) atTop
        (𝓝 (L.B 0 c' (per x))) := (hBc c' _ (hs' x).1).tendsto.comp hlim0 |>.congr fun _ => rfl
    refine tendsto_nhds_unique h1 (h2.congr fun m => ?_)
    rw [(hs x.1 x.2).2 _ (hws m), ← L.act _ (hws m)]
    exact ((hs _ (hstab c' x.1 x.2)).2 _ (hws m)).symm
  have hset : {p | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.toLogPeriods.E x x' = 0) ∧ p = chartPer bas A T0 B x} =
      {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, x.2⟩, (hrad x).1 hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, x.2⟩, (hrad ⟨x.1, x.2⟩).2 hx, rfl⟩
  refine ⟨W, I, per, s, chartQ Pr A T0 0, hI, ?_, hinj', hs', ?_, ?_, hHerm, ?_, ?_, ?_⟩
  · intro x k hk hx
    have h2 : x ∈ chartW bas B := hsat x k hk hx.1
    refine ⟨h2, fun y hy => ?_⟩
    have h3 := hx.2 y hy
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left hk
  · intro ws x p h1 h2 h3
    obtain ⟨x₀, hx₀⟩ := hlim ws x p h1 h2 h3
    exact ⟨⟨x₀.1, x₀.2⟩, hx₀⟩
  · rw [← hspan]
    congr 1
  · intro x x'
    exact hIm (toZ x) (toZ x')
  · intro x hx
    exact hKill (toZ x) ((hrad (toZ x)).2 hx)
  · refine limit_of_data E n a g Λ Ψ L σ m b W I per s (chartQ Pr A T0 0) (chartQ Pr A T0) ρ' hσ hb (fun x hx => hx.1)
      (fun x hx y hy => hx.2 y hy.1) hinj' hact hs' hHerm ?_ hQc rfl hρ' ?_
    · intro v
      rw [← hset]
      exact hPos v
    · intro w hw hwρ y
      obtain ⟨p, h1, h2, h3⟩ := hrep w hw hwρ y
      refine ⟨p, ?_, fun x hx => ?_, h3⟩
      · refine Submodule.span_mono ?_ h1
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, (hrad x).1 hx, rfl⟩
      · exact h2 ⟨x, hx.1⟩ ((hrad ⟨x, hx.1⟩).2 hx)

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodDecompositionNearBoundaryStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_decomposition_near_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsCMFam σ → IsEigFrames (Metric.ball 0 1) L.B σ b → ∃ (W : Submodule (𝓞 E) Λ) (I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (s : W → (Fin n → ℂ) → Fin g → ℂ) (Hb : Matrix (Fin g) (Fin g) ℂ), (∀ x, x ∈ I ↔ x ∈ W ∧ ∀ y ∈ W, L.toLogPeriods.E x y = 0) ∧ IsSaturated I ∧ Function.Injective per ∧ (∀ x : W, ContinuousAt (s x) 0 ∧ s x 0 = per x ∧ ∀ w ∈ logCover L.a_le, s x (expCover a w) = L.P w x) ∧ (∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀) ∧ Submodule.span ℂ (Set.range per) = ⊤ ∧ Hb.IsHermitian ∧ (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.toLogPeriods.E x x') ∧ (∀ x : W, (x : Λ) ∈ I → Hb *ᵥ star (per x) = 0) ∧ ∀ ν : ℝ, PhiNormSq (L.B 0) (fun x y => y ⬝ᵥ Hb *ᵥ star x) (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) 1 σ (fun τ i => b τ i 0) ν → 0 < ν ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ → |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) - Real.log ν| < ε := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.limit_at_centre | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.limit_at_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.limit_at_centre <;> assumption)
end
