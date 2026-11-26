module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOperatorGLnSmoothAffineTranslationSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelOperatorRowFrequencyColumnTranslate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnipotentTimesGLrSetClosedSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnipotentTimesGLrSetClosedSubgroup
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem levSetInf_closed_subgroup : ∀ (E : Type) [Field E] [NumberField E] (n r : ℕ),
    (∀ g ∈ levSetInf E n r, ∀ h ∈ levSetInf E n r, g * h ∈ levSetInf E n r) ∧
    (∀ g ∈ levSetInf E n r, g⁻¹ ∈ levSetInf E n r) ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u ∈ levSetInf E n r) ∧ IsClosed (levSetInf E n r) := by
  intro E _ _ n r
  refine ⟨fun g hg h hh w => ?_, fun g hg w => ?_, fun u hu => ?_, ?_⟩
  · rw [map_mul]
    exact (levSet_closed_subgroup n r).1 _ (hg w) _ (hh w)
  · rw [map_inv]
    exact (levSet_closed_subgroup n r).2.1 _ (hg w)
  · obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    exact mem_levSetInf.2 fun i _ => ⟨fun j hj => h0 i j hj, h1 i⟩
  · have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) (Cinf E) =>
        (g : Matrix (Fin n) (Fin n) (Cinf E)) i j :=
      fun i j => (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Cinf E))).matrix_elem i j
    have hs : levSetInf E n r = {g : GL (Fin n) (Cinf E) | ∀ i : Fin n, r ≤ (i : ℕ) →
        (∀ j, j < i → (g : Matrix (Fin n) (Fin n) (Cinf E)) i j = 0) ∧
          (g : Matrix (Fin n) (Fin n) (Cinf E)) i i = 1} := Set.ext fun g => mem_levSetInf
    rw [hs]
    simp only [Set.setOf_forall, Set.setOf_and]
    refine isClosed_iInter fun i => isClosed_iInter fun _ => IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const
    · exact isClosed_eq (hc i i) continuous_const

end GlobalTheory.JSW.MirCinf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnipotentTimesGLrSetClosedSubgroupStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup : ∀ (E : Type) [Field E] [NumberField E] (n r : ℕ), (∀ g ∈ levSetInf E n r, ∀ h ∈ levSetInf E n r, g * h ∈ levSetInf E n r) ∧ (∀ g ∈ levSetInf E n r, g⁻¹ ∈ levSetInf E n r) ∧ (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u ∈ levSetInf E n r) ∧ IsClosed (levSetInf E n r) := by
  first | exact @GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup | exact GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup | (intros; apply GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCutUnipBMulLevSet
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

theorem truncatedRow_unipotent_mul_and_ne_zero : ∀ (n : ℕ) (ρ : Fin n), ∀ g ∈ levSet n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n), rowCut ρ ((u * g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ)) ∧
    ∃ j, j ≤ ρ ∧ rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) j ≠ 0 := by
  intro n ρ g hg
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB ℂ).1 hu
    funext j
    unfold rowCut
    split_ifs with hj
    · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ρ]
      · rw [hu1, one_mul]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [hu0 ρ k h, zero_mul]
        · have h' := Fin.lt_def.1 h
          rw [(hg k (by omega)).1 j (lt_of_le_of_lt hj h), mul_zero]
      · simp
    · rfl
  · by_contra hne
    push_neg at hne
    have hinv := (GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 g hg
    have h1 : ((g * g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ρ ρ = 1 := by simp
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : k ≤ ρ
      · have := hne k hk
        simp only [rowCut, hk, if_true] at this
        rw [this, zero_mul]
      · push_neg at hk
        have h' := Fin.lt_def.1 hk
        rw [(hinv k (by omega)).1 ρ hk, mul_zero]

end GlobalTheory.JSW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzero
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem rowCutInf_unipB_mul_levSetInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n),
    ∀ g ∈ levSetInf E n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) =
      rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧
    ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  intro E _ _ n ρ g hg
  have hw : ∀ w, compGL w g ∈ levSet n (ρ + 1) := hg
  have hc : ∀ w (x : GL (Fin n) (Cinf E)) j,
      rowCut ρ ((compGL w x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) j =
        rowCutInf ρ (x : Matrix (Fin n) (Fin n) (Cinf E)) j w := by
    intro w x j
    unfold rowCut rowCutInf
    split_ifs <;> rfl
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    have hmem : ∀ w, compGL w u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n) := by
      intro w
      refine (GlobalTheory.SmGL.mem_unipB ℂ).2 ⟨fun i j h => ?_, fun i => ?_⟩
      · rw [compGL_apply, hu0 i j h]; rfl
      · rw [compGL_apply, hu1 i]; rfl
    funext j w
    rw [← hc, ← hc, map_mul]
    exact congrFun ((truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).1 _ (hmem w)) j
  · intro w
    obtain ⟨j, hj, hne⟩ := (truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).2
    exact ⟨j, hj, by rwa [← hc]⟩

end GlobalTheory.JSW.MirCinf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzeroStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n), ∀ g ∈ levSetInf E n (ρ + 1), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧ ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | exact GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | (intros; apply GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanMatrixSmoothingNeZeroAtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanMatrixSmoothingNeZeroAtOne
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smoothMatInf_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (W : GL (Fin n) (Cinf E) → ℂ), Continuous W → W 1 ≠ 0 →
    ∃ α : (Fin n → Fin n → Cinf E) → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧
      tsupport α ⊆ {x | IsUnit (Matrix.of x)} ∧ smoothMatInf α W 1 ≠ 0 := by
  intro E _ _ n W hW h1
  have hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) := by
    open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))
  have hS0 : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
    have e : {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} =
        Set.range (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) :=
      Set.ext fun x => ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩
    rw [e]; exact hemb.isOpen_range
  have hGL : ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
    rw [hemb.isInducing.continuousOn_iff]
    exact continuousOn_id.congr fun x hx => val_toGLInf hx
  set S : Set (Fin n → Fin n → Cinf E) := {x | IsUnit (Matrix.of x)} with hSdef
  have hS : IsOpen S := hS0
  have hF : ContinuousOn (fun x : Fin n → Fin n → Cinf E => onMatInf W (Matrix.of x)) S := by
    refine (hW.comp_continuousOn hGL).congr fun x hx => ?_
    exact onMatInf_of_isUnit W hx
  set c : ℂ := starRingEnd ℂ (W 1) with hc
  set U : Set (Fin n → Fin n → Cinf E) := S ∩ (fun x => (c * onMatInf W (Matrix.of x)).re) ⁻¹' Set.Ioi 0 with hUdef
  have hU : IsOpen U :=
    (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hF)).isOpen_inter_preimage hS isOpen_Ioi
  set x0 : Fin n → Fin n → Cinf E := fun i j => (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j with hx0def
  have hx0 : Matrix.of x0 = 1 := by ext i j; rfl
  have hval : onMatInf W (Matrix.of x0) = W 1 := by
    rw [hx0]; simpa using onMatInf_val W 1
  have hpos : 0 < (c * W 1).re := by
    rw [hc, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.2 h1
  have hx0U : x0 ∈ U := by
    refine ⟨?_, ?_⟩
    · show IsUnit (Matrix.of x0); rw [hx0]; exact isUnit_one
    · show 0 < (c * onMatInf W (Matrix.of x0)).re; rw [hval]; exact hpos
  obtain ⟨ρ, h1ρ, h2ρ, h3ρ, h4ρ, h5ρ⟩ := exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hx0U)
  have hts : tsupport (fun x => (ρ x : ℂ)) ⊆ U :=
    (tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) ρ).trans h1ρ
  have hcs : HasCompactSupport (fun x => (ρ x : ℂ)) := h2ρ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨fun x => (ρ x : ℂ), Complex.ofRealCLM.contDiff.comp h3ρ, hcs, hts.trans Set.inter_subset_left, ?_⟩
  set f : (Fin n → Fin n → Cinf E) → ℂ := fun a => (ρ a : ℂ) * onMatInf W (Matrix.of a) with hfdef
  have e : smoothMatInf (fun x => (ρ x : ℂ)) W 1 = ∫ a, f a := by
    simp [smoothMatInf, f]
  have hsub : tsupport f ⊆ S := tsupport_mul_subset_left.trans (hts.trans Set.inter_subset_left)
  have hfc : Continuous f :=
    ((Complex.continuous_ofReal.comp h3ρ.continuous).continuousOn.mul hF).continuous_of_tsupport_subset hS hsub
  have hfs : HasCompactSupport f := hcs.mul_right
  have hint : Integrable f volume := hfc.integrable_of_hasCompactSupport hfs
  have hnn : ∀ a, 0 ≤ (c * f a).re := by
    intro a
    have hr : 0 ≤ ρ a := (h4ρ ⟨a, rfl⟩).1
    have eq : (c * f a).re = ρ a * (c * onMatInf W (Matrix.of a)).re := by
      simp only [f]
      rw [mul_left_comm, Complex.re_ofReal_mul]
    rw [eq]
    by_cases ha : ρ a = 0
    · simp [ha]
    · have : a ∈ U := h1ρ (subset_tsupport _ ha)
      exact mul_nonneg hr (le_of_lt this.2)
  have hne : (c * f x0).re ≠ 0 := by
    simp only [f]
    rw [h5ρ, hval]
    simpa using hpos.ne'
  have hcont : Continuous fun a => (c * f a).re := Complex.continuous_re.comp (continuous_const.mul hfc)
  have hsupp : HasCompactSupport fun a => (c * f a).re :=
    hfs.comp_left (g := fun z : ℂ => (c * z).re) (by simp)
  have key : 0 < ∫ a, (c * f a).re ∂volume :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnn (x := x0) hne
  have hre : ∫ a, (c * f a).re = (∫ a, c * f a).re := integral_re (hint.const_mul c)
  rw [e]
  intro h0
  rw [hre, integral_const_mul, h0, mul_zero, Complex.zero_re] at key
  exact lt_irrefl _ key

end GlobalTheory.JSW.MirCinf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanMatrixSmoothingNeZeroAtOneStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedeanMatrixSmoothing_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (W : GL (Fin n) (Cinf E) → ℂ), Continuous W → W 1 ≠ 0 → ∃ α : (Fin n → Fin n → Cinf E) → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ {x | IsUnit (Matrix.of x)} ∧ smoothMatInf α W 1 ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | exact GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | (intros; apply GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionMatrixInvertibleLevelReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMatEqAdd
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW

variable {n : ℕ}

open scoped Matrix

theorem secMat_of_ne (ρ j : Fin n) (v : Fin n → ℂ) {i : Fin n} (hi : i ≠ ρ) (l : Fin n) :
    secMat ρ j v i l = if l = Equiv.swap j ρ i then 1 else 0 := by
  simp [secMat, hi]

theorem secMat_self (ρ j : Fin n) (v : Fin n → ℂ) (l : Fin n) :
    secMat ρ j v ρ l = if l ≤ ρ then v l else 0 := by
  simp [secMat]

theorem swap_of_lt' {ρ j i : Fin n} (hj : j ≤ ρ) (hi : ρ < i) : Equiv.swap j ρ i = i :=
  Equiv.swap_apply_of_ne_of_ne (lt_of_le_of_lt hj hi).ne' hi.ne'

theorem isUnit_secMat (ρ j : Fin n) (hj : j ≤ ρ) (v : Fin n → ℂ) (hv : v j ≠ 0) :
    IsUnit (Matrix.of (secMat ρ j v)) := by
  rw [← Matrix.vecMul_injective_iff_isUnit]
  have key : ∀ e : Fin n → ℂ, e ᵥ* Matrix.of (secMat ρ j v) = 0 → e = 0 := by
    intro e he
    have hcol : ∀ l, ∑ i, e i * secMat ρ j v i l = 0 := fun l => by
      have := congrFun he l
      simpa [Matrix.vecMul, dotProduct] using this
    have hρ : e ρ = 0 := by
      have h := hcol j
      rw [Finset.sum_eq_single ρ] at h
      · rw [secMat_self, if_pos hj] at h
        exact (mul_eq_zero.1 h).resolve_right hv
      · intro i _ hi
        rw [secMat_of_ne _ _ _ hi, if_neg, mul_zero]
        intro h'
        apply hi
        calc i = Equiv.swap j ρ (Equiv.swap j ρ i) := (Equiv.swap_apply_self _ _ _).symm
          _ = Equiv.swap j ρ j := by rw [← h']
          _ = ρ := Equiv.swap_apply_left _ _
      · simp
    funext i
    by_cases hi : i = ρ
    · rw [hi]; exact hρ
    · have h := hcol (Equiv.swap j ρ i)
      rw [Finset.sum_eq_single i] at h
      · rw [secMat_of_ne _ _ _ hi, if_pos rfl, mul_one] at h
        exact h
      · intro i' _ hi'
        by_cases h'' : i' = ρ
        · rw [h'', hρ, zero_mul]
        · rw [secMat_of_ne _ _ _ h'', if_neg, mul_zero]
          intro h3
          exact hi' ((Equiv.swap j ρ).injective h3).symm
      · simp
  intro c d hcd
  have := key (c - d) (by
    change (c - d) ᵥ* _ = 0
    rw [Matrix.sub_vecMul]
    exact sub_eq_zero.2 hcd)
  exact sub_eq_zero.1 this

def secLin (ρ : Fin n) : (Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i l => if i = ρ ∧ l ≤ ρ then v l else 0
      map_add' := fun v w => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h]
      map_smul' := fun c v => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h] }

theorem secMat_eq_add (ρ j : Fin n) (v : Fin n → ℂ) : secMat ρ j v = secMat ρ j 0 + secLin ρ v := by
  funext i l
  by_cases hi : i = ρ
  · subst hi
    by_cases hl : l ≤ i <;> simp [secMat, secLin, hl]
  · simp [secMat, secLin, hi]

theorem secMat_main : ∀ (n : ℕ) (ρ j : Fin n), j ≤ ρ → (∀ v : Fin n → ℂ, v j ≠ 0 → IsUnit (Matrix.of (secMat ρ j v))) ∧ (∀ g ∈ levSet n (ρ + 1), rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) j ≠ 0 → g * (toGL (Matrix.of (secMat ρ j (rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ)))))⁻¹ ∈ levSet n ρ) ∧ ∃ L : (Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ), ∀ v, secMat ρ j v = secMat ρ j 0 + L v := by
  intro n ρ j hj
  refine ⟨fun v hv => isUnit_secMat ρ j hj v hv, ?_, secLin ρ, secMat_eq_add ρ j⟩
  intro g hg hgj
  set v := rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) with hv
  have hS := isUnit_secMat ρ j hj v hgj
  set S := toGL (Matrix.of (secMat ρ j v)) with hSdef
  have hSv : (S : Matrix (Fin n) (Fin n) ℂ) = Matrix.of (secMat ρ j v) := val_toGL hS
  have hSlev : S ∈ levSet n (ρ + 1) := by
    intro i hi
    have hiρ : ρ < i := by rw [Fin.lt_def]; omega
    refine ⟨fun l hl => ?_, ?_⟩
    · rw [hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_neg hl.ne]
    · rw [hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_pos rfl]
  have hp : g * S⁻¹ ∈ levSet n (ρ + 1) :=
    (GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).1 g hg _ ((GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 S hSlev)
  set P := ((g * S⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hPdef
  have hPS : P * Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hSv, hPdef, ← Units.val_mul, inv_mul_cancel_right]
  let w : Fin n → ℂ := fun i => if i = ρ then 1 else if i < ρ then 0 else (g : Matrix (Fin n) (Fin n) ℂ) ρ i
  have hw : w ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ := by
    funext l
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    by_cases hl : l ≤ ρ
    · rw [Finset.sum_eq_single ρ]
      · simp [w, secMat_self, hl, hv, rowCut]
      · intro i _ hi
        rcases lt_or_gt_of_ne hi with h | h
        · simp [w, hi, h]
        · rw [secMat_of_ne _ _ _ hi, swap_of_lt' hj h, if_neg (lt_of_le_of_lt hl h).ne, mul_zero]
      · simp
    · have hlρ : ρ < l := lt_of_not_ge hl
      rw [Finset.sum_eq_single l]
      · simp [w, secMat_of_ne _ _ _ hlρ.ne', swap_of_lt' hj hlρ, hlρ.ne', not_lt.2 hlρ.le]
      · intro i _ hi
        by_cases h1 : i = ρ
        · rw [h1, secMat_self, if_neg hl, mul_zero]
        · rcases lt_or_gt_of_ne h1 with h | h
          · simp [w, h1, h]
          · rw [secMat_of_ne _ _ _ h1, swap_of_lt' hj h, if_neg (Ne.symm hi), mul_zero]
      · simp
  have hPw : P ρ ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ := by
    rw [← hPS]
    funext l
    simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]
  have hrow : P ρ = w := (Matrix.vecMul_injective_iff_isUnit.2 hS) (hPw.trans hw.symm)
  intro i hi
  by_cases hiρ : (i : ℕ) = ρ
  · have hie : i = ρ := Fin.ext hiρ
    subst hie
    refine ⟨fun l hl => ?_, ?_⟩
    · change P i l = 0
      rw [hrow]
      simp [w, hl, hl.ne]
    · change P i i = 1
      rw [hrow]
      simp [w]
  · exact hp i (by omega)

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionMatrixInvertibleLevelReduction
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mapMatrix_secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) (w : InfinitePlace E) :
    (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix (Matrix.of (secMatInf ρ j v)) =
      Matrix.of (secMat ρ (j w) (fun l => v l w)) := by
  ext i l; rfl

theorem isUnit_secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (hj : ∀ w, j w ≤ ρ) (v : Fin n → Cinf E)
    (hv : ∀ w, v (j w) w ≠ 0) : IsUnit (Matrix.of (secMatInf ρ j v)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
  intro w
  have h := RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) (Matrix.of (secMatInf ρ j v))
  rw [mapMatrix_secMatInf] at h
  have hu := isUnit_secMat ρ (j w) (hj w) (fun l => v l w) (hv w)
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  have h' : (Matrix.of (secMatInf ρ j v)).det w = (Matrix.of (secMat ρ (j w) (fun l => v l w))).det := h
  rw [h']
  exact hu

theorem secMatInf_mem_lev (ρ : Fin n) (j : InfinitePlace E → Fin n) (hj : ∀ w, j w ≤ ρ) (v : Fin n → Cinf E)
    (hv : ∀ w, v (j w) w ≠ 0) : toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1) := by
  rw [mem_levSetInf, val_toGLInf (isUnit_secMatInf ρ j hj v hv)]
  intro i hi
  have hiρ : ρ < i := by rw [Fin.lt_def]; omega
  refine ⟨fun l hl => funext fun w => ?_, funext fun w => ?_⟩
  · change secMat ρ (j w) (fun l => v l w) i l = 0
    rw [secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' (hj w) hiρ, if_neg hl.ne]
  · change secMat ρ (j w) (fun l => v l w) i i = 1
    rw [secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' (hj w) hiρ, if_pos rfl]

theorem rowCutInf_apply (ρ : Fin n) (g : GL (Fin n) (Cinf E)) (w : InfinitePlace E) (l : Fin n) :
    rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) l w = rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) l := by
  unfold rowCutInf rowCut
  split_ifs <;> rfl

def secLinInf (ρ : Fin n) : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i l => if i = ρ ∧ l ≤ ρ then v l else 0
      map_add' := fun v w => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h]
      map_smul' := fun c v => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h] }

theorem secMatInf_eq_add (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) :
    secMatInf ρ j v = secMatInf ρ j 0 + secLinInf ρ v := by
  funext i l w
  by_cases hi : i = ρ
  · subst hi
    by_cases hl : l ≤ i <;> simp [secMatInf, secMat, secLinInf, hl]
  · simp [secMatInf, secMat, secLinInf, hi]

theorem secMatInf_main : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n) (j : InfinitePlace E → Fin n), (∀ w, j w ≤ ρ) → (∀ v : Fin n → Cinf E, (∀ w, v (j w) w ≠ 0) → IsUnit (Matrix.of (secMatInf ρ j v)) ∧ toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1)) ∧ (∀ g ∈ levSetInf E n (ρ + 1), (∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0) → g * (toGLInf (Matrix.of (secMatInf ρ j (rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))))))⁻¹ ∈ levSetInf E n ρ) ∧ ∃ L : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E), ∀ v, secMatInf ρ j v = secMatInf ρ j 0 + L v := by
  intro E _ _ n ρ j hj
  refine ⟨fun v hv => ⟨isUnit_secMatInf ρ j hj v hv, secMatInf_mem_lev ρ j hj v hv⟩, ?_, secLinInf ρ, secMatInf_eq_add ρ j⟩
  intro g hg hgj w
  set v := rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) with hvdef
  have hS := isUnit_secMatInf ρ j hj v hgj
  have hne : rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (j w) ≠ 0 := by
    rw [← rowCutInf_apply]; exact hgj w
  have hcomp : compGL w (toGLInf (Matrix.of (secMatInf ρ j v))) =
      toGL (Matrix.of (secMat ρ (j w) (rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))) := by
    have hu := isUnit_secMat ρ (j w) (hj w) _ hne
    apply Units.ext
    rw [val_toGL hu]
    ext i l
    rw [compGL_apply, val_toGLInf hS]
    change secMat ρ (j w) (fun l => v l w) i l = _
    congr 1
    funext l
    exact rowCutInf_apply ρ g w l
  rw [map_mul, map_inv, hcomp]
  exact (secMat_main n ρ (j w) (hj w)).2.1 (compGL w g) (hg w) hne

end GlobalTheory.JSW.MirCinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionMatrixInvertibleLevelReductionStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSectionMatrix_invertible_level_reduction : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n) (j : InfinitePlace E → Fin n), (∀ w, j w ≤ ρ) → (∀ v : Fin n → Cinf E, (∀ w, v (j w) w ≠ 0) → IsUnit (Matrix.of (secMatInf ρ j v)) ∧ toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1)) ∧ (∀ g ∈ levSetInf E n (ρ + 1), (∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0) → g * (toGLInf (Matrix.of (secMatInf ρ j (rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))))))⁻¹ ∈ levSetInf E n ρ) ∧ ∃ L : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E), ∀ v, secMatInf ρ j v = secMatInf ρ j 0 + L v := by
  first | (exact @GlobalTheory.JSW.MirCinf.secMatInf_main) | (exact GlobalTheory.JSW.MirCinf.secMatInf_main) | (intros; apply GlobalTheory.JSW.MirCinf.secMatInf_main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothCompactPartitionOnCompact
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff Manifold

namespace GlobalTheory

theorem exists_smooth_compact_partition_on_compact :
    ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (K : Set Z),
    IsCompact K → ∀ (ι : Type) [Fintype ι] (U : ι → Set Z), (∀ i, IsOpen (U i)) →
    K ⊆ ⋃ i, U i → ∃ φ : ι → Z → ℂ, (∀ i, ContDiff ℝ ∞ (φ i) ∧ HasCompactSupport (φ i) ∧
      tsupport (φ i) ⊆ U i) ∧ ∀ z ∈ K, ∑ i, φ i z = 1 := by
  intro Z _ _ _ K hK ι _ U hU hKU
  classical
  haveI : ProperSpace Z := FiniteDimensional.proper ℝ Z
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Z)
  have hcov : K ⊆ ⋃ i, U i ∩ Metric.ball (0 : Z) R := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKU hz)
    exact Set.mem_iUnion.2 ⟨i, hi, hR hz⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ Z)
    hK.isClosed (fun i => U i ∩ Metric.ball (0 : Z) R)
    (fun i => (hU i).inter Metric.isOpen_ball) hcov
  have hρs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i) := fun i =>
    contMDiff_iff_contDiff.1 (ρ i).contMDiff
  refine ⟨fun i z => ((ρ i z : ℝ) : ℂ), fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hρs i)
  · have h1 : tsupport (fun z => ((ρ i z : ℝ) : ℂ)) ⊆ tsupport (ρ i) :=
      tsupport_comp_subset Complex.ofReal_zero _
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Z) R) (isClosed_tsupport _) ?_
    exact h1.trans ((hρ i).trans (Set.inter_subset_right.trans Metric.ball_subset_closedBall))
  · exact (tsupport_comp_subset Complex.ofReal_zero _).trans ((hρ i).trans Set.inter_subset_left)
  · intro z hz
    have h2 := ρ.sum_eq_one hz
    rw [finsum_eq_sum_of_fintype] at h2
    simp only
    rw [← Complex.ofReal_sum, h2, Complex.ofReal_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovArchimedeanTotallyComplexMirabolic
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem isOpenEmbedding_valGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

theorem isOpen_isUnit_ofInf : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
  have := (isOpenEmbedding_valGLInf (E := E) (n := n)).isOpen_range
  convert this using 1
  ext x
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩

theorem continuousOn_toGLInf :
    ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
  rw [isOpenEmbedding_valGLInf.isInducing.continuousOn_iff]
  exact continuousOn_id.congr fun x hx => val_toGLInf hx

theorem isWhitInf_smoothMatInf {W : GL (Fin n) (Cinf E) → ℂ} (hW : IsWhitInf W) (α : (Fin n → Fin n → Cinf E) → ℂ) :
    IsWhitInf (smoothMatInf α W) := by
  intro u hu g
  simp only [smoothMatInf]
  rw [← integral_const_mul]
  congr 1
  funext a
  rw [Units.val_mul, mul_assoc (u : Matrix (Fin n) (Fin n) (Cinf E))]
  by_cases h : IsUnit ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a)
  · obtain ⟨x, hx⟩ := h
    rw [← hx, ← Units.val_mul, onMatInf_val, onMatInf_val, hW u hu]; ring
  · have h' : ¬ IsUnit ((u : Matrix (Fin n) (Fin n) (Cinf E)) * ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a)) :=
      fun h' => h ((Units.isUnit_units_mul u _).1 h')
    simp [onMatInf, h, h']

theorem mem_unipB_of_levSetInf_zero {g : GL (Fin n) (Cinf E)} (hg : g ∈ levSetInf E n 0) :
    g ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j h => (mem_levSetInf.1 hg i (Nat.zero_le _)).1 j h,
    fun i => (mem_levSetInf.1 hg i (Nat.zero_le _)).2⟩

theorem levSetInf_mono {r : ℕ} {g : GL (Fin n) (Cinf E)} (hg : g ∈ levSetInf E n r) : g ∈ levSetInf E n (r + 1) :=
  mem_levSetInf.2 fun i hi => mem_levSetInf.1 hg i (by omega)

theorem levRepInf_zero (n : ℕ) : LevRepInf E n 0 fun W => W 1 := by
  intro Y _ _ _ B hB hBe ⟨D, C, hD, _, hDC⟩
  have h1 : (1 : GL (Fin n) (Cinf E)) ∈ levSetInf E n 0 := (GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup E n 0).2.2.1 1 (one_mem _)
  have hΦ : ContDiff ℝ ∞ fun y => B (y, matInf (1 : GL (Fin n) (Cinf E))) :=
    hB.comp_contDiff (contDiff_id.prodMk contDiff_const) fun y => (1 : GL (Fin n) (Cinf E)).isUnit
  have hΦc : HasCompactSupport fun y => B (y, matInf (1 : GL (Fin n) (Cinf E))) :=
    HasCompactSupport.intro hD fun y hy => by_contra fun h => hy (hDC y 1 h1 h).1
  obtain ⟨X, _, ν, _, κ, τ, h1, h2, h3, h4⟩ := GlobalTheory.JSW.exists_rapid_superposition_characters _ _ hΦ hΦc
  refine ⟨fun W y g => ∫ x, κ x * (𝐞 (τ x y) : ℂ) * W (g * 1) ∂ν,
    ⟨X, inferInstance, ν, inferInstance, κ, fun _ => 1, τ, ⟨h1, fun _ _ => measurable_const, h2, fun N => ?_⟩,
      fun _ _ _ _ => rfl⟩, fun W _ hW y g hg => ?_⟩
  · refine ((h3 N).const_mul (htInf (1 : GL (Fin n) (Cinf E)) ^ N)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_pow]; ring
  · have hg' := mem_unipB_of_levSetInf_zero hg
    have e := hBe y g hg' 1
    simp only [mul_one] at e
    simp only
    rw [integral_mul_const, ← h4, hW g hg', e]; ring

theorem step_chart (ρ : Fin n) (hρ : (ρ : ℕ) + 1 < n) {lam : (GL (Fin n) (Cinf E) → ℂ) → ℂ}
    (ih : LevRepInf E n ρ lam) {α : (Fin n → Fin n → Cinf E) → ℂ}
    (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α) (hαs : tsupport α ⊆ {x | IsUnit (Matrix.of x)})
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] {B : Y × (Fin n → Fin n → Cinf E) → ℂ}
    (hB : ContDiffOn ℝ ∞ B {p | IsUnit (Matrix.of p.2)}) (hBe : ∀ y, IsWhitInf fun g => B (y, matInf g))
    {C : Set (GL (Fin n) (Cinf E))} (hC : IsCompact C)
    (hBC : ∀ y, ∀ g ∈ levSetInf E n (ρ + 1), B (y, matInf g) ≠ 0 →
      ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u⁻¹ * g ∈ C)
    {j : InfinitePlace E → Fin n} (hj : ∀ w, j w ≤ ρ) {φ : Y × (Fin n → Cinf E) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ {z | ∀ w, z.2 (j w) w ≠ 0}) :
    ∃ T : (GL (Fin n) (Cinf E) → ℂ) → Y → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T ∧
      ∀ W, IsModGrowthInf W → IsWhitInf W → ∀ y, ∀ g ∈ levSetInf E n (ρ + 1),
        T W y g = φ (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) * B (y, matInf g) *
          lam (smoothMatInf α W) := by
  obtain ⟨hs1, hs2, L, hL⟩ := GlobalTheory.T.archimedeanSectionMatrix_invertible_level_reduction E n ρ j hj
  have hU : IsOpen {z : Y × (Fin n → Cinf E) | ∀ w, z.2 (j w) w ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const
  obtain ⟨χ, hχ, hχ1⟩ := GlobalTheory.exists_smooth_compact_partition_on_compact _ _ hφc.isCompact Unit
    (fun _ => {z : Y × (Fin n → Cinf E) | ∀ w, z.2 (j w) w ≠ 0}) (fun _ => hU) (by simpa [Set.iUnion_const] using hφs)
  obtain ⟨hχa, hχb, hχc⟩ := hχ ()
  have hsd : ContDiff ℝ ∞ (secMatInf ρ j) := by
    rw [show secMatInf ρ j = fun v => secMatInf ρ j 0 + L v from funext hL]
    exact contDiff_const.add L.contDiff
  let B' : (Y × (Fin n → Cinf E)) × (Fin n → Fin n → Cinf E) → ℂ := fun p =>
    φ p.1 * B (p.1.1, fun a b => (Matrix.of p.2 * Matrix.of (secMatInf ρ j p.1.2)) a b)
  have hB'v : ∀ (z : Y × (Fin n → Cinf E)) (g : GL (Fin n) (Cinf E)), (∀ w, z.2 (j w) w ≠ 0) →
      B' (z, matInf g) = φ z * B (z.1, matInf (g * toGLInf (Matrix.of (secMatInf ρ j z.2)))) := by
    intro z g hz
    have : matInf (g * toGLInf (Matrix.of (secMatInf ρ j z.2))) =
        fun a b => (Matrix.of (matInf g) * Matrix.of (secMatInf ρ j z.2)) a b := by
      funext a b
      simp only [matInf, Units.val_mul, val_toGLInf (hs1 _ hz).1]
      rfl
    rw [this]
  have hφ0 : ∀ z : Y × (Fin n → Cinf E), φ z ≠ 0 → ∀ w, z.2 (j w) w ≠ 0 :=
    fun z hz => hφs (subset_tsupport _ hz)
  have hB' : ContDiffOn ℝ ∞ B' {p | IsUnit (Matrix.of p.2)} := by
    intro p hp
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hz : p.1 ∈ tsupport φ
    · refine (hφ.comp contDiff_fst).contDiffAt.mul ?_
      have hin : ContDiff ℝ ∞ fun p : (Y × (Fin n → Cinf E)) × (Fin n → Fin n → Cinf E) =>
          (p.1.1, fun a b => (Matrix.of p.2 * Matrix.of (secMatInf ρ j p.1.2)) a b) := by
        refine contDiff_fst.fst.prodMk (contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_)
        simp only [Matrix.mul_apply, Matrix.of_apply]
        refine ContDiff.sum fun l _ => ContDiff.mul ?_ ?_
        · exact contDiff_pi.1 (contDiff_pi.1 contDiff_snd a) l
        · exact contDiff_pi.1 (contDiff_pi.1 (hsd.comp contDiff_fst.snd) l) b
      refine ContDiffAt.comp p (hB.contDiffAt ((isOpen_isUnit_ofInf.preimage continuous_snd).mem_nhds ?_))
        hin.contDiffAt
      exact IsUnit.mul hp (hs1 _ (hφs hz)).1
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [continuous_fst.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hz)] with y hy
      simp only [B']
      rw [hy, Pi.zero_apply, zero_mul]
  have hB'e : ∀ z, IsWhitInf fun g => B' (z, matInf g) := by
    intro z u hu g
    by_cases hz : φ z = 0
    · simp [B', hz]
    · simp only [hB'v z _ (hφ0 z hz)]
      have e := hBe z.1 u hu (g * toGLInf (Matrix.of (secMatInf ρ j z.2)))
      simp only at e
      rw [mul_assoc, e]; ring
  have hcont : ContinuousOn (fun p : GL (Fin n) (Cinf E) × (Y × (Fin n → Cinf E)) =>
      p.1 * (toGLInf (Matrix.of (secMatInf ρ j p.2.2)))⁻¹) (C ×ˢ tsupport φ) :=
    continuousOn_fst.mul (ContinuousOn.inv (continuousOn_toGLInf.comp
      (hsd.continuous.comp continuous_snd.snd).continuousOn fun p hp => (hs1 _ (hφs hp.2)).1))
  obtain ⟨T, hT, hT'⟩ := ih (Y × (Fin n → Cinf E)) B' hB' hB'e
    ⟨tsupport φ, _, hφc.isCompact, (hC.prod hφc.isCompact).image_of_continuousOn hcont, fun z g hg h => by
      have hz : φ z ≠ 0 := fun h0 => h (by simp [B', h0])
      rw [hB'v z g (hφ0 z hz)] at h
      obtain ⟨u, hu, hu'⟩ := hBC z.1 _ ((GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup E n (ρ + 1)).1 g (levSetInf_mono hg) _
        (hs1 _ (hφ0 z hz)).2) (right_ne_zero_of_mul h)
      exact ⟨subset_tsupport _ hz, u, hu, ⟨(_, z), ⟨hu', subset_tsupport _ hz⟩, by simp [mul_assoc]⟩⟩⟩
  have hT2 := GlobalTheory.T.kernelOperator_GLn_smoothAffineTranslation_section E n _ (secMatInf ρ j 0) (L.comp (ContinuousLinearMap.snd ℝ Y (Fin n → Cinf E))) (χ ()) α
    hχa hχb (fun z hz => by simpa [← hL] using (hs1 _ (hχc hz)).1) hα hαc hαs T hT
  obtain ⟨T', hT3, hT4⟩ := GlobalTheory.T.exists_kernelOperator_rowFrequency_columnTranslate E n ρ hρ Y _ hT2
  refine ⟨T', hT3, fun W hW hWe y g hg => ?_⟩
  rw [hT4 W hW hWe y g hg]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', ← hL]
  by_cases hv : ∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0
  · rw [hT' _ (GlobalTheory.T.isArchimedeanModerateGrowth_matrixSmoothingIntegral E n α hα.continuous hαc hαs W hW) (isWhitInf_smoothMatInf hWe α) _ _ (hs2 g hg hv),
      hB'v _ _ hv, inv_mul_cancel_right]
    by_cases a1 : φ (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) = 0
    · simp [a1]
    · have := hχ1 _ (subset_tsupport _ a1)
      simp only [Finset.univ_unique, Finset.sum_singleton] at this
      rw [this, one_mul]
  · have a1 : φ (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) = 0 := by_contra fun h => hv (hφ0 _ h)
    have a2 : χ () (y, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) = 0 :=
      by_contra fun h => hv (hχc (subset_tsupport _ h))
    simp [a1, a2]

theorem levRepInf_succ (ρ : Fin n) (hρ : (ρ : ℕ) + 1 < n) {lam : (GL (Fin n) (Cinf E) → ℂ) → ℂ}
    (ih : LevRepInf E n ρ lam) {α : (Fin n → Fin n → Cinf E) → ℂ} (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    (hαs : tsupport α ⊆ {x | IsUnit (Matrix.of x)}) :
    LevRepInf E n (ρ + 1) fun W => lam (smoothMatInf α W) := by
  classical
  intro Y _ _ _ B hB hBe ⟨D, C, hD, hC, hDC⟩
  have hrc : Continuous fun g : GL (Fin n) (Cinf E) => rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) := by
    refine continuous_pi fun l => ?_
    by_cases h : l ≤ ρ
    · simp only [rowCutInf, h, if_true]
      exact Units.continuous_val.matrix_elem ρ l
    · simp only [rowCutInf, h, if_false]
      exact continuous_const
  obtain ⟨hl1, hl2, hl3, hl4⟩ := GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup E n (ρ + 1)
  have hK : IsCompact (D ×ˢ ((fun g : GL (Fin n) (Cinf E) => rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ''
      (C ∩ levSetInf E n (ρ + 1)))) := hD.prod ((hC.inter_right hl4).image hrc)
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.exists_smooth_compact_partition_on_compact _ _ hK
    (InfinitePlace E → {j : Fin n // j ≤ ρ}) (fun j => {z : Y × (Fin n → Cinf E) | ∀ w, z.2 (j w).1 w ≠ 0})
    (fun _ => by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const) (by
      rintro ⟨y, v⟩ ⟨-, c, hc, rfl⟩
      choose j hj hj' using (GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero E n ρ c hc.2).2
      exact Set.mem_iUnion.2 ⟨fun w => ⟨j w, hj w⟩, hj'⟩)
  choose T hT hT' using fun j : InfinitePlace E → {j : Fin n // j ≤ ρ} => step_chart ρ hρ ih hα hαc hαs hB hBe hC
    (fun y g hg h => (hDC y g hg h).2) (j := fun w => (j w).1) (fun w => (j w).2) (hφ j).1 (hφ j).2.1 (hφ j).2.2
  refine ⟨_, GlobalTheory.T.isArchimedeanRapidKernelOperator_finset_sum E n Y _ T hT, fun W hW hWe y g hg => ?_⟩
  simp only [hT' _ W hW hWe y g hg, ← Finset.sum_mul]
  by_cases h : B (y, matInf g) = 0
  · simp [h]
  · obtain ⟨hy, u, hu, hu'⟩ := hDC y g hg h
    have hc : u⁻¹ * g ∈ levSetInf E n (ρ + 1) := hl1 _ (hl3 _ (inv_mem hu)) _ hg
    rw [hφ1 _ ⟨hy, u⁻¹ * g, ⟨hu', hc⟩, (GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero E n ρ g hg).1 _ (inv_mem hu)⟩, one_mul]

theorem exists_levRepInf (r : ℕ) :
    r < n → ∀ W₀ : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W₀ → W₀ 1 ≠ 0 → ∃ lam, lam W₀ ≠ 0 ∧ LevRepInf E n r lam := by
  induction r with
  | zero => exact fun _ W₀ _ h => ⟨_, h, levRepInf_zero n⟩
  | succ r ih =>
    intro hr W₀ hW h
    obtain ⟨α, hα, hαc, hαs, hα1⟩ := GlobalTheory.T.exists_archimedeanMatrixSmoothing_ne_zero_at_one E n W₀ hW.1 h
    obtain ⟨lam, h1, h2⟩ := ih (by omega) _ (GlobalTheory.T.isArchimedeanModerateGrowth_matrixSmoothingIntegral E n α hα.continuous hαc hαs W₀ hW) hα1
    exact ⟨_, h1, levRepInf_succ ⟨r, by omega⟩ hr h2 hα hαc hαs⟩

theorem mirSet_eq_levSetInf (m : ℕ) : mirSet (Cinf E) m = levSetInf E (m + 1) m := by
  ext g
  rw [mem_levSetInf]
  refine ⟨fun h i hi => ?_, fun h j => ?_⟩
  · obtain rfl : i = Fin.last m := Fin.ext (by have := i.2; simp; omega)
    exact ⟨fun j hj => by simp [h j, hj.ne], by simp [h _]⟩
  · have := h (Fin.last m) (by simp)
    split_ifs with hj
    · rw [hj]; exact this.2
    · exact this.1 j (Fin.lt_last_iff_ne_last.2 hj)

theorem kirillov_cinf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (β f : GL (Fin (m + 1)) (Cinf E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, β (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * β y) → (∃ B : Lie E (m + 1) → ℂ, ContDiffOn ℝ ∞ B (invSet E (m + 1)) ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), B (toL y.val) = β y) → (∃ C : Set (GL (Fin (m + 1)) (Cinf E)), IsCompact C ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, β y ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), u⁻¹ * y ∈ C) → (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, f (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * f y) → Continuous f → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) → f 1 ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, ∫ x, k x * f (y * γ x) ∂ν = β y := by
  intro E _ _ _ m β f hβe ⟨Bβ, hBβ, hBβv⟩ ⟨C, hC, hβC⟩ hfe hfc ⟨Cf, Nf, hf⟩ hf1
  have hC0 : 0 ≤ Cf := by
    have h := (norm_nonneg _).trans (hf 1)
    exact nonneg_of_mul_nonneg_left h (pow_pos (by unfold height; positivity) _)
  have hfm : IsModGrowthInf f := ⟨hfc, Cf * 3 ^ Nf, Nf, fun y => by
    have h0 : 0 ≤ height y := by unfold height; positivity
    calc ‖f y‖ ≤ Cf * height y ^ Nf := hf y
      _ ≤ Cf * (3 * htInf y) ^ Nf :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (height_le_htInf y) Nf) hC0
      _ = Cf * 3 ^ Nf * htInf y ^ Nf := by rw [mul_pow]; ring⟩
  obtain ⟨lam, hl, hrep⟩ := exists_levRepInf (E := E) (n := m + 1) m (Nat.lt_succ_self m) f hfm hf1
  have hv : ∀ g : GL (Fin (m + 1)) (Cinf E), Bβ (matInf g) = β g := fun g => hBβv g
  obtain ⟨T, ⟨X, _, ν, _, k, γ, η, hk, hT⟩, hT'⟩ := hrep Unit (fun p => Bβ p.2)
    (hBβ.comp contDiff_snd.contDiffOn fun p hp => hp) (fun _ => by simp only [hv]; exact hβe)
    ⟨Set.univ, C, isCompact_univ, hC, fun y g hg h =>
      ⟨trivial, hβC g ((mirSet_eq_levSetInf (E := E) m) ▸ hg) (by rwa [hv] at h)⟩⟩
  refine ⟨X, inferInstance, ν, inferInstance, fun x => (lam f)⁻¹ * k x, γ, ?_, fun p hp => ?_⟩
  · refine IsRapidInf.of_htInf (hk.1.const_mul _) hk.2.1 fun N => ?_
    refine ((hk.2.2.2 N).const_mul ‖(lam f)⁻¹‖).congr (Filter.Eventually.of_forall fun x => ?_)
    have : η x = 0 := Subsingleton.elim _ _
    simp [this, mul_assoc]
  · have e := hT' f hfm hfe 0 p ((mirSet_eq_levSetInf (E := E) m) ▸ hp)
    rw [hT f hfm, hv] at e
    simp only [map_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at e
    simp only [mul_assoc]
    rw [integral_const_mul, e, mul_comm, mul_assoc, mul_inv_cancel₀ hl, mul_one]

end GlobalTheory.JSW.MirCinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovArchimedeanTotallyComplexMirabolicStatement
open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_archimedean_totallyComplex_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (β f : GL (Fin (m + 1)) (Cinf E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, β (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * β y) → (∃ B : Lie E (m + 1) → ℂ, ContDiffOn ℝ ∞ B (invSet E (m + 1)) ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), B (toL y.val) = β y) → (∃ C : Set (GL (Fin (m + 1)) (Cinf E)), IsCompact C ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, β y ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), u⁻¹ * y ∈ C) → (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, f (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * f y) → Continuous f → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) → f 1 ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, ∫ x, k x * f (y * γ x) ∂ν = β y := by
  first | exact @GlobalTheory.JSW.MirCinf.kirillov_cinf | exact GlobalTheory.JSW.MirCinf.kirillov_cinf | (intros; apply GlobalTheory.JSW.MirCinf.kirillov_cinf <;> assumption)
end
