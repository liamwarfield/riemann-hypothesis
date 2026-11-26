module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.ReNonnegPsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.BQRSingle
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem b_qR_single {L : Type} [Field L] [NumberField L] {N : ℕ} [DecidableEq (InfinitePlace L)]
    (h : HS L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    qR h (Pi.single w x) = (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  unfold qR
  rw [Finset.sum_eq_single w (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
    (fun hw => absurd (Finset.mem_univ w) hw), Pi.single_eq_same]

private theorem b_cl_at {L : Type} [Field L] [NumberField L] {N : ℕ} {δ : ℝ} {h k : HS L N}
    (hcl : Cl δ h k) (w : InfinitePlace L) (x : Fin N → ℂ) :
    |(star x ⬝ᵥ (mat k w *ᵥ x)).re - (star x ⬝ᵥ (mat h w *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  classical
  have := hcl (Pi.single w x)
  rwa [b_qR_single, b_qR_single] at this

private theorem b_toR_ne {L : Type} [Field L] [NumberField L] {N : ℕ} {v : Lat L N} (hv : v ≠ 0) :
    toR v ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
  intro h0
  have := congrFun (congrFun h0 w) a
  simp only [toR, Pi.zero_apply] at this ha
  apply ha
  simpa [embO] using this

private theorem b_qR_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N} (hh : h ∈ Pos L N)
    {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨c, hc, hev⟩ := UpperTheory.V.KT.lowbd L N h hh
  have h1 := hev.self_of_nhds z
  have : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 : 0 < ‖z‖ ^ 2 := by positivity
  nlinarith

private theorem b_emb_val {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  simp [emb, toP, toK, embO, Matrix.GeneralLinearGroup.map_apply]

private theorem b_ginv {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    ((((emb L N γ) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← b_emb_val, map_inv, Pi.inv_apply]

private theorem b_transp {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    star z ⬝ᵥ (Mᵀ *ᵥ z) = star (star z) ⬝ᵥ (M *ᵥ star z) := by
  rw [star_star, mulVec_transpose, dotProduct_comm (star z), ← dotProduct_mulVec]

theorem pf_Basic : Basic := by
  intro L _ _ N hN
  classical
  refine ⟨?p1, ?p2, ?p3, ?p4, ?p5, ?p6⟩
  · intro h hh
    have hfin : ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite := fun B => by
      obtain ⟨S, hS, hev⟩ := UpperTheory.V.KT.locfin L N h hh B
      refine hS.subset fun v hv => ?_
      by_contra hvS
      exact absurd hv (not_le.2 (hev.self_of_nhds v hvS))
    have hpos : ∀ v : Lat L N, v ≠ 0 → 0 < q h v := fun v hv => b_qR_pos hh (b_toR_ne hv)
    obtain ⟨v0, hv0⟩ : ∃ v0 : Lat L N, v0 ≠ 0 := by
      refine ⟨Pi.single (⟨0, hN⟩ : Fin N) 1, fun h0 => ?_⟩
      have := congrFun h0 ⟨0, hN⟩
      simp at this
    obtain ⟨vm, ⟨hvm0, -⟩, hvm⟩ := Set.exists_min_image {v : Lat L N | v ≠ 0 ∧ q h v ≤ q h v0}
      (fun v => q h v) ((hfin (q h v0)).subset fun v hv => hv.2) ⟨v0, hv0, le_rfl⟩
    have mlow : ∀ v : Lat L N, v ≠ 0 → q h vm ≤ q h v := fun v hv => by
      by_cases hle : q h v ≤ q h v0
      · exact hvm v ⟨hv, hle⟩
      · exact (hvm v0 ⟨hv0, le_rfl⟩).trans (not_le.1 hle).le
    haveI : Nonempty {y : Lat L N // y ≠ 0} := ⟨⟨v0, hv0⟩⟩
    have hlam : lam h = q h vm := by
      unfold lam
      refine le_antisymm (ciInf_le ⟨q h vm, ?_⟩ (⟨vm, hvm0⟩ : {y : Lat L N // y ≠ 0}))
        (le_ciInf fun y => mlow y.1 y.2)
      rintro _ ⟨y, rfl⟩
      exact mlow y.1 y.2
    refine ⟨by rw [hlam]; exact hpos vm hvm0, fun v hv => by rw [hlam]; exact mlow v hv,
      ⟨vm, hvm0, hlam.symm⟩, fun w => ?_, hfin⟩
    exact (hh w).inv.transpose
  · intro γ h v
    simp only [q, qR, ac, mat_actL, smul_lat, toR_mulVec, b_ginv]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  · intro γ
    let γt : Gm L N := ⟨(γ : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ, ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ,
      by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    refine ⟨γt⁻¹, fun h hh => HS_ext fun w => ?_⟩
    simp only [dualH, mat_mkHS, ac, mat_actL, b_ginv, inv_inv]
    have hT : ((γt : Matrix (Fin N) (Fin N) (𝓞 L))).map (embO w) =
        ((γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w))ᵀ := by
      ext i j; rfl
    rw [hT]
    set M := (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hM
    set G := ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hG
    have hMG : M * G = 1 := by
      rw [hM, hG, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGinv : G⁻¹ = M := Matrix.inv_eq_left_inv hMG
    have hCT : Mᴴᵀ = Mᵀᴴ := by ext i j; simp
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hGinv, ← conjTranspose_nonsing_inv, hGinv,
      transpose_mul, transpose_mul, hCT]
  · intro δ hδ hδ2 h hh k hcl
    have hat := fun w x => b_cl_at hcl w x
    have hk : k ∈ Pos L N := fun w => by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos (mat_herm k w) (by
        intro x hx
        have h1 := (Complex.pos_iff.1 ((hh w).dotProduct_mulVec_pos hx)).1
        have h2 := (abs_le.1 (hat w x)).1
        exact Complex.pos_iff.2 ⟨by nlinarith, (herm_im _ (mat_herm k w) x).symm⟩)
    refine ⟨hk, fun z => ?_⟩
    have per : ∀ w, |(star (z w) ⬝ᵥ (mat (dualH k) w *ᵥ z w)).re -
        (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re| ≤
        2 * δ * (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re := by
      intro w
      simp only [dualH, mat_mkHS]
      rw [b_transp, b_transp]
      have i1 := invmono (mat h w) (mat k w) (hh w) (hk w) (1 - δ) (by linarith)
        (fun x => by have := (abs_le.1 (hat w x)).1; rw [sub_mul, one_mul]; linarith) (star (z w))
      have i2 := invmono (mat k w) (mat h w) (hk w) (hh w) (1 + δ)⁻¹ (by positivity)
        (fun x => by
          rw [inv_mul_le_iff₀ (by linarith)]
          have := (abs_le.1 (hat w x)).2
          rw [add_mul, one_mul]; linarith) (star (z w))
      have hD := re_nonneg_psd (hh w).inv.posSemidef (star (z w))
      have i2' := mul_le_mul_of_nonneg_left i2 (by linarith : (0 : ℝ) ≤ 1 + δ)
      rw [← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul] at i2'
      refine abs_le.2 ⟨by nlinarith [mul_nonneg hδ hD], by nlinarith [mul_nonneg hδ hD]⟩
    unfold qR
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => per w)
  · intro δ hδ h hh k hcl w u v
    have hat := fun x => b_cl_at hcl w x
    have hA : (mat k w - mat h w).IsHermitian := (mat_herm k w).sub (mat_herm h w)
    have hb : ∀ x : Fin N → ℂ, |(star x ⬝ᵥ ((mat k w - mat h w) *ᵥ x)).re| ≤
        δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
      intro x; rw [sub_mulVec, dotProduct_sub, Complex.sub_re]; exact hat x
    have := csq _ _ hA (hh w).posSemidef δ hδ hb u v
    rw [sub_mulVec, dotProduct_sub] at this
    have ha := re_nonneg_psd (hh w).posSemidef u
    have hb' := re_nonneg_psd (hh w).posSemidef v
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg δ) ha) hb']
  · obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (𝕜 := ℝ) (HSsub L N)
    have hent : ∀ w a b, ContDiff ℝ (⊤ : ℕ∞) (fun h : HS L N => mat h w a b) := fun w a b => by
      have e : (fun h : HS L N => mat h w a b) =
          (fun x : InfinitePlace L → Fin N → Fin N → ℂ => x w a b) ∘ (HSsub L N).subtypeL := rfl
      rw [e]
      exact (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) a) b).comp
        (HSsub L N).subtypeL.contDiff
    have hF : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun h : HS L N => ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ)) (Pos L N) := by
      refine contDiffOn_pi' fun w => contDiffOn_pi' fun a => contDiffOn_pi' fun b => ?_
      intro h hh
      have hdet : (mat h w).det ≠ 0 := ((hh w).det_pos).ne'
      exact (cd_inv (fun h : HS L N => mat h w) (fun i j => hent w i j) b a h hdet).contDiffWithinAt
    have e : (dualH : HS L N → HS L N) =
        fun h => P ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) := by
      funext h; exact (hP (dualH h)).symm
    rw [e]
    exact P.contDiff.comp_contDiffOn hF

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GProper
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem qR_smul_VR {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) (c : ℝ)
    (z : VR L N) : qR h (c • z) = c ^ 2 * qR h z := by
  show ∑ w, (star ((c • z) w) ⬝ᵥ mat h w *ᵥ (c • z) w).re =
    c ^ 2 * ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (c • z) w = (c : ℂ) • z w := by
    ext i; simp [Complex.real_smul]
  rw [e, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp [smul_eq_mul, Complex.conj_ofReal]
  ring

private theorem qR_pos_of_mem_Pos_of_VR_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) (z : VR L N) (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨w0, hw0⟩ : ∃ w, z w ≠ 0 := by
    by_contra hc; push_neg at hc; exact hz (funext hc)
  show 0 < ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  have hnn : ∀ w, 0 ≤ (star (z w) ⬝ᵥ mat h w *ᵥ z w).re := fun w => by
    have := (hp w).posSemidef.dotProduct_mulVec_nonneg (z w)
    exact (Complex.nonneg_iff.mp this).1
  have hpos : 0 < (star (z w0) ⬝ᵥ mat h w0 *ᵥ z w0).re := (hp w0).re_dotProduct_pos hw0
  exact Finset.sum_pos' (fun w _ => hnn w) ⟨w0, Finset.mem_univ _, hpos⟩

private theorem continuous_qR_comp {L : Type} [Field L] [NumberField L] {N : ℕ} {X : Type*}
    [TopologicalSpace X] {f : X → HS L N} {g : X → VR L N} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => qR (f x) (g x) := by
  show Continuous fun x => ∑ w, (star (g x w) ⬝ᵥ mat (f x) w *ᵥ g x w).re
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  have h1 : Continuous fun x => g x w := (continuous_apply w).comp hg
  have h2 : Continuous fun x => mat (f x) w :=
    (continuous_apply w).comp (continuous_subtype_val.comp hf)
  exact h1.star.dotProduct (h2.matrix_mulVec h1)

private theorem qR_zero_right {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) :
    qR h 0 = 0 := by
  simpa using qR_smul_VR h 0 0

private theorem exists_pos_smul_unit_sphere_eq_of_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (z : VR L N)
    (hz : z ≠ 0) : ∃ r : ℝ, 0 < r ∧ ∃ u ∈ Metric.sphere (0 : VR L N) 1, z = r • u := by
  refine ⟨‖z‖, norm_pos_iff.mpr hz, ‖z‖⁻¹ • z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

private theorem ne_zero_of_mem_unit_sphere_VR {L : Type} [Field L] [NumberField L] {N : ℕ}
    (u : VR L N) (hu : u ∈ Metric.sphere (0 : VR L N) 1) : u ≠ 0 := by
  rintro rfl
  simp at hu

private theorem exists_qR_le_mul_qR_on_compact_subset_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (K : Set (HS L N))
    (hK : IsCompact K) (hKP : K ⊆ Pos L N) (h0 : HS L N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ z, qR h0 z ≤ C * qR h z := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hc : ContinuousOn (fun p : HS L N × VR L N => qR h0 p.2 / qR p.1 p.2)
      (K ×ˢ Metric.sphere (0 : VR L N) 1) := by
    refine ContinuousOn.div ?_ (continuous_qR_comp continuous_fst continuous_snd).continuousOn ?_
    · exact (continuous_qR_comp continuous_const continuous_snd).continuousOn
    · rintro ⟨h, z⟩ ⟨hh, hz⟩
      exact (qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) z (ne_zero_of_mem_unit_sphere_VR z hz)).ne'
  obtain ⟨C, hC⟩ := (hK.prod hS).bddAbove_image hc
  refine ⟨max C 0, le_max_right _ _, fun h hh z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp [qR_zero_right]
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) u (ne_zero_of_mem_unit_sphere_VR u hu)
  have hb : qR h0 u / qR h u ≤ C := hC ⟨(h, u), ⟨hh, hu⟩, rfl⟩
  have h1 : qR h0 u ≤ max C 0 * qR h u := by
    rw [div_le_iff₀ hpu] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpu.le)
  rw [qR_smul_VR, qR_smul_VR]
  calc r ^ 2 * qR h0 u ≤ r ^ 2 * (max C 0 * qR h u) := mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = max C 0 * (r ^ 2 * qR h u) := by ring

private theorem eventually_nhds_unit_sphere_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ u ∈ Metric.sphere (0 : VR L N) 1,
      |qR k u - qR h u| - 1 / 2 * qR h u < 0 := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have c1 : Continuous fun p : HS L N × VR L N => qR p.1 p.2 :=
    continuous_qR_comp continuous_fst continuous_snd
  have c2 : Continuous fun p : HS L N × VR L N => qR h p.2 :=
    continuous_qR_comp continuous_const continuous_snd
  refine hS.eventually_forall_of_forall_eventually fun u hu => ?_
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h hp u (ne_zero_of_mem_unit_sphere_VR u hu)
  set f : HS L N × VR L N → ℝ := fun p => |qR p.1 p.2 - qR h p.2| - 1 / 2 * qR h p.2 with hf
  have hcont : Continuous f :=
    ((c1.sub c2).abs).sub (continuous_const.mul c2)
  have hv : f (h, u) < 0 := by
    show |qR h u - qR h u| - 1 / 2 * qR h u < 0
    rw [sub_self, abs_zero, zero_sub, neg_lt_zero]
    linarith
  have h2 : ∀ᶠ p in nhds (h, u), f p < 0 := hcont.continuousAt.eventually (Iio_mem_nhds hv)
  filter_upwards [h2] with p hp'
  exact hp'

private theorem eventually_nhds_abs_qR_sub_le_half_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ z : VR L N, |qR k z - qR h z| ≤ 1 / 2 * qR h z := by
  filter_upwards [eventually_nhds_unit_sphere_of_mem_Pos h hp] with k hk z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [qR_zero_right, qR_zero_right]
    norm_num
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  rw [qR_smul_VR, qR_smul_VR, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
  have h1 : |qR k u - qR h u| ≤ 1 / 2 * qR h u := by linarith [hk u hu]
  calc r ^ 2 * |qR k u - qR h u| ≤ r ^ 2 * (1 / 2 * qR h u) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = 1 / 2 * (r ^ 2 * qR h u) := by ring

theorem pf_GProper : GProper := by
  intro hB L _ _ N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨?_, ?_⟩
    · have hu : Pos L 0 = Set.univ := by
        ext h
        simp only [Set.mem_univ, iff_true]
        intro w
        refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => absurd (Subsingleton.elim x 0) hx
        exact h.2 w
      rw [hu]
      exact isOpen_univ
    · intro K _ _
      apply Set.Subsingleton.finite
      intro a _ b _
      exact Units.ext (Subsingleton.elim _ _)
  obtain ⟨hPos, hEq, -, hCl, -, -⟩ := hB L N hN
  refine ⟨?_, ?_⟩
  · refine isOpen_iff_mem_nhds.mpr fun h hh => ?_
    filter_upwards [eventually_nhds_abs_qR_sub_le_half_of_mem_Pos h hh] with k hk
    exact (hCl (1 / 2) (by norm_num) le_rfl h hh k hk).1
  intro K hK hKP
  rcases K.eq_empty_or_nonempty with rfl | ⟨h0, hh0⟩
  · simp
  obtain ⟨C, hC0, hC⟩ := exists_qR_le_mul_qR_on_compact_subset_Pos K hK hKP h0
  have hbd : ∀ i : Fin N, ∃ B : ℝ, ∀ h ∈ K, q h (Pi.single i 1 : UpperTheory.V.KT.Lat L N) ≤ B := by
    intro i
    have hc : Continuous fun h : HS L N => qR h (toR (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) :=
      continuous_qR_comp continuous_id continuous_const
    obtain ⟨B, hB'⟩ := hK.bddAbove_image hc.continuousOn
    exact ⟨B, fun h hh => hB' ⟨h, hh, rfl⟩⟩
  choose B hBd using hbd
  have hF : (⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}).Finite :=
    Set.finite_iUnion fun i => (hPos h0 (hKP hh0)).2.2.2.2 _
  have hmaps : ∀ γ ∈ {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K},
      (fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ∈
        Set.pi Set.univ (fun _ => ⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}) := by
    rintro γ ⟨h, hh, hγ⟩ i -
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    show q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ≤ C * B i
    calc q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
        ≤ C * q h (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) := hC h hh _
      _ = C * q (ac γ h) (Pi.single i 1 : UpperTheory.V.KT.Lat L N) := by rw [hEq]
      _ ≤ C * B i := mul_le_mul_of_nonneg_left (hBd i _ hγ) hC0
  have hinj : Set.InjOn (fun γ : Gm L N => fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
      {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K} := by
    intro a _ b _ hab
    have hinv : (a⁻¹ : Gm L N) = b⁻¹ := by
      apply Units.ext
      ext j i
      have e := congrFun (congrFun hab i) j
      change ((↑(a⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j =
        ((↑(b⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j at e
      simpa [Matrix.mulVec_single_one] using e
    exact inv_injective hinv
  exact Set.Finite.of_finite_image ((Set.Finite.pi fun _ => hF).subset (Set.image_subset_iff.mpr hmaps)) hinj

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.QRNonneg
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem re_nonneg {h : HS L N} (hh : h ∈ Pos L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    0 ≤ (star x ⬝ᵥ (mat h w *ᵥ x)).re :=
  (Complex.le_def.1 ((hh w).posSemidef.dotProduct_mulVec_nonneg x)).1

private theorem qR_nonneg {h : HS L N} (hh : h ∈ Pos L N) (z : VR L N) : 0 ≤ qR h z :=
  Finset.sum_nonneg fun w _ => re_nonneg hh w _

private theorem qR_para (h : HS L N) (a b : VR L N) : qR h (a - b) + qR h (a + b) = 2 * qR h a + 2 * qR h b := by
  simp only [qR, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, star_sub, star_add, mulVec_sub, mulVec_add, sub_dotProduct, add_dotProduct,
    dotProduct_sub, dotProduct_add, Complex.sub_re, Complex.add_re]
  ring

private theorem toR_add (u v : Lat L N) : toR (u + v) = toR u + toR v := by
  funext w a; simp [toR]

private def bb (h : HS L N) (u v : Lat L N) : ℝ := ∑ w, (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w)).re

private theorem bb_add (h : HS L N) (u v : Lat L N) : bb h u (v + u) = bb h u v + q h u := by
  simp only [bb, q, qR, toR_add, Pi.add_apply, mulVec_add, dotProduct_add, Complex.add_re, Finset.sum_add_distrib]

private theorem bb_sq (h : HS L N) (u v : Lat L N) :
    0 ≤ qR (rk h v) (toR u) ∧ bb h u v ^ 2 ≤ Fintype.card (InfinitePlace L) * qR (rk h v) (toR u) := by
  have e : ∀ w, (star (toR u w) ⬝ᵥ (mat (rk h v) w *ᵥ toR u w)).re =
      Complex.normSq (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w)) := by
    intro w
    have e1 : mat (rk h v) w = vecMulVec (mat h w *ᵥ toR v w) (star (mat h w *ᵥ toR v w)) := rfl
    rw [e1, dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul,
      star_dotProduct (mat h w *ᵥ toR v w), Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have e2 : qR (rk h v) (toR u) = ∑ w, Complex.normSq (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w)) :=
    Finset.sum_congr rfl fun w _ => e w
  rw [e2]
  refine ⟨Finset.sum_nonneg fun w _ => Complex.normSq_nonneg _, sq_sum_le_card_mul_sum_sq.trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) (Nat.cast_nonneg _)
  rw [sq]; exact Complex.re_sq_le_normSq _

private theorem rho_mem (x : ℝ) : 0 ≤ rho x ∧ rho x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem rho_one {x : ℝ} (hx : x ≤ 1) : rho x = 1 := Real.smoothTransition.one_of_one_le (by linarith)

private theorem rho_zero {x : ℝ} (hx : 4 ≤ x) : rho x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem num1 {r B a F G : ℝ} (h1 : B ^ 2 ≤ r * F) (h2 : (B + a) ^ 2 ≤ r * G) : a ^ 2 / 2 ≤ r * (F + G) := by
  nlinarith [sq_nonneg (2 * B + a)]

private theorem num2 {r a s C n Z W : ℝ} (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hC : 0 < C) (hZ : 1 ≤ Z) (hW : 0 ≤ W)
    (h1 : s ≤ 16 * a) (h2 : Z ≤ C * n) (h3 : n * (a ^ 2 / 2) ≤ r * (W + W)) : 1 / (1024 * r * C) ≤ (s ^ 2 * Z)⁻¹ * W := by
  rw [← div_eq_inv_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * (s ^ 2 * Z) ≤ 1 * ((16 * a) ^ 2 * (C * n)) := by gcongr
    _ = 512 * C * (n * (a ^ 2 / 2)) := by ring
    _ ≤ 512 * C * (r * (W + W)) := by gcongr
    _ = _ := by ring

private theorem term_low {C : ℝ} (hC : 0 < C) {h : HS L N} (hh : h ∈ Pos L N)
    (hfin : ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite) {s : ℝ} (hs : 0 < s)
    (hcnt : (({v : Lat L N | q h v ≤ 16 * (s / 4)}.ncard : ℕ) : ℝ) ≤ C * ({v : Lat L N | q h v ≤ s / 4}.ncard : ℕ))
    (u : Lat L N) (ha : 0 < q h u) (h1 : s ≤ 16 * q h u) (h2 : 4 * q h u ≤ s) :
    1 / (1024 * (Fintype.card (InfinitePlace L) : ℝ) * C) ≤ qR (term s h) (toR u) := by
  classical
  have hz : ∀ v, v ∉ (hfin (16 * (s / 4))).toFinset → rho (q h v / s) = 0 := fun v hv => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hv
    exact rho_zero (by rw [le_div_iff₀ hs]; linarith)
  have hone : ∀ v, q h v ≤ s → v ∈ (hfin (16 * (s / 4))).toFinset ∧ rho (q h v / s) = 1 := fun v hv =>
    ⟨by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; linarith, rho_one ((div_le_one hs).2 hv)⟩
  rw [Set.ncard_eq_toFinset_card _ (hfin _), Set.ncard_eq_toFinset_card _ (hfin _)] at hcnt
  have hS : ∀ v ∈ (hfin (s / 4)).toFinset, q h v ≤ s / 4 := fun v hv => by
    rwa [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  generalize (hfin (16 * (s / 4))).toFinset = T at hz hone hcnt
  generalize (hfin (s / 4)).toFinset = S at hS hcnt
  have eZ : zed s h = ∑ v ∈ T, rho (q h v / s) :=
    finsum_eq_sum_of_support_subset _ fun v hv => by_contra fun hn => hv (hz v hn)
  have eW : (∑ᶠ v : Lat L N, rho (q h v / s) • rk h v) = ∑ v ∈ T, rho (q h v / s) • rk h v :=
    finsum_eq_sum_of_support_subset _ fun v hv => by_contra fun hn => hv (by simp only [hz v hn, zero_smul])
  have eT : qR (term s h) (toR u) = (s ^ 2 * zed s h)⁻¹ * ∑ v ∈ T, rho (q h v / s) * qR (rk h v) (toR u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← evR_apply, term, eW, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul, evR_apply]
  have hq0 : q h 0 ≤ s := by
    have : toR (0 : Lat L N) = 0 := by funext w a; simp [toR]
    simp [q, qR, this, hs.le]
  have hZ1 : 1 ≤ zed s h := by
    rw [eZ, ← (hone 0 hq0).2]
    exact Finset.single_le_sum (f := fun v => rho (q h v / s)) (fun v _ => (rho_mem _).1) (hone 0 hq0).1
  have hZ2 : zed s h ≤ C * S.card := by
    refine le_trans ?_ hcnt
    rw [eZ]
    exact (Finset.sum_le_card_nsmul _ _ 1 fun v _ => (rho_mem _).2).trans (by simp)
  have hnn : ∀ v, 0 ≤ rho (q h v / s) * qR (rk h v) (toR u) := fun v => mul_nonneg (rho_mem _).1 (bb_sq h u v).1
  have hsub : ∀ S' : Finset (Lat L N), (∀ v ∈ S', q h v ≤ s) →
      ∑ v ∈ S', qR (rk h v) (toR u) ≤ ∑ v ∈ T, rho (q h v / s) * qR (rk h v) (toR u) := by
    intro S' hS'
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => (hone v (hS' v hv)).1) fun v _ _ => hnn v)
    rw [(hone v (hS' v hv)).2, one_mul]
  have a1 := hsub S fun v hv => (hS v hv).trans (by linarith)
  have a2 := hsub (S.image (· + u)) fun v' hv' => by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
    have k1 := qR_para h (toR v) (toR u)
    have k2 := qR_nonneg hh (toR v - toR u)
    have k3 := hS v hv
    rw [← toR_add] at k1
    unfold q at k3 h2 ⊢
    linarith
  rw [Finset.sum_image fun a _ b _ e => add_right_cancel e] at a2
  have hr : (0 : ℝ) < Fintype.card (InfinitePlace L) := Nat.cast_pos.2 Fintype.card_pos
  rw [eT]
  refine num2 hr ha hs hC hZ1 (Finset.sum_nonneg fun v _ => hnn v) h1 hZ2 ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (add_le_add a1 a2) hr.le)
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← nsmul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun v _ => num1 (bb_sq h u v).2 ?_
  rw [← bb_add]; exact (bb_sq h u _).2

theorem pf_GRLow : GRLow := by
  intro hB hCt hE hTL L _ _ N hN μ hμ
  obtain ⟨C, hC, hcnt⟩ := hCt L N 16
  obtain ⟨_, hT⟩ := hTL L N hN
  obtain ⟨c, C2, hc, hcmp⟩ := hμ.cmp
  have hr : (0 : ℝ) < Fintype.card (InfinitePlace L) := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨min (1 / 16) (1 / (1024 * (Fintype.card (InfinitePlace L) : ℝ) * C)),
    lt_min (by norm_num) (one_div_pos.2 (mul_pos (mul_pos (by norm_num) hr) hC)), fun h hh => ?_⟩
  obtain ⟨-, hRP, hge⟩ := hE L N hN μ hμ h hh
  obtain ⟨u, hu, e⟩ := ((hB L N hN).1 _ hRP).2.2.1
  obtain ⟨hl, hlq, -, hdP, hfin⟩ := (hB L N hN).1 h hh
  have hμ0 : 0 < μ h := (mul_pos hc ((hB L N hN).1 _ hdP).1).trans_le (hcmp h hh).1
  have ha : 0 < q h u := hl.trans_le (hlq u hu)
  rw [← e]
  by_cases hcase : 1 / 16 ≤ μ h * q h u
  · exact (min_le_left _ _).trans (hcase.trans (hge (toR u)))
  refine (min_le_right _ _).trans ?_
  obtain ⟨k, hk0, hk1⟩ := exists_mem_Ico_zpow (mul_pos (show (0 : ℝ) < 16 by norm_num) ha) (show (1 : ℝ) < 4 by norm_num)
  have hp : ∀ j : ℤ, (0 : ℝ) < 4 ^ j := fun j => zpow_pos (by norm_num) _
  rw [zpow_add_one₀ (by norm_num)] at hk1
  refine (term_low hC hh hfin (hp k) (hcnt h hh _ (div_pos (hp k) (by norm_num)).le) u ha hk0 (by linarith)).trans ?_
  obtain ⟨k1, -, hk1'⟩ := exists_mem_Ico_zpow (div_pos (show (0 : ℝ) < 4 by norm_num) hμ0) (show (1 : ℝ) < 4 by norm_num)
  obtain ⟨k2, hk2, -⟩ := exists_mem_Ico_zpow hl (show (1 : ℝ) < 4 by norm_num)
  have hsupp : (Function.support fun j : ℤ => rho ((4 : ℝ) ^ j * μ h) • term ((4 : ℝ) ^ j) h) ⊆
      (insert k (Finset.Icc k2 k1) : Finset ℤ) := by
    intro j hj
    by_contra hn
    have hn' : j < k2 ∨ k1 < j := by
      simp only [Finset.coe_insert, Finset.coe_Icc, Set.mem_insert_iff, Set.mem_Icc] at hn
      omega
    refine hj ?_
    rcases hn' with h1 | h1
    · have : 4 * (4 : ℝ) ^ j ≤ lam h := by
        refine le_trans ?_ hk2
        rw [mul_comm, ← zpow_add_one₀ (by norm_num)]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      simp only [(hT _ (hp j) h hh 0).2.1 this, smul_zero]
    · have : 4 ≤ (4 : ℝ) ^ j * μ h := by
        rw [← div_le_iff₀ hμ0]
        exact hk1'.le.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
      simp only [rho_zero this, zero_smul]
  have h1 : rho ((4 : ℝ) ^ k * μ h) = 1 := by
    refine rho_one ((mul_le_mul_of_nonneg_right hk0 hμ0.le).trans ?_)
    have := not_le.1 hcase
    linarith [mul_comm (μ h) (q h u), mul_assoc 16 (q h u) (μ h)]
  change _ ≤ evR (toR u) (ret μ h)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ret, finsum_eq_sum_of_support_subset _ hsupp, map_add (f := _), map_sum]
  simp only [map_smul, smul_eq_mul, evR_apply]
  refine le_add_of_nonneg_of_le (mul_nonneg hμ0.le (qR_nonneg hh _)) ?_
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun j : ℤ => rho ((4 : ℝ) ^ j * μ h) * qR (term ((4 : ℝ) ^ j) h) (toR u))
    (fun j _ => mul_nonneg (rho_mem _).1 (hT _ (hp j) h hh _).1.1) (Finset.mem_insert_self k _))
  simp only [h1, one_mul]

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GRSmooth
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem sm_rho_nonneg (x : ℝ) : 0 ≤ rho x := Real.smoothTransition.nonneg _

private theorem toR_zero : toR (0 : UpperTheory.V.KT.Lat L N) = 0 := by
  unfold toR
  funext w a
  simp

private theorem q_zero_right (h : HS L N) : q h 0 = 0 := by
  unfold q qR
  rw [toR_zero]
  simp

private theorem rk_zero_right (h : HS L N) : rk h 0 = 0 := by
  ext w i j
  unfold rk mkHS
  simp [toR_zero, vecMulVec]

private theorem contDiff_hs_entry (w : InfinitePlace L) (i j : Fin N) :
    ContDiff ℝ ⊤ (fun h : HS L N => (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j) := by
  have hc : ContDiff ℝ ⊤ (fun h : HS L N => (h : InfinitePlace L → Fin N → Fin N → ℂ)) :=
    (HSsub L N).subtypeL.contDiff
  exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hc w) i) j

private theorem contDiff_qR_left (x : VR L N) : ContDiff ℝ ⊤ (fun h : HS L N => qR h x) := by
  unfold qR mat
  apply ContDiff.sum
  intro w _
  refine Complex.reCLM.contDiff.comp ?_
  simp only [dotProduct, mulVec, Matrix.of_apply]
  apply ContDiff.sum
  intro i _
  refine contDiff_const.mul ?_
  apply ContDiff.sum
  intro j _
  exact (contDiff_hs_entry w i j).mul contDiff_const

private theorem contDiff_rk_left (v : UpperTheory.V.KT.Lat L N) : ContDiff ℝ ⊤ (fun h : HS L N => rk h v) := by
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (HSsub L N)
  have e : (fun h : HS L N => rk h v) =
      fun h => P ((rk h v : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) := by
    funext h
    rw [hP]
  rw [e]
  refine P.contDiff.comp ?_
  have hm : ∀ w i, ContDiff ℝ ⊤
      (fun h : HS L N => (of ((h : InfinitePlace L → Fin N → Fin N → ℂ) w) *ᵥ toR v w) i) := by
    intro w i
    simp only [mulVec, dotProduct, Matrix.of_apply]
    apply ContDiff.sum
    intro j _
    exact (contDiff_hs_entry w i j).mul contDiff_const
  unfold rk mkHS mat
  refine contDiff_pi.2 fun w => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [vecMulVec, Matrix.of_apply, Pi.star_apply]
  exact (hm w i).mul (Complex.conjCLE.contDiff.comp (hm w j))

private theorem smoothTransition_eq_zero_of_four_mul_le (y t : ℝ) (ht : 0 < t) (hy : 4 * t ≤ y) :
    Real.smoothTransition ((4 - y / t) / 3) = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 4 ≤ y / t := (le_div_iff₀ ht).2 (by linarith)
  linarith

private theorem contDiff_rho : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rho := by
  unfold rho
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem pf_GRSmooth : GRSmooth := by
  classical
  unfold GRSmooth Basic RSmooth
  intro hB L _ _ N hN μ hμ
  obtain ⟨h1, -, ⟨c, C, hc, hcmp⟩, -⟩ := hμ
  obtain ⟨hP, -⟩ := hB L N hN
  unfold ret
  apply contDiffOn_of_locally_contDiffOn
  intro h0 hh0
  have hl0 : 0 < lam h0 := (hP h0 hh0).1
  have hd0 : 0 < lamD h0 := by
    unfold lamD
    exact (hP _ (hP h0 hh0).2.2.2.1).1
  have hμ0 : 0 < μ h0 := lt_of_lt_of_le (mul_pos hc hd0) (hcmp h0 hh0).1
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (8 / μ h0) (by norm_num : (1:ℝ) < 4)
  obtain ⟨S, hSf, hS⟩ := locfin L N h0 hh0 (4 * (4:ℝ) ^ n1)
  have hq : ∀ᶠ k in nhds h0, ∀ v ∈ S, v ≠ 0 → lam h0 / 2 < q k v := by
    refine (Filter.eventually_all_finite hSf).2 ?_
    intro v _
    by_cases hv : v = 0
    · exact Filter.Eventually.of_forall (fun _ hne => absurd hv hne)
    · have hcont : ContinuousAt (fun k : HS L N => q k v) h0 :=
        (contDiff_qR_left (toR v)).continuous.continuousAt
      have hlt : lam h0 / 2 < q h0 v := by
        have := (hP h0 hh0).2.1 v hv
        linarith
      filter_upwards [hcont.eventually (lt_mem_nhds hlt)] with k hk _ using hk
  have hμe : ∀ᶠ k in nhdsWithin h0 (Pos L N), μ h0 / 2 < μ k :=
    (h1.continuousOn.continuousWithinAt hh0).eventually (lt_mem_nhds (by linarith))
  have hall : ∀ᶠ k in nhdsWithin h0 (Pos L N), μ h0 / 2 < μ k ∧
      (∀ y ∉ S, 4 * (4:ℝ) ^ n1 < q k y) ∧ (∀ v ∈ S, v ≠ 0 → lam h0 / 2 < q k v) :=
    hμe.and ((hS.filter_mono nhdsWithin_le_nhds).and (hq.filter_mono nhdsWithin_le_nhds))
  obtain ⟨u, hu, h0u, hsub⟩ := mem_nhdsWithin.1 hall
  refine ⟨u, hu, h0u, ?_⟩
  set m : ℝ := min (lam h0 / 2) (4 * (4:ℝ) ^ n1) with hmEq
  have hm : 0 < m := lt_min (by linarith) (by positivity)
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (4 / m) (by norm_num : (1:ℝ) < 4)
  set S' : Finset (UpperTheory.V.KT.Lat L N) := insert 0 hSf.toFinset with hSEq
  have key : ∀ h ∈ Pos L N ∩ u,
      μ h • h + ∑ᶠ k : ℤ, rho ((4:ℝ) ^ k * μ h) • term ((4:ℝ) ^ k) h =
      μ h • h + ∑ k ∈ Finset.Icc (-(n0:ℤ)) (n1:ℤ), rho ((4:ℝ) ^ k * μ h) •
        ((((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k))⁻¹ •
          ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) • rk h v) := by
    intro h hh
    obtain ⟨hμh, hSq, hSq0⟩ := hsub ⟨hh.2, hh.1⟩
    have hfar : ∀ k : ℤ, k ≤ (n1:ℤ) → ∀ v ∉ S', 4 * (4:ℝ) ^ k ≤ qR h (toR v) := by
      intro k hk v hv
      have hvS : v ∉ S := fun hvS => hv (Finset.mem_insert_of_mem (hSf.mem_toFinset.2 hvS))
      have h2 := hSq v hvS
      have h3 : (4:ℝ) ^ k ≤ (4:ℝ) ^ (n1:ℤ) := zpow_le_zpow_right₀ (by norm_num) hk
      rw [zpow_natCast] at h3
      have h4 : q h v = qR h (toR v) := rfl
      linarith
    have hterm : ∀ k : ℤ, k ≤ (n1:ℤ) → term ((4:ℝ) ^ k) h =
        ((((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k))⁻¹ •
          ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) • rk h v) := by
      intro k hk
      have ht : (0:ℝ) < (4:ℝ) ^ k := by positivity
      unfold term zed
      rw [finsum_eq_sum_of_support_subset _ (s := S') ?_, finsum_eq_sum_of_support_subset _ (s := S') ?_]
      · rfl
      all_goals
        refine Function.support_subset_iff'.2 fun v hv => ?_
        have hrz : rho (qR h (toR v) / (4:ℝ) ^ k) = 0 := by
          unfold rho
          exact smoothTransition_eq_zero_of_four_mul_le _ _ ht (hfar k hk v hv)
        first
          | exact hrz
          | rw [show rho (q h v / (4:ℝ) ^ k) = 0 from hrz, zero_smul]
    have hsmall : ∀ k : ℤ, k < -(n0:ℤ) → term ((4:ℝ) ^ k) h = 0 := by
      intro k hk
      have ht : (0:ℝ) < (4:ℝ) ^ k := by positivity
      have hk4 : 4 * (4:ℝ) ^ k < m := by
        have h3 : (4:ℝ) ^ k ≤ (4:ℝ) ^ (-(n0:ℤ)) := zpow_le_zpow_right₀ (by norm_num) hk.le
        rw [_root_.zpow_neg, zpow_natCast] at h3
        have h5 : ((4:ℝ) ^ n0)⁻¹ < m / 4 := by
          rw [inv_lt_comm₀ (by positivity) (by positivity)]
          calc (m / 4)⁻¹ = 4 / m := by field_simp
            _ < 4 ^ n0 := hn0
        linarith
      unfold term
      rw [finsum_eq_zero_of_forall_eq_zero, smul_zero]
      intro v
      by_cases hv : v = 0
      · rw [hv, rk_zero_right, smul_zero]
      · have hqv : m ≤ q h v := by
          by_cases hvS : v ∈ S
          · exact le_trans (min_le_left _ _) (hSq0 v hvS hv).le
          · exact le_trans (min_le_right _ _) (hSq v hvS).le
        have hrz : rho (q h v / (4:ℝ) ^ k) = 0 := by
          unfold rho
          exact smoothTransition_eq_zero_of_four_mul_le _ _ ht (by linarith)
        rw [hrz, zero_smul]
    have hbig : ∀ k : ℤ, (n1:ℤ) < k → rho ((4:ℝ) ^ k * μ h) = 0 := by
      intro k hk
      unfold rho
      apply Real.smoothTransition.zero_of_nonpos
      have h3 : (4:ℝ) ^ (n1:ℤ) ≤ (4:ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk.le
      rw [zpow_natCast] at h3
      have h6 : 8 / μ h0 * (μ h0 / 2) = 4 := by field_simp; ring
      have h7 : 8 / μ h0 * (μ h0 / 2) ≤ (4:ℝ) ^ k * μ h := by
        apply mul_le_mul (by linarith) hμh.le (by positivity) (by positivity)
      linarith
    congr 1
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-(n0:ℤ)) (n1:ℤ)) ?_]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [hterm k (Finset.mem_Icc.1 hk).2]
    · refine Function.support_subset_iff'.2 fun k hk => ?_
      simp only [Finset.coe_Icc, Set.mem_Icc, not_and_or, not_le] at hk
      rcases hk with hk | hk
      · show rho ((4:ℝ) ^ k * μ h) • term ((4:ℝ) ^ k) h = 0
        rw [hsmall k hk, smul_zero]
      · show rho ((4:ℝ) ^ k * μ h) • term ((4:ℝ) ^ k) h = 0
        rw [hbig k hk, zero_smul]
  refine ContDiffOn.congr ?_ key
  refine (h1.mono Set.inter_subset_left).smul contDiffOn_id |>.add ?_
  refine ContDiffOn.sum fun k _ => ?_
  have hr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun h : HS L N => rho ((4:ℝ) ^ k * μ h)) (Pos L N ∩ u) :=
    contDiff_rho.comp_contDiffOn (contDiffOn_const.mul (h1.mono Set.inter_subset_left))
  have hz : ∀ v : UpperTheory.V.KT.Lat L N, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : HS L N => rho (qR h (toR v) / (4:ℝ) ^ k)) (Pos L N ∩ u) := fun v =>
    (contDiff_rho.comp (((contDiff_qR_left (toR v)).of_le le_top).div_const _)).contDiffOn
  have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : HS L N => (((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k))⁻¹) (Pos L N ∩ u) := by
    refine ContDiffOn.inv (contDiffOn_const.mul (ContDiffOn.sum fun v _ => hz v)) ?_
    intro h _
    have ht : (0:ℝ) < (4:ℝ) ^ k := by positivity
    have hone : (1:ℝ) ≤ ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) := by
      have h0mem : (0 : UpperTheory.V.KT.Lat L N) ∈ S' := by
        rw [hSEq]
        exact Finset.mem_insert_self _ _
      have hle := Finset.single_le_sum (f := fun v => rho (qR h (toR v) / (4:ℝ) ^ k))
        (fun v _ => sm_rho_nonneg _) h0mem
      have hq0 : qR h (toR 0) = 0 := q_zero_right h
      have hr0 : rho 0 = 1 := by
        unfold rho
        exact Real.smoothTransition.one_of_one_le (by norm_num)
      simp only [hq0, zero_div, hr0] at hle
      exact hle
    have : 0 < ((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) := by positivity
    exact this.ne'
  have hsum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : HS L N => ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) • rk h v)
      (Pos L N ∩ u) := by
    refine ContDiffOn.sum fun v _ => ?_
    exact ContDiffOn.smul (hz v) (((contDiff_rk_left v).of_le le_top).contDiffOn)
  exact hr.smul (hinv.smul hsum)

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end
