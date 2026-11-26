module

public import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm
public import Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.FinBound
open MeasureTheory Filter Topology GlobalTheory.WeilM

noncomputable section
namespace PositivityTheory.ThKEst.W

theorem real_bound (h : CoefReal) (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] (β : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hβ : ∀ y, β y = 0 → y = 0) :
    ∃ ν : Measure Y, ν.IsAddHaarMeasure ∧ ∀ N : ℕ, ∃ p : Seminorm ℂ (SchwartzMap Y ℂ), Continuous p ∧
      ∀ (f₁ f₂ : SchwartzMap Y ℂ) (x y : Y), ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (β y u : ℝ)) * f₁ (u + x) *
        (starRingEnd ℂ) (f₂ u) ∂ν‖ * (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂ := by
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ Y))
  let T : V ≃L[ℝ] Y := (toEuclidean (E := Y)).symm
  refine ⟨Measure.map T volume, T.isAddHaarMeasure_map _, fun N => ?_⟩
  obtain ⟨p, hp, hb⟩ := h V N
  let S : Y →ₗ[ℝ] (V →L[ℝ] ℝ) := (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ)).toLinearMap ∘ₗ
    (β.compl₂ T.toLinearEquiv.toLinearMap)
  have hS : ∀ y v, S y v = β y (T v) := fun _ _ => rfl
  obtain ⟨K₁, -, hK₁⟩ := S.exists_antilipschitzWith (LinearMap.ker_eq_bot'.2 fun y hy => hβ y (LinearMap.ext fun u => by
    have := hS y (T.symm u)
    rw [hy, T.apply_symm_apply] at this
    exact this.symm))
  let K : NNReal := 1 + K₁ + ‖(T : V →L[ℝ] Y)‖₊
  have hK : (K : ℝ) = 1 + K₁ + ‖(T : V →L[ℝ] Y)‖ := rfl
  let c := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  refine ⟨K ^ N • p.comp c.toLinearMap, (hp.comp c.continuous).const_smul (K ^ N), fun f₁ f₂ x y => ?_⟩
  have h1 := hb (c f₁) (c f₂) (T.symm x) ((InnerProductSpace.toDual ℝ V).symm (S y))
  have e : ∫ u, Complex.exp (2 * Real.pi * Complex.I * (β y u : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)
      ∂(Measure.map T volume) = ∫ u, Complex.exp (2 * Real.pi * Complex.I *
        (inner ℝ u ((InnerProductSpace.toDual ℝ V).symm (S y)) : ℝ)) * c f₁ (u + T.symm x) * (starRingEnd ℂ) (c f₂ u) := by
    rw [show Measure.map T volume = Measure.map T.toHomeomorph.toMeasurableEquiv volume from rfl, integral_map_equiv]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only [real_inner_comm _ u, InnerProductSpace.toDual_symm_apply, hS]
    simp [c]
  rw [e]
  rw [LinearIsometryEquiv.norm_map] at h1
  have hx : ‖x‖ ≤ ‖(T : V →L[ℝ] Y)‖ * ‖T.symm x‖ := by simpa using (T : V →L[ℝ] Y).le_opNorm (T.symm x)
  have hy : ‖y‖ ≤ K₁ * ‖S y‖ := by
    have := hK₁.le_mul_dist y 0
    rwa [map_zero, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero] at this
  have n1 := norm_nonneg (T : V →L[ℝ] Y)
  have n2 := norm_nonneg (T.symm x)
  have n3 := norm_nonneg (S y)
  have n4 := K₁.coe_nonneg
  have h2 : 1 + ‖x‖ + ‖y‖ ≤ K * (1 + ‖T.symm x‖ + ‖S y‖) := by
    rw [hK]
    nlinarith [mul_nonneg n1 n3, mul_nonneg n4 n2]
  have hK1 : (1 : ℝ) ≤ K ^ N := one_le_pow₀ (by rw [hK]; linarith)
  have q := mul_nonneg (apply_nonneg p (c f₁)) (apply_nonneg p (c f₂))
  calc _ ≤ _ * (K * (1 + ‖T.symm x‖ + ‖S y‖)) ^ N := by gcongr
    _ = K ^ N * (_ * (1 + ‖T.symm x‖ + ‖S y‖) ^ N) := by rw [mul_pow, mul_left_comm]
    _ ≤ K ^ N * (p (c f₁) * p (c f₂)) := by gcongr
    _ ≤ K ^ N * (K ^ N * (p (c f₁) * p (c f₂))) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left q hK1) (zero_le_one.trans hK1)
    _ = _ := by
      simp only [Seminorm.smul_apply, Seminorm.comp_apply, NNReal.smul_def, NNReal.coe_pow, smul_eq_mul,
        ContinuousLinearMap.coe_coe]
      ring

theorem sb_inv {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {φ : G → ℂ} (hφ : φ ∈ SB G) :
    ∀ᶠ k in 𝓝 (0 : G), ∀ x, φ (x + k) = φ x := by
  have h1 : ∀ᶠ k in 𝓝 (0 : G), ∀ x ∈ tsupport φ, φ (x + k) = φ x ∧ φ (x - k) = φ x :=
    hφ.2.isCompact.eventually_forall_of_forall_eventually fun x _ => by
      have a := (hφ.1.comp_continuous (f := fun z : G × G => z.2 + z.1) (by fun_prop)).eventually_eq (0, x)
      have b := (hφ.1.comp_continuous (f := fun z : G × G => z.2 - z.1) (by fun_prop)).eventually_eq (0, x)
      have c := (hφ.1.comp_continuous (f := fun z : G × G => z.2) (by fun_prop)).eventually_eq (0, x)
      filter_upwards [a, b, c] with z a b c
      simp only [Function.comp, add_zero, sub_zero] at a b c
      exact ⟨a.trans c.symm, b.trans c.symm⟩
  filter_upwards [h1] with k hk x
  by_cases hx : x ∈ tsupport φ
  · exact (hk x hx).1
  by_cases hx' : x + k ∈ tsupport φ
  · simpa using (hk _ hx').2.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem fin_bound {G H : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] [TopologicalSpace H] (ν : Measure G) [ν.IsAddHaarMeasure] (χ : H → G → ℂ) (hn : ∀ y u, ‖χ y u‖ = 1)
    (ha : ∀ y u u', χ y (u + u') = χ y u * χ y u')
    (hd : ∀ U ∈ 𝓝 (0 : G), ∃ K, IsCompact K ∧ ∀ y, (∀ u ∈ U, χ y u = 1) → y ∈ K) {φ₁ φ₂ : G → ℂ} (h₁ : φ₁ ∈ SB G)
    (h₂ : φ₂ ∈ SB G) : ∃ (C : ℝ) (K : Set (G × H)), IsCompact K ∧ ∀ x y,
      ‖∫ u, χ y u * φ₁ (u + x) * (starRingEnd ℂ) (φ₂ u) ∂ν‖ ≤ C ∧
      (∫ u, χ y u * φ₁ (u + x) * (starRingEnd ℂ) (φ₂ u) ∂ν ≠ 0 → (x, y) ∈ K) := by
  obtain ⟨C, hC⟩ := h₁.1.continuous.bounded_above_of_compact_support h₁.2
  obtain ⟨K, hK, hK'⟩ := hd _ ((sb_inv h₁).and (sb_inv h₂))
  have hi : Integrable φ₂ ν := h₂.1.continuous.integrable_of_hasCompactSupport h₂.2
  refine ⟨∫ u, C * ‖φ₂ u‖ ∂ν, ((fun z : G × G => z.1 - z.2) '' (tsupport φ₁ ×ˢ tsupport φ₂)) ×ˢ K,
    ((h₁.2.isCompact.prod h₂.2.isCompact).image (by fun_prop)).prod hK, fun x y => ⟨?_, fun h0 => ⟨?_, hK' y fun k hk => ?_⟩⟩⟩
  · refine norm_integral_le_of_norm_le (hi.norm.const_mul C) (.of_forall fun u => ?_)
    rw [norm_mul, norm_mul, hn, one_mul, RCLike.norm_conj]
    gcongr
    exact hC _
  · by_contra hx
    refine h0 (integral_eq_zero_of_ae (.of_forall fun u => ?_))
    by_contra hu
    simp only [Pi.zero_apply, mul_eq_zero, not_or, map_eq_zero] at hu
    exact hx ⟨(u + x, u), ⟨subset_tsupport _ hu.1.2, subset_tsupport _ hu.2⟩, add_sub_cancel_left _ _⟩
  · refine (mul_eq_right₀ h0).1 ?_
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_add_right_eq_self _ k]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only
    rw [ha, add_right_comm, hk.1, hk.2]
    ring

end PositivityTheory.ThKEst.W
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK NumberField.mixedEmbedding
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open scoped TensorProduct ENNReal NNReal Classical

noncomputable section
namespace PositivityTheory.ThKEst

namespace W

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem trace_emb (a : F) : Algebra.trace ℝ (mixedSpace F) (mixedEmbedding F a) = (Algebra.trace ℚ F a : ℚ) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (latticeBasis F), Algebra.trace_eq_matrix_trace (integralBasis F), Matrix.trace,
    Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    latticeBasis_apply, ← map_mul, latticeBasis_repr_apply]

theorem trace_nondeg (l : κ → mixedSpace F) (h : ∀ y, Algebra.trace ℝ (mixedSpace F) (l ⬝ᵥ y) = 0) : l = 0 := by
  classical
  funext i
  refine (latticeBasis F).ext_elem fun j => ?_
  have := h (Pi.single i (mixedEmbedding F ((integralBasis F).traceDual j)))
  rw [dotProduct_single, ← (latticeBasis F).sum_repr (l i)] at this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, latticeBasis_apply, ← map_mul, trace_emb,
    Module.Basis.trace_mul_traceDual] at this
  simpa [apply_ite] using this

theorem dual_one [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) : ∃ C : Set (Af F), IsCompact C ∧
    ∀ y, (∀ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ψ (fi F (a * y)) = 1) → y ∈ C := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ
  choose b hb using h1
  have hO : ∀ v : Pl (F := F), IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := fun v => isCompact_iff_compactSpace.2
    (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  let P : Pl (F := F) → Prop := fun v => ∀ y : Fv F v,
    (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F
  refine ⟨_, isCompact_box (fun v => if P v then (v.adicCompletionIntegers F : Set (Fv F v)) else
    (b v * ·) '' (v.adicCompletionIntegers F : Set (Fv F v))) (fun v => ?_) ?_, fun y hy v => ?_⟩
  · split_ifs
    · exact hO v
    · exact (hO v).image (continuous_const.mul continuous_id)
  · filter_upwards [h2] with v hv
    rw [if_pos hv]
  · have key : ∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (evalV F v y * t) = 1 := fun t ht => by
      have := hy (singleFin v t) fun u => by
        show evalV F u (singleFin v t) ∈ _
        by_cases e : u = v
        · subst e; rwa [evalV_singleFin_self]
        · rw [evalV_singleFin_ne e]; exact zero_mem _
      rw [show fi F (singleFin v t * y) = atPlace v t * fi F y from (mul_fi (atPlace v t) y).symm, atPlace_mul_right,
        mul_comm] at this
      exact this
    split_ifs with h
    · exact (h _).1 key
    · have hb0 : b v ≠ 0 := fun h0 => hb v (by simpa [h0] using key 0 (zero_mem _))
      refine ⟨evalV F v y / b v, ?_, mul_div_cancel₀ _ hb0⟩
      by_contra hn
      have h3 := ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left hn
      have hy0 : evalV F v y ≠ 0 := fun h0 => hn (by rw [h0, zero_div]; exact zero_mem _)
      have := key _ h3
      rw [inv_div, mul_div_cancel₀ _ hy0] at this
      exact hb v this

theorem dual_cpt [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (U : Set (κ → Af F)) (hU : U ∈ 𝓝 0) :
    ∃ K, IsCompact K ∧ ∀ y : κ → Af F, (∀ u ∈ U, ψ (fi F (u ⬝ᵥ y)) = 1) → y ∈ K := by
  obtain ⟨C, hC, h⟩ := dual_one hψ
  choose N hN hNU using fun i : κ => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F ((fun x : Af F => (Pi.single i x : κ → Af F)) ⁻¹' U)
    ((continuous_single (A := fun _ : κ => Af F) i).continuousAt.preimage_mem_nhds (show U ∈ 𝓝 (Pi.single i 0) by rwa [Pi.single_zero]))
  refine ⟨_, isCompact_univ_pi fun i => hC.image (f := (algebraMap F (Af F) (N i : F)⁻¹ * ·))
    (continuous_const.mul continuous_id), fun y hy i _ => ⟨N i • y i, h _ fun a ha => ?_, ?_⟩⟩
  · have := hy _ (hNU i a ha)
    rwa [single_dotProduct, smul_mul_assoc, ← mul_smul_comm] at this
  · have : (N i : F) ≠ 0 := by exact_mod_cast (hN i).ne'
    simp only
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ this, map_one, one_mul]


variable (F κ) in
def spl : ((κ → mixedSpace F) × (κ → Af F)) ≃+ (κ → AF F) where
  toFun p i := re F (p.1 i) + fi F (p.2 i)
  invFun x := (fun i => evI F (x i), fun i => (x i).2)
  left_inv p := Prod.ext (funext fun i => by simp only [evI_add, evI_re, evI_fi, add_zero]) (funext fun i => zero_add _)
  right_inv x := funext fun i => re_add_fi _
  map_add' p q := funext fun i => by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add (f := _)]; abel

theorem spl_cont : Continuous (spl F κ) := by
  show Continuous (fun p : (κ → mixedSpace F) × (κ → Af F) => fun i => re F (p.1 i) + fi F (p.2 i))
  have hfi : Continuous (fi F) := by
    show Continuous fun x : Af F => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F 0 x
    exact continuous_const.prodMk continuous_id
  exact continuous_pi fun i => (continuous_re.comp ((continuous_apply i).comp continuous_fst)).add
    (hfi.comp ((continuous_apply i).comp continuous_snd))

theorem spl_symm_cont : Continuous (spl F κ).symm := by
  show Continuous (fun x : κ → AF F => ((fun i => evI F (x i)), (fun i => (x i).2)))
  exact (continuous_pi fun i => cont_evI.comp (continuous_apply i)).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

theorem pureA_spl (f : (κ → mixedSpace F) → ℂ) (φ : (κ → Af F) → ℂ) (p : (κ → mixedSpace F) × (κ → Af F)) :
    pureA F f φ (spl F κ p) = f p.1 * φ p.2 := by
  show f (fun i => evI F (spl F κ p i)) * φ (fun i => (spl F κ p i).2) = f p.1 * φ p.2
  congr 1
  · congr 1
    funext i
    show evI F (re F (p.1 i) + fi F (p.2 i)) = p.1 i
    rw [evI_add, evI_re, evI_fi, add_zero]
  · congr 1
    funext i
    show (re F (p.1 i)).2 + (fi F (p.2 i)).2 = p.2 i
    exact zero_add _

theorem spl_dot (p q : (κ → mixedSpace F) × (κ → Af F)) :
    spl F κ p ⬝ᵥ spl F κ q = re F (p.1 ⬝ᵥ q.1) + fi F (p.2 ⬝ᵥ q.2) := by
  simp only [dotProduct]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (re F (p.1 i) + fi F (p.2 i)) * (re F (q.1 i) + fi F (q.2 i)) =
    re F (p.1 i * q.1 i) + fi F (p.2 i * q.2 i)
  rw [add_mul, mul_add, mul_add, re_mul, re_mul_fi, mul_comm (fi F (p.2 i)) (re F (q.1 i)), re_mul_fi, mul_fi,
    add_zero, zero_add]
  rfl

theorem coef_split [IsTotallyReal F] (hR : CoefReal) {ψ : AddChar (AF F) ℂ} (hstd : IsStd ψ) (μ : Measure (κ → AF F))
    (hμ : μ.IsAddHaarMeasure) {φ₁ φ₂ : (κ → Af F) → ℂ} (h₁ : φ₁ ∈ SB _) (h₂ : φ₂ ∈ SB _) (N : ℕ) :
    ∃ (p : Seminorm ℂ (SInf F κ)) (C : ℝ) (K : Set ((κ → Af F) × (κ → Af F))), Continuous p ∧ 0 ≤ C ∧ IsCompact K ∧
      ∀ (f₁ f₂ : SInf F κ) x y, ‖coef F ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (spl F κ x, spl F κ y)‖ *
        (1 + ‖x.1‖ + ‖y.1‖) ^ N ≤ C * (p f₁ * p f₂) ∧
        (coef F ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (spl F κ x, spl F κ y) ≠ 0 → (x.2, y.2) ∈ K) := by
  have hψ := isCharAF hstd
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ → Af F) := borel _
  haveI : BorelSpace (κ → Af F) := ⟨rfl⟩
  letI : MeasurableSpace (κ → mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedSpace F) := ⟨rfl⟩
  let β : (κ → mixedSpace F) →ₗ[ℝ] (κ → mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y u => -Algebra.trace ℝ (mixedSpace F) (u ⬝ᵥ y))
      (fun _ _ _ => by rw [dotProduct_add, map_add (f := _), neg_add]) (fun _ _ _ => by rw [dotProduct_smul, map_smul, smul_neg])
      (fun _ _ _ => by rw [add_dotProduct, map_add (f := _), neg_add]) (fun _ _ _ => by rw [smul_dotProduct, map_smul, smul_neg])
  obtain ⟨ν, hν, hb⟩ := real_bound hR _ β fun y hy => trace_nondeg y fun u => by
    rw [dotProduct_comm, ← neg_eq_zero]
    exact LinearMap.congr_fun hy u
  obtain ⟨p, hp, hb⟩ := hb N
  let ν' : Measure (κ → Af F) := Measure.addHaar
  obtain ⟨C, K, hK, hC⟩ := fin_bound ν' (fun y u : κ → Af F => ψ (fi F (u ⬝ᵥ y))) (fun _ _ => hψ.2.1 _)
    (fun _ _ _ => by rw [add_dotProduct, map_add (f := _), AddChar.map_add_eq_mul]) (dual_cpt hψ) h₁ h₂
  haveI : (ν.prod ν').IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI : (Measure.map (spl F κ) (ν.prod ν')).IsAddHaarMeasure :=
    (spl F κ).isAddHaarMeasure_map (ν.prod ν') spl_cont spl_symm_cont
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ = c • Measure.map (spl F κ) (ν.prod ν') := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  let e : ((κ → mixedSpace F) × (κ → Af F)) ≃ₜ (κ → AF F) := ⟨(spl F κ).toEquiv, spl_cont, spl_symm_cont⟩
  have key : ∀ (f₁ f₂ : SInf F κ) x y, coef F ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (spl F κ x, spl F κ y) =
      c * (ψ (⅟(2 : AF F) * (spl F κ x ⬝ᵥ spl F κ y)) *
        ((∫ u, Complex.exp (2 * Real.pi * Complex.I * (β y.1 u : ℝ)) * f₁ (u + x.1) * (starRingEnd ℂ) (f₂ u) ∂ν) *
        ∫ u, ψ (fi F (u ⬝ᵥ y.2)) * φ₁ (u + x.2) * (starRingEnd ℂ) (φ₂ u) ∂ν')) := fun f₁ f₂ x y => by
    rw [coef, hc, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, ← integral_prod_mul,
      show Measure.map (spl F κ) (ν.prod ν') = Measure.map e.toMeasurableEquiv (ν.prod ν') from rfl,
      integral_map_equiv]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun u => ?_)
    show ψ (spl F κ u ⬝ᵥ spl F κ y + _) * pureA F f₁ φ₁ (spl F κ u + spl F κ x) *
      (starRingEnd ℂ) (pureA F f₂ φ₂ (spl F κ u)) = _
    rw [← map_add (f := _), pureA_spl, pureA_spl, spl_dot u y, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, psi_re hstd,
      map_mul (starRingEnd ℂ)]
    simp only [β, LinearMap.mk₂_apply, Prod.fst_add, Prod.snd_add, Complex.ofReal_neg, mul_neg, neg_mul]
    ring
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0).1
  refine ⟨p, c * C, K, hp, by positivity, hK, fun f₁ f₂ x y => ⟨?_, fun h => (hC x.2 y.2).2 fun h0 => h ?_⟩⟩
  · rw [key, norm_mul, norm_mul, norm_mul, hψ.2.1, one_mul, Complex.norm_real, NNReal.norm_eq]
    have a := hb f₁ f₂ x.1 y.1
    have b := (hC x.2 y.2).1
    have gen : ∀ A B D Q : ℝ, 0 ≤ A * D → A * D ≤ Q → B ≤ C → c * (A * B) * D ≤ c * C * Q := fun A B D Q h0 h1 h2 => by
      calc c * (A * B) * D = c * (B * (A * D)) := by ring
        _ ≤ c * (C * Q) := mul_le_mul_of_nonneg_left (mul_le_mul h2 h1 h0 hC0) c.coe_nonneg
        _ = _ := (mul_assoc _ _ _).symm
    exact gen _ _ _ _ (by positivity) a b
  · rw [key, h0, mul_zero, mul_zero, mul_zero]

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem lin_cont (m : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] Ten F E n d) : Continuous m := by
  have := PositivityTheory.ThKEst.LatticeQuotientCompactness.topRing (F := F) (E := E)
  have hm : ∀ x : (κ → AF F) × (κ → AF F), m x =
      ∑ i, x.1 i • m (Pi.single i 1, 0) + ∑ i, x.2 i • m (0, Pi.single i 1) := by
    intro x
    have hx : x = ∑ i, x.1 i • ((Pi.single i 1 : κ → AF F), (0 : κ → AF F)) +
        ∑ i, x.2 i • ((0 : κ → AF F), (Pi.single i 1 : κ → AF F)) := by
      ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul]
  have hc : Continuous fun x : (κ → AF F) × (κ → AF F) =>
      (∑ i, x.1 i • m (Pi.single i 1, 0) + ∑ i, x.2 i • m (0, Pi.single i 1) : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    fun_prop
  have he : (⇑m : (κ → AF F) × (κ → AF F) → Ten F E n d) = fun x =>
      (∑ i, x.1 i • m (Pi.single i 1, 0) + ∑ i, x.2 i • m (0, Pi.single i 1) : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    funext hm
  rw [he]
  exact hc

theorem piInf_fi {w : InfinitePlace F} (τ : EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : piInf τ (fi F 1 • z) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have h0 : GlobalTheory.AdelicU.evInf F w (fi F 1) = 0 := by
    show GlobalTheory.AutFunCompare.evW w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F (fi F 1)) = 0
    have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F (fi F 1) = 0 := rfl
    rw [h, map_zero]
  have h1 : piInf τ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (fi F 1)) = 0 := by
    show GlobalTheory.AdelicU.infEmb τ (GlobalTheory.AdelicU.compInf F E w (fi F 1 ⊗ₜ[F] (1 : E))) = 0
    have h2 : GlobalTheory.AdelicU.compInf F E w (fi F 1 ⊗ₜ[F] (1 : E)) = 0 := by
      show Algebra.TensorProduct.map (GlobalTheory.AdelicU.evInf F w) (AlgHom.id F E) (fi F 1 ⊗ₜ[F] (1 : E)) = 0
      rw [Algebra.TensorProduct.map_tmul, h0, TensorProduct.zero_tmul]
    rw [h2, map_zero]
  rw [h1, zero_mul]

theorem sz_le (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] Ten F E n d) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x y, 1 + sz τ (m (spl F κ x, spl F κ y)) ≤ K * (1 + ‖x.1‖ + ‖y.1‖) := by
  let L : InfinitePlace F → Fin n → Fin d → ((κ → mixedSpace F) × (κ → mixedSpace F)) →+ ℂ := fun w i j =>
    { toFun := fun p => piInf (τ w) (m (spl F κ (p.1, 0), spl F κ (p.2, 0)) i j)
      map_zero' := by
        rw [show ((0 : (κ → mixedSpace F) × (κ → mixedSpace F)).1, (0 : κ → Af F)) = 0 from rfl]
        simp only [show ((0 : (κ → mixedSpace F) × (κ → mixedSpace F)).2, (0 : κ → Af F)) = 0 from rfl, map_zero,
          Prod.mk_zero_zero, Matrix.zero_apply]
      map_add' := fun p q => by
        have e : ∀ a b : κ → mixedSpace F, spl F κ (a + b, 0) = spl F κ (a, 0) + spl F κ (b, 0) := fun a b => by
          rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
        rw [Prod.fst_add, Prod.snd_add, e, e, ← Prod.mk_add_mk, map_add (f := _), Matrix.add_apply, map_add (f := _)] }
  have hL : ∀ w i j, Continuous (L w i j) := fun w i j =>
    (LatticeQuotientCompactness.continuous_piInf (τ w)).comp ((continuous_apply j).comp ((continuous_apply i).comp ((lin_cont m).comp
      ((spl_cont.comp (continuous_fst.prodMk continuous_const)).prodMk
        (spl_cont.comp (continuous_snd.prodMk continuous_const))))))
  let K := ∑ w, ∑ i, ∑ j, ‖(L w i j).toRealLinearMap (hL w i j)‖
  have hK : 0 ≤ K := by positivity
  refine ⟨1 + K, by linarith, fun x y => ?_⟩
  have e : (spl F κ x, spl F κ y) = (spl F κ (x.1, 0), spl F κ (y.1, 0)) + fi F 1 • (spl F κ x, spl F κ y) := by
    have : ∀ x, spl F κ x = spl F κ (x.1, 0) + fi F 1 • spl F κ x := fun x => funext fun i => by
      show re F _ + fi F _ = re F _ + fi F 0 + fi F 1 * (re F _ + fi F _)
      rw [map_zero, add_zero, mul_add, mul_comm (fi F 1) (re F _), re_mul_fi, fi_mul, zero_add, one_mul]
    exact Prod.ext (this x) (this y)
  have h1 : sz τ (m (spl F κ x, spl F κ y)) ≤ K * (‖x.1‖ + ‖y.1‖) := by
    simp only [sz, K, Finset.sum_mul]
    refine Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [e, map_add (f := _), map_smul, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), piInf_fi, add_zero]
    refine (((L w i j).toRealLinearMap (hL w i j)).le_opNorm (x.1, y.1)).trans ?_
    gcongr
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  nlinarith [norm_nonneg x.1, norm_nonneg y.1]

end W

open W

theorem coefBd_of : CoefReal → CoefBd := by
  intro hR F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ φ₁ h₁ φ₂ h₂ N
  haveI := hP.base.cm.1
  obtain ⟨p, C, K, hp, hC, hK, h⟩ := coef_split hR hP.base.std μ hμ h₁ h₂ N
  obtain ⟨L, hL, hsz⟩ := sz_le B.emb M.co.e.symm.toLinearMap
  have hLN : 0 ≤ C * L ^ N := by positivity
  refine ⟨(NNReal.mk (1 + C * L ^ N) (by positivity)) • p,
    (fun q => M.co.e.symm (spl F _ (0, q.1), spl F _ (0, q.2))) '' K, hp.const_smul _,
    hK.image ((lin_cont M.co.e.symm.toLinearMap).comp ((spl_cont.comp (continuous_const.prodMk continuous_fst)).prodMk
      (spl_cont.comp (continuous_const.prodMk continuous_snd)))), fun f₁ f₂ z => ?_⟩
  obtain ⟨w, rfl⟩ := M.co.e.symm.surjective z
  obtain ⟨x, hx⟩ := (spl F _).surjective w.1
  obtain ⟨y, hy⟩ := (spl F _).surjective w.2
  obtain rfl : w = (spl F _ x, spl F _ y) := Prod.ext hx.symm hy.symm
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨a, b⟩ := h f₁ f₂ x y
  by_cases h0 : coef F B.ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (spl F _ x, spl F _ y) = 0
  · rw [h0, norm_zero]
    exact mul_nonneg (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (LatticeQuotientCompactness.maj_nonneg _ _ _ _)
  have s0 := LatticeQuotientCompactness.sz_nonneg B.emb (M.co.e.symm (spl F _ x, spl F _ y))
  rw [maj, if_pos, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  · have q := mul_nonneg (apply_nonneg p f₁) (apply_nonneg p f₂)
    calc _ ≤ _ * (L * (1 + ‖x.1‖ + ‖y.1‖)) ^ N := by gcongr; exact hsz x y
      _ = L ^ N * (_ * (1 + ‖x.1‖ + ‖y.1‖) ^ N) := by rw [mul_pow, mul_left_comm]
      _ ≤ L ^ N * (C * (p f₁ * p f₂)) := by gcongr
      _ ≤ ((1 + C * L ^ N) * p f₁) * ((1 + C * L ^ N) * p f₂) := by
        nlinarith [mul_nonneg hLN q, mul_nonneg (mul_nonneg hLN hLN) q]
  · refine ⟨_, ⟨_, b h0, rfl⟩, fun u hu => ?_⟩
    rw [← map_sub, ← map_smul, map_eq_zero_iff _ M.co.e.symm.injective, Prod.mk_sub_mk, ← map_sub, ← map_sub]
    have : ∀ x : (Fin n × Fin d → mixedSpace F) × (Fin n × Fin d → Af F), u • spl F _ (x - (0, x.2)) = 0 := fun x =>
      funext fun i => by
        show u * (re F _ + fi F (x.2 i - x.2 i)) = 0
        rw [sub_self, map_zero, add_zero, ← re_add_fi u, hu, map_zero, zero_add, mul_comm, re_mul_fi]
    exact Prod.ext (this x) (this y)

end PositivityTheory.ThKEst
end
