module

public import Mathlib

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AbsTprod

theorem multipliable_of_summable_abs_sub_one {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) : Multipliable a := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hm := multipliable_one_add_of_summable h'
  have hfun : (fun v => 1 + (a v - 1)) = a := funext fun v => by ring
  rwa [hfun] at hm

theorem tprod_nonneg_of_nonneg {ι : Type} {a : ι → ℝ} (hm : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v := by
  exact tprod_nonneg h0

theorem tprod_ne_zero_of_summable {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (h0 : ∀ v, a v ≠ 0) : ∏' v, a v ≠ 0 := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hne : ∀ v, 1 + (a v - 1) ≠ 0 := fun v => by simpa using h0 v
  have hp := tprod_one_add_ne_zero_of_summable (f := fun v => a v - 1) hne h'
  simpa using hp

theorem tprod_eq_prod_mul_tprod_compl {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (S : Finset ι) :
    Multipliable (fun v : {v // v ∉ S} => a v.1) ∧
      ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1 := by
  have hsub : ∀ p : ι → Prop, Multipliable (fun v : {v // p v} => a v.1) := fun p =>
    GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one (a := fun v : {v // p v} => a v.1)
      (h.comp_injective Subtype.val_injective)
  refine ⟨hsub _, ?_⟩
  have key := Multipliable.tprod_mul_tprod_compl (f := a) (s := (S : Set ι))
    (hsub (· ∈ (S : Set ι))) (hsub (· ∈ (S : Set ι)ᶜ))
  rw [← key, Finset.tprod_subtype']
  rfl

theorem abs_tprod : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by
  intro ι a h
  have hm := GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one h
  refine ⟨hm, fun S => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_eq_prod_mul_tprod_compl h S, fun hpos => ?_,
    fun h0 => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm h0⟩
  exact lt_of_le_of_ne (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm fun v => (hpos v).le)
    (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_ne_zero_of_summable h fun v => (hpos v).ne').symm

end GlobalTheory.CompanionTheory.SW.AbsTprod
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliableStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_product_multipliable : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod | exact GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod | (intros; apply GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatticeUnimod

theorem unimodular_of_isFundamentalDomain :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G),
      IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ →
        μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ 𝓕 h𝓕 hfin
  have h0 : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hmap : ∀ g : G, μ.map (· * g) = μ := by
    intro g
    have hc : μ.map (· * g) = Measure.haarScalarFactor (μ.map (· * g)) μ • μ :=
      Measure.isMulLeftInvariant_eq_smul _ _
    have hF : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
      h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hm : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := hF.measure_eq h𝓕
    have e1 : (μ.map (· * g)) 𝓕 = μ ((· * g) ⁻¹' 𝓕) :=
      (MeasurableEquiv.mulRight g).map_apply 𝓕
    have e2 : ((Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0) : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕 := by
      have e3 := congrArg (fun m : Measure G => m 𝓕) hc
      simp only [Measure.smul_apply] at e3
      rw [e1, hm] at e3
      rw [one_mul]
      exact e3.symm
    have e4 := (ENNReal.mul_left_inj h0 hfin.ne).1 e2
    have e5 : Measure.haarScalarFactor (μ.map (· * g)) μ = 1 := ENNReal.coe_eq_one.1 e4
    rw [e5, one_smul] at hc
    exact hc
  haveI hR : μ.IsMulRightInvariant := ⟨hmap⟩
  refine ⟨h0, hR, ⟨?_⟩⟩
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable,
      ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hVpos : 0 < μ V := Measure.measure_pos_of_mem_nhds μ hV1
  have e : c ^ 2 * μ V = 1 ^ 2 * μ V := by
    conv_rhs => rw [μeq]
    simp
  have e2 : c ^ 2 = 1 ^ 2 := (ENNReal.mul_left_inj hVpos.ne' hV.measure_lt_top.ne).1 e
  have e3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective e2
  rw [hc, e3, one_smul]

end GlobalTheory.CompanionTheory.SW.LatticeUnimod
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodularStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_covolume_unimodular : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain | exact GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SymmetricInvertibleExistsPosdefCongruence
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SymmetricInvertibleExistsPosdefCongruence
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem exists_posDef_majorant_of_isSymm :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 →
      ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by
  intro ι _ _ B hsym hdet
  have hH : B.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsym
  obtain ⟨U, hU⟩ : ∃ U : Matrix ι ι ℝ, U = (hH.eigenvectorUnitary : Matrix ι ι ℝ) := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d : ι → ℝ, d = hH.eigenvalues := ⟨_, rfl⟩
  have hUs : star U * U = 1 := by subst hU; simp
  have hsU : U * star U = 1 := by subst hU; simp
  have hspec : B = U * Matrix.diagonal d * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    subst hU hdd
    simp [Unitary.conjStarAlgAut_apply]
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    rw [hdd] at hi
    apply hdet
    rw [hH.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have conj : ∀ a b : ι → ℝ, (U * Matrix.diagonal a * star U) * (U * Matrix.diagonal b * star U) =
      U * Matrix.diagonal (fun i => a i * b i) * star U := by
    intro a b
    calc U * Matrix.diagonal a * star U * (U * Matrix.diagonal b * star U)
        = U * Matrix.diagonal a * (star U * U) * Matrix.diagonal b * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal a * Matrix.diagonal b) * star U := by
          rw [hUs, Matrix.mul_one, Matrix.mul_assoc U]
      _ = _ := by rw [Matrix.diagonal_mul_diagonal]
  have hinv : B⁻¹ = U * Matrix.diagonal (fun i => (d i)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hspec, conj]
    rw [show (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) from funext fun i => mul_inv_cancel₀ (hd i),
      Matrix.diagonal_one, Matrix.mul_one, hsU]
  refine ⟨U * Matrix.diagonal (fun i => |d i|) * star U, ?_, ?_⟩
  · rw [Matrix.IsUnit.posDef_star_right_conjugate_iff ⟨⟨U, star U, hsU, hUs⟩, rfl⟩,
      Matrix.posDef_diagonal_iff]
    exact fun i => abs_pos.mpr (hd i)
  · rw [hinv, conj, conj]
    conv_rhs => rw [hspec]
    congr 3
    funext i
    show |d i| * (d i)⁻¹ * |d i| = d i
    rw [mul_right_comm, abs_mul_abs_self, mul_inv_cancel_right₀ (hd i)]

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SymmetricInvertibleExistsPosdefCongruenceStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_invertible_exists_posdef_congruence : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 → ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | exact GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | (intros; apply GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealContinuousEmbeddingInfiniteAdeles
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealContinuousEmbeddingInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicRealLine

theorem norm_eq_abs_ringEquiv {F : Type} [Field F] {w : InfinitePlace F} (hw : w.IsReal)
    (x : w.Completion) :
    ‖x‖ = |InfinitePlace.Completion.ringEquivRealOfIsReal hw x| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).dist_eq x 0
  have h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal hw) 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  rw [h0, dist_zero_right, dist_zero_right] at h
  rw [← h, Real.norm_eq_abs]
  rfl

theorem exists_continuous_real_embedding :
    ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
      (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧
        ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
          ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  intro F _ _ hF
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => @IsTotallyReal.isReal F _ hF w
  refine ⟨⟨Pi.ringHom fun w =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).symm.toRingHom, ?_⟩, ?_⟩
  · refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm.continuous
  · intro θ _ t w
    have hφ := DFunLike.congr_fun (Subsingleton.elim
      (((InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).toRingHom.comp
        ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) : ℝ →+* ℝ)
      (RingHom.id ℝ)) t
    change InfinitePlace.Completion.ringEquivRealOfIsReal (hr w) (θ t w) = t at hφ
    rw [GlobalTheory.CompanionTheory.AdelicRealLine.norm_eq_abs_ringEquiv (hr w), hφ]

end GlobalTheory.CompanionTheory.AdelicRealLine
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealContinuousEmbeddingInfiniteAdelesStatement
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_real_continuous_embedding_infinite_adeles : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧ ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ → ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  first | exact @GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding | exact GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding | (intros; apply GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GroupActionHaarScalingContinuous
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GroupActionHaarScalingContinuous
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.ModulusAction

theorem exists_continuous_modulus :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
      [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (μ : Measure V) [μ.IsAddHaarMeasure] (T : Type) [Group T] [TopologicalSpace T]
      [FirstCountableTopology T] [LocallyCompactSpace T] (a : T → V →+ V),
      (Continuous fun p : T × V => a p.1 p.2) → Continuous (fun t : T => t⁻¹) →
      (∀ y, a 1 y = y) → (∀ s t y, a (s * t) y = a s (a t y)) →
      ∃ χ : T →* ℝ≥0, Continuous χ ∧ ∀ t, μ.map (a t) = χ t • μ := by
  intro V _ _ _ _ _ _ _ _ μ _ T _ _ _ _ a ha hinv h1 hmul
  have hat : ∀ t, Continuous (a t) := fun t => by
    have h := ha.comp (continuous_const.prodMk (continuous_id (X := V)) :
      Continuous fun y : V => (t, y))
    exact h
  have hleft : ∀ t y, a t⁻¹ (a t y) = y := by
    intro t y
    rw [← hmul, inv_mul_cancel, h1]
  have hright : ∀ t y, a t (a t⁻¹ y) = y := by
    intro t y
    rw [← hmul, mul_inv_cancel, h1]
  have hfin : ∀ t, IsFiniteMeasureOnCompacts (μ.map (a t)) := by
    intro t
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply (hat t).measurable hK.isClosed.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) ((hK.image (hat t⁻¹)).measure_lt_top)
    intro y hy
    exact ⟨a t y, hy, hleft t y⟩
  have hinvar : ∀ t, (μ.map (a t)).IsAddLeftInvariant := by
    intro t
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_add g) (hat t).measurable]
    have e : (fun x => g + x) ∘ a t = a t ∘ fun x => a t⁻¹ g + x := by
      funext x
      simp only [Function.comp_apply, map_add (f := _), hright]
    rw [e, ← Measure.map_map (hat t).measurable (measurable_const_add _),
      map_add_left_eq_self]
  have hscale : ∀ t, ∃ c : ℝ≥0, μ.map (a t) = c • μ := by
    intro t
    haveI := hfin t
    haveI := hinvar t
    exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩
  choose c hc using hscale
  obtain ⟨f, hfc, hf0, hfx⟩ := exists_continuous_nonneg_pos (0 : V)
  have hI : 0 < ∫ y, f y ∂μ :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hfx
  have hint : ∀ t (g : V → ℝ), Continuous g →
      ∫ y, g (a t y) ∂μ = (c t : ℝ) * ∫ y, g y ∂μ := by
    intro t g hg
    rw [← integral_map (hat t).measurable.aemeasurable hg.aestronglyMeasurable, hc t,
      integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hform : ∀ t, (c t : ℝ) * ∫ y, f y ∂μ = ∫ y, f (a t y) ∂μ := fun t =>
    (hint t f f.continuous).symm
  have hone : c 1 = 1 := by
    apply NNReal.coe_injective
    apply mul_right_cancel₀ hI.ne'
    rw [hform, NNReal.coe_one, one_mul]
    simp only [h1]
  have hmulc : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    apply NNReal.coe_injective
    apply mul_right_cancel₀ hI.ne'
    rw [hform, NNReal.coe_mul]
    calc ∫ y, f (a (s * t) y) ∂μ = ∫ y, f (a s (a t y)) ∂μ := by simp only [hmul]
      _ = (c t : ℝ) * ∫ y, f (a s y) ∂μ := hint t (fun z => f (a s z)) (f.continuous.comp (hat s))
      _ = (c s : ℝ) * (c t : ℝ) * ∫ y, f y ∂μ := by rw [← hform s]; ring
  have hF : Continuous fun t => ∫ y, f (a t y) ∂μ := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    obtain ⟨N, hN, hNn⟩ := exists_compact_mem_nhds t₀
    set s : Set V := (fun p : T × V => a p.1 p.2) '' (((fun t => t⁻¹) '' N) ×ˢ tsupport f)
      with hsdef
    have hs : IsCompact s := ((hN.image hinv).prod hfc.isCompact).image ha
    have hG : Continuous fun t => ∫ y in s, f (a t y) ∂μ := by
      refine continuous_parametric_integral_of_continuous ?_ hs
      exact f.continuous.comp ha
    refine hG.continuousAt.congr (Filter.eventually_of_mem hNn fun t ht => ?_)
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    by_contra hne
    exact hy ⟨(t⁻¹, a t y), ⟨⟨t, ht, rfl⟩, subset_tsupport _ hne⟩, hleft t y⟩
  have hcreal : (fun t => (c t : ℝ)) = fun t => (∫ y, f (a t y) ∂μ) / ∫ y, f y ∂μ :=
    funext fun t => eq_div_of_mul_eq hI.ne' (hform t)
  refine ⟨{ toFun := c, map_one' := hone, map_mul' := hmulc }, ?_, hc⟩
  show Continuous c
  have hcont : Continuous fun t => (c t : ℝ) := by
    rw [hcreal]
    exact hF.div_const _
  exact Continuous.subtype_mk hcont fun t => (c t).2

end GlobalTheory.CompanionTheory.Adelic.ModulusAction
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GroupActionHaarScalingContinuousStatement
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_action_haar_scaling_continuous : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : Type) [Group T] [TopologicalSpace T] [FirstCountableTopology T] [LocallyCompactSpace T] (a : T → V →+ V), (Continuous fun p : T × V => a p.1 p.2) → Continuous (fun t : T => t⁻¹) → (∀ y, a 1 y = y) → (∀ s t y, a (s * t) y = a s (a t y)) → ∃ χ : T →* ℝ≥0, Continuous χ ∧ ∀ t, μ.map (a t) = χ t • μ := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus | exact GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus | (intros; apply GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus <;> assumption)
end
end
