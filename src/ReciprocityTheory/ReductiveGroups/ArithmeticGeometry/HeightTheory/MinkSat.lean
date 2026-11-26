module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Qdist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SingleMemStandardLattice

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ExistsSmallSaturatingVector
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ExistsNeZeroMemNormSqLeGramDetDivRelIndex
namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule Matrix

theorem relIndex_nsmul_mem {E : Type*} [AddCommGroup E] (H L : AddSubgroup E) {x : E}
    (hx : x ∈ L) : H.relIndex L • x ∈ H := by
  exact AddSubgroup.nsmul_relIndex_mem H hx

theorem exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (hN : 0 < N) (w : Fin N → E) (hw : LinearIndependent ℝ w) (Λ : AddSubgroup E)
    (hΛ : ∀ i, w i ∈ Λ) (hI : (span ℤ (Set.range w)).toAddSubgroup.relIndex Λ ≠ 0) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ‖v‖ ^ 2 ≤ N * ((gram ℝ w).det /
      ((span ℤ (Set.range w)).toAddSubgroup.relIndex Λ : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by
  classical
  set S : AddSubgroup E := (span ℤ (Set.range w)).toAddSubgroup with hS
  set I : ℕ := S.relIndex Λ with hIdef
  have hI0 : (I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hI
  set V : Submodule ℝ E := Submodule.span ℝ (Set.range w) with hV
  have hSV : ∀ x ∈ S, x ∈ V := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hΛV : ∀ x ∈ Λ, x ∈ V := by
    intro x hx
    have h1 : I • x ∈ S := relIndex_nsmul_mem S Λ hx
    have h2 : (I : ℝ) • x ∈ V := by rw [Nat.cast_smul_eq_nsmul]; exact hSV _ h1
    have h3 := V.smul_mem ((I : ℝ)⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ hI0, one_smul] at h3
  have hSΛ : S ≤ Λ := by
    intro x hx
    have hle : span ℤ (Set.range w) ≤ Λ.toIntSubmodule :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hΛ i)
    exact hle hx
  have hfin : Module.finrank ℝ V = N := by rw [finrank_span_eq_card hw, Fintype.card_fin]
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  let f : OrthonormalBasis (Fin N) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hfin)
  let wV : Fin N → V := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hwV : LinearIndependent ℝ wV := LinearIndependent.of_comp V.subtype hw
  let φ : V ≃ₗ[ℝ] (Fin N → ℝ) := f.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))
  have hφ : ∀ v : V, φ v = (f.repr v).ofLp := fun v => rfl
  let vb : Fin N → (Fin N → ℝ) := fun i => φ (wV i)
  have hvb : LinearIndependent ℝ vb := hwV.map' φ.toLinearMap (LinearEquiv.ker _)
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let b : Module.Basis (Fin N) ℝ (Fin N → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hvb (by simp)
  have hb : ∀ i, b i = φ (wV i) := fun i => by simp [b, vb]
  set d := (Matrix.of ⇑b).det with hd
  have hgram : (gram ℝ w).det = d ^ 2 := by
    have hG : gram ℝ w = Matrix.of ⇑b * (Matrix.of ⇑b).transpose := by
      ext i j
      rw [Matrix.gram_apply, Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.transpose_apply, hb, hφ]
      have e1 : inner ℝ (w i) (w j) = inner ℝ (f.repr (wV i)) (f.repr (wV j)) := by
        rw [LinearIsometryEquiv.inner_map_map]
        rfl
      rw [e1, PiLp.inner_apply]
      simp [mul_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  have hnorm : ∀ v : V, ‖(v : E)‖ ^ 2 = ∑ j, (φ v j) ^ 2 := by
    intro v
    change ‖v‖ ^ 2 = _
    rw [← f.repr.norm_map, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs, hφ]
  let χ : V →+ (Fin N → ℝ) := φ.toLinearMap.toAddMonoidHom
  have hχ : Function.Injective χ := φ.injective
  let ι : V →+ E := V.subtype.toAddMonoidHom
  let L2g : AddSubgroup (Fin N → ℝ) := (Λ.comap ι).map χ
  let L1 : Submodule ℤ (Fin N → ℝ) := span ℤ (Set.range b)
  have hL1g : L1.toAddSubgroup = (S.comap ι).map χ := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, AddSubgroup.mem_comap]
    constructor
    · intro hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      refine ⟨∑ i, c i • wV i, ?_, ?_⟩
      · show ((∑ i, c i • wV i : V) : E) ∈ S
        rw [hS, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun ℤ]
        exact ⟨c, by simp [wV]⟩
      set_option synthInstance.maxHeartbeats 100000 in
        · simp [χ, hb, map_sum]
    · rintro ⟨v, hv, rfl⟩
      have hv' : (v : E) ∈ span ℤ (Set.range w) := hv
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv'
      have hvc : v = ∑ i, c i • wV i := Subtype.ext (by simp [wV, ← hc])
      rw [hvc]
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, by simp [χ, hb, map_sum]⟩
  have hΛr : Λ ≤ ι.range := fun x hx => ⟨⟨x, hΛV x hx⟩, rfl⟩
  have hrel : L1.toAddSubgroup.relIndex L2g = I := by
    rw [hL1g, AddSubgroup.relIndex_map_map_of_injective _ _ hχ, AddSubgroup.relIndex_comap,
      AddSubgroup.map_comap_eq_self hΛr]
  let L2 : Submodule ℤ (Fin N → ℝ) := L2g.toIntSubmodule
  have hL12 : L1 ≤ L2 := by
    intro x hx
    have h1 : x ∈ L1.toAddSubgroup := hx
    rw [hL1g] at h1
    exact AddSubgroup.map_mono (AddSubgroup.comap_mono hSΛ) h1
  let b' : Module.Basis (Fin N) ℝ (Fin N → ℝ) := b.unitsSMul (fun _ => Units.mk0 ((I : ℝ)⁻¹) (inv_ne_zero hI0))
  have hb' : ∀ i, b' i = (I : ℝ)⁻¹ • b i := fun i => by
    show (b.unitsSMul _) i = _
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hL2sub : (L2 : Set (Fin N → ℝ)) ⊆ span ℤ (Set.range b') := by
    intro x hx
    have h1 : L1.toAddSubgroup.relIndex L2g • x ∈ L1.toAddSubgroup := relIndex_nsmul_mem _ _ hx
    rw [hrel] at h1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h1
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
    have hx' : x = (I : ℝ)⁻¹ • (I • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hI0, one_smul]
    rw [hx', ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb', smul_comm]
  haveI : DiscreteTopology L2 := DiscreteTopology.of_subset (inferInstance :
    DiscreteTopology (span ℤ (Set.range b'))) hL2sub
  haveI : IsZLattice ℝ L2 := ⟨by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_le.mpr fun x hx => Submodule.subset_span (hL12 (Submodule.subset_span hx))⟩
  have hcov1 : ZLattice.covolume L1 MeasureTheory.volume = |d| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L1 MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b MeasureTheory.volume), MeasureTheory.Measure.real,
      ZSpan.volume_fundamentalDomain, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hcov2 : ZLattice.covolume L2 MeasureTheory.volume = |d| / I := by
    have h := ZLattice.covolume_div_covolume_eq_relIndex L1 L2 hL12
    have h' : L1.toAddSubgroup.relIndex L2.toAddSubgroup = I := hrel
    rw [h', hcov1] at h
    have hpos : 0 < ZLattice.covolume L2 MeasureTheory.volume := ZLattice.covolume_pos L2 _
    field_simp at h ⊢
    linarith
  let b2 := (Module.Free.chooseBasis ℤ L2).ofZLatticeBasis ℝ L2
  have hspan2 : span ℤ (Set.range b2) = L2 := Module.Basis.ofZLatticeBasis_span ℝ L2 _
  have hF2 : MeasureTheory.IsAddFundamentalDomain L2 (ZSpan.fundamentalDomain b2) MeasureTheory.volume := by
    have := ZSpan.isAddFundamentalDomain b2 MeasureTheory.volume
    rwa [hspan2] at this
  have hvolF2 : MeasureTheory.volume (ZSpan.fundamentalDomain b2) = ENNReal.ofReal (|d| / I) := by
    rw [← hcov2, ZLattice.covolume_eq_measure_fundamentalDomain L2 MeasureTheory.volume hF2,
      MeasureTheory.Measure.real, ENNReal.ofReal_toReal
        (ZSpan.fundamentalDomain_isBounded b2).measure_lt_top.ne]
  haveI : Countable ↥L2.toAddSubgroup := by
    have hc : ((L2.toAddSubgroup : AddSubgroup (Fin N → ℝ)) : Set (Fin N → ℝ)) ⊆
        Set.range (fun c : Fin N → ℤ => ∑ i, c i • b' i) := by
      intro z hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hL2sub hz)
      exact ⟨c, hc⟩
    exact ((Set.countable_range _).mono hc).to_subtype
  haveI : DiscreteTopology ↥L2.toAddSubgroup := inferInstanceAs (DiscreteTopology L2)
  set t : ℝ := (|d| / I) ^ ((N : ℝ)⁻¹) with ht
  have hq : 0 ≤ |d| / I := div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have ht0 : 0 ≤ t := Real.rpow_nonneg hq _
  have htN : t ^ N = |d| / I := Real.rpow_inv_natCast_pow hq (by omega)
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (μ := MeasureTheory.volume) (L := L2.toAddSubgroup)
    (s := Set.Icc (-(fun _ : Fin N => t)) (fun _ : Fin N => t))
    hF2 (fun z hz => ⟨neg_le_neg hz.2, by simpa using neg_le_neg hz.1⟩) (convex_Icc _ _) isCompact_Icc
    (by
      rw [hvolF2, Real.volume_Icc_pi, Module.finrank_fin_fun]
      have e2 : ∏ i : Fin N, ENNReal.ofReal ((fun _ : Fin N => t) i - (-(fun _ : Fin N => t)) i) =
          2 ^ N * ENNReal.ofReal (|d| / I) := by
        simp only [Pi.neg_apply, sub_neg_eq_add, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        rw [← ENNReal.ofReal_pow (by positivity), show t + t = 2 * t by ring, mul_pow, htN,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [e2, mul_comm])
  have hxL2 : (x : Fin N → ℝ) ∈ L2g := x.2
  obtain ⟨v, hv, hvx⟩ := AddSubgroup.mem_map.mp hxL2
  have hxj : ∀ j, |(x : Fin N → ℝ) j| ≤ t := fun j =>
    abs_le.mpr ⟨by simpa using hxs.1 j, hxs.2 j⟩
  refine ⟨(v : E), hv, ?_, ?_⟩
  · intro h0
    apply hx0
    have hv0 : v = 0 := Subtype.ext h0
    apply Subtype.ext
    rw [← hvx, hv0, map_zero]
    rfl
  have hxv : ∀ j, φ v j = (x : Fin N → ℝ) j := fun j => by rw [← hvx]; rfl
  rw [hnorm v]
  calc ∑ j, (φ v j) ^ 2 ≤ ∑ _j : Fin N, t ^ 2 := Finset.sum_le_sum fun j _ => by
        have := pow_le_pow_left₀ (abs_nonneg _) (hxj j) 2
        rwa [sq_abs, ← hxv j] at this
    _ = N * ((gram ℝ w).det / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hgram, ht, one_div]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq, mul_comm, Real.rpow_mul hq, Real.rpow_natCast,
          div_pow, sq_abs]

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField
open scoped ComplexOrder

noncomputable def hQdist {K : Type} [Field K] {r k : ℕ} (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (q : Fin r → K) : ℝ :=
  ⨅ z : Fin k → ℂ, Real.sqrt (∑ i, ‖σ (q i) + ∑ j, z j * σ (b j i)‖ ^ 2)

section Final

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem quotDist_eq_sqrt_norm (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (q : Fin r → K) : hQdist σ b q = Real.sqrt (hns (hPm σ b *ᵥ fun i => σ (q i))) := by
  set v : Fin r → ℂ := fun i => σ (q i) with hv
  set G := (hBm σ b)ᴴ * hBm σ b with hG
  have hterm : ∀ z : Fin k → ℂ,
      (∑ i, ‖σ (q i) + ∑ j, z j * σ (b j i)‖ ^ 2) = hns (v + hBm σ b *ᵥ z) := by
    intro z
    simp only [hns]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [v, hBm, mulVec, dotProduct, mul_comm]
  have hdec : ∀ z, v + hBm σ b *ᵥ z =
      hPm σ b *ᵥ v + hBm σ b *ᵥ (z + G⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ v)) := by
    intro z
    simp only [hPm, sub_mulVec, one_mulVec, mulVec_add, ← mulVec_mulVec]
    abel
  have hmin : ∀ z, hns (hPm σ b *ᵥ v) ≤ hns (v + hBm σ b *ᵥ z) := by
    intro z
    rw [hdec z, normSqSum_add_of_orthogonal _ _ (orthogonalProjector_orthogonal σ hb _ _)]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  have hat : v + hBm σ b *ᵥ (-(G⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ v))) = hPm σ b *ᵥ v := by
    rw [hdec, neg_add_cancel, mulVec_zero, add_zero]
  unfold hQdist
  simp_rw [hterm]
  apply le_antisymm
  · exact (ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact Real.sqrt_nonneg _⟩ _).trans_eq (by rw [hat])
  · exact le_ciInf fun z => Real.sqrt_le_sqrt (hmin z)

theorem norm_orthProj_sq_sum {b : Fin k → Fin r → K} (hb : LinearIndependent K b) (q : Fin r → K) :
    ‖hpv b q‖ ^ 2 = ∑ σ, hQdist σ b q ^ 2 := by
  rw [hpv, norm_realCoords_sq]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [quotDist_eq_sqrt_norm σ hb, Real.sq_sqrt (by unfold hns; positivity)]

theorem orthProj_mem_span {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) {t : Fin r → K}
    (ht : t ∈ Submodule.span (𝓞 K) (Set.range c)) :
    hpv b t ∈ Submodule.span ℤ (Set.range (hwv b c)) := by
  classical
  obtain ⟨o, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 ht
  have e : ∀ j, o j • c j = ∑ a, (RingOfIntegers.basis K).repr (o j) a • (integralBasis K a • c j) := by
    intro j
    conv_lhs => rw [← (RingOfIntegers.basis K).sum_repr (o j)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_assoc, integralBasis_apply, algebraMap_smul]
  have e2 : hpv b (∑ j, o j • c j) = ∑ j, ∑ a, (RingOfIntegers.basis K).repr (o j) a • hwv b c (j, a) := by
    simp_rw [e]
    change hpvHom b _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
    rfl
  rw [e2]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, a), rfl⟩)

theorem orthProjVector_mem {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hc : ∀ j, c j ∈ hStd K r) (p : Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    hwv b c p ∈ (hStd K r).toAddSubgroup.map (hpvHom b) := by
  refine ⟨integralBasis K p.2 • c p.1, ?_, rfl⟩
  show integralBasis K p.2 • c p.1 ∈ hStd K r
  rw [integralBasis_apply, algebraMap_smul]
  exact Submodule.smul_mem _ _ (hc p.1)

theorem relIndex_orthProj_lattice {m : ℕ} {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) (hc : ∀ j, c j ∈ hStd K r) :
    (Submodule.span ℤ (Set.range (hwv b c))).toAddSubgroup.relIndex
        ((hStd K r).toAddSubgroup.map (hpvHom b)) =
      (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        (hStd K r).toAddSubgroup := by
  classical
  rw [← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right,
    ← AddSubgroup.inf_relIndex_right (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔
      Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup]
  congr 1
  ext q
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup]
  constructor
  · rintro ⟨hW, hq⟩
    refine ⟨?_, hq⟩
    obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hW
    set t : Fin r → K := ∑ p, n p • (integralBasis K p.2 • c p.1) with htdef
    have ht : t ∈ Submodule.span (𝓞 K) (Set.range c) := by
      refine Submodule.sum_mem _ fun p _ => Submodule.smul_of_tower_mem _ _ ?_
      rw [integralBasis_apply, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.1, rfl⟩)
    have hft : hpv b t = hpvHom b q := by
      rw [← hn]
      change hpvHom b t = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [t, map_sum, map_zsmul]
      rfl
    have hz : hpv b (q - t) = 0 := by
      change hpvHom b (q - t) = 0
      rw [map_sub]
      change hpvHom b q - hpv b t = 0
      rw [hft, sub_self]
    rw [projectedVector_eq_zero_iff hb] at hz
    have htL : t ∈ hStd K r :=
      (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hc j)) ht
    have hsat : q - t ∈ ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b :=
      ⟨Submodule.sub_mem _ hq htL, hz⟩
    have := Submodule.add_mem_sup hsat ht
    rwa [sub_add_cancel] at this
  · rintro ⟨hS, hq⟩
    refine ⟨?_, hq⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hS
    change hpvHom b (y + z) ∈ _
    rw [map_add (f := _)]
    have hy0 : hpvHom b y = 0 := (projectedVector_eq_zero_iff hb y).mpr hy.2
    rw [hy0, zero_add]
    exact orthProj_mem_span b c hz

end Final

section Main

theorem exists_small_saturating_vector (K : Type) [Field K] [NumberField K] (r k : ℕ) (b : Fin k → Fin r → K)
    (hb : LinearIndependent K b) (hbL : ∀ j, b j ∈ hStd K r) (hk : k < r) :
    ∃ q : Fin r → 𝓞 K, (fun i => (q i : K)) ∉ Submodule.span K (Set.range b) ∧
      meanK (fun σ => Real.log (hQdist σ b (fun i => (q i : K)))) ≤
        ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b) b /
            ((Module.finrank ℚ K : ℝ) * ((r - k : ℕ) : ℝ)) +
          1 / 2 * Real.log ((r - k : ℕ) : ℝ) +
          1 / 2 * Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) := by
  classical
  set m := r - k with hmdef
  have hm : 0 < m := by omega
  have hkm : k + m = r := by omega
  obtain ⟨c, hc, hli, hsp⟩ := exists_integral_completion hb hk.le
  have hdeg := latDeg_saturation hkm hbL c hc hli hsp
  set n := Module.finrank ℚ K with hndef
  have hn : 0 < n := Module.finrank_pos
  have hcardI : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = n := by
    rw [hndef, Module.finrank_eq_card_basis (integralBasis K)]
  have hcardE : Fintype.card (K →+* ℂ) = n := NumberField.Embeddings.card K ℂ
  set N := m * n with hNdef
  have hN : 0 < N := Nat.mul_pos hm hn
  have hcardJ : Fintype.card (Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = N := by
    rw [Fintype.card_prod, Fintype.card_fin, hcardI]
  let eN : Fin N ≃ (Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :=
    (Fintype.equivFinOfCardEq hcardJ).symm
  let w := hwv b c ∘ eN
  have hgw : gram ℝ w = (gram ℝ (hwv b c)).submatrix eN eN := by
    ext i j
    simp [gram_apply, w]
  set P := ∏ σ : K →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re with hPdef
  set D := |(NumberField.discr K : ℝ)| with hDdef
  have hdetw : (gram ℝ w).det = D ^ m * P := by
    rw [hgw, det_submatrix_equiv_self, det_gram_projectedLatticeVectors b hb c]
  have hdpos : 0 < D := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hPpos : 0 < P := Finset.prod_pos fun σ _ => quotGram_det_pos σ hb c hli
  have hGpos : 0 < (gram ℝ w).det := by rw [hdetw]; positivity
  have hwli : LinearIndependent ℝ w := linearIndependent_of_det_gram_ne_zero hGpos.ne'
  set Λ := (hStd K r).toAddSubgroup.map (hpvHom b) with hΛ
  have hwmem : ∀ i, w i ∈ Λ := fun i => orthProjVector_mem b c hc (eN i)
  have hrange : Set.range w = Set.range (hwv b c) := eN.surjective.range_comp _
  set I := (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔
    Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex (hStd K r).toAddSubgroup with hIdef
  have hrel : (Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex Λ = I := by
    rw [hrange]; exact relIndex_orthProj_lattice hb c hc
  have hI0 : I ≠ 0 := by
    have h1 := ReciprocityTheory.MultiplicativeHeights.DegAdd.relIndex_ne_zero_of_fg (hStd K r) standardLattice_fg (Fin.append b c)
      (fun x _ => hsp x)
    have hle : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) ≤
        ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact Submodule.mem_sup_left ⟨hbL i, Submodule.subset_span ⟨i, rfl⟩⟩
      · rw [Fin.append_right]
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
    have hdvd := AddSubgroup.relIndex_dvd_of_le_left (hStd K r).toAddSubgroup
      (show (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup ≤
        (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup
        from hle)
    intro h0
    rw [← hIdef, h0] at hdvd
    exact h1 (Nat.eq_zero_of_zero_dvd hdvd)
  obtain ⟨v, hvΛ, hv0, hvb⟩ := exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex hN w hwli Λ hwmem (by rw [hrel]; exact hI0)
  rw [hrel, hdetw] at hvb
  obtain ⟨q, hqL, rfl⟩ := AddSubgroup.mem_map.mp hvΛ
  have hq : q ∉ Submodule.span K (Set.range b) := fun h => hv0 ((projectedVector_eq_zero_iff hb q).mpr h)
  have hqL' : q ∈ hStd K r := hqL
  rw [mem_standardLattice_iff] at hqL'
  choose q' hq' using hqL'
  have hqq : (fun i => ((q' i : 𝓞 K) : K)) = q := funext hq'
  refine ⟨q', by rw [hqq]; exact hq, ?_⟩
  rw [hqq]
  set X : (K →+* ℂ) → ℝ := fun σ => hns (hPm σ b *ᵥ fun l => σ (q l)) with hX
  have hXpos : ∀ σ, 0 < X σ := fun σ => normSqSum_pos (orthogonalProjector_mulVec_ne_zero σ hb hq)
  have hdist : ∀ σ, Real.log (hQdist σ b q) = Real.log (X σ) / 2 := fun σ => by
    rw [quotDist_eq_sqrt_norm σ hb, Real.log_sqrt (hXpos σ).le]
  have hsumX : ∑ σ, X σ = ‖hpvHom b q‖ ^ 2 := by
    show _ = ‖hpv b q‖ ^ 2
    rw [norm_orthProj_sq_sum hb]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [quotDist_eq_sqrt_norm σ hb, Real.sq_sqrt (hXpos σ).le]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hamgm : ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) ≤ Real.log ((1 / (n : ℝ)) * ∑ σ, X σ) := by
    have hw0 : ∀ σ ∈ (Finset.univ : Finset (K →+* ℂ)), (0 : ℝ) ≤ 1 / (n : ℝ) :=
      fun _ _ => by positivity
    have hw1 : ∑ σ ∈ (Finset.univ : Finset (K →+* ℂ)), 1 / (n : ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, hcardE, nsmul_eq_mul]
      field_simp
    have h := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (fun _ => 1 / (n : ℝ)) X hw0
      hw1 (fun σ _ => (hXpos σ).le)
    have hprod : 0 < ∏ σ, X σ ^ (1 / (n : ℝ)) :=
      Finset.prod_pos fun σ _ => Real.rpow_pos_of_pos (hXpos σ) _
    have hlog := Real.log_le_log hprod h
    rw [Real.log_prod (fun σ _ => (Real.rpow_pos_of_pos (hXpos σ) _).ne')] at hlog
    simp only [Real.log_rpow (hXpos _)] at hlog
    rw [Finset.mul_sum]
    exact hlog
  have hIr : (0 : ℝ) < I := by exact_mod_cast Nat.pos_of_ne_zero hI0
  have hquot : ReciprocityTheory.MultiplicativeHeights.quotDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) b c =
      Real.log I - 1 / 2 * Real.log P := by
    simp only [ReciprocityTheory.MultiplicativeHeights.quotDeg]
    rw [hPdef, Real.log_prod (fun σ _ => (quotGram_det_pos σ hb c hli).ne')]
  have hlogG : Real.log (D ^ m * P / (I : ℝ) ^ 2) =
      m * Real.log D + Real.log P - 2 * Real.log I := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hNr : (N : ℝ) = m * n := by rw [hNdef]; push_cast; ring
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hY : Real.log ((1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)))) =
      Real.log m + (1 / (N : ℝ)) * (m * Real.log D + Real.log P - 2 * Real.log I) := by
    rw [show (1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ))) =
        (m : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)) by rw [hNr]; field_simp]
    rw [Real.log_mul hmr.ne' (Real.rpow_pos_of_pos (by positivity) _).ne',
      Real.log_rpow (by positivity), hlogG]
  have hmean : meanK (fun σ => Real.log (hQdist σ b q)) =
      1 / 2 * ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) := by
    simp only [meanK, hdist, hcardE]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  have hsum_pos : 0 < (1 / (n : ℝ)) * ∑ σ, X σ :=
    mul_pos (by positivity) (Finset.sum_pos (fun σ _ => hXpos σ) Finset.univ_nonempty)
  have hstep : Real.log ((1 / (n : ℝ)) * ∑ σ, X σ) ≤
      Real.log ((1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)))) := by
    apply Real.log_le_log hsum_pos
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hsumX]
    exact hvb
  rw [hmean, hdeg, hquot]
  have hD1 : Real.log (D ^ (1 / (n : ℝ))) = 1 / (n : ℝ) * Real.log D := Real.log_rpow hdpos _
  rw [hD1]
  have key : 1 / 2 * ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) ≤
      1 / 2 * (Real.log m + (1 / (N : ℝ)) * (m * Real.log D + Real.log P - 2 * Real.log I)) := by
    rw [← hY]
    exact mul_le_mul_of_nonneg_left (hamgm.trans hstep) (by norm_num)
  refine key.trans (le_of_eq ?_)
  rw [hNr]
  field_simp
  ring

end Main

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem mink_sat (K : Type) [Field K] [NumberField K] (r k : ℕ) (b : Fin k → Fin r → K)
    (hb : LinearIndependent K b) (hbL : ∀ j, b j ∈ stdLat K r) (hk : k < r) :
    ∃ q : Fin r → 𝓞 K, (fun i => (q i : K)) ∉ Submodule.span K (Set.range b) ∧
      meanK (fun σ => Real.log (qdist σ b (fun i => (q i : K)))) ≤
        ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b) b /
            ((Module.finrank ℚ K : ℝ) * ((r - k : ℕ) : ℝ)) +
          1 / 2 * Real.log ((r - k : ℕ) : ℝ) +
          1 / 2 * Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) :=
  exists_small_saturating_vector K r k b hb hbL hk

end ReciprocityTheory.ChartRestriction.G.T0
