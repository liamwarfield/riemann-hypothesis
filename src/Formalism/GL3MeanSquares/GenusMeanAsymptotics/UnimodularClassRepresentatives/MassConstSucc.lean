module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLand
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FactorIdentity

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoBallCount
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MeasurableSetBallSet
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthBasisMem
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_orth_basis_mem [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) :
    ∃ b : Basis (Fin (finrank K V)) K V, (∀ i, b i ∈ L) ∧ ∀ i j, i ≠ j → h (b i) (b j) = 0 := by
  obtain ⟨e, he, -⟩ := orthBasisPos K hK V h hs hd
  choose n hn hnx using fun i => Formalism.HermitianLatticesTheory.traceReal_mult L hL (e i)
  have hb : ∀ i, e.unitsSMul (fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i))) i =
      (n i : K) • e i := fun i => by rw [Basis.unitsSMul_apply]; rfl
  refine ⟨e.unitsSMul fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i)), fun i => ?_,
    fun i j hij => ?_⟩
  · rw [hb, Int.cast_smul_eq_zsmul]; exact hnx i
  · simp only [hb, map_smulₛₗ, LinearMap.smul_apply, he i j hij, smul_zero]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem form_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V) :
    h x x = ∑ i, star (b.repr x i) * b.repr x i * h (b i) (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hj
    simp [ho j i hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem re_form_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V)
    (φ : K →+* ℂ) :
    (φ (h x x)).re = ∑ i, (φ (h (b i) (b i))).re * Complex.normSq (φ (b.repr x i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [form_eq b ho x, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul, mul_comm]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem forall_embedding_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V)
    (T : ℝ) :
    (∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T) ↔ ∀ w : {w : InfinitePlace K // w.IsComplex},
      ∑ i, (w.1.embedding (h (b i) (b i))).re * Complex.normSq (w.1.embedding (b.repr x i)) ≤ T := by
  have : IsTotallyComplex K := hK.1
  constructor
  · intro hφ w
    rw [← re_form_eq hK b ho]
    exact hφ _
  · intro hw φ
    have h1 := hw ⟨InfinitePlace.mk φ, IsTotallyComplex.isComplex _⟩
    rw [← re_form_eq hK b ho] at h1
    rcases InfinitePlace.embedding_mk_eq φ with h2 | h2
    · rwa [h2] at h1
    · rwa [h2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h1

theorem gdet_eq_prod {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis (Fin (finrank K V)) K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) : gdet h b = ∏ i, h (b i) (b i) := by
  unfold gdet
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, ho i j hij]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem place_form_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {x : V} (hx : x ≠ 0) (w : InfinitePlace K) :
    w (h x x) = (w.embedding (h x x)).re := by
  have h1 : star (h x x) = h x x := hs.eq x x
  have h2 : (w.embedding (h x x)).im = 0 := by
    rw [← Complex.conj_eq_iff_im, ← hK.2.1, h1]
  rw [← InfinitePlace.norm_embedding_eq, ← Complex.abs_re_eq_norm.2 h2,
    abs_of_pos (hd x hx w.embedding)]

open scoped Classical in
theorem prod_place_gdet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (b : Basis (Fin (finrank K V)) K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) :
    ∏ w : InfinitePlace K, w (gdet h b) =
      ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re := by
  have : IsTotallyComplex K := hK.1
  rw [← (Equiv.subtypeUnivEquiv (fun w : InfinitePlace K => IsTotallyComplex.isComplex w)).prod_comp]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [gdet_eq_prod b ho, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact place_form_eq hK hs hd (b.ne_zero i) _

theorem isLattice_span [FiniteDimensional K V] (b : Basis (Fin (finrank K V)) K V) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range b)) :=
  Submodule.IsLattice.of_fg K ⟨(Set.finite_range b).toFinset, by rw [Set.Finite.coe_toFinset]⟩
end Formalism.HermitianLattices.Ext.L3.BallB
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FundamentalDomainPiBasis
open NumberField NumberField.mixedEmbedding MeasureTheory Module

open scoped Classical

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallC

variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι]

def psi [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    (ι → mixedSpace K) ≃ₗ[ℝ] ({w : InfinitePlace K // w.IsComplex} → ι → ℂ) where
  toFun y := fun w i => (y i).2 w
  invFun z := fun i => (fun w => isEmptyElim w, fun w => z w i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext i
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv z := rfl

theorem psi_apply [IsEmpty {w : InfinitePlace K // w.IsReal}] (y : ι → mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) : psi K ι y w i = (y i).2 w := rfl

theorem measurePreserving_psi [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (psi K ι) volume volume := by
  let e := (psi K ι).toContinuousLinearEquiv
  have he : ∀ y, e y = psi K ι y := fun y => rfl
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e volume = volume
  have : (Measure.map e volume).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  let K₀ : TopologicalSpace.PositiveCompacts
      ({w : InfinitePlace K // w.IsComplex} → ι → ℂ) :=
    ⟨⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩, by
      change (interior (Metric.closedBall 0 1)).Nonempty
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0, Metric.mem_ball_self one_pos⟩⟩
  have hK₀ : (K₀ : Set ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) = Metric.closedBall 0 1 := rfl
  rw [Measure.addHaarMeasure_unique (Measure.map e volume) K₀,
    Measure.addHaarMeasure_unique (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) K₀]
  congr 1
  rw [hK₀, Measure.map_apply e.continuous.measurable Metric.isClosed_closedBall.measurableSet]
  have h1 : e ⁻¹' Metric.closedBall 0 1 = Set.pi Set.univ fun _ : ι =>
      (Set.univ : Set ({w : InfinitePlace K // w.IsReal} → ℝ)) ×ˢ
        Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.closedBall (0 : ℂ) 1 := by
    ext y
    simp only [Set.mem_preimage, mem_closedBall_zero_iff, he, Set.mem_pi, Set.mem_univ,
      Set.mem_prod, true_and, forall_true_left, pi_norm_le_iff_of_nonneg zero_le_one, psi_apply]
    exact forall_comm
  have h2 : (Metric.closedBall 0 1 : Set ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_closedBall_zero_iff, Set.mem_pi, Set.mem_univ, forall_true_left,
      pi_norm_le_iff_of_nonneg zero_le_one]
  have h3 : volume (Set.univ : Set ({w : InfinitePlace K // w.IsReal} → ℝ)) = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  rw [h1, h2, volume_pi_pi, volume_pi_pi]
  simp only [volume_pi_pi, Measure.volume_eq_prod, Measure.prod_prod, h3, one_mul]
  exact Finset.prod_comm

def piBasis : Basis (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (ι → mixedSpace K) :=
  Pi.basis fun _ => latticeBasis K

theorem fundamentalDomain_piBasis : ZSpan.fundamentalDomain (piBasis K ι) =
    Set.pi Set.univ fun _ => ZSpan.fundamentalDomain (latticeBasis K) := by
  ext y
  simp only [ZSpan.mem_fundamentalDomain, Set.mem_pi, Set.mem_univ, true_implies, forall_const, piBasis,
    Pi.basis_repr, Sigma.forall]

theorem mem_span_piBasis (y : ι → mixedSpace K) :
    y ∈ Submodule.span ℤ (Set.range (piBasis K ι)) ↔
      ∀ i, ∃ a : 𝓞 K, mixedEmbedding K (algebraMap (𝓞 K) K a) = y i := by
  simp only [Basis.mem_span_iff_repr_mem ℤ, piBasis, Pi.basis_repr, Sigma.forall]
  refine forall_congr' fun i => ?_
  refine (Basis.mem_span_iff_repr_mem ℤ (latticeBasis K) (y i)).symm.trans ?_
  rw [mem_span_latticeBasis]
  simp [NumberField.mixedEmbedding.integerLattice, LinearMap.mem_range]

theorem covolume_piBasis :
    ZLattice.covolume (Submodule.span ℤ (Set.range (piBasis K ι))) volume =
      ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) ^ Fintype.card ι := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (piBasis K ι) volume),
    measureReal_def, fundamentalDomain_piBasis, volume_pi_pi, ENNReal.toReal_prod, Finset.prod_const,
    Finset.card_univ, ← measureReal_def,
    ← ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (latticeBasis K) volume),
    span_latticeBasis, covolume_integerLattice]

end Formalism.HermitianLattices.Ext.L3.BallC
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscreteTopologyOfZsmul
open MeasureTheory Module ZSpan Filter Topology Pointwise Bornology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure]

private theorem volume_image_equivFun_eq_map_symm {ι : Type*} [Fintype ι] (B : Basis ι ℝ E)
    (s : Set E) : volume (B.equivFun '' s) = Measure.map B.equivFunL.symm volume s := by
  rw [LinearEquiv.image_eq_preimage_symm]
  exact (B.equivFunL.symm.toHomeomorph.toMeasurableEquiv.map_apply s).symm

private theorem volume_image_equivFun_fundamentalDomain_eq_one {ι : Type*} [Fintype ι] (B : Basis ι ℝ E) :
    volume (B.equivFun '' fundamentalDomain B) = 1 := by
  have h : B.equivFun '' fundamentalDomain B = Set.univ.pi fun _ : ι ↦ Set.Ico (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_image, mem_fundamentalDomain, Set.mem_univ_pi]
    constructor
    · rintro ⟨m, hm, rfl⟩ i
      simpa [Basis.equivFun_apply] using hm i
    · intro hx
      refine ⟨B.equivFun.symm x, fun i ↦ ?_, B.equivFun.apply_symm_apply x⟩
      have hxi := congrFun (B.equivFun.apply_symm_apply x) i
      rw [Basis.equivFun_apply] at hxi
      rw [hxi]
      exact hx i
  rw [h, volume_pi_pi]
  simp

private theorem covolume_eq_addHaarScalarFactor_mul_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ν ν' : Measure E) [ν.IsAddHaarMeasure] [ν'.IsAddHaarMeasure] :
    ZLattice.covolume Λ ν =
      (Measure.addHaarScalarFactor ν ν' : ℝ) * ZLattice.covolume Λ ν' := by
  have h := Measure.isAddLeftInvariant_eq_smul ν ν'
  let b := Module.Free.chooseBasis ℤ Λ
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ ν (ZLattice.isAddFundamentalDomain b ν),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ ν' (ZLattice.isAddFundamentalDomain b ν')]
  generalize Measure.addHaarScalarFactor ν ν' = c at h ⊢
  rw [h]
  exact measureReal_nnreal_smul_apply _

theorem volume_image_equivFun {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (s : Set E) :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) =
      μ s / ENNReal.ofReal (ZLattice.covolume L μ) := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure E,
      ν = Measure.map (b.ofZLatticeBasis ℝ L).equivFunL.symm volume := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := hν ▸ inferInstance
  have hcov : ZLattice.covolume L ν = 1 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L ν (ZLattice.isAddFundamentalDomain b ν),
      measureReal_def, hν, ← volume_image_equivFun_eq_map_symm, volume_image_equivFun_fundamentalDomain_eq_one,
      ENNReal.toReal_one]
  rw [volume_image_equivFun_eq_map_symm, ← hν, covolume_eq_addHaarScalarFactor_mul_covolume L μ ν, hcov, mul_one,
    ENNReal.ofReal_coe_nnreal]
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  generalize Measure.addHaarScalarFactor μ ν = c at hc h ⊢
  have hc0 : (c : ENNReal) ≠ 0 := by simpa using hc.ne'
  rw [h, Measure.coe_nnreal_smul_apply, mul_comm, ENNReal.mul_div_cancel_right hc0 ENNReal.coe_ne_top]

theorem tendsto_card_div_pow {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : μ (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s / ZLattice.covolume L μ)) := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  have hfr : frontier (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' frontier s :=
    (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFunL.toHomeomorph.image_frontier
      s).symm
  have hlim : volume.real (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      μ.real s / ZLattice.covolume L μ := by
    rw [measureReal_def, volume_image_equivFun L μ, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L μ).le, measureReal_def]
  have key := ZLattice.covolume.tendsto_card_div_pow'' (Module.Free.chooseBasis ℤ L) hs₁ hs₂
    (by rw [hfr, volume_image_equivFun L μ, hs₃, ENNReal.zero_div])
  rw [hlim, hcard] at key
  exact key

set_option backward.isDefEq.respectTransparency.types false in
theorem covolume_div_covolume (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ / ZLattice.covolume L₂ μ =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure E,
      ν = Measure.map (Module.finBasis ℝ E).equivFunL.symm volume := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := hν ▸ inferInstance
  have he : MeasurePreserving (Module.finBasis ℝ E).equivFunL.symm volume ν := by
    rw [hν]
    exact (Module.finBasis ℝ E).equivFunL.symm.continuous.measurable.measurePreserving _
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  rw [covolume_eq_addHaarScalarFactor_mul_covolume L₁ μ ν, covolume_eq_addHaarScalarFactor_mul_covolume L₂ μ ν,
    mul_div_mul_left _ _ (NNReal.coe_pos.mpr hc).ne', ← ZLattice.covolume_comap L₁ ν volume he,
    ← ZLattice.covolume_comap L₂ ν volume he,
    ZLattice.covolume_div_covolume_eq_relIndex _ _ (fun _ h' ↦ h h'),
    ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
    LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.relIndex_map_map_of_injective _ _ (Module.finBasis ℝ E).equivFunL.injective]

theorem discreteTopology_of_zsmul {Λ₁ Λ : Submodule ℤ E} [DiscreteTopology Λ₁] {N : ℤ}
    (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) : DiscreteTopology Λ := by
  refine DiscreteTopology.of_continuous_injective (β := Λ₁)
    (f := fun y : Λ ↦ (⟨N • (y : E), h y y.2⟩ : Λ₁)) ?_ ?_
  · exact ((continuous_zsmul N).comp continuous_subtype_val).subtype_mk _
  · intro y z hyz
    have h' : N • (y : E) = N • (z : E) := congrArg Subtype.val hyz
    rw [← Int.cast_smul_eq_zsmul ℝ N (y : E), ← Int.cast_smul_eq_zsmul ℝ N (z : E)] at h'
    exact Subtype.ext (smul_right_injective E (Int.cast_ne_zero.mpr hN) h')

theorem tendsto_card_of_le (Λ₁ Λ : Submodule ℤ E) [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁]
    (hle : Λ₁ ≤ Λ) {N : ℤ} (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) {s : Set E}
    (hs₁ : IsBounded s) (hs₂ : MeasurableSet s) (hs₃ : Convex ℝ s) :
    Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 ∧
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • Λ : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s * (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) /
        ZLattice.covolume Λ₁ μ)) := by
  have : DiscreteTopology Λ := discreteTopology_of_zsmul hN h
  have : IsZLattice ℝ Λ := ⟨by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := Λ₁)]
    exact Submodule.span_mono hle⟩
  have hidx := covolume_div_covolume μ Λ₁ Λ hle
  have h₁ := (ZLattice.covolume_pos Λ₁ μ).ne'
  have h₂ := (ZLattice.covolume_pos Λ μ).ne'
  have hne : (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) ≠ 0 := by
    rw [← hidx]
    exact div_ne_zero h₁ h₂
  refine ⟨by exact_mod_cast hne, ?_⟩
  have key := tendsto_card_div_pow Λ μ hs₁ hs₂ (hs₃.addHaar_frontier μ)
  convert key using 2
  rw [← hidx]
  field_simp

end Formalism.HermitianLattices.Ext.L3.BallA
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VolumeNormSqLeOne
open MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallC

theorem volume_normSq_le_one (M : ℕ) :
    volume {x : Fin M → ℂ | ∑ i, Complex.normSq (x i) ≤ 1} =
      ENNReal.ofReal (Real.pi ^ M / (M.factorial : ℝ)) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have e : {x : Fin 0 → ℂ | ∑ i, Complex.normSq (x i) ≤ 1} = Set.univ := by
      ext x; simp
    rw [e, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
    simp
  · haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    have h := Complex.volume_sum_rpow_le (Fin M) (p := 2) one_le_two 1
    have hset : {x : Fin M → ℂ | ∑ i, Complex.normSq (x i) ≤ 1} =
        {x : Fin M → ℂ | (∑ i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_one]
      simp only [Real.rpow_two, Complex.normSq_eq_norm_sq]
    rw [hset, h, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
    congr 1
    have e1 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
    have e2 : 2 * (M : ℝ) / 2 + 1 = (M : ℝ) + 1 := by ring
    rw [e1, e2, Real.Gamma_two, mul_one, Real.Gamma_nat_eq_factorial]

def ell {M : ℕ} (a : Fin M → ℝ) : Set (Fin M → ℂ) := {z | ∑ i, a i * Complex.normSq (z i) ≤ 1}

variable {M : ℕ} (a : Fin M → ℝ)

theorem mem_ell {z : Fin M → ℂ} : z ∈ ell a ↔ ∑ i, a i * Complex.normSq (z i) ≤ 1 := Iff.rfl

theorem isClosed_ell : IsClosed (ell a) := by
  unfold ell
  exact isClosed_le (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Complex.continuous_normSq.comp (continuous_apply i))) continuous_const

variable {a}

theorem volume_ell (ha : ∀ i, 0 < a i) :
    volume (ell a) = ENNReal.ofReal (Real.pi ^ M / (M.factorial : ℝ) / ∏ i, a i) := by
  let g : Fin M → (ℂ →ₗ[ℝ] ℂ) := fun i => Real.sqrt (a i) • LinearMap.id
  let f : (Fin M → ℂ) →ₗ[ℝ] (Fin M → ℂ) := LinearMap.pi fun i => (g i) ∘ₗ LinearMap.proj i
  have hf : ∀ z i, f z i = (Real.sqrt (a i) : ℂ) * z i := by
    intro z i
    simp [f, g, Complex.real_smul]
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [g, LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex]
    exact Real.sq_sqrt (ha i).le
  have hs : ∀ z, ∑ i, Complex.normSq (f z i) = ∑ i, a i * Complex.normSq (z i) := by
    intro z
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (ha i).le]
  have hpre : ell a = f ⁻¹' {x | ∑ i, Complex.normSq (x i) ≤ 1} := by
    ext z
    simp only [ell, Set.mem_setOf_eq, Set.mem_preimage, hs]
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  rw [hpre, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rw [hdet]; exact hprod.ne'),
    volume_normSq_le_one, hdet, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_of_pos (inv_pos.mpr hprod)]
  ring

theorem convex_ell (ha : ∀ i, 0 < a i) : Convex ℝ (ell a) := by
  intro x hx y hy s t hs ht hst
  simp only [ell, Set.mem_setOf_eq] at hx hy ⊢
  have key : ∀ i, a i * Complex.normSq ((s • x + t • y) i) ≤
      s * (a i * Complex.normSq (x i)) + t * (a i * Complex.normSq (y i)) := by
    intro i
    have h1 : Complex.normSq ((s • x + t • y) i) ≤
        s * Complex.normSq (x i) + t * Complex.normSq (y i) := by
      simp only [Pi.add_apply, Pi.smul_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      have ht' : t = 1 - s := by linarith
      subst ht'
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg ((x i).re - (y i).re)),
        mul_nonneg (mul_nonneg hs ht) (sq_nonneg ((x i).im - (y i).im))]
    calc a i * Complex.normSq ((s • x + t • y) i)
        ≤ a i * (s * Complex.normSq (x i) + t * Complex.normSq (y i)) :=
          mul_le_mul_of_nonneg_left h1 (ha i).le
      _ = s * (a i * Complex.normSq (x i)) + t * (a i * Complex.normSq (y i)) := by ring
  calc ∑ i, a i * Complex.normSq ((s • x + t • y) i)
      ≤ ∑ i, (s * (a i * Complex.normSq (x i)) + t * (a i * Complex.normSq (y i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = s * ∑ i, a i * Complex.normSq (x i) + t * ∑ i, a i * Complex.normSq (y i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ s * 1 + t * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hst]

theorem isBounded_ell (ha : ∀ i, 0 < a i) : Bornology.IsBounded (ell a) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨∑ i, (1 + (a i)⁻¹), fun z hz => ?_⟩
  rw [mem_closedBall_zero_iff]
  simp only [ell, Set.mem_setOf_eq] at hz
  have hnn : ∀ j, 0 ≤ 1 + (a j)⁻¹ := fun j => add_nonneg zero_le_one (inv_nonneg.mpr (ha j).le)
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hnn i)).mpr fun i => ?_
  have hi : a i * Complex.normSq (z i) ≤ 1 :=
    le_trans (Finset.single_le_sum (f := fun j => a j * Complex.normSq (z j))
      (fun j _ => mul_nonneg (ha j).le (Complex.normSq_nonneg _)) (Finset.mem_univ i)) hz
  have h2 : Complex.normSq (z i) ≤ (a i)⁻¹ := by
    rw [← one_div, le_div_iff₀ (ha i), mul_comm]
    exact hi
  rw [Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖z i‖ ≤ 1 + (a i)⁻¹ := by nlinarith [sq_nonneg (‖z i‖ - 1)]
  exact h3.trans (Finset.single_le_sum (f := fun j => 1 + (a j)⁻¹) (fun j _ => hnn j)
    (Finset.mem_univ i))

end Formalism.HermitianLattices.Ext.L3.BallC
end
end

open NumberField NumberField.mixedEmbedding MeasureTheory Module Pointwise

open scoped Classical

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallD

open BallB BallC

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def emb (b : Basis (Fin (finrank K V)) K V) : V →+ (Fin (finrank K V) → mixedSpace K) where
  toFun x := fun i => mixedEmbedding K (b.repr x i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem emb_apply (b : Basis (Fin (finrank K V)) K V) (x : V) (i : Fin (finrank K V)) :
    emb b x i = mixedEmbedding K (b.repr x i) := rfl

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem emb_injective (b : Basis (Fin (finrank K V)) K V) : Function.Injective (emb b) := by
  intro x y hxy
  apply b.repr.injective
  ext i
  exact mixedEmbedding_injective K (congrFun hxy i)

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem psi_emb [IsEmpty {w : InfinitePlace K // w.IsReal}] (b : Basis (Fin (finrank K V)) K V)
    (x : V) (w : {w : InfinitePlace K // w.IsComplex}) (i : Fin (finrank K V)) :
    psi K (Fin (finrank K V)) (emb b x) w i = w.1.embedding (b.repr x i) := by
  rw [psi_apply, emb_apply, mixedEmbedding_apply_isComplex]

def lat (b : Basis (Fin (finrank K V)) K V) (L : Submodule (𝓞 K) V) :
    Submodule ℤ (Fin (finrank K V) → mixedSpace K) :=
  AddSubgroup.toIntSubmodule (L.toAddSubgroup.map (emb b))

omit [StarRing K] [IsScalarTower (𝓞 K) K V] in
theorem mem_lat {b : Basis (Fin (finrank K V)) K V} {L : Submodule (𝓞 K) V}
    {y : Fin (finrank K V) → mixedSpace K} : y ∈ lat b L ↔ ∃ x ∈ L, emb b x = y := Iff.rfl

omit [StarRing K] in
theorem lat_span (b : Basis (Fin (finrank K V)) K V) :
    lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (piBasis K (Fin (finrank K V)))) := by
  ext y
  rw [mem_span_piBasis, mem_lat]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨a, ha⟩ := (b.mem_span_iff_repr_mem (𝓞 K) x).1 hx i
    exact ⟨a, by rw [ha]; rfl⟩
  · intro hy
    choose a ha using hy
    have hr : ∀ i, b.repr (b.equivFun.symm fun i => algebraMap (𝓞 K) K (a i)) i =
        algebraMap (𝓞 K) K (a i) := by
      intro i
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    refine ⟨b.equivFun.symm fun i => algebraMap (𝓞 K) K (a i),
      (b.mem_span_iff_repr_mem (𝓞 K) _).2 fun i => ⟨a i, (hr i).symm⟩, funext fun i => ?_⟩
    rw [emb_apply, hr, ha]

def ballSet [IsEmpty {w : InfinitePlace K // w.IsReal}] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (b : Basis (Fin (finrank K V)) K V) : Set (Fin (finrank K V) → mixedSpace K) :=
  (psi K (Fin (finrank K V))) ⁻¹' Set.pi Set.univ fun w =>
    ell fun i => (w.1.embedding (h (b i) (b i))).re

variable [IsEmpty {w : InfinitePlace K // w.IsReal}] {h : V →ₗ⋆[K] V →ₗ[K] K}
  {b : Basis (Fin (finrank K V)) K V}

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem measurableSet_ballSet : MeasurableSet (ballSet h b) :=
  ((isClosed_set_pi fun _ _ => isClosed_ell _).preimage
    (psi K (Fin (finrank K V))).toContinuousLinearEquiv.continuous).measurableSet

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem convex_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    Convex ℝ (ballSet h b) :=
  (convex_pi fun w _ => convex_ell (hA w)).linear_preimage (psi K (Fin (finrank K V))).toLinearMap

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isBounded_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    Bornology.IsBounded (ballSet h b) := by
  have h1 : ballSet h b = (psi K (Fin (finrank K V))).toContinuousLinearEquiv.symm ''
      Set.pi Set.univ fun w => ell fun i => (w.1.embedding (h (b i) (b i))).re :=
    ((psi K (Fin (finrank K V))).toContinuousLinearEquiv.image_symm_eq_preimage _).symm
  rw [h1]
  exact (psi K (Fin (finrank K V))).toContinuousLinearEquiv.symm.lipschitzWith.isBounded_image
    (Bornology.IsBounded.pi fun w => isBounded_ell (hA w))

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem volume_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    volume.real (ballSet h b) =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ InfinitePlace.nrComplexPlaces K /
        ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re := by
  have hm : MeasurableSet (Set.pi Set.univ fun w : {w : InfinitePlace K // w.IsComplex} =>
      ell fun i => (w.1.embedding (h (b i) (b i))).re) :=
    (isClosed_set_pi fun _ _ => isClosed_ell _).measurableSet
  rw [measureReal_def, ballSet,
    (measurePreserving_psi K (Fin (finrank K V))).measure_preimage hm.nullMeasurableSet,
    volume_pi_pi, ENNReal.toReal_prod]
  have h1 : ∀ w : {w : InfinitePlace K // w.IsComplex},
      (volume (ell fun i => (w.1.embedding (h (b i) (b i))).re)).toReal =
        Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ) /
          ∏ i, (w.1.embedding (h (b i) (b i))).re := by
    intro w
    rw [volume_ell (hA w), ENNReal.toReal_ofReal]
    exact div_nonneg (by positivity) (Finset.prod_nonneg fun i _ => (hA w i).le)
  simp only [h1]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

theorem card_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (L : Submodule (𝓞 K) V) {j : ℕ} (hj : 0 < j) :
    ballCount h L ((j : ℝ) ^ 2) =
      Nat.card ↑(ballSet h b ∩ (j : ℝ)⁻¹ • (lat b L : Set (Fin (finrank K V) → mixedSpace K))) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have key : ∀ x : V, (j : ℝ)⁻¹ • emb b x ∈ ballSet h b ↔
      ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ (j : ℝ) ^ 2 := by
    intro x
    rw [forall_embedding_iff hK b ho x]
    simp only [ballSet, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, mem_ell,
      map_smul]
    refine forall_congr' fun w => ?_
    have h1 : ∀ i, Complex.normSq (((j : ℝ)⁻¹ • psi K (Fin (finrank K V)) (emb b x)) w i) =
        ((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i)) := by
      intro i
      rw [Pi.smul_apply, Pi.smul_apply, psi_emb, Complex.real_smul, map_mul, Complex.normSq_ofReal]
      field_simp
    simp only [h1]
    have h2 : ∑ i, (w.1.embedding (h (b i) (b i))).re *
        (((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i))) =
        (∑ i, (w.1.embedding (h (b i) (b i))).re *
          Complex.normSq (w.1.embedding (b.repr x i))) / (j : ℝ) ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, div_le_one (by positivity)]
  unfold ballCount
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨(j : ℝ)⁻¹ • emb b x.1, (key x.1).2 x.2.2,
      Set.smul_mem_smul_set ⟨x.1, x.2.1, rfl⟩⟩) ⟨?_, ?_⟩)
  · intro x y hxy
    have h1 : (j : ℝ)⁻¹ • emb b x.1 = (j : ℝ)⁻¹ • emb b y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (emb_injective b (smul_right_injective _ (inv_ne_zero hj'.ne') h1))
  · rintro ⟨y, hy1, hy2⟩
    obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hy2
    exact ⟨⟨x, hx, (key x).1 hy1⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.BallD
end
end

open NumberField Module Filter Topology

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem tendsto_ballCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    Tendsto (fun j : ℕ => (ballCount h L ((j : ℝ) ^ 2) : ℝ) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L))) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  obtain ⟨b, hbL, ho⟩ := BallB.exists_orth_basis_mem hK hs hd hL
  have hBL : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
  have hB : Submodule.IsFullLattice K (Submodule.span (𝓞 K) (Set.range b)) :=
    { toIsLattice := BallB.isLattice_span b
      span_eq_top := by
        apply top_unique
        rw [← b.span_eq]
        exact Submodule.span_mono Submodule.subset_span }
  obtain ⟨N, hN, hNx⟩ := LocF.exists_zsmul_le hL.toIsLattice hB
  have hlat1 : BallD.lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := BallD.lat_span b
  have hle : Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) ≤ BallD.lat b L := by
    rw [← hlat1]
    intro y hy
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hBL hx, rfl⟩
  have hNy : ∀ y ∈ BallD.lat b L,
      N • y ∈ Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := by
    intro y hy
    rw [← hlat1]
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨N • x, hNx x hx, map_zsmul (BallD.emb b) N x⟩
  have hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re :=
    fun w i => hd (b i) (b.ne_zero i) w.1.embedding
  obtain ⟨hidx, hT⟩ := BallA.tendsto_card_of_le (μ := MeasureTheory.volume)
    (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) (BallD.lat b L) hle hN hNy
    (BallD.isBounded_ballSet hA) BallD.measurableSet_ballSet (BallD.convex_ballSet hA)
  have hfr : finrank ℝ (Fin (finrank K V) → NumberField.mixedEmbedding.mixedSpace K) = 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      NumberField.mixedEmbedding.finrank, finrank_eq_two_fDeg hK]
    ring
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    rw [BallC.covolume_piBasis, covolume_integerLattice_eq hK, Fintype.card_fin, ← pow_mul]
  have hidx' : (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
      (BallD.lat b L).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [← hlat1]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (BallD.emb_injective b)
  have hI0 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [← hidx']; exact hidx
  have hnorm := BallB.normD_mul_relIndex hK hLi b hbL hI0
  have hgdet := BallB.prod_place_gdet hK hs hd b ho
  have hvol := BallD.volume_ballSet hA
  have hP : 0 < ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re :=
    Finset.prod_pos fun w _ => Finset.prod_pos fun i _ => hA w i
  have hIr : ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hI0
  have hND : normD h L ≠ 0 := by
    intro h0
    rw [h0, zero_mul, hgdet] at hnorm
    linarith
  have hV : Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) ≠ 0 := pow_ne_zero _ (vInv_pos K).ne'
  have hlim : MeasureTheory.volume.real (BallD.ballSet h b) *
      ((Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
        (BallD.lat b L).toAddSubgroup : ℝ) /
      ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L) := by
    rw [hvol, hcov, hidx', ← hgdet, ← hnorm, nrComplexPlaces_eq_fDeg hK]
    field_simp
  rw [← hlim]
  refine Tendsto.congr' ?_ hT
  filter_upwards [eventually_gt_atTop 0] with j hj
  rw [BallD.card_eq hK ho L hj, hfr]

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassRatioEqLvalue
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem massRatio_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
  have hv := vInv_pos K
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  refine mul_pos (div_pos (pow_pos (mul_pos ?_ (pow_pos (div_pos hv Real.pi_pos) _)) _) ?_)
    (lValEta_pos hK M hM)
  · exact_mod_cast Nat.factorial_pos _
  · exact Real.sqrt_pos.mpr (pow_pos (mul_pos two_pos hv) _)

theorem massRatio_eq_lvalue (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) (hm : 2 ≤ m) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K m =
      (((m - 1).factorial : ℝ) / Real.pi ^ m) ^ Formalism.HermitianLatticesTheory.fDeg K *
        Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * m) /
          Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F m := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  rw [lValEta_eq_lValEtaF hK hF m hm, mul_comm (Formalism.HermitianLatticesTheory.fDeg K) m, pow_mul, ← mul_pow, div_pow]
  congr 3
  ring

end Formalism.HermitianLattices.Ext.L3
end
end

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

namespace Step

theorem final_algebra (μ c lam D P a mm vv sq lV : ℝ) (f : ℕ) (hD : 0 < D) (hP : 0 < P)
    (ha : 0 < a) (hmm : 0 < mm) (hvv : 0 < vv) (hsq : 0 < sq)
    (h : μ * ((P / (mm * a)) ^ f / (vv * D)) = 0 + c * lam * D⁻¹ * ((mm ^ f)⁻¹ / sq * lV)) :
    μ = c * ((a / P) ^ f * vv / sq * lV) * lam := by
  have hD' := hD.ne'
  have hP' := hP.ne'
  have ha' := ha.ne'
  have hmm' := hmm.ne'
  have hvv' := hvv.ne'
  have hsq' := hsq.ne'
  have hX : (P / (mm * a)) ^ f / (vv * D) ≠ 0 := by positivity
  rw [zero_add] at h
  rw [eq_div_of_mul_eq hX h, div_pow, mul_pow, div_pow]
  field_simp

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem normD_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : 0 < normD h L := by
  have hd' : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x hne φ
    simp [hx] at this
  have hne := LocF.discrIdeal_ne_bot hd' hL hLi
  unfold normD
  apply Real.sqrt_pos.mpr
  have : Ideal.absNorm (discrIdeal h L) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hne
  exact_mod_cast Nat.pos_of_ne_zero this

theorem tendsto_left (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    Tendsto (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (Formalism.HermitianLatticesTheory.mass h L *
        ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
          (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L)))) := by
  rw [RankOne.mass_eq_sum h L s hsr, Finset.sum_mul]
  simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ fun M hM => ?_
  have hg := hsr.1 M hM
  obtain ⟨hMi, -, hMD⟩ := integral_of_mem_genus hK hF hs hd hL hLi hg
  have ht := (tendsto_ballCount hK hF hs hd hg.1 hMi).const_mul
    ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)⁻¹)
  rw [hMD] at ht
  refine ht.congr fun j => ?_
  rw [div_eq_mul_inv (ballCount h M ((j : ℝ) ^ 2) : ℝ), div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem tendsto_right (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {c : ℝ} (hc : MassConst K F (finrank K V - 1) c) :
    Tendsto (fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (0 + c * lamG F h L * (normD h L)⁻¹ *
        ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
          Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F (finrank K V)))) := by
  have hf : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have hexp : 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V ≠ 0 := by positivity
  have h1 : Tendsto (fun j : ℕ => Formalism.HermitianLatticesTheory.mass h L /
      (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hexp).comp tendsto_natCast_atTop_atTop)
  have h2 := (tendsto_singS_sum hK hF hs hd hL hLi hm).const_mul
    (c * lamG F h L * (normD h L)⁻¹)
  refine (h1.add h2).congr fun j => ?_
  rw [add_div]
  congr 1
  rw [finsum_mem_congr rfl fun n hn => repMass_eq hH hLI hK hF hs hd hL hLi hm hc hn,
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    ← Finset.mul_sum, zpow_neg, zpow_natCast, ← pow_mul, ← mul_assoc 2, div_eq_mul_inv]
  ring

end Step

theorem massConst_succ (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc0 : 0 < c) (hc : MassConst K F (m - 1) c) :
    MassConst K F m (c * Formalism.HermitianLatticesTheory.massRatioRightSide K m) := by
  unfold MassConst
  intro V _ _ _ _ _ h L hs hd hfin hL hLi
  subst hfin
  obtain ⟨s, hsr⟩ := StabilizerLattices.exists_classReps hs hd hL.toIsLattice
  have hlim := Step.tendsto_left hK hF hs hd hL hLi hsr
  have hlim2 := Step.tendsto_right hH hLI hK hF hs hd hL hLi hm hc
  have hfun : (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) =
      fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    funext j
    rw [sum_ballCount_eq hK hF hs hd hL.toIsLattice hLi hsr (by positivity)]
  rw [hfun] at hlim
  have hAB := tendsto_nhds_unique hlim hlim2
  have hn0 : 0 < finrank K V := by omega
  have hfact : ((finrank K V).factorial : ℝ) =
      (finrank K V : ℝ) * ((finrank K V - 1).factorial : ℝ) := by
    rw [← Nat.mul_factorial_pred hn0.ne']
    push_cast
    ring
  rw [hfact, zpow_neg, zpow_natCast] at hAB
  have hv := vInv_pos K
  have key := Step.final_algebra (Formalism.HermitianLatticesTheory.mass h L) c (lamG F h L) (normD h L)
    (Real.pi ^ finrank K V) ((finrank K V - 1).factorial : ℝ) (finrank K V : ℝ)
    (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
    (Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K)) (lValEtaF K F (finrank K V))
    (Formalism.HermitianLatticesTheory.fDeg K) (Step.normD_pos hd hL hLi) (by positivity) (by positivity)
    (by exact_mod_cast hn0) (by positivity) (by positivity) hAB
  rw [massRatio_eq_lvalue hK hF (finrank K V) hm]
  exact key

end Formalism.HermitianLattices.Ext.L3
