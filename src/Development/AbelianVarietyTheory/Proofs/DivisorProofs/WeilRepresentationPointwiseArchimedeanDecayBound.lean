module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordActionSquareIntegrableBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedPiTensor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundPeriodicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitCubeTranslatesSlabPeriodicLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitCubeTranslatesSlabPeriodicLe
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem lintegral_cube_slab_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G)
    (π : G →+ (Fin N → ℝ)) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) (U : Set G)
    (hS : MeasurableSet {w | w - ι (π w) ∈ U})
    (hfin : ∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) (hper : ∀ w, ∀ u ∈ U, φ (w + u) = φ w) (y : G) :
    μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ := by
  set S : Set G := {w | w - ι (π w) ∈ U} with hSdef
  let ν : Measure (Fin N → ℝ) := (μ.restrict S).map π
  have hν : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S) := fun A hA => by
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have : IsFiniteMeasureOnCompacts ν := ⟨fun A hA => by
    rw [hν A hA.measurableSet]
    exact lt_top_iff_ne_top.2 (hfin A hA)⟩
  have : ν.IsAddLeftInvariant := (forall_measure_preimage_add_iff ν).1 fun t A hA => by
    rw [hν A hA, hν _ (measurable_const_add t hA), ← measure_preimage_add μ (ι t) (π ⁻¹' A ∩ S)]
    congr 1
    ext w
    simp only [hSdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, map_add (f := _), hπι, add_sub_add_left_eq_sub]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have hcube : MeasurableSet (cube N) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hvol : volume (cube N) = 1 := by
    simp [cube, Real.volume_Icc_pi]
  have hνc : μ (π ⁻¹' cube N ∩ S) = c := by
    rw [← hν _ hcube, hc, Measure.smul_apply, hvol]; simp
  have hf : Measurable fun t => φ (y + ι t) := hφ.comp (measurable_const_add y |>.comp hι.measurable)
  have e1 : ∫⁻ t in cube N, φ (y + ι t) ∂ν = c * ∫⁻ t in cube N, φ (y + ι t) := by
    rw [hc, Measure.restrict_smul, lintegral_smul_measure]; rfl
  rw [hνc, ← e1, setLIntegral_map hcube hf hπ.measurable,
    Measure.restrict_restrict (hπ.measurable hcube)]
  have e2 : ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + ι (π w)) ∂μ = ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + w) ∂μ := by
    refine setLIntegral_congr_fun ((hπ.measurable hcube).inter hS) fun w hw => ?_
    have := hper (y + ι (π w)) _ hw.2
    rw [← this]
    congr 1
    abel
  rw [e2]
  calc ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + w) ∂μ ≤ ∫⁻ w, φ (y + w) ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ w, φ w ∂μ := lintegral_add_left_eq_self φ y

end GlobalTheory.ArchDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitCubeTranslatesSlabPeriodicLeStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_unitCube_translates_slabPeriodic_le : ∀ {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G) (π : G →+ (Fin N → ℝ)), Continuous ι → Continuous π → (∀ t, π (ι t) = t) → ∀ (U : Set G), MeasurableSet {w | w - ι (π w) ∈ U} → (∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤) → ∀ (φ : G → ℝ≥0∞), Measurable φ → (∀ w, ∀ u ∈ U, φ (w + u) = φ w) → ∀ y : G, μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ := by
  first | exact @GlobalTheory.ArchDecay.lintegral_cube_slab_le | exact GlobalTheory.ArchDecay.lintegral_cube_slab_le | (intros; apply GlobalTheory.ArchDecay.lintegral_cube_slab_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabOpenUnitCubeHaarPosFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabOpenUnitCubeHaarPosFinite
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

def intFin : Set (Af F) := {x | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

theorem isOpen_intFin : IsOpen (intFin F) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun _ => Valued.isOpen_valuationSubring _)

theorem isCompact_intFin : IsCompact (intFin F) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem sub_archIn_apply (w : κ → AF F) (i : κ) :
    (w - archIn F κ (archOut F κ w)) i = ((0 : Ainf F), (w i).2) := by
  have h : archIn F κ (archOut F κ w) i = infAd F (evI F (w i)) := by
    rw [archIn_apply, archOut_apply, LinearEquiv.symm_apply_apply]; rfl
  rw [Pi.sub_apply, h]
  refine Prod.ext ?_ ?_
  · change (w i).1 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F) (w i).1) = 0
    rw [RingEquiv.symm_apply_apply, sub_self]
  · change (w i).2 - 0 = (w i).2
    rw [sub_zero]

theorem mem_slab_iff (m : ℕ) (hm : 0 < m) (w : κ → AF F) :
    w ∈ slab F κ m ↔ ∀ i, algebraMap F (Af F) ((m : F)⁻¹) * (w i).2 ∈ intFin F := by
  have hm0 : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hc : algebraMap F (Af F) ((m : F)⁻¹) * (m : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, inv_mul_cancel₀ hm0, map_one]
  change (∀ i, ∃ a : AF F, _ ∧ _ ∧ _) ↔ _
  refine forall_congr' fun i => ?_
  rw [sub_archIn_apply]
  constructor
  · rintro ⟨a, -, ha, he⟩
    have h2 : (w i).2 = (m : Af F) * a.2 := by
      have := congrArg Prod.snd he
      rw [this]
      change sndA F ((m : AF F) * a) = _
      rw [map_mul, map_natCast]; rfl
    intro v
    rw [h2, ← mul_assoc, hc, one_mul]
    exact ha v
  · intro h
    refine ⟨pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2), ?_, fun v => h v, ?_⟩
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F) 0 = 0
      exact map_zero _
    · refine Prod.ext ?_ ?_
      · change (0 : Ainf F) = fstA F ((m : AF F) * pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2))
        rw [map_mul]
        change (0 : Ainf F) = fstA F (m : AF F) * 0
        rw [mul_zero]
      · change (w i).2 = sndA F ((m : AF F) * pairA F 0 (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2))
        rw [map_mul, map_natCast]
        change (w i).2 = (m : Af F) * (algebraMap F (Af F) ((m : F)⁻¹) * (w i).2)
        rw [← mul_assoc, mul_comm (m : Af F), hc, one_mul]

theorem isOpen_slab (m : ℕ) (hm : 0 < m) : IsOpen (slab F κ m) := by
  have : slab F κ m = ⋂ i, (fun w : κ → AF F => algebraMap F (Af F) ((m : F)⁻¹) * (w i).2) ⁻¹' intFin F := by
    ext w; rw [mem_slab_iff F κ m hm]; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i => (isOpen_intFin F).preimage
    (continuous_const.mul (continuous_snd.comp (continuous_apply i)))

theorem archIn_mem_slab (t : Fin (dimA F κ) → ℝ) : archIn F κ t ∈ slab F κ 1 := by
  rw [mem_slab_iff F κ 1 one_pos]
  intro i v
  have : (archIn F κ t i).2 = 0 := rfl
  rw [this, mul_zero]
  exact zero_mem _

open scoped Pointwise in
theorem slab_open_cube_pos_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧ ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ := by
  intro F _ _ κ _
  refine ⟨fun m hm => isOpen_slab F κ m hm, fun μ hμ => ?_⟩
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  refine ⟨?_, fun A hA => ?_⟩
  · let U := archOut F κ ⁻¹' (Set.univ.pi fun _ => Set.Ioo (0 : ℝ) 1) ∩ slab F κ 1
    have hU : IsOpen U :=
      ((isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage (continuous_archOut F κ)).inter
        (isOpen_slab F κ 1 one_pos)
    have hne : U.Nonempty := by
      refine ⟨archIn F κ (fun _ => 1 / 2), ?_, archIn_mem_slab F κ _⟩
      simp only [Set.mem_preimage, archOut_archIn, Set.mem_pi, Set.mem_univ, true_implies]
      intro _; constructor <;> norm_num
    refine lt_of_lt_of_le (hU.measure_pos μ hne) (measure_mono ?_)
    exact Set.inter_subset_inter_left _ (Set.preimage_mono (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self))
  · let K : Set (κ → AF F) := (fun y : κ → Af F => fun i => pairA F 0 (y i)) '' Set.univ.pi fun _ => intFin F
    have hK : IsCompact K := by
      refine (isCompact_univ_pi fun _ => isCompact_intFin F).image (continuous_pi fun i => ?_)
      exact (continuous_const.prodMk (continuous_apply i) : Continuous fun y : κ → Af F => ((0 : Ainf F), y i))
    have hsub : archOut F κ ⁻¹' A ∩ slab F κ 1 ⊆ archIn F κ '' A + K := by
      rintro w ⟨hwA, hw⟩
      refine Set.mem_add.2 ⟨archIn F κ (archOut F κ w), ⟨_, hwA, rfl⟩, w - archIn F κ (archOut F κ w),
        ⟨fun i => (w i).2, fun i _ => ?_, funext fun i => (sub_archIn_apply F κ w i).symm⟩, add_sub_cancel _ _⟩
      have h := (mem_slab_iff F κ 1 one_pos w).1 hw i
      rwa [Nat.cast_one, inv_one, map_one, one_mul] at h
    exact ((measure_mono hsub).trans_lt ((hA.image (continuous_archIn F κ)).add hK).measure_lt_top).ne

end GlobalTheory.ArchDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabOpenUnitCubeHaarPosFiniteStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSlab_open_unitCube_haar_pos_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧ ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ := by
  first | exact @GlobalTheory.ArchDecay.slab_open_cube_pos_finite | exact GlobalTheory.ArchDecay.slab_open_cube_pos_finite | (intros; apply GlobalTheory.ArchDecay.slab_open_cube_pos_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabCoveredByTranslatesOfSmallerSlab
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabCoveredByTranslatesOfSmallerSlab
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.SlabCover

open IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

theorem exists_int_approx (m : ℕ) (hm : 0 < m) (y : Af F)
    (hy : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, ∃ t : Af F, (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) ∧
      y - algebraMap F (Af F) (r : F) = (m : Af F) * t := by
  have hm' : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  set g : Af F → Af F := fun x => algebraMap F (Af F) (m : F)⁻¹ * (x - y) with hg
  have hgc : Continuous g := continuous_const.mul (continuous_id.sub continuous_const)
  set U : Set (Af F) := g ⁻¹' {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} with hU
  have hUo : IsOpen U :=
    (RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)).preimage hgc
  have hyU : y ∈ U := by
    intro v
    simp only [hg, sub_self, mul_zero]
    exact zero_mem _
  obtain ⟨ρ, hρ⟩ := (PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)).exists_mem_open hUo ⟨y, hyU⟩
  have hmm : (m : Af F) * algebraMap F (Af F) (m : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, mul_inv_cancel₀ hm', map_one]
  have he : algebraMap F (Af F) ρ = y + (m : Af F) * g (algebraMap F (Af F) ρ) := by
    simp only [hg, ← mul_assoc, hmm, one_mul]; ring
  have hint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (algebraMap F (Af F) ρ) v ∈ v.adicCompletionIntegers F := by
    intro v
    rw [he]
    show y v + (m : v.adicCompletion F) * (g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F
    exact add_mem (hy v) (mul_mem (natCast_mem _ m) (hρ v))
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F ρ
    (fun v => by
      have h := hint v
      rw [mem_adicCompletionIntegers] at h
      exact (valuedAdicCompletion_eq_valuation' v ρ).symm.trans_le h)
  refine ⟨r, -g (algebraMap F (Af F) ρ), fun v => ?_, ?_⟩
  · show -(g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F
    exact neg_mem (hρ v)
  · have : ((r : 𝓞 F) : F) = ρ := hr
    rw [this]
    conv_lhs => rw [he]
    ring

theorem exists_residues (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset F, S.card ≤ m ^ Module.finrank ℚ F ∧ ∀ r : 𝓞 F, ∃ ρ ∈ S, ∃ q : 𝓞 F, (r : F) - ρ = (m : F) * (q : F) := by
  set b := RingOfIntegers.basis F
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  refine ⟨(Fintype.piFinset fun _ : ι => Finset.range m).image
    (fun c => (((∑ k, (c k : ℤ) • b k : 𝓞 F)) : F)), ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
      ← Module.finrank_eq_card_basis b, RingOfIntegers.rank]
  · intro r
    have hmz : (0 : ℤ) < m := by exact_mod_cast hm
    refine ⟨_, Finset.mem_image.2 ⟨fun k => ((b.repr r k) % m).toNat, ?_, rfl⟩,
      ∑ k, ((b.repr r k) / m) • b k, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro k
      rw [Finset.mem_range]
      have h1 := Int.emod_nonneg (b.repr r k) hmz.ne'
      have h2 := Int.emod_lt_of_pos (b.repr r k) hmz
      omega
    · have hc : ∀ k, (((b.repr r k) % m).toNat : ℤ) = (b.repr r k) % m := fun k =>
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))
      have key : r - ∑ k, (((b.repr r k) % m).toNat : ℤ) • b k = (m : 𝓞 F) * ∑ k, ((b.repr r k) / m) • b k := by
        have hr := b.sum_repr r
        set a := b.repr r
        simp only [hc, Finset.mul_sum]
        conv_lhs => rw [← hr, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h := Int.emod_add_mul_ediv (a k) m
        have h' : ((a k % m : ℤ) : 𝓞 F) + (m : 𝓞 F) * ((a k / m : ℤ) : 𝓞 F) = ((a k : ℤ) : 𝓞 F) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : 𝓞 F)) h
        simp only [zsmul_eq_mul]
        linear_combination (-(b k)) * h'
      have := congrArg (fun x : 𝓞 F => (x : F)) key
      simpa using this

end GlobalTheory.ArchDecay.SlabCover

namespace GlobalTheory.ArchDecay.SlabCover

variable {F : Type} [Field F] [NumberField F]

theorem exists_finite_residues (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset F, S.card ≤ m ^ Module.finrank ℚ F ∧ ∀ y : Af F,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F) →
      ∃ ρ ∈ S, ∃ z : Af F, (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), z v ∈ v.adicCompletionIntegers F) ∧
        y - algebraMap F (Af F) ρ = (m : Af F) * z := by
  obtain ⟨S, hS, hres⟩ := exists_residues (F := F) m hm
  refine ⟨S, hS, fun y hy => ?_⟩
  obtain ⟨r, t, ht, hrt⟩ := exists_int_approx m hm y hy
  obtain ⟨ρ, hρS, q, hq⟩ := hres r
  refine ⟨ρ, hρS, t + algebraMap F (Af F) (q : F), fun v => ?_, ?_⟩
  · show t v + algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F q) ∈ v.adicCompletionIntegers F
    exact add_mem (ht v) (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v q)
  · have e : algebraMap F (Af F) ρ = algebraMap F (Af F) (r : F) - (m : Af F) * algebraMap F (Af F) (q : F) := by
      rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, ← map_sub, ← hq]; ring_nf
    rw [e, mul_add, ← hrt]; ring

end GlobalTheory.ArchDecay.SlabCover

namespace GlobalTheory.ArchDecay

open GlobalTheory.ArchDecay.SlabCover

theorem slab_subset_and_cover : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c : ℕ, ∀ m : ℕ, 0 < m →
    slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧ (∀ r ∈ R, arch F r = 0) ∧
      ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m := by
  intro F _ _ κ _
  refine ⟨Module.finrank ℚ F * Fintype.card κ, fun m hm => ⟨?_, ?_⟩⟩
  · intro w hw i
    obtain ⟨a, ha0, hai, hae⟩ := hw i
    refine ⟨(m : AF F) * a, ?_, fun v => ?_, ?_⟩
    · show InfiniteAdeleRing.ringEquiv_mixedSpace F ((m : Ainf F) * a.1) = 0
      have : InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 = 0 := ha0
      rw [map_mul, this, mul_zero]
    · show ((m : AF F) * a).2 v ∈ v.adicCompletionIntegers F
      show (m : v.adicCompletion F) * a.2 v ∈ v.adicCompletionIntegers F
      exact mul_mem (natCast_mem _ m) (hai v)
    · rw [hae, Nat.cast_one, one_mul]
  · obtain ⟨S, hS, hres⟩ := exists_finite_residues (F := F) m hm
    let emb : (κ → F) → (κ → AF F) := fun f i => pairA F 0 (algebraMap F (Af F) (f i))
    refine ⟨(Fintype.piFinset fun _ : κ => S).image emb, ?_, ?_, ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, pow_mul]
      exact Nat.pow_le_pow_left hS _
    · intro r hr
      obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hr
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    · intro w hw
      have hw' := hw
      choose a ha0 hai hae using hw'
      have hy : ∀ i, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (a i).2 v ∈ v.adicCompletionIntegers F :=
        fun i v => hai i v
      choose ρ hρS z hz hρz using fun i => hres (a i).2 (hy i)
      refine ⟨emb ρ, Finset.mem_image.2 ⟨ρ, Fintype.mem_piFinset.2 hρS, rfl⟩, ?_⟩
      have harch : arch F (emb ρ) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      have hout : archOut F κ (w - emb ρ) = archOut F κ w := by
        rw [map_sub, archOut_apply F κ (emb ρ), harch, map_zero, sub_zero]
      intro i
      refine ⟨pairA F 0 (z i), map_zero _, fun v => hz i v, ?_⟩
      have h1 : (a i).1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1 = 0 := ha0 i
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this
      have h2 : (w - archIn F κ (archOut F κ w)) i = a i := by rw [hae i, Nat.cast_one, one_mul]
      rw [hout]
      have h3 : (w - emb ρ - archIn F κ (archOut F κ w)) i = (w - archIn F κ (archOut F κ w)) i - emb ρ i := by
        simp only [Pi.sub_apply]; abel
      rw [h3, h2]
      refine Prod.ext ?_ ?_
      · show (a i).1 - 0 = (m : Ainf F) * 0
        rw [h1, sub_zero, mul_zero]
      · show (a i).2 - algebraMap F (Af F) (ρ i) = (m : Af F) * z i
        exact hρz i

end GlobalTheory.ArchDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabCoveredByTranslatesOfSmallerSlabStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSlab_covered_by_translates_of_smaller_slab : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c : ℕ, ∀ m : ℕ, 0 < m → slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧ (∀ r ∈ R, arch F r = 0) ∧ ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m := by
  first | exact @GlobalTheory.ArchDecay.slab_subset_and_cover | exact GlobalTheory.ArchDecay.slab_subset_and_cover | (intros; apply GlobalTheory.ArchDecay.slab_subset_and_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzContinuousHasDerivAtArchimedeanLin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzContinuousHasDerivAtArchimedeanLin
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.SchLine

theorem continuous_pureA (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : Continuous (pureA F f g) := by
  unfold pureA
  refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_)) (hg.1.continuous.comp (continuous_pi fun i => ?_))
  · exact (continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  · exact continuous_snd.comp (continuous_apply i)

theorem continuous_of_mem (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact continuous_pureA F f g hg
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul a Φ _ h => exact h.const_smul a

theorem line_shift (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) (t s : ℝ) :
    x + (fun i => infAd F (s • v i)) = (x + fun i => infAd F (t • v i)) + fun i => infAd F ((s - t) • v i) := by
  funext i
  simp only [Pi.add_apply]
  rw [add_assoc, ← infAd_add, ← add_smul, add_sub_cancel]

theorem schline : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ schA F κ, Continuous g ∧
    ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t := by
  intro F _ _ κ _ g hg
  refine ⟨continuous_of_mem F hg, fun v x t => ?_⟩
  set y : κ → AF F := x + fun i => infAd F (t • v i)
  have h0 : HasDerivAt (fun u : ℝ => g (y + fun i => infAd F (u • v i))) (dD F v g y) (t - t) := by
    rw [sub_self]
    exact ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hg).1 y).hasDerivAt
  have h1 := h0.comp_sub_const t t
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show g (x + fun i => infAd F (s • v i)) = g (y + fun i => infAd F ((s - t) • v i))
  rw [line_shift F x v t s]

end GlobalTheory.ArchDecay.SchLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzContinuousHasDerivAtArchimedeanLinStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_continuous_hasDerivAt_archimedeanLine : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ schA F κ, Continuous g ∧ ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ), HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t := by
  first | exact @GlobalTheory.ArchDecay.SchLine.schline | exact GlobalTheory.ArchDecay.SchLine.schline | (intros; apply GlobalTheory.ArchDecay.SchLine.schline <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundPeriodicSchwartz
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem schA_line (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : ∀ g ∈ schA F κ, Continuous g ∧
    ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t :=
  GlobalTheory.T.adelicSchwartz_continuous_hasDerivAt_archimedeanLine F κ

theorem slice_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G) (π : G →+ (Fin N → ℝ))
    (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) (U : Set G)
    (hU : MeasurableSet {w | w - ι (π w) ∈ U})
    (hfin : ∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) (hper : ∀ w, ∀ u ∈ U, φ (w + u) = φ w) (y : G) :
    μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ :=
  GlobalTheory.T.lintegral_unitCube_translates_slabPeriodic_le μ ι π hι hπ hπι U hU hfin φ hφ hper y

theorem slab_top (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧
        ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ :=
  GlobalTheory.T.archimedeanSlab_open_unitCube_haar_pos_finite F κ

theorem slab_cover (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ c : ℕ, ∀ m : ℕ, 0 < m → slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧
      (∀ r ∈ R, arch F r = 0) ∧ ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m :=
  GlobalTheory.T.archimedeanSlab_covered_by_translates_of_smaller_slab F κ

end GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem wordD_cons (v : κ → mixedEmbedding.mixedSpace F) (w : List (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → AF F) → ℂ) : wordD F (v :: w) f = dD F v (wordD F w f) := rfl

theorem per_dD {m : ℕ} {f : (κ → AF F) → ℂ} (h : Per F m f) (v : κ → mixedEmbedding.mixedSpace F) :
    Per F m (dD F v f) := by
  intro x z hz
  unfold dD
  congr 1
  funext t
  rw [add_right_comm]
  exact h _ z hz

theorem per_wordD {m : ℕ} {f : (κ → AF F) → ℂ} (h : Per F m f) (w : List (κ → mixedEmbedding.mixedSpace F)) :
    Per F m (wordD F w f) := by
  induction w with
  | nil => exact h
  | cons v w ih => rw [wordD_cons]; exact per_dD ih v

theorem wordD_mem {f : (κ → AF F) → ℂ} (hf : f ∈ schA F κ) (w : List (κ → mixedEmbedding.mixedSpace F)) :
    wordD F w f ∈ schA F κ := by
  induction w with
  | nil => exact hf
  | cons v w ih => rw [wordD_cons]; exact GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F κ (Sum.inl v) _ ih

theorem archIn_single (j : Fin (dimA F κ)) (s : ℝ) :
    archIn F κ (Pi.single j s) = fun i => infAd F (s • ubasis F κ j i) := by
  funext i
  rw [archIn_apply]
  congr 1
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_eq_single j (fun c hc => by simp [Pi.single_apply, hc])]
  simp

theorem sobolev_schA {f : (κ → AF F) → ℂ} (hf : f ∈ schA F κ) (x : κ → AF F) (B : ℝ)
    (hB : ∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ dimA F κ → (∀ v ∈ w, ∃ j, v = ubasis F κ j) →
      ∫ t in cube (dimA F κ), ‖wordD F w f (x + archIn F κ t)‖ ^ 2 ≤ B) :
    ‖f x‖ ^ 2 ≤ 4 ^ dimA F κ * B := by
  let A : ℕ → Set ((κ → AF F) → ℂ) := fun p =>
    {u | ∃ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ p ∧ (∀ v ∈ w, ∃ j, v = ubasis F κ j) ∧
      u = wordD F w f}
  have hA : Monotone A := fun p q hpq u ⟨w, h1, h2, h3⟩ => ⟨w, h1.trans hpq, h2, h3⟩
  have key := GlobalTheory.ThetaGrowth.sobolev_iter (dimA F κ) 0 (fun j s => archIn F κ (Pi.single j s)) A B x
    (fun j => (continuous_archIn F κ).comp (continuous_single (A := fun _ : Fin (dimA F κ) => ℝ) j)) hA ?_ ?_ f ⟨[], by simp, by simp, rfl⟩
  · exact key
  · rintro p u ⟨w, h1, h2, rfl⟩
    have hmem := wordD_mem hf w
    refine ⟨(schA_line F κ _ hmem).1, fun j => ⟨wordD F (ubasis F κ j :: w) f,
      ⟨_, by simpa using h1, ?_, rfl⟩, fun y => ?_⟩⟩
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact ⟨j, rfl⟩
      · exact h2 v hv
    · have hd := (schA_line F κ _ hmem).2 (ubasis F κ j) y
      have hc : Continuous fun s : ℝ => y + fun i => infAd F (s • ubasis F κ j i) :=
        continuous_const.add (continuous_pi fun i => (continuous_infAd F).comp (continuous_id.smul continuous_const))
      have := GlobalTheory.sobolev_endpoint_one_variable ℂ (fun s => wordD F w f (y + fun i => infAd F (s • ubasis F κ j i)))
        (fun s => dD F (ubasis F κ j) (wordD F w f) (y + fun i => infAd F (s • ubasis F κ j i))) 1 one_pos
        (fun t _ => hd t)
        (((schA_line F κ _ (wordD_mem hf (ubasis F κ j :: w))).1.comp hc).continuousOn)
      simp only [archIn_single, wordD_cons]
      simpa [infAd_zero, ← Pi.zero_def] using this
  · rintro u ⟨w, h1, h2, rfl⟩
    have e : ∀ t : Fin (dimA F κ) → ℝ, ∑ j, archIn F κ (Pi.single j (t j)) = archIn F κ t := by
      intro t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.univ_sum_single]
    simp only [e]
    exact hB w (by simpa using h1) h2

end GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem cube_bound (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ φ : (κ → AF F) → ℂ, Continuous φ → Per F m φ → ∀ b : ℝ, 0 ≤ b →
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b → ∀ y,
        ∫ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨hopen, hμ1⟩ := slab_top F κ
  obtain ⟨h0, hfin1⟩ := hμ1 μ hμ
  obtain ⟨c, hc⟩ := slab_cover F κ
  have hQc : IsCompact (cube (dimA F κ)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hc₁ : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ≠ ⊤ := hfin1 _ hQc
  refine ⟨(μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal⁻¹, c, by positivity,
    fun m hm φ hφ hper b hb hL y => ?_⟩
  obtain ⟨hsub, R, hRc, hR0, hRcov⟩ := hc m hm
  have hcm : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ≤
      (m : ℝ≥0∞) ^ c * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by
    calc μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)
        ≤ ∑ r ∈ R, μ ((fun w => r + w) '' (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m)) := by
          refine (measure_mono ?_).trans (measure_biUnion_finset_le R _)
          rintro w ⟨hwQ, hw1⟩
          obtain ⟨r, hr, hwr⟩ := hRcov w hw1
          have hπr : archOut F κ r = 0 := by rw [archOut_apply, hR0 r hr, map_zero]
          refine Set.mem_biUnion hr ⟨w - r, ⟨?_, hwr⟩, by abel_nf⟩
          show archOut F κ (w - r) ∈ cube (dimA F κ)
          rw [map_sub, hπr, sub_zero]; exact hwQ
      _ = ∑ r ∈ R, μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Set.image_add_left, measure_preimage_add]
      _ = R.card * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr; exact_mod_cast hRc
  have hS := slice_le μ (archIn F κ) (archOut F κ) (continuous_archIn F κ) (continuous_archOut F κ)
    (archOut_archIn F κ) (perSet F κ m) (hopen m hm).measurableSet
    (fun A hA => ne_top_of_le_ne_top (hfin1 A hA) (measure_mono (Set.inter_subset_inter_right _ hsub)))
    (fun w => ‖φ w‖ₑ ^ 2) (hφ.measurable.enorm.pow_const 2)
    (fun w u hu => by simp only [hper w u hu]) y
  set X := ∫⁻ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ₑ ^ 2
  have h1 : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) * X ≤ (m : ℝ≥0∞) ^ c * ENNReal.ofReal b :=
    calc _ ≤ (m : ℝ≥0∞) ^ c * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) * X := by gcongr
      _ = (m : ℝ≥0∞) ^ c * (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) * X) := by ring
      _ ≤ _ := by gcongr; exact hS.trans hL
  have hI : ∫ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ ^ 2 = X.toReal := by
    have hcont : Continuous fun t => ‖φ (y + archIn F κ t)‖ ^ 2 :=
      (hφ.comp (continuous_const.add (continuous_archIn F κ))).norm.pow 2
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖φ (y + archIn F κ t)‖ ^ 2)
      (ae_of_all _ fun _ => by positivity) hcont.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h2 : (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal * X.toReal ≤ (m : ℝ) ^ c * b := by
    rw [← ENNReal.toReal_mul]
    refine (ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) h1).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hb]
  have hpos : 0 < (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal := ENNReal.toReal_pos h0.ne' hc₁
  rw [hI, mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hpos, mul_comm]
  exact h2

theorem sobolev_per : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ (P : ℕ) (C : ℝ) (c : ℕ), ∀ m : ℕ, 0 < m → ∀ f ∈ schA F κ,
      Per F m f → ∀ b : ℝ, 0 ≤ b → (∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ P → (∀ v ∈ w, ‖v‖ ≤ 1) →
        ∫⁻ x, ‖wordD F w f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b) → ∀ x, ‖f x‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  intro F _ _ κ _ μ hμ
  obtain ⟨C₀, c, -, hb⟩ := cube_bound μ hμ
  refine ⟨dimA F κ, 4 ^ dimA F κ * C₀, c, fun m hm f hf hper b hb0 hw x => ?_⟩
  have := sobolev_schA hf x (C₀ * m ^ c * b) fun w hl hv =>
    hb m hm _ (schA_line F κ _ (wordD_mem hf w)).1 (per_wordD hper w) b hb0
      (hw w hl fun v hv' => by obtain ⟨j, rfl⟩ := hv v hv'; rw [norm_ubasis]) x
  calc _ ≤ _ := this
    _ = _ := by ring

end GlobalTheory.ArchDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundPeriodicSchwartzStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_bound_periodic_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ (P : ℕ) (C : ℝ) (c : ℕ), ∀ m : ℕ, 0 < m → ∀ f ∈ schA F κ, Per F m f → ∀ b : ℝ, 0 ≤ b → (∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ P → (∀ v ∈ w, ‖v‖ ≤ 1) → ∫⁻ x, ‖wordD F w f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b) → ∀ x, ‖f x‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  first | exact @GlobalTheory.ArchDecay.sobolev_per | exact GlobalTheory.ArchDecay.sobolev_per | (intros; apply GlobalTheory.ArchDecay.sobolev_per <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddNormPowLeSumLinearFormPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddNormPowLeSumLinearFormPow
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem onePlusNormPow_le_sum_linearForm_pow : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ), ∃ (K : ℕ) (l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (C : ℝ), (∀ j, ‖l j‖ ≤ 1) ∧ ∀ y, (1 + ‖y‖) ^ N ≤ C * (1 + ∑ j, |l j y| ^ N) := by
  intro F _ _ κ _ N
  let b := Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)
  let K := Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)
  let c : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
    fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let w : Fin K → ℝ := fun j => (1 + ‖c j‖) * ‖b j‖
  have hw : ∀ j, 0 ≤ w j := fun j => by positivity
  let W : ℝ := 1 + ∑ j, w j
  have hW1 : 1 ≤ W := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hw j); simp only [W]; linarith
  have hwW : ∀ j, w j ≤ W := fun j => by
    have := Finset.single_le_sum (f := w) (fun j _ => hw j) (Finset.mem_univ j)
    simp only [W]; linarith
  let l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := fun j => (1 + ‖c j‖)⁻¹ • c j
  have hl : ∀ j, ‖l j‖ ≤ 1 := fun j => by
    have h0 : 0 < 1 + ‖c j‖ := by positivity
    simp only [l, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h0]
    rw [inv_mul_le_iff₀ h0]; linarith
  have hlw : ∀ j y, |l j y| * w j = |b.repr y j| * ‖b j‖ := fun j y => by
    have h0 : 0 < 1 + ‖c j‖ := by positivity
    simp only [l, w, c, ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos h0]
    field_simp
  have hnorm : ∀ y, ‖y‖ ≤ ∑ j, |l j y| * w j := fun y => by
    calc ‖y‖ = ‖∑ j, b.repr y j • b j‖ := by rw [b.sum_repr y]
      _ ≤ ∑ j, ‖b.repr y j • b j‖ := norm_sum_le _ _
      _ = ∑ j, |l j y| * w j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hlw, norm_smul, Real.norm_eq_abs]
  refine ⟨K, l, ((K : ℝ) + 1) ^ N * W ^ N, hl, fun y => ?_⟩
  have hS : 0 ≤ ∑ j, |l j y| ^ N := Finset.sum_nonneg fun j _ => by positivity
  rcases N with _ | n
  · simp only [pow_zero, one_mul]
    have : (0:ℝ) ≤ ∑ _x : Fin K, (1:ℝ) := by positivity
    linarith
  let f : Option (Fin K) → ℝ := fun o => Option.elim o 1 fun j => |l j y| * w j
  have hf : ∀ o ∈ (Finset.univ : Finset (Option (Fin K))), 0 ≤ f o := by
    intro o _; cases o with
    | none => simp [f]
    | some j => simp only [f, Option.elim_some]; exact mul_nonneg (abs_nonneg _) (hw j)
  have h1 : 1 + ‖y‖ ≤ ∑ o, f o := by
    rw [Fintype.sum_option]; simp only [f, Option.elim_none, Option.elim_some]
    linarith [hnorm y]
  have h2 := pow_sum_le_card_mul_sum_pow hf n
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin, Fintype.sum_option] at h2
  simp only [f, Option.elim_none, Option.elim_some, one_pow] at h2
  have h3 : ∑ j, (|l j y| * w j) ^ (n + 1) ≤ W ^ (n + 1) * ∑ j, |l j y| ^ (n + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hw j) (hwW j) _) (by positivity)
  have hW : 1 ≤ W ^ (n + 1) := one_le_pow₀ hW1
  have hK : ((K : ℝ) + 1) ^ n ≤ ((K : ℝ) + 1) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith [(K.cast_nonneg : (0:ℝ) ≤ K)]) (Nat.le_succ n)
  have hKn : 0 ≤ ((K : ℝ) + 1) ^ n := by positivity
  calc (1 + ‖y‖) ^ (n + 1) ≤ (∑ o, f o) ^ (n + 1) :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ ≤ ((K : ℝ) + 1) ^ n * (1 + ∑ j, (|l j y| * w j) ^ (n + 1)) := by
        rw [Fintype.sum_option]; simpa [f] using h2
    _ ≤ ((K : ℝ) + 1) ^ n * (W ^ (n + 1) * (1 + ∑ j, |l j y| ^ (n + 1))) := by
        gcongr; nlinarith
    _ ≤ ((K : ℝ) + 1) ^ (n + 1) * W ^ (n + 1) * (1 + ∑ j, |l j y| ^ (n + 1)) := by
        rw [← mul_assoc]; gcongr

end GlobalTheory.ArchDecay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddNormPowLeSumLinearFormPowStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_norm_pow_le_sum_linearForm_pow : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ), ∃ (K : ℕ) (l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (C : ℝ), (∀ j, ‖l j‖ ≤ 1) ∧ ∀ y, (1 + ‖y‖) ^ N ≤ C * (1 + ∑ j, |l j y| ^ N) := by
  first | exact @GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow | exact GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow | (intros; apply GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem per_mM {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {m : ℕ} {f : (κ → AF F) → ℂ}
    (h : Per F m f) (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) : Per F m (mM F l f) := by
  intro x z hz
  have hev : ∀ a b : AF F, evI F (a + b) = evI F a + evI F b := fun a b =>
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hmul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b =>
    map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have ha : arch F (x + z) = arch F x := by
    funext i
    obtain ⟨a, ha0, -, hza⟩ := hz i
    show evI F (x i + z i) = evI F (x i)
    rw [hev, hza, hmul, ha0, mul_zero, add_zero]
  unfold mM
  rw [ha, h x z hz]

theorem norm_word_rep {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) (N : ℕ) :
    ‖word F (List.replicate N (Sum.inr l)) f x‖ = |l (arch F x)| ^ N * ‖f x‖ := by
  induction N with
  | zero => simp [word]
  | succ N ih =>
    rw [List.replicate_succ, word_cons]
    show ‖(l (arch F x) : ℂ) * word F (List.replicate N (Sum.inr l)) f x‖ = _
    rw [norm_mul, ih, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    ring

theorem om_bound_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨K, l, C0, hl, hpoly⟩ := GlobalTheory.T.one_add_norm_pow_le_sum_linearForm_pow F (Fin n × Fin d) N
  obtain ⟨P, Cs, c, hsob⟩ := GlobalTheory.T.sobolev_bound_periodic_schwartz F (Fin n × Fin d) μ hμ
  obtain ⟨C1, k1, hfin⟩ := GlobalTheory.T.weilRep_finite_periodicity_polynomial_height F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C2, k2, hL2⟩ := GlobalTheory.T.word_action_square_integrable_bound F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ μ hμ (P + N)
  set A : ℝ := max (max Cs 0 * max C1 1 ^ c * max C2 0) 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  refine ⟨max C0 0 * (K + 1) * A, k1 * c + k2, fun g h x => ?_⟩
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH1 : 1 ≤ H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1)
    (by exact_mod_cast one_le_heightGL F h.1)
  obtain ⟨m, hm0, hmC, hper⟩ := hfin g h

  have key : ∀ w : List (Op F (Fin n × Fin d)), w.length ≤ N → (∀ o ∈ w, ∃ l', o = Sum.inr l' ∧ ‖l'‖ ≤ 1) →
      ‖word F w (om (g, h) Φ) x‖ ≤ A * H ^ (k1 * c + k2) := by
    intro w hw hwo
    have hS : word F w (om (g, h) Φ) ∈ schA F (Fin n × Fin d) ∧ Per F m (word F w (om (g, h) Φ)) := by
      clear hw
      induction w with
      | nil => exact ⟨(hP.weil.isUSplitting).pres _ _ hΦ, hper⟩
      | cons o w ih =>
        obtain ⟨l', rfl, -⟩ := hwo o List.mem_cons_self
        obtain ⟨i1, i2⟩ := ih fun o' ho' => hwo o' (List.mem_cons_of_mem _ ho')
        exact ⟨GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F _ (Sum.inr l') _ i1, per_mM i2 l'⟩
    have hH0 : 0 ≤ H := le_trans zero_le_one hH1
    have hb : 0 ≤ max C2 0 * H ^ k2 := mul_nonneg (le_max_right _ _) (pow_nonneg hH0 _)
    have hw' : ∀ v : List (Fin n × Fin d → mixedEmbedding.mixedSpace F), v.length ≤ P → (∀ u ∈ v, ‖u‖ ≤ 1) →
        ∫⁻ y, ‖wordD F v (word F w (om (g, h) Φ)) y‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (max C2 0 * H ^ k2) := by
      intro v hv hv1
      have hlen : (v.map Sum.inl ++ w).length ≤ P + N := by
        rw [List.length_append, List.length_map]; omega
      have hsz : ∀ o ∈ v.map Sum.inl ++ w, size F o ≤ 1 := by
        intro o ho
        rcases List.mem_append.1 ho with ho | ho
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ho
          exact hv1 u hu
        · obtain ⟨l', rfl, hl'⟩ := hwo o ho
          exact hl'
      have h3 := hL2 g h (v.map Sum.inl ++ w) hlen hsz
      rw [word_append] at h3
      exact h3.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _)))
    have h2 := hsob m hm0 _ hS.1 hS.2 (max C2 0 * H ^ k2) hb hw' x
    have hm' : (m : ℝ) ^ c ≤ (max C1 1 * H ^ k1) ^ c :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _))) c
    have e1 : ‖word F w (om (g, h) Φ) x‖ ^ 2 ≤ A * H ^ (k1 * c + k2) := by
      refine h2.trans ?_
      calc Cs * (m : ℝ) ^ c * (max C2 0 * H ^ k2)
          ≤ max Cs 0 * (max C1 1 * H ^ k1) ^ c * (max C2 0 * H ^ k2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) hm' (by positivity) (le_max_right _ _)) hb
        _ = (max Cs 0 * max C1 1 ^ c * max C2 0) * H ^ (k1 * c + k2) := by
            rw [mul_pow, ← pow_mul, pow_add]; ring
        _ ≤ A * H ^ (k1 * c + k2) := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _)
    have hT : 1 ≤ A * H ^ (k1 * c + k2) := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ hH1)
    nlinarith [norm_nonneg (word F w (om (g, h) Φ) x)]
  have hx := hpoly (arch F x)
  have k0 : ‖om (g, h) Φ x‖ ≤ A * H ^ (k1 * c + k2) := by
    simpa [word] using key [] (by simp) (by simp)
  have kj : ∀ j, |l j (arch F x)| ^ N * ‖om (g, h) Φ x‖ ≤ A * H ^ (k1 * c + k2) := fun j => by
    have h4 := key (List.replicate N (Sum.inr (l j))) (by simp)
      (fun o ho => ⟨l j, List.eq_of_mem_replicate ho, hl j⟩)
    rwa [norm_word_rep] at h4
  show ‖om (g, h) Φ x‖ * (1 + ‖arch F x‖) ^ N ≤ _
  calc ‖om (g, h) Φ x‖ * (1 + ‖arch F x‖) ^ N
      ≤ ‖om (g, h) Φ x‖ * (max C0 0 * (1 + ∑ j, |l j (arch F x)| ^ N)) :=
        mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
          (norm_nonneg _)
    _ = max C0 0 * (‖om (g, h) Φ x‖ + ∑ j, |l j (arch F x)| ^ N * ‖om (g, h) Φ x‖) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ max C0 0 * (A * H ^ (k1 * c + k2) + ∑ _j : Fin K, A * H ^ (k1 * c + k2)) :=
        mul_le_mul_of_nonneg_left (add_le_add k0 (Finset.sum_le_sum fun j _ => kj j)) (le_max_right _ _)
    _ = max C0 0 * (K + 1) * A * H ^ (k1 * c + k2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.ArchDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  first | exact @GlobalTheory.ArchDecay.om_bound_arch | exact GlobalTheory.ArchDecay.om_bound_arch | (intros; apply GlobalTheory.ArchDecay.om_bound_arch <;> assumption)
end
