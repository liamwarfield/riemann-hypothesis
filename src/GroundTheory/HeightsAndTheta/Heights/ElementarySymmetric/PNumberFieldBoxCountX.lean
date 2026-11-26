module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeVanishingHomog

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeImageZLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.mixedEmbedding

noncomputable def latticeImage (F : Type*) [Field F] (L : AddSubgroup F) : Submodule ℤ (mixedSpace F) :=
  (L.map (mixedEmbedding F).toAddMonoidHom).toIntSubmodule

theorem mem_latticeImage {F : Type*} [Field F] (L : AddSubgroup F) (y : mixedSpace F) :
    y ∈ latticeImage F L ↔ ∃ x ∈ L, mixedEmbedding F x = y := by
  change y ∈ L.map (mixedEmbedding F).toAddMonoidHom ↔ _
  simp


open scoped Classical in
def LatticeImageZLattice.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (L : AddSubgroup F), L.FG →
    (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) →
      ∃ _ : DiscreteTopology (latticeImage F L), IsZLattice ℝ (E := mixedSpace F) (latticeImage F L)

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsEmbeddingSumPlaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace

def EmbeddingSumPlaces.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : (F →+* ℂ) → ℝ),
    (∀ σ, g (ComplexEmbedding.conjugate σ) = g σ) →
      ∑ σ : F →+* ℂ, g σ = ∑ w : InfinitePlace F, (mult w : ℝ) * g w.embedding

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCovolumeRelIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory

def CovolumeRelIndex.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁]
    [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂], L₁ ≤ L₂ →
      ZLattice.covolume L₁ μ = (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) * ZLattice.covolume L₂ μ

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeImageZLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.mixedEmbedding

theorem LatticeImageZLattice.exists_int_mul_integral {F : Type} [Field F] [NumberField F]
    (L : AddSubgroup F) (hfg : L.FG) : ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ L, IsIntegral ℤ (N • x) := by
  obtain ⟨S, hS⟩ := hfg
  have halg : ∀ s : F, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ (y • s) := fun s =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic s)).exists_integral_multiple
  choose y hy0 hyint using halg
  refine ⟨∏ s ∈ S, y s, Finset.prod_ne_zero_iff.mpr fun s _ => hy0 s, ?_⟩
  have h : ∀ z : L, z ∈ AddSubsemigroup.closure (↑S : Set L) →
      IsIntegral ℤ ((∏ s ∈ S, y s) • (z : F)) := by
    intro z hz
    induction hz using AddSubsemigroup.closure_induction with
    | mem s hs =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun t : L => y t) (show s ∈ S from hs)
      rw [hc, mul_comm, mul_smul]
      exact (hyint s).zsmul c
    | add a b _ _ ha hb => simpa [smul_add] using ha.add hb
  intro x hx
  exact h ⟨x, hx⟩ (hS ▸ AddSubsemigroup.mem_top _)



open scoped Classical in
theorem LatticeImageZLattice.proof : LatticeImageZLattice.Statement := by
  intro F _ _ L hfg hfull
  obtain ⟨N, hN0, hLint⟩ := LatticeImageZLattice.exists_int_mul_integral L hfg

  let e : mixedSpace F →ₗ[ℝ] mixedSpace F := (N : ℝ) • LinearMap.id
  have he₁ : Continuous e := continuous_const_smul (N : ℝ)
  have he₂ : Function.Injective e := fun a b h =>
    smul_right_injective (mixedSpace F) (Int.cast_ne_zero.mpr hN0 : (N : ℝ) ≠ 0) h
  have hdisc : DiscreteTopology (ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e) :=
    ZLattice.comap_discreteTopology ℝ _ he₁ he₂
  have hle : (latticeImage F L : Set (mixedSpace F)) ⊆
      ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_latticeImage L z).mp hz
    show e (mixedEmbedding F x) ∈ mixedEmbedding.integerLattice F
    refine ⟨⟨N • x, hLint x hx⟩, ?_⟩
    change mixedEmbedding F (N • x) = (N : ℝ) • mixedEmbedding F x
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have : DiscreteTopology (latticeImage F L) := DiscreteTopology.of_subset hdisc hle
  refine ⟨this, ⟨?_⟩⟩

  rw [eq_top_iff, ← (latticeBasis F).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨n, hn, hnL⟩ := hfull (integralBasis F i)
  have hmem : mixedEmbedding F ((n : F) * integralBasis F i) ∈ latticeImage F L :=
    (mem_latticeImage L _).mpr ⟨_, hnL, rfl⟩
  have hb : latticeBasis F i = (n : ℝ)⁻¹ • mixedEmbedding F ((n : F) * integralBasis F i) := by
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul, latticeBasis_apply]
  rw [hb]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNumberFieldBoxCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory

namespace NumberFieldBoxCount

theorem inf_full {F : Type*} [Field F] {L B : AddSubgroup F}
    (hL : ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) (hB : ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ B) :
    ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L ⊓ B := by
  intro x
  obtain ⟨n, hn, hnx⟩ := hL x
  obtain ⟨m, hm, hmx⟩ := hB x
  refine ⟨m * n, Nat.mul_pos hm hn, ?_, ?_⟩
  · have h := L.nsmul_mem hnx m
    rw [nsmul_eq_mul, ← mul_assoc] at h
    simpa using h
  · have h := B.nsmul_mem hmx n
    rw [nsmul_eq_mul, ← mul_assoc] at h
    simpa [mul_comm] using h

theorem fg_of_le {G : Type*} [AddCommGroup G] {H K : AddSubgroup G} (hK : K.FG) (hHK : H ≤ K) : H.FG := by
  have hK' : (AddSubgroup.toIntSubmodule K).FG := by
    rwa [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup]
  have hH' := hK'.of_le (S := AddSubgroup.toIntSubmodule H) hHK
  rwa [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup] at hH'

theorem forall_le_iff {F : Type*} [Field F] [NumberField F] (ρ : (F →+* ℂ) → ℝ)
    (hρc : ∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) (x : F) :
    (∀ σ : F →+* ℂ, ‖σ x‖ ≤ ρ σ) ↔ ∀ w : InfinitePlace F, normAtPlace w (mixedEmbedding F x) ≤ ρ w.embedding := by
  refine ⟨fun h w => ?_, fun h σ => ?_⟩
  · rw [normAtPlace_apply, ← norm_embedding_eq]
    exact h _
  · have h' := h (InfinitePlace.mk σ)
    rw [normAtPlace_apply, InfinitePlace.apply] at h'
    rcases embedding_mk_eq σ with e | e
    · rwa [e] at h'
    · rwa [e, hρc] at h'

theorem card_eq {F : Type*} [Field F] [NumberField F] (ρ : (F →+* ℂ) → ℝ)
    (hρc : ∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) (L : AddSubgroup F) :
    Nat.card {x : L // ∀ σ : F →+* ℂ, ‖σ (x : F)‖ ≤ ρ σ} =
      {y : mixedSpace F | y ∈ latticeImage F L ∧ ∀ w, normAtPlace w y ≤ ρ w.embedding}.ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_eq_of_bijective (fun x => ⟨mixedEmbedding F x.1,
    (mem_latticeImage _ _).2 ⟨x.1, x.1.2, rfl⟩, (forall_le_iff ρ hρc _).1 x.2⟩) ⟨?_, ?_⟩
  · intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (mixedEmbedding_injective F h'))
  · rintro ⟨y, hy, hyb⟩
    obtain ⟨x, hx, rfl⟩ := (mem_latticeImage _ _).1 hy
    exact ⟨⟨⟨x, hx⟩, (forall_le_iff ρ hρc x).2 hyb⟩, rfl⟩

theorem relIndex_latticeImage {F : Type*} [Field F] [NumberField F] (H K : AddSubgroup F) :
    (latticeImage F H).toAddSubgroup.relIndex (latticeImage F K).toAddSubgroup = H.relIndex K := by
  simp only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (mixedEmbedding_injective F)


open scoped Classical in
theorem proof (h1 : LatticeImageZLattice.Statement) (h2 : CovolumeRelIndex.Statement)
    (h4 : EmbeddingSumPlaces.Statement) (h5 : MixedBoxCount.Statement) : NumberFieldBoxCount.Statement := by
  intro F _ _ B hB hBf
  obtain ⟨_, _⟩ := h1 F B hB hBf
  refine ⟨Module.finrank ℚ F * Real.log 2 + Real.log (ZLattice.covolume (latticeImage F B)) -
    Real.log (convexBodyLTFactor F : ℝ), ?_⟩
  intro L hL hLf ρ hρ hρc
  obtain ⟨_, _⟩ := h1 F L hL hLf
  obtain ⟨_, _⟩ := h1 F (L ⊓ B) (fg_of_le hL inf_le_left) (inf_full hLf hBf)
  have mono : ∀ {H K : AddSubgroup F}, H ≤ K → latticeImage F H ≤ latticeImage F K := by
    intro H K hHK
    refine (Submodule.toAddSubgroup_le _ _).1 ?_
    simp only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.map_mono hHK
  have cL := h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F L) (mono inf_le_left)
  have cB := h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F B) (mono inf_le_right)
  rw [relIndex_latticeImage, AddSubgroup.inf_relIndex_left] at cL
  rw [relIndex_latticeImage, AddSubgroup.inf_relIndex_right] at cB
  have p0 := ZLattice.covolume_pos (latticeImage F (L ⊓ B)) volume
  have pL := ZLattice.covolume_pos (latticeImage F L) volume
  have pB := ZLattice.covolume_pos (latticeImage F B) volume
  have r1 : (0 : ℝ) < B.relIndex L := by
    by_contra hc; have hc' := not_lt.1 hc; nlinarith
  have r2 : (0 : ℝ) < L.relIndex B := by
    by_contra hc; have hc' := not_lt.1 hc; nlinarith
  have hgen : genIndex L B = ZLattice.covolume (latticeImage F B) / ZLattice.covolume (latticeImage F L) := by
    rw [genIndex, div_eq_div_iff r2.ne' pL.ne']
    linarith
  obtain ⟨-, hcount⟩ := h5 F (latticeImage F L) (fun w => ρ w.embedding) (fun w => hρ _)
  have hsum := h4 F (fun σ => Real.log (ρ σ)) (fun σ => by simp only [hρc])
  rw [card_eq ρ hρc L, hsum, hgen, Real.log_div pB.ne' pL.ne']
  linarith

end NumberFieldBoxCount

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PEmbeddingSumPlaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace


open scoped Classical in
theorem EmbeddingSumPlaces.proof : EmbeddingSumPlaces.Statement := by
  intro F _ _ g hg
  rw [← Finset.univ.sum_fiberwise (fun σ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have h : ∀ σ ∈ ({σ | InfinitePlace.mk σ = w} : Finset (F →+* ℂ)), g σ = g w.embedding := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    subst hσ
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, hg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast card_filter_mk_eq w

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCovolumeRelIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory Module ZLattice


open scoped Classical in
theorem CovolumeRelIndex.proof : CovolumeRelIndex.Statement := by
  intro E _ _ _ _ _ μ _ L₁ L₂ _ _ _ _ h
  let f : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := (Module.finBasis ℝ E).equivFunL.symm
  let ν : Measure (Fin (finrank ℝ E) → ℝ) := μ.map f.symm
  have : ν.IsAddHaarMeasure := f.symm.isAddHaarMeasure_map μ
  have hf : MeasurePreserving f ν μ := by
    refine ⟨f.continuous.measurable, ?_⟩
    simp only [ν]
    rw [Measure.map_map f.continuous.measurable f.symm.continuous.measurable]
    have : (⇑f ∘ ⇑f.symm) = id := by ext x; simp
    rw [this, Measure.map_id]
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have scale : ∀ (L : Submodule ℤ (Fin (finrank ℝ E) → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
      covolume L ν = (c : ℝ) * covolume L volume := by
    intro L _ _
    rw [covolume_eq_measure_fundamentalDomain L ν
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) ν),
      covolume_eq_measure_fundamentalDomain L volume
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) volume)]
    conv_lhs => rw [hν]
    exact measureReal_nnreal_smul_apply c
  have hidx : ((ZLattice.comap ℝ L₁ f.toLinearMap).toAddSubgroup.relIndex
      (ZLattice.comap ℝ L₂ f.toLinearMap).toAddSubgroup : ℝ) =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
      LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]
  have key := covolume_div_covolume_eq_relIndex (ZLattice.comap ℝ L₁ f.toLinearMap)
    (ZLattice.comap ℝ L₂ f.toLinearMap) (fun _ h' ↦ h h')
  have hne := covolume_ne_zero (ZLattice.comap ℝ L₂ f.toLinearMap) volume
  rw [← covolume_comap L₁ μ ν hf, ← covolume_comap L₂ μ ν hf, scale, scale, ← hidx, ← key]
  field_simp

end GroundTheory.Heights₂.Heights.Targets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem NumberFieldBoxCount.proof_closed : NumberFieldBoxCount.Statement :=
  NumberFieldBoxCount.proof LatticeImageZLattice.proof CovolumeRelIndex.proof EmbeddingSumPlaces.proof
    (MixedBoxCount.proof LatticeCountVolume.proof)

end GroundTheory.Heights₂.Heights.Targets
