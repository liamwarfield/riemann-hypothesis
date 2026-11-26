module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLe
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.ReImLattice

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem covolume_prod (μ : Measure E) [μ.IsAddHaarMeasure] (L L' : Submodule ℤ E)
    [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L] [IsZLattice ℝ L'] :
    ZLattice.covolume (L.prod L') (μ.prod μ) = ZLattice.covolume L μ * ZLattice.covolume L' μ := by
  have hD : IsAddFundamentalDomain (L.prod L') (latticeDomain L ×ˢ latticeDomain L')
      (μ.prod μ) := by
    refine IsAddFundamentalDomain.mk' ((measurableSet_latticeDomain L).prod
      (measurableSet_latticeDomain L')).nullMeasurableSet fun x => ?_
    obtain ⟨a, ha, hu⟩ := existsUnique_add_mem_latticeDomain L x.1
    obtain ⟨a', ha', hu'⟩ := existsUnique_add_mem_latticeDomain L' x.2
    refine ⟨⟨(a, a'), a.2, a'.2⟩, ⟨?_, ?_⟩, ?_⟩
    · simpa [Submodule.vadd_def, add_comm] using ha
    · simpa [Submodule.vadd_def, add_comm] using ha'
    · rintro ⟨b, hb⟩ hb'
      have h1 := hu ⟨b.1, hb.1⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.1)
      have h2 := hu' ⟨b.2, hb.2⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.2)
      apply Subtype.ext
      simp [← h1, ← h2]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hD, measureReal_prod_prod,
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L μ),
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L' μ)]

theorem reflection_stable (μ : Measure E) [μ.IsAddHaarMeasure] (M : Submodule ℤ (E × E))
    [DiscreteTopology M] [IsZLattice ℝ M] (hM : ∀ p ∈ M, (p.1, -p.2) ∈ M) (A B : Submodule ℤ E)
    (hA : ∀ y, y ∈ A ↔ (y, (0 : E)) ∈ M) (hB : ∀ y, y ∈ B ↔ ((0 : E), y) ∈ M) :
    (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧
      ZLattice.covolume A μ * ZLattice.covolume B μ ≤
        2 ^ Module.finrank ℝ E * ZLattice.covolume M (μ.prod μ) := by
  have h2A : ∀ p ∈ M, p.1 + p.1 ∈ A := fun p hp => by
    rw [hA]
    have := M.add_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  have h2B : ∀ p ∈ M, p.2 + p.2 ∈ B := fun p hp => by
    rw [hB]
    have := M.sub_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  haveI dA : DiscreteTopology A :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : A => (⟨(x.1, 0), (hA _).1 x.2⟩ : M))
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.1) h))
  haveI dB : DiscreteTopology B :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : B => (⟨(0, x.1), (hB _).1 x.2⟩ : M))
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.2) h))
  have key : ∀ (C : Submodule ℤ E) (f : E × E →ₗ[ℝ] E), Function.Surjective f →
      (∀ p ∈ M, f p + f p ∈ C) → Submodule.span ℝ (C : Set E) = ⊤ := by
    intro C f hf hC
    rw [eq_top_iff, ← LinearMap.range_eq_top.2 hf, LinearMap.range_eq_map,
      ← IsZLattice.span_top (K := ℝ) (L := M), Submodule.map_span, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have h := (Submodule.span ℝ (C : Set E)).smul_mem (2⁻¹ : ℝ) (Submodule.subset_span (hC p hp))
    rwa [← two_smul ℝ, inv_smul_smul₀ two_ne_zero] at h
  haveI lA : IsZLattice ℝ A := ⟨key A (LinearMap.fst ℝ E E) LinearMap.fst_surjective h2A⟩
  haveI lB : IsZLattice ℝ B := ⟨key B (LinearMap.snd ℝ E E) LinearMap.snd_surjective h2B⟩
  refine ⟨⟨dA, lA⟩, ⟨dB, lB⟩, ?_⟩
  have hle : A.prod B ≤ M := fun p hp => by
    have := M.add_mem ((hA _).1 hp.1) ((hB _).1 hp.2)
    simpa using this
  rw [← covolume_prod μ A B, covolume_eq_relIndex_mul_of_haar (μ.prod μ) _ M hle]
  refine mul_le_mul_of_nonneg_right ?_ (ZLattice.covolume_pos M (μ.prod μ)).le
  let f : M.toAddSubgroup →+ A :=
    { toFun := fun p => ⟨p.1.1 + p.1.1, h2A _ p.2⟩
      map_zero' := by ext; simp
      map_add' := fun p q => by ext; simp; abel }
  have hK : (nsmulAddMonoidHom (α := A) 2).range.index = 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.index_range_nsmul, ZLattice.rank ℝ A]
  have hc : (A.prod B).toAddSubgroup.addSubgroupOf M.toAddSubgroup =
      (nsmulAddMonoidHom (α := A) 2).range.comap f := by
    ext p
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_prod,
      AddSubgroup.mem_comap, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨⟨_, h1⟩, Subtype.ext (by simp [f, two_nsmul])⟩
    · rintro ⟨y, hy⟩
      have h1 : y.1 + y.1 = p.1.1 + p.1.1 := by
        have := congrArg Subtype.val hy
        simpa [f, two_nsmul] using this
      have h2 : y.1 = p.1.1 := by
        rw [← two_smul ℝ, ← two_smul ℝ] at h1
        exact smul_right_injective E two_ne_zero h1
      have h3 : p.1.1 ∈ A := h2 ▸ y.2
      refine ⟨h3, (hB _).2 ?_⟩
      have := M.sub_mem p.2 ((hA _).1 h3)
      convert this using 1
      ext <;> simp
  have hidx : (A.prod B).toAddSubgroup.relIndex M.toAddSubgroup ≤ 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.relIndex, hc, AddSubgroup.index_comap, ← hK, ← AddSubgroup.relIndex_top_right]
    refine AddSubgroup.relIndex_le_of_le_right le_top ?_
    rw [AddSubgroup.relIndex_top_right, hK]
    positivity
  exact_mod_cast hidx

end General

noncomputable def reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    ((ι → κ → ℝ) × (ι → κ → ℝ)) ≃L[ℝ] (ι → κ → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p v i => ⟨p.1 v i, p.2 v i⟩
      invFun := fun z => (fun v i => (z v i).re, fun v i => (z v i).im)
      map_add' := fun p q => by ext v i; apply Complex.ext <;> simp
      map_smul' := fun c p => by ext v i; apply Complex.ext <;> simp
      left_inv := fun p => rfl
      right_inv := fun z => rfl }

theorem reImEquiv_apply {ι κ : Type} [Fintype ι] [Fintype κ] (p : (ι → κ → ℝ) × (ι → κ → ℝ))
    (v : ι) (i : κ) : reImEquiv ι κ p v i = ⟨p.1 v i, p.2 v i⟩ := rfl

theorem measurePreserving_reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (reImEquiv ι κ) (Measure.prod volume volume) volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow (κ → ℝ) (κ → ℝ) ι).symm
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ κ).symm
  have h3 := Complex.volume_preserving_equiv_real_prod.symm
  have h4 := volume_preserving_pi (ι := κ) (fun _ => h3)
  have h5 := volume_preserving_pi (ι := ι) (fun _ => h4.comp h2)
  exact h5.comp h1

theorem real_imag_covolume_le : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (L : Submodule ℤ (ι → κ → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L], (∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) → ∀ A B : Submodule ℤ (ι → κ → ℝ), (∀ y, y ∈ A ↔ (fun v i => (y v i : ℂ)) ∈ L) → (∀ y, y ∈ B ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L) → (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧ ZLattice.covolume A volume * ZLattice.covolume B volume ≤ 2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume := by
  intro ι κ _ _ L _ _ hL A B hA hB
  have hmem : ∀ p, p ∈ ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap ↔ reImEquiv ι κ p ∈ L :=
    fun p => Iff.rfl
  have h := reflection_stable volume (ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap)
    (fun p hp => by
      rw [hmem] at hp ⊢
      convert hL _ hp using 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply]) A B
    (fun y => by
      rw [hA, hmem]
      congr! 1)
    (fun y => by
      rw [hB, hmem]
      congr! 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply])
  haveI : (volume : Measure (κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : ((volume : Measure (ι → κ → ℝ)).prod (volume : Measure (ι → κ → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [ZLattice.covolume_comap L volume _ (measurePreserving_reImEquiv ι κ)] at h
  have hr : Module.finrank ℝ (ι → κ → ℝ) = Fintype.card ι * Fintype.card κ := by
    rw [Module.finrank_pi_fintype]; simp
  rwa [hr] at h

end GlobalTheory.ReImLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjStable_lattice_real_imag_covolume_le : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (L : Submodule ℤ (ι → κ → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L], (∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) → ∀ A B : Submodule ℤ (ι → κ → ℝ), (∀ y, y ∈ A ↔ (fun v i => (y v i : ℂ)) ∈ L) → (∀ y, y ∈ B ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L) → (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧ ZLattice.covolume A volume * ZLattice.covolume B volume ≤ 2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume := by
  first | exact @GlobalTheory.ReImLattice.real_imag_covolume_le | exact GlobalTheory.ReImLattice.real_imag_covolume_le | (intros; apply GlobalTheory.ReImLattice.real_imag_covolume_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageEqOfMemLowKSub
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOnGExistsContDiffCompactSupportExtension
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

namespace GlobalTheory

theorem smoothOnG_exists_contDiff_compactSupport_extension :
    ∀ (n : ℕ) (ε : Fin n → Bool) (β : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε β →
      HasCompactSupport (fun g : UJ ε => β (umat g)) →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        ∀ g : UJ ε, β (umat g) = F (fun i j => umat g i j) := by
  intro n ε β hβ hc
  obtain ⟨F₀, hF₀, hF₀eq⟩ := smoothOnG_exists_contDiff_extension n ε β hβ

  have hp : Continuous (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
    have hu : Continuous (fun g : UJ ε => umat g) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_pi fun i => continuous_pi fun j => hu.matrix_elem i j

  have hK : IsCompact ((fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) ''
      tsupport (fun g : UJ ε => β (umat g))) := hc.isCompact.image hp
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0

  let χ : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨fun x => (χ x : ℂ) * F₀ x, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hF₀
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro g
    have h₀ : F₀ (fun i j => umat g i j) = β (umat g) := hF₀eq (umat g) g.2
    by_cases hz : β (umat g) = 0
    · show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [h₀, hz, mul_zero]
    · have hmem : (fun i j => umat g i j : Fin n → Fin n → ℂ) ∈ Metric.closedBall 0 χ.rIn := by
        refine Metric.closedBall_subset_closedBall ?_ (hR ⟨g, subset_tsupport _ hz, rfl⟩)
        show R ≤ max R 0 + 1
        linarith [le_max_left R 0]
      show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [χ.one_of_mem_closedBall hmem, h₀, Complex.ofReal_one, one_mul]

end GlobalTheory
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory

noncomputable def leftMulEntries {n : ℕ} (a : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (Fin n → Fin n → ℂ) ≃L[ℂ] (Fin n → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x i j => ((a : Matrix (Fin n) (Fin n) ℂ) * Matrix.of x) i j
      invFun := fun x i j => (((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.of x) i j
      map_add' := fun x y => by
        have h := Matrix.mul_add (a : Matrix (Fin n) (Fin n) ℂ) (Matrix.of x) (Matrix.of y)
        exact h
      map_smul' := fun c x => by
        have h := Matrix.mul_smul (a : Matrix (Fin n) (Fin n) ℂ) c (Matrix.of x)
        exact h
      left_inv := fun x => by
        have h := Units.inv_mul_cancel_left a (Matrix.of x)
        exact h
      right_inv := fun x => by
        have h := Units.mul_inv_cancel_left a (Matrix.of x)
        exact h }

private lemma inUJ_of_mem_Kset' {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) : Formalism.REAL.inUJ ε g := by
  have hu : star g * g = 1 := Unitary.star_mul_self_of_mem hg.1
  unfold Formalism.REAL.inUJ
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hu, Matrix.one_mul]

private lemma mul_mem_Kset {n : ℕ} {ε : Fin n → Bool} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) (hg' : g' ∈ Formalism.REAL.Kset ε) : g * g' ∈ Formalism.REAL.Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hg'.1, ?_⟩
  rw [Matrix.mul_assoc, hg'.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

private lemma exists_UJ_umat_eq_of_mem_Kset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) : ∃ k : Formalism.REAL.UJ ε, umat k = g :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩,
    inUJ_of_mem_Kset' hg⟩, rfl⟩

theorem exists_smooth_average_eq_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (w : H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → w ∈ lowKSub ε lam σ → w ≠ 0 → ∀ u ∈ lowKSub ε lam σ, ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g : UJ ε, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) := by
  intro n ε H _ _ _ σ lam w hrep hK hw hw0 u hu
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have humat : Continuous fun g : Formalism.REAL.UJ ε => umat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w :=
    (hrep.2.2 w).comp_continuous humat hmem
  have he : Continuous fun g : Formalism.REAL.UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ) := humat

  have hint : ∀ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      HasCompactSupport (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j)) →
      Integrable (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j) • σ (umat g) w) (muG ε) := by
    intro F hFd _ hFg
    have hc : Continuous fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j) := hFd.continuous.comp he
    exact (hc.smul hcont).integrable_of_hasCompactSupport
      (hFg.smul_right (f' := fun g : Formalism.REAL.UJ ε => σ (umat g) w))

  obtain ⟨α, hαs, hαc, hαfix⟩ := exists_smooth_fix_lowKSub n ε lam H σ hrep hK
  obtain ⟨F0, hF0d, hF0c, hF0e⟩ :=
    smoothOnG_exists_contDiff_compactSupport_extension n ε α hαs hαc
  have hF0g : HasCompactSupport (fun g : Formalism.REAL.UJ ε => F0 (fun i j => umat g i j)) := by
    have hfun : (fun g : Formalism.REAL.UJ ε => F0 (fun i j => umat g i j)) = fun g => α (umat g) :=
      funext fun g => (hF0e g).symm
    rw [hfun]
    exact hαc
  have hbase : ∫ g, F0 (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) = w := by
    refine ext_inner_left ℂ fun v => ?_
    rw [← integral_inner (hint F0 hF0d hF0c hF0g) v]
    simp_rw [inner_smul_right, ← hF0e]
    exact hαfix w hw v

  let T : Submodule ℂ H :=
    { carrier := {v | ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
          HasCompactSupport (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j)) ∧
          v = ∫ g, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε)}
      add_mem' := by
        rintro _ _ ⟨F1, h1d, h1c, h1g, rfl⟩ ⟨F2, h2d, h2c, h2g, rfl⟩
        refine ⟨fun y => F1 y + F2 y, h1d.add h2d, h1c.add h2c, h1g.add h2g, ?_⟩
        rw [← integral_add (hint F1 h1d h1c h1g) (hint F2 h2d h2c h2g)]
        simp only [add_smul]
      zero_mem' := by
        refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, HasCompactSupport.zero, ?_⟩
        simp
      smul_mem' := by
        rintro c _ ⟨F1, h1d, h1c, h1g, rfl⟩
        refine ⟨fun y => c * F1 y, contDiff_const.mul h1d, h1c.mul_left, h1g.mul_left, ?_⟩
        rw [← integral_smul]
        simp only [mul_smul] }

  have hgen : ∀ g ∈ Formalism.REAL.Kset ε, σ g w ∈ T := by
    intro g hg
    obtain ⟨k, rfl⟩ := exists_UJ_umat_eq_of_mem_Kset hg
    let a : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    have hshift : ∀ x : Formalism.REAL.UJ ε,
        leftMulEntries a (fun i j => umat x i j) = fun i j => umat (k⁻¹ * x) i j := fun x => rfl
    refine ⟨fun y => F0 (leftMulEntries a y), ?_, ?_, ?_, ?_⟩
    · exact hF0d.comp ((leftMulEntries a).contDiff.restrict_scalars ℝ)
    · exact hF0c.comp_homeomorph (leftMulEntries a).toHomeomorph
    · simp only [hshift]
      exact hF0g.comp_homeomorph (Homeomorph.mulLeft k⁻¹)
    · simp only [hshift]
      have hinv := integral_mul_left_eq_self (μ := muG ε)
        (fun x : Formalism.REAL.UJ ε => F0 (fun i j => umat (k⁻¹ * x) i j) • σ (umat x) w) k
      simp only [inv_mul_cancel_left] at hinv
      rw [← hinv]
      have hmul : ∀ x : Formalism.REAL.UJ ε, F0 (fun i j => umat x i j) • σ (umat (k * x)) w
          = σ (umat k) (F0 (fun i j => umat x i j) • σ (umat x) w) := by
        intro x
        rw [map_smul]
        congr 1
        show σ (umat k * umat x) w = σ (umat k) (σ (umat x) w)
        rw [hrep.1.2 _ (hmem k) _ (hmem x)]
        rfl
      simp_rw [hmul]
      rw [ContinuousLinearMap.integral_comp_comm _ (hint F0 hF0d hF0c hF0g), hbase]

  let S' : Submodule ℂ H := Submodule.span ℂ {v | ∃ g ∈ Formalism.REAL.Kset ε, v = σ g w}
  have hS'le : S' ≤ lowKSub ε lam σ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hK.2.1 g hg w hw
  have hS'st : IsKStableOn ε σ S' := by
    intro g hg v hv
    have hle : S' ≤ S'.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', hg', rfl⟩
      show σ g (σ g' w) ∈ S'
      refine Submodule.subset_span ⟨g * g', mul_mem_Kset hg hg', ?_⟩
      rw [hrep.1.2 g (inUJ_of_mem_Kset' hg) g' (inUJ_of_mem_Kset' hg')]
      rfl
    exact hle hv
  have h1K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
    ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  have hwS' : w ∈ S' := Submodule.subset_span ⟨1, h1K, by rw [hrep.1.1]; rfl⟩
  have hS'eq : S' = lowKSub ε lam σ := by
    rcases hK.2.2.1 S' hS'le hS'st with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hwS')) hw0
    · exact h
  have huS' : u ∈ S' := by rw [hS'eq]; exact hu
  have huT : u ∈ T := Submodule.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact hgen g hg) huS'
  obtain ⟨F, hFd, hFc, _, hFu⟩ := huT
  exact ⟨F, hFd, hFc, hFu⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSizeEqLeast
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.NearLower

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
  (X : InfinitePlace K → Matrix ι ι ℂ)


omit [_root_.NumberField.IsTotallyComplex K] in
theorem le_of_le_span (hX : ∀ v, IsUnit (X v).det) {L S N : Submodule (𝓞 K) V} (hL : L.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (hN : N ≤ L)
    (h : (N : Set V) ⊆ Submodule.span K (S : Set V)) : N ≤ S := by
  have hle : S ⊔ N ≤ L := sup_le hS.1 hN
  have hsp : Submodule.span K ((S ⊔ N : Submodule (𝓞 K) V) : Set V) = Submodule.span K (S : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 hy
      exact Submodule.add_mem _ (Submodule.subset_span hs) (h hn)
    · exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)
  have h1 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hle)).2.1
  have h2 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hS.1)).2.1
  have h3 : rkK (S ⊔ N) = rkK S := by unfold rkK; rw [hsp]
  have h4 := (satBasic _ _ _ (Formalism.HermitianLatticesTheory.realize b X) L (plLat K V ι b X hX L hL).1).2.2.1 S (S ⊔ N) hS
    le_sup_left hle (by rw [h1, h2, h3])
  exact sup_eq_left.1 h4

theorem exists_size_eq_least (hX : ∀ v, IsUnit (X v).det) {B : Submodule (𝓞 K) V} (hB : B.FG) (h0 : B ≠ ⊥) :
    ∃ N : Submodule (𝓞 K) V, N ≤ B ∧ N ≠ ⊥ ∧ size b X N = leastSize b X B := by
  obtain ⟨-, -, ⟨N, hsat, hN, hsl⟩, -⟩ :=
    muChar _ _ _ (Formalism.HermitianLatticesTheory.realize b X) B (plLat K V ι b X hX B hB).1 h0
  refine ⟨N, hsat.1, hN, ?_⟩
  rw [(sizeMu K V ι b X hX B hB h0).2.2.2.1,
    (sizeMu K V ι b X hX N (Submodule.FG.of_le hB hsat.1) hN).1, hsl]

theorem map_le_of_sizes (hX : ∀ v, IsUnit (X v).det) {L S A : Submodule (𝓞 K) V} (hL : L.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (hA : A ≤ L) (ψ : V →ₗ[K] V)
    (hψ : A.map (ψ.restrictScalars (𝓞 K)) ≤ L) {δ t : ℝ} (hδ : 0 < δ)
    (hn : ∀ v y, Formalism.HermitianLatticesTheory.normAt b X v (ψ y) ≤ δ * Formalism.HermitianLatticesTheory.normAt b X v y)
    (hAt : A ≠ ⊥ → largestSize b X A ≤ t)
    (hSt : ∀ N, S < N → N ≤ L → δ * t < sizeQ b X N S) :
    A.map (ψ.restrictScalars (𝓞 K)) ≤ S := by
  have hQ := quotRealize K V ι b X hX L S hL hS
  set U := Submodule.span K (S : Set V) with hU
  obtain ⟨κ, _, _, b', X', hX', hnorm, hq⟩ := hQ
  by_cases h0 : A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) = ⊥
  · refine le_of_le_span b X hX hL hS hψ ?_
    rintro _ ⟨y, hy, rfl⟩
    have : (U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K) y ∈ A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) :=
      Submodule.mem_map_of_mem hy
    rw [h0, Submodule.mem_bot] at this
    exact (Submodule.Quotient.mk_eq_zero U).1 this
  exfalso
  have hA0 : A ≠ ⊥ := fun h => h0 (by rw [h, Submodule.map_bot])
  have hAfg : A.FG := Submodule.FG.of_le hL hA
  set B := L.map (U.mkQ.restrictScalars (𝓞 K)) with hB
  have hBfg : B.FG := hL.map _
  have hAB : A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨ψ y, hψ ⟨y, hy, rfl⟩, rfl⟩
  have hB0 : B ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hAB))
  have hM := sizeIneq K V ι _ κ b X b' X' hX hX' (U.mkQ ∘ₗ ψ) A B hAfg hBfg hAB h0

  have hop : ∀ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ) ≤ δ := by
    intro v
    refine Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X b' X' hX _ v δ hδ.le fun y => ?_
    refine le_trans ?_ (hn v y)
    rw [LinearMap.comp_apply, hnorm]
    refine (Submodule.norm_starProjection_apply_le _ _).trans (le_of_eq ?_)
    rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HN.PlaceOperatorNorms.cnorm_eq]
    rfl
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hP : (∏ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ)) ^ ((1 : ℝ) / (nPl K : ℝ)) ≤ δ := by
    have h1 : ∏ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ) ≤ δ ^ nPl K := by
      calc _ ≤ ∏ _v : InfinitePlace K, δ := Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hop v
        _ = δ ^ nPl K := by rw [Finset.prod_const, Finset.card_univ]; rfl
    calc _ ≤ (δ ^ nPl K) ^ ((1 : ℝ) / (nPl K : ℝ)) :=
          Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _) h1 (by positivity)
      _ = δ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, mul_one_div_cancel hf.ne', Real.rpow_one]

  obtain ⟨N, hNB, hN0, hNs⟩ := exists_size_eq_least b' X' hX' hBfg hB0
  set N' := L ⊓ N.comap (U.mkQ.restrictScalars (𝓞 K)) with hN'
  have hS0 : ∀ s ∈ S, U.mkQ s = 0 := fun s hs => (Submodule.Quotient.mk_eq_zero U).2 (Submodule.subset_span hs)
  have hSN : S ≤ N' := by
    intro s hs
    refine ⟨hS.1 hs, ?_⟩
    show U.mkQ s ∈ N
    rw [hS0 s hs]; exact N.zero_mem
  have hmap : N'.map (U.mkQ.restrictScalars (𝓞 K)) = N := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hy.2
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := hNB hz
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
  have hne : S ≠ N' := by
    intro h
    apply hN0
    rw [← hmap, ← h, eq_bot_iff]
    rintro _ ⟨s, hs, rfl⟩
    exact hS0 s hs
  have hlt := hSt N' (lt_of_le_of_ne hSN hne) inf_le_left
  rw [(hq N' hSN inf_le_left).2, hmap, hNs] at hlt
  have hpos : 0 < largestSize b X A := by
    rw [(sizeMu K V ι b X hX A hAfg hA0).2.2.2.2.1]; exact Real.exp_pos _
  have h2 := (div_le_iff₀ hpos).1 (hM.trans hP)
  have h3 := mul_le_mul_of_nonneg_left (hAt hA0) hδ.le
  linarith

end General

theorem cnorm_mulVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (M *ᵥ u) ≤ Real.sqrt (Formalism.REAL.hs M) * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm Formalism.REAL.hs
  rw [← Real.sqrt_mul (by positivity), Finset.sum_mul]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => ‖M i j‖) (fun j => ‖u j‖))
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  simp only [Matrix.mulVec, dotProduct]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)

theorem hs_conj_sub_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (M.map (starRingEnd ℂ) - 1) = Formalism.REAL.hs (M - 1) := by
  unfold Formalism.REAL.hs
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.norm_conj ((M - 1) i j)]
  simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp

theorem normAt_sub_one_le (I : AutInst) (x : I.GA) (g : Matrix (Fin I.n) (Fin I.n) I.E) (w : InfinitePlace I.E)
    {δ : ℝ} (h : Real.sqrt (Formalism.REAL.hs ((frm I x w)⁻¹ * g.map w.embedding * frm I x w - 1)) ≤ δ)
    (y : Fin I.n → I.E) :
    Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w (Matrix.toLin' (g - 1) y) ≤
      δ * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  have hX := GlobalTheory.NearLowerCompare.frm_isUnit I x
  have e : (frm I x w)⁻¹ * (LinearMap.toMatrix (bas I) (bas I) (Matrix.toLin' (g - 1))).map w.embedding *
      frm I x w = (frm I x w)⁻¹ * g.map w.embedding * frm I x w - 1 := by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.map_sub _ (map_sub _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ (hX w)]
  unfold Formalism.HermitianLatticesTheory.normAt
  rw [Formalism.HN.PlaceOperatorNorms.fcoord_map (bas I) (frm I x) (bas I) (frm I x) hX w, e]
  exact (cnorm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _))

theorem lowers (I : AutInst) (x : I.GA) (de : ℝ) (hde : 0 < de) (γ : GL (Fin I.n) I.E) (a : I.GA)
    (h1 : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (h2 : ∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (h3 : I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (ha : a ∈ nearSet I x de) (t : ℝ) (ht : 0 < t) :
    (stepLe I x t).map ((Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1)).restrictScalars (𝓞 I.E)) ≤
      stepLe I x (de * t) := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  obtain ⟨-, -, -, -, -, hK, hw⟩ := GlobalTheory.T.autPoint_rational_equivariance I x γ a h1 h2 h3
  have hΛ := hK.1 ha.2.1
  obtain ⟨hA, -, -, -, hAt, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht
  obtain ⟨hS, -, -, -, -, -, hSt, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (de * t) (mul_pos hde ht)
  refine map_le_of_sizes (bas I) (frm I x) (GlobalTheory.NearLowerCompare.frm_isUnit I x)
    (GlobalTheory.NearLowerCompare.lamX_isLattice I x).fg hS hA.1 _ ?_ hde ?_ hAt hSt
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ lamX I x := hA.1 hy
    have : Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E) y ∈ lamX I x := by
      rw [← hΛ]; exact ⟨y, hy', rfl⟩
    simpa [map_sub, Matrix.sub_mulVec] using (lamX I x).sub_mem this hy'
  · intro w
    refine normAt_sub_one_le I x _ w ?_
    rcases hw w with h | h
    · rw [h]; exact ha.2.2 _
    · rw [h, hs_conj_sub_one]; exact ha.2.2 _

theorem nearSet_eq (I : AutInst) (x : I.GA) (de : ℝ) (hde : 0 < de) (hde' : de < 1 / 4)
    (hl : 1 / 2 ≤ least I x) : nearSet I x de = {1} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨GlobalTheory.Count.Test.one_mem_nearSet I x hde.le, fun a ha => ?_⟩
  by_cases hn : I.n = 0
  · have := GlobalTheory.NearLowerCompare.subsingleton_GA I hn
    exact Subsingleton.elim _ _
  have hn1 : 1 ≤ I.n := Nat.one_le_iff_ne_zero.2 hn
  obtain ⟨γ, h1, h2, h3⟩ := ha.1
  have hlow := lowers I x de hde γ a h1 h2 h3 ha 2 two_pos
  have hbot : stepLe I x (de * 2) = ⊥ :=
    ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (de * 2) (by positivity)).2.2.2.2.2.2.2.2 hn1).2.1.2 (by linarith)
  have hspan := (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1
  have h0 : lamX I x ≠ ⊥ := by
    intro h0
    have h1 := hspan
    rw [h0] at h1
    have : Nonempty (Fin I.n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    simp at h1
  have hle : lamX I x ≤ stepLe I x 2 := by
    refine le_sSup ⟨le_rfl, h0, ?_⟩
    rw [(GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x).2.1 hn1]
    exact inv_le_of_inv_le₀ two_pos (by linarith)
  have hz : Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) = 0 := by
    refine LinearMap.ext_on hspan fun y hy => ?_
    have := hlow ⟨y, hle hy, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact this
  have hγ : (γ : Matrix (Fin I.n) (Fin I.n) I.E) = 1 :=
    sub_eq_zero.1 (Matrix.toLin'.map_eq_zero_iff.1 hz)
  rw [hγ] at h2 h3
  refine Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))
  · have := h2 v
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))] at this
    exact this
  · rw [Matrix.map_one _ (map_zero _) (map_one _)] at h3
    exact h3

theorem near_lowers_steps : ∀ (I : AutInst) (x : I.GA) (de : ℝ), 0 < de → de < 1 / 4 → (∀ (γ : GL (Fin I.n) I.E) (a : I.GA), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → a ∈ nearSet I x de → ∀ t : ℝ, 0 < t → (stepLe I x t).map ((Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1)).restrictScalars (𝓞 I.E)) ≤ stepLe I x (de * t)) ∧ (1 / 2 ≤ least I x → nearSet I x de = {1}) :=
  fun I x de h0 h1 => ⟨lowers I x de h0, nearSet_eq I x de h0 h1⟩

end GlobalTheory.NearLower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableTranslatedLatticeFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableTranslatedLatticeFunctions
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.LatMeasurable

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def oneInf : MatInf E j := fun _ a b => (1 : Matrix (Fin j) (Fin j) ℂ) a b

theorem of_oneInf (w : InfinitePlace E) : Matrix.of (oneInf E j w) = 1 := rfl

theorem detNorm_oneInf : 0 < detNorm E j (oneInf E j) := by
  unfold detNorm
  simp [of_oneInf]

variable {E j}

theorem isUnit_det_of_pos {g : MatInf E j} (hg : 0 < detNorm E j g) (w : InfinitePlace E) :
    IsUnit (Matrix.of (g w)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hz : detNorm E j g = 0 := by
    unfold detNorm
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by simp [h0])
  linarith

def act (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) : VecInf E j →ₗ[ℤ] VecInf E j where
  toFun x w := A w *ᵥ x w
  map_add' x y := by funext w; simp [Matrix.mulVec_add]
  map_smul' c x := by funext w; exact Matrix.mulVec_smul (A w) c (x w)

theorem act_apply (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) (x : VecInf E j) (w : InfinitePlace E) :
    act A x w = A w *ᵥ x w := rfl

theorem act_act {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ} (h : ∀ w, A w * B w = 1) (x : VecInf E j) :
    act A (act B x) = x := by
  funext w
  simp only [act_apply, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem latAt_eq (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) :
    latAt E j Λ g = (latAt E j Λ (oneInf E j)).map (act fun w => (Matrix.of (g w))⁻¹) := by
  unfold latAt
  rw [Submodule.map_span, ← Set.image_comp]
  congr 2
  funext y w
  simp [act_apply, of_oneInf]

private lemma dualAt_act_transpose (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) (x y : VecInf E j) :
    ∑ w, (act A x w ⬝ᵥ y w).re = ∑ w, (x w ⬝ᵥ act (fun w => (A w)ᵀ) y w).re := by
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [act_apply]
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

theorem dualAt_map (L : Submodule ℤ (VecInf E j)) {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ}
    (h : ∀ w, A w * B w = 1) :
    dualAt E j (L.map (act A)) = (dualAt E j L).map (act fun w => (B w)ᵀ) := by
  have hBA : ∀ w, B w * A w = 1 := fun w => mul_eq_one_comm.mp (h w)
  have hT : ∀ y, act (fun w => (B w)ᵀ) (act (fun w => (A w)ᵀ) y) = y := fun y =>
    act_act (fun w => by rw [← Matrix.transpose_mul, h w, Matrix.transpose_one]) y
  have hT' : ∀ y, act (fun w => (A w)ᵀ) (act (fun w => (B w)ᵀ) y) = y := fun y =>
    act_act (fun w => by rw [← Matrix.transpose_mul, hBA w, Matrix.transpose_one]) y
  unfold dualAt
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hy
    refine ⟨act (fun w => (A w)ᵀ) y, fun x hx => ?_, hT y⟩
    obtain ⟨z, hz⟩ := hy _ (Submodule.mem_map_of_mem hx)
    exact ⟨z, by rw [← dualAt_act_transpose A x y]; exact hz⟩
  · rintro ⟨y', hy', rfl⟩ x hx
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨z, hz⟩ := hy' x' hx'
    exact ⟨z, by rw [dualAt_act_transpose A x' _, hT' y']; exact hz⟩

theorem tsum_map (L : Submodule ℤ (VecInf E j)) {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ}
    (h : ∀ w, A w * B w = 1) (Φ : VecInf E j → ENNReal) :
    ∑' x : {x : VecInf E j // x ∈ L.map (act A) ∧ x ≠ 0}, Φ x.1 =
      ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ (act A x.1) := by
  have hBA : ∀ w, B w * A w = 1 := fun w => mul_eq_one_comm.mp (h w)
  let e : {x : VecInf E j // x ∈ L ∧ x ≠ 0} ≃ {x : VecInf E j // x ∈ L.map (act A) ∧ x ≠ 0} :=
    { toFun := fun x => ⟨act A x.1, Submodule.mem_map_of_mem x.2.1, fun h0 => x.2.2 (by
          rw [← act_act hBA x.1, h0, map_zero])⟩
      invFun := fun y => ⟨act B y.1, by
          obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.2.1
          rw [← hxy, act_act hBA]
          exact hx, fun h0 => y.2.2 (by rw [← act_act h y.1, h0, map_zero])⟩
      left_inv := fun x => Subtype.ext (act_act hBA x.1)
      right_inv := fun y => Subtype.ext (act_act h y.1) }
  exact (e.tsum_eq (fun x => Φ x.1)).symm

def pairL (y : VecInf E j) : VecInf E j →ₗ[ℝ] ℝ where
  toFun x := ∑ w, (x w ⬝ᵥ y w).re
  map_add' x x' := by simp [add_dotProduct, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_dotProduct, Finset.mul_sum]

theorem pairL_injective : Function.Injective (pairL : VecInf E j → _) := by
  classical
  intro y y' hyy
  have key : ∀ (w : InfinitePlace E) (a : Fin j) (c : ℂ), (c * y w a).re = (c * y' w a).re := by
    intro w a c
    have hv : ∀ z : VecInf E j, pairL z (Pi.single w (Pi.single a c)) = (c * z w a).re := by
      intro z
      show ∑ v, ((Pi.single w (Pi.single a c) : VecInf E j) v ⬝ᵥ z v).re = _
      rw [Finset.sum_eq_single w (fun v _ hne => by simp [hne]) (by simp)]
      simp [single_dotProduct]
    rw [← hv y, ← hv y', hyy]
  funext w a
  apply Complex.ext
  · simpa using key w a 1
  · simpa using key w a Complex.I

theorem countable_dualAt (L : Submodule ℤ (VecInf E j)) (hL : Submodule.span ℝ (L : Set (VecInf E j)) = ⊤) :
    Countable (dualAt E j L) := by
  have hsym : ∀ x y : VecInf E j, pairL y x = pairL x y := fun x y => by
    show ∑ w, (x w ⬝ᵥ y w).re = ∑ w, (y w ⬝ᵥ x w).re
    exact Finset.sum_congr rfl fun w _ => by rw [dotProduct_comm]
  have hint : ∀ y ∈ dualAt E j L, ∀ x ∈ L, ∃ z : ℤ, pairL x y = z := by
    intro y hy x hx
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨z, hz⟩ := hy' x hx
      exact ⟨z, by rw [← hsym x y]; exact hz⟩
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha⟩ := h1
      obtain ⟨c, hc⟩ := h2
      exact ⟨a + c, by rw [map_add (f := _), ha, hc]; push_cast; ring⟩
    | smul n y _ h1 =>
      obtain ⟨a, ha⟩ := h1
      exact ⟨n * a, by rw [map_zsmul, ha, zsmul_eq_mul]; push_cast; ring⟩
  obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent ℝ (L : Set (VecInf E j))
  haveI : Finite b := hbli.finite
  choose φ hφ using fun (y : dualAt E j L) (i : b) => hint y.1 y.2 i.1 (hbL i.2)
  refine Function.Injective.countable (f := φ) ?_
  intro y y' hyy
  apply Subtype.ext
  apply pairL_injective
  refine LinearMap.ext_on (s := (b : Set (VecInf E j))) (hbspan.trans hL) ?_
  intro x hx
  have e1 := hφ y ⟨x, hx⟩
  have e2 := hφ y' ⟨x, hx⟩
  dsimp only at e1 e2
  rw [hsym x y.1, hsym x y'.1, e1, e2, hyy]

theorem measurable_of_continuous {β : Type} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (w : InfinitePlace E) (f : Matrix (Fin j) (Fin j) ℂ → β) (hf : Continuous f) :
    Measurable fun g : MatInf E j => f (Matrix.of (g w)) := by
  have hc : Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ => f (Matrix.of (g w)) :=
    hf.comp (continuous_apply w)
  exact hc.measurable

theorem measurable_detNorm : Measurable (detNorm E j) := by
  unfold detNorm
  exact Finset.measurable_prod _ fun w _ =>
    measurable_of_continuous w (fun M => ‖M.det‖ ^ 2) (continuous_id.matrix_det.norm.pow 2)

theorem measurable_act_inv (x : VecInf E j) :
    Measurable fun g : MatInf E j => act (fun w => (Matrix.of (g w))⁻¹) x := by
  refine Measurable.of_eval fun w => ?_
  simp only [act_apply]
  have hinv : ∀ M : Matrix (Fin j) (Fin j) ℂ, M⁻¹ = (M.det)⁻¹ • M.adjugate := fun M => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [hinv]
  have hd : Measurable fun g : MatInf E j => (Matrix.of (g w)).det :=
    measurable_of_continuous w (fun M => M.det) continuous_id.matrix_det
  refine Measurable.of_eval fun a => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun b _ => ?_
  exact (hd.inv.mul (measurable_of_continuous w (fun M => M.adjugate a b)
    (continuous_id.matrix_adjugate.matrix_elem a b))).mul_const _

theorem measurable_act_transpose (x : VecInf E j) :
    Measurable fun g : MatInf E j => act (fun w => (Matrix.of (g w))ᵀ) x := by
  refine Measurable.of_eval fun w => ?_
  simp only [act_apply]
  exact measurable_of_continuous w (fun M => Mᵀ *ᵥ x w)
    (continuous_id.matrix_transpose.matrix_mulVec continuous_const)

theorem measurable_indicator_of_eqOn {f f' : MatInf E j → ENNReal} (hf' : Measurable f')
    (h : ∀ g, 0 < detNorm E j g → f g = f' g) :
    Measurable fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator f g := by
  have hS : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
    measurableSet_lt measurable_const measurable_detNorm
  convert hf'.indicator hS using 1
  funext g
  exact congrFun (Set.indicator_congr fun g hg => h g hg) g

private lemma countable_nonzero_lattice_vectors (L : Submodule ℤ (VecInf E j)) [Countable L] :
    Countable {x : VecInf E j // x ∈ L ∧ x ≠ 0} :=
  Function.Injective.countable (f := fun x : {x : VecInf E j // x ∈ L ∧ x ≠ 0} => (⟨x.1, x.2.1⟩ : L))
    fun _ _ hab => Subtype.ext (congrArg (fun y : L => (y : VecInf E j)) hab)

theorem measurable_latFun : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => w (covAt E j (latAt E j Λ g))) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ g ∧ x ≠ 0}, Φ x.1) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ g) ∧ x ≠ 0}, Φ x.1) g) := by
  intro E _ _ hE j wt Φ hw hΦ Λ hΛ
  obtain ⟨κ, -, hK⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE j).1 Λ hΛ
  obtain ⟨⟨hd, hz⟩, -, -, -⟩ := hK (oneInf E j) (detNorm_oneInf E j)
  haveI : Countable (latAt E j Λ (oneInf E j)) :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  haveI : Countable (dualAt E j (latAt E j Λ (oneInf E j))) := countable_dualAt _ hz.span_top
  haveI := countable_nonzero_lattice_vectors (latAt E j Λ (oneInf E j))
  haveI := countable_nonzero_lattice_vectors (dualAt E j (latAt E j Λ (oneInf E j)))
  have hinv : ∀ g : MatInf E j, 0 < detNorm E j g → ∀ w, (Matrix.of (g w))⁻¹ * Matrix.of (g w) = 1 :=
    fun g hg w => Matrix.nonsing_inv_mul _ (isUnit_det_of_pos hg w)
  have htr : ∀ g : MatInf E j, 0 < detNorm E j g →
      ∀ w, (Matrix.of (g w))ᵀ * ((Matrix.of (g w))⁻¹)ᵀ = 1 := by
    intro g hg w
    rw [← Matrix.transpose_mul, hinv g hg w, Matrix.transpose_one]
  refine ⟨?_, ?_, ?_⟩
  · exact measurable_indicator_of_eqOn (f' := fun g => wt (κ / detNorm E j g))
      (hw.comp (measurable_const.div measurable_detNorm)) fun g hg => by simp only [(hK g hg).2.1]
  · refine measurable_indicator_of_eqOn
      (f' := fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ (oneInf E j) ∧ x ≠ 0},
        Φ (act (fun w => (Matrix.of (g w))⁻¹) x.1))
      (Measurable.tsum fun x => hΦ.comp (measurable_act_inv x.1)) fun g hg => ?_
    try dsimp only
    rw [latAt_eq Λ g, tsum_map _ (hinv g hg) Φ]
  · refine measurable_indicator_of_eqOn
      (f' := fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ (oneInf E j)) ∧ x ≠ 0},
        Φ (act (fun w => (Matrix.of (g w))ᵀ) x.1))
      (Measurable.tsum fun x => hΦ.comp (measurable_act_transpose x.1)) fun g hg => ?_
    try dsimp only
    rw [latAt_eq Λ g, dualAt_map _ (hinv g hg), tsum_map _ (htr g hg) Φ]

end GlobalTheory.LatMeasurable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableTranslatedLatticeFunctionsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_translatedLattice_functions : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => w (covAt E j (latAt E j Λ g))) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ g ∧ x ≠ 0}, Φ x.1) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ g) ∧ x ≠ 0}, Φ x.1) g) := by
  first
  | exact @GlobalTheory.LatMeasurable.measurable_latFun
  | intro E _ _ hE j w Φ hw hΦ Λ hΛ
    exact GlobalTheory.LatMeasurable.measurable_latFun E hE j w Φ hw hΦ Λ hΛ.toIsLattice
end
end
