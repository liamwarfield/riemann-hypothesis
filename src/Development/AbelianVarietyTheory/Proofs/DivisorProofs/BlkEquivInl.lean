module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
public import GroundTheory.AutomorphicForms.ReductionCore
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfInertCore
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BottomMinor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
noncomputable section

open Matrix

namespace GlobalTheory.LeviGA

variable {R S : Type} [CommRing R] [CommRing S] {a r : ℕ}

def blkEquiv (h : r ≤ a) : Fin r ⊕ Fin (a - r) ≃ Fin a :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

@[simp] theorem blkEquiv_inl (h : r ≤ a) (i : Fin r) : ((blkEquiv h (Sum.inl i) : Fin a) : ℕ) = i := rfl

@[simp] theorem blkEquiv_inr (h : r ≤ a) (i : Fin (a - r)) : ((blkEquiv h (Sum.inr i) : Fin a) : ℕ) = r + i := rfl


variable (R) in
def blkMat (h : r ≤ a) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin (a - r)) (Fin (a - r)) R →* Matrix (Fin a) (Fin a) R where
  toFun p := Matrix.reindex (blkEquiv h) (blkEquiv h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blkGL (h : r ≤ a) : GL (Fin r) R × GL (Fin (a - r)) R →* GL (Fin a) R :=
  (Units.map (blkMat R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem blkGL_val (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) :
    (blkGL h p : Matrix (Fin a) (Fin a) R) =
      Matrix.reindex (blkEquiv h) (blkEquiv h) (Matrix.fromBlocks (p.1 : Matrix _ _ R) 0 0 (p.2 : Matrix _ _ R)) :=
  rfl

theorem blkGL_apply (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) (i j : Fin r ⊕ Fin (a - r)) :
    (blkGL h p : Matrix (Fin a) (Fin a) R) (blkEquiv h i) (blkEquiv h j) =
      Matrix.fromBlocks (p.1 : Matrix _ _ R) 0 0 (p.2 : Matrix _ _ R) i j := by
  rw [blkGL_val, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem blkGL_block (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) (i j : Fin a) :
    ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (blkGL h p : Matrix (Fin a) (Fin a) R) i j = 0 := by
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  rw [blkGL_apply]
  rcases i with i | i <;> rcases j with j | j
  · left; simp
  · right; simp
  · right; simp
  · left; simp

theorem exists_blkGL (h : r ≤ a) (m : GL (Fin a) R)
    (hm : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (m : Matrix (Fin a) (Fin a) R) i j = 0) :
    ∃ p, blkGL h p = m := by
  obtain ⟨M, hM⟩ : ∃ M, M = (m : Matrix (Fin a) (Fin a) R).submatrix (blkEquiv h) (blkEquiv h) := ⟨_, rfl⟩
  have h12 : M.toBlocks₁₂ = 0 := by
    ext i j
    rw [Matrix.toBlocks₁₂, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]
    rcases hm (blkEquiv h (Sum.inl i)) (blkEquiv h (Sum.inr j)) with h' | h'
    · rw [blkEquiv_inl, blkEquiv_inr] at h'; omega
    · exact h'
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]
    rcases hm (blkEquiv h (Sum.inr i)) (blkEquiv h (Sum.inl j)) with h' | h'
    · rw [blkEquiv_inl, blkEquiv_inr] at h'; omega
    · exact h'
  have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h12, h21]
  have hdet : IsUnit M.det := by
    rw [hM, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
  rw [hMb, Matrix.det_fromBlocks_zero₂₁] at hdet
  have hA : IsUnit M.toBlocks₁₁ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)
  have hD : IsUnit M.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdet)
  refine ⟨(hA.unit, hD.unit), Units.ext ?_⟩
  rw [blkGL_val]
  simp only [IsUnit.unit_spec]
  rw [← hMb, hM]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]

theorem map_blkGL (h : r ≤ a) (f : R →+* S) (p : GL (Fin r) R × GL (Fin (a - r)) R) :
    Units.map f.mapMatrix.toMonoidHom (blkGL h p) =
      blkGL h (Units.map f.mapMatrix.toMonoidHom p.1, Units.map f.mapMatrix.toMonoidHom p.2) := by
  apply Units.ext
  simp only [Units.coe_map, blkGL_val]
  ext i j
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.reindex_apply]

end GlobalTheory.LeviGA

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
noncomputable section
open NumberField Topology MeasureTheory Filter Metric
open scoped Pointwise

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem countable_ratN (r : ℕ) : Countable (ratN E a r) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  refine Function.Surjective.countable (f := fun q : BlockIx a r → E =>
    (⟨fun p => algebraMap E (Ad E) (q p), q, rfl⟩ : ratN E a r)) ?_
  rintro ⟨x, q, rfl⟩
  exact ⟨q, rfl⟩

theorem covol_lt_top {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx a r → Ad E))
    (h : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) : μ 𝓕 < ⊤ := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have := countable_ratN (E := E) (a := a) r
  let Cm : Set (BlockIx a r → Ad E) := Set.univ.pi fun _ => K
  have hCm : IsCompact Cm := isCompact_univ_pi fun _ => hK
  have hcovm : ∀ x : BlockIx a r → Ad E, ∃ γ : ratN E a r, x ∈ γ +ᵥ Cm := by
    intro x
    choose q hq using fun p => hcov (x p)
    refine ⟨⟨fun p => algebraMap E (Ad E) (q p), q, rfl⟩, fun p => x p - algebraMap E (Ad E) (q p),
      fun p _ => hq p, ?_⟩
    funext p
    show algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p)) = x p
    abel
  have h1 : μ 𝓕 ≤ ∑' γ : ratN E a r, μ ((γ +ᵥ Cm) ∩ 𝓕) := by
    calc μ 𝓕 ≤ μ (⋃ γ : ratN E a r, ((γ +ᵥ Cm) ∩ 𝓕)) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨γ, hγ⟩ := hcovm x
          exact Set.mem_iUnion.mpr ⟨γ, hγ, hx⟩
      _ ≤ ∑' γ : ratN E a r, μ ((γ +ᵥ Cm) ∩ 𝓕) := measure_iUnion_le _
  have : MeasurableConstVAdd (ratN E a r) (BlockIx a r → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a r → Ad E => (γ : BlockIx a r → Ad E) + x).measurable⟩
  have : VAddInvariantMeasure (ratN E a r) (BlockIx a r → Ad E) μ :=
    ⟨fun γ s _ => measure_preimage_add μ (γ : BlockIx a r → Ad E) s⟩
  rw [← h.measure_eq_tsum Cm] at h1
  exact h1.trans_lt hCm.measure_lt_top

theorem chart_unip_periodic {r : ℕ} {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) (q : BlockIx a r → E)
    (x : BlockIx a r → Ad E) :
    chart φ.1 (unip ((fun p => algebraMap E (Ad E) (q p)) + x) * g) = chart φ.1 (unip x * g) := by
  rw [unip_add, unip_algebraMap, mul_assoc]
  funext y
  unfold chart
  split_ifs
  · rw [mul_assoc, hφ.left]
  · rfl

theorem chart_cont_bound {r : ℕ} {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) (X : Lie E a) :
    (∀ y ∈ invSet E a, Continuous fun x : BlockIx a r → Ad E => chart φ.1 (unip x * g) y) ∧
    (∀ y ∈ invSet E a, Continuous fun x : BlockIx a r → Ad E => fderiv ℝ (chart φ.1 (unip x * g)) y X) ∧
    ∀ S : Set (Lie E a), IsCompact S → S ⊆ invSet E a → ∃ C, ∀ x : BlockIx a r → Ad E, ∀ y ∈ S,
      ‖chart φ.1 (unip x * g) y‖ ≤ C ∧ ‖fderiv ℝ (chart φ.1 (unip x * g)) y X‖ ≤ C := by
  have h1 := (GlobalTheory.T.chart_unipotent_fderiv_continuousOn E a r φ hφ g X).1
  have h2 := (GlobalTheory.T.chart_unipotent_fderiv_continuousOn E a r φ hφ g X).2
  have hm : ∀ y ∈ invSet E a, ∀ x : BlockIx a r → Ad E,
      ((x, y) : (BlockIx a r → Ad E) × Lie E a) ∈ Set.univ ×ˢ invSet E a :=
    fun y hy x => Set.mem_prod.2 ⟨Set.mem_univ _, hy⟩
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun S hS hSi => ?_⟩
  · have := h1.comp_continuous (continuous_id.prodMk continuous_const) (hm y hy)
    exact this
  · have := h2.comp_continuous (continuous_id.prodMk continuous_const) (hm y hy)
    exact this
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact ((Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S) := (isCompact_univ_pi fun _ => hK).prod hS
  have hsub : (Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S ⊆ Set.univ ×ˢ invSet E a :=
    Set.prod_mono (Set.subset_univ _) hSi
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn (h1.mono hsub)
  obtain ⟨C2, hC2⟩ := hKc.exists_bound_of_continuousOn (h2.mono hsub)
  refine ⟨max C1 C2, fun x y hy => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : x = (fun p => algebraMap E (Ad E) (q p)) + fun p => x p - algebraMap E (Ad E) (q p) := by
    funext p
    show x p = algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p))
    exact (add_sub_cancel _ _).symm
  have hx' : ((fun p => x p - algebraMap E (Ad E) (q p)), y) ∈ (Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S :=
    ⟨fun p _ => hq p, hy⟩
  rw [hx, chart_unip_periodic hφ]
  exact ⟨(hC1 _ hx').trans (le_max_left _ _), (hC2 _ hx').trans (le_max_right _ _)⟩

theorem isCuspidal_lie (X : Lie E a) (φ : Sm E a) (hφ : IsCuspForm φ) : IsCuspidal (lie E a X φ).1 := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  haveI := hμ
  obtain ⟨hc1, hc2, hb⟩ := chart_cont_bound (r := r) hφ.1 g X
  let ℓ : ℝ → Lie E a := fun t => oneL E a + t • X
  have hℓc : Continuous ℓ := continuous_const.add (continuous_id.smul continuous_const)
  have hT : IsOpen (ℓ ⁻¹' invSet E a) := isOpen_invSet.preimage hℓc
  have h0T : (0:ℝ) ∈ ℓ ⁻¹' invSet E a := by
    show oneL E a + (0:ℝ) • X ∈ invSet E a
    rw [zero_smul, add_zero]; exact isUnit_one
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hT 0 h0T
  have hε : 0 < δ / 2 := by positivity
  have hS : IsCompact (ℓ '' closedBall 0 (δ / 2)) := (isCompact_closedBall 0 (δ / 2)).image hℓc
  have hSinv : ℓ '' closedBall 0 (δ / 2) ⊆ invSet E a := by
    rintro _ ⟨t, ht, rfl⟩; exact hball (closedBall_subset_ball (by linarith) ht)
  obtain ⟨C, hC⟩ := hb _ hS hSinv
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hballT : ∀ t ∈ ball (0:ℝ) (δ / 2), ℓ t ∈ invSet E a := fun t ht => hball (ball_subset_ball (by linarith) ht)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕)
    (F := fun t x => chart φ.1 (unip x * g) (ℓ t))
    (F' := fun t x => fderiv ℝ (chart φ.1 (unip x * g)) (ℓ t) X) (x₀ := 0)
    (bound := fun _ => C) (s := ball 0 (δ / 2)) (ball_mem_nhds 0 hε) ?meas ?int ?meas' ?bd (integrable_const C) ?diff
  case meas =>
    filter_upwards [ball_mem_nhds (0:ℝ) hε] with t ht
    exact (hc1 _ (hballT t ht)).aestronglyMeasurable
  case int =>
    refine Integrable.of_bound (hc1 _ (hballT 0 (mem_ball_self hε))).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun x => (hC x _ ⟨0, mem_closedBall_self hε.le, rfl⟩).1
  case meas' => exact (hc2 _ (hballT 0 (mem_ball_self hε))).aestronglyMeasurable
  case bd =>
    exact Filter.Eventually.of_forall fun x t ht => (hC x _ ⟨t, ball_subset_closedBall ht, rfl⟩).2
  case diff =>
    refine Filter.Eventually.of_forall fun x t ht => ?_
    have hd := ((contDiffAt_chart φ.2 (unip x * g) (hballT t ht)).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt ℓ X t := by
      have := ((hasDerivAt_id t).smul_const X).const_add (oneL E a)
      rw [one_smul] at this
      exact this
    exact hd.comp_hasDerivAt t hl
  have heq : (fun t => ∫ x in 𝓕, chart φ.1 (unip x * g) (ℓ t) ∂μ) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ball_mem_nhds (0:ℝ) hε] with t ht
    have hu : IsUnit (Matrix.of (ℓ t)) := hballT t ht
    have e : ∀ x : BlockIx a r → Ad E, chart φ.1 (unip x * g) (ℓ t) = φ.1 (unip x * (g * infGL E a hu.unit)) := fun x => by
      rw [chart, dite_eq_left hu, mul_assoc]
    simp only [e]
    exact hφ.2 r h0 h1 μ 𝓕 hμ hF _
  have h2 := key.2.unique ((hasDerivAt_const (0:ℝ) (0:ℂ)).congr_of_eventuallyEq heq)
  have e0 : ℓ 0 = oneL E a := by simp [ℓ]
  simp only [e0] at h2
  exact h2

theorem isCuspidal_lie_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (X : Lie E a) (φ : Sm E a), IsCuspForm φ → IsCuspidal (lie E a X φ).1 :=
  fun _ _ _ _ _ X φ h => isCuspidal_lie X φ h

end GlobalTheory.CuspRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspFormStatement
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_lieAction_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsCuspForm φ → GlobalTheory.CuspRep.IsCuspidal (GlobalTheory.CuspRep.lie E a X φ).1 := by
  first | exact @GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm | exact GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm | (intros; apply GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCAlpha

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def lapOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    ((lieS E a i j (atEmb τ 1)) ^ 2 + (lieS E a i j (atEmb τ Complex.I)) ^ 2)

def casKOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (1 / 4 : ℂ) •
    ((lieS E a i j (atEmb τ 1) - lieS E a j i (atEmb τ 1)) ^ 2 +
      (lieS E a i j (atEmb τ Complex.I) + lieS E a j i (atEmb τ Complex.I)) ^ 2)

def vecF (X : Lie E a) (f : Lie E a → ℂ) : Lie E a → ℂ := fun y => fderiv ℝ f y (rmul X y)

def lapF (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    (vecF E a (toL (Matrix.single i j (atEmb τ 1))) (vecF E a (toL (Matrix.single i j (atEmb τ 1))) f) +
      vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) (vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) f))

def polyF (p : Polynomial ℂ) (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (lapF E a)^[k] f

end GlobalTheory.HCAlpha

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.ZalgCpt

theorem zalg_comm_cptRep : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (k : GlobalTheory.CuspRep.Kinf E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)),
    z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.cptRep E a k = GlobalTheory.CuspRep.cptRep E a k * z := by
  intro E _ _ _ a k z hz
  have hle : GlobalTheory.CuspRep.Zalg E a ≤ Subalgebra.centralizer ℂ {GlobalTheory.CuspRep.cptRep E a k} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u (Unitary.toUnits k)).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle hz) _ rfl).symm

end GlobalTheory.ZalgCpt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRepStatement
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_zalg_commute_compactRep : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (k : GlobalTheory.CuspRep.Kinf E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.cptRep E a k = GlobalTheory.CuspRep.cptRep E a k * z := by
  first | exact @GlobalTheory.ZalgCpt.zalg_comm_cptRep | exact GlobalTheory.ZalgCpt.zalg_comm_cptRep | (intros; apply GlobalTheory.ZalgCpt.zalg_comm_cptRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def absDetA (g : GA E a) : ℝ :=
  GroundTheory.Automorphic.Reduction.adeleAbs ((Matrix.GeneralLinearGroup.det g : (Ad E)ˣ) : Ad E)

theorem absDetA_pos (g : GA E a) : 0 < absDetA g := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det g)]
  exact ((GroundTheory.Global.IdeleGroup.ideleModule E) (Matrix.GeneralLinearGroup.det g)).2

theorem absDetA_one : absDetA (1 : GA E a) = 1 := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det (1 : GA E a)), map_one, map_one]
  rfl


variable (E a) in
def band : Set (GA E a) := {g | 1 ≤ absDetA g ∧ absDetA g ≤ 2}

theorem one_mem_band : (1 : GA E a) ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, absDetA_one]; norm_num

end GlobalTheory.HCF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

theorem Zalg_mul_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a)
    (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a →
      z * GlobalTheory.CuspRep.lie E a X = GlobalTheory.CuspRep.lie E a X * z := by
  intro E _ _ _ a X z hz
  have h : GlobalTheory.CuspRep.Zalg E a ≤ Subalgebra.centralizer ℂ {GlobalTheory.CuspRep.lie E a X} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (commute_cap_lie τ u X).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (h hz) _ rfl).symm

end GlobalTheory.CuspRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieActionStatement
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_zalg_commute_lie_action : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.lie E a X = GlobalTheory.CuspRep.lie E a X * z := by
  first | exact @GlobalTheory.CuspRep.Zalg_mul_lie | exact GlobalTheory.CuspRep.Zalg_mul_lie | (intros; apply GlobalTheory.CuspRep.Zalg_mul_lie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainUnipotent
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

theorem constTerm_unip_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (y : BlockIx a r → Ad E) (g : GA E a), ∫ x in 𝓕, f (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 f hf y g
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  set h : (BlockIx a r → Ad E) → ℂ := fun x => f (unip x * g) with hh
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), h (γ +ᵥ x) = h x := by
    rintro ⟨_, e, rfl⟩ x
    change f (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = f (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hf]
  have hL : ∀ x, f (unip x * (unip y * g)) = h (x + y) := fun x => by
    simp only [hh, unip_add, mul_assoc]
  simp_rw [hL]

  have hmp : MeasurePreserving (fun x : BlockIx a r → Ad E => x + y) μ μ := measurePreserving_add_right μ y
  have hemb : MeasurableEmbedding (fun x : BlockIx a r → Ad E => x + y) :=
    (MeasurableEquiv.addRight y).measurableEmbedding
  let S : Set (BlockIx a r → Ad E) := (fun x => x - y) ⁻¹' 𝓕
  have hpre : (fun x : BlockIx a r → Ad E => x + y) ⁻¹' S = 𝓕 := by
    ext x; simp [S]
  have hS : IsAddFundamentalDomain (ratN E a r) S μ := by
    refine h𝓕.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · exact (measurePreserving_sub_right μ y).quasiMeasurePreserving
    · intro γ x
      change (γ : BlockIx a r → Ad E) + x - y = (γ : BlockIx a r → Ad E) + (x - y)
      abel
  calc ∫ x in 𝓕, h (x + y) ∂μ = ∫ x in (fun x : BlockIx a r → Ad E => x + y) ⁻¹' S, h (x + y) ∂μ := by rw [hpre]
    _ = ∫ x in S, h x ∂μ := hmp.setIntegral_preimage_emb hemb h S
    _ = ∫ x in 𝓕, h x ∂μ := hS.setIntegral_eq h𝓕 hinv

end GlobalTheory.CuspRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainUnipotentStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamental_domain_unipotent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (y : BlockIx a r → Ad E) (g : GA E a), ∫ x in 𝓕, f (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  first | exact @GlobalTheory.CuspRep.constTerm_unip_invariant | exact GlobalTheory.CuspRep.constTerm_unip_invariant | (intros; apply GlobalTheory.CuspRep.constTerm_unip_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowerEmbedding
open NumberField IsDedekindDomain IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

set_option linter.style.haveILetI false

namespace GlobalTheory.FrobEmb

theorem exists_frob_all (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (hc : ∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) (p : ℕ) (hp : p.Prime) :
    ∃ σ : E ≃ₐ[ℚ] E, ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ σ P := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(p : ℤ)}) (by simpa using hp.ne_zero) P
  haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨σ, fun Q _ _ => ?_⟩
  obtain ⟨t, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have := hσ.conj t
  rwa [hc t σ, mul_inv_cancel_right] at this

theorem isArithFrobAt_frobG (D : D7) (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : IsArithFrobAt ℤ (D.host.sigmaOf (frobG D p)) P := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have h : ∃ g : D.R.GG, ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf g) P := by
    obtain ⟨σ, hσ⟩ := exists_frob_all D.host.E (fun a b =>
      (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])) p hp
    obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
    have hg' : D.host.sigmaOf g = σ := hg
    exact ⟨g, hg' ▸ hσ⟩
  unfold frobG
  rw [dite_eq_left h]
  exact h.choose_spec P

end GlobalTheory.FrobEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeLower
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.EulerProductSatake
open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors

noncomputable section

abbrev Place (K : Type) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)

def normAt {K : Type} [Field K] [NumberField K] (w : Place K) : ℝ :=
  (Ideal.absNorm w.asIdeal : ℝ)

section Euler

variable {K : Type} [Field K] [NumberField K] {ι : Type}

def localFactor (I : Finset ι) (x : Place K → ι → ℂ) (w : Place K) : ℂ :=
  ∏ i ∈ I, (1 - x w i)⁻¹

def eulerProd (T : Set (Place K)) (I : Finset ι) (x : Place K → ι → ℂ) : ℂ :=
  ∏' w : {w : Place K // w ∉ T}, localFactor I x w.1

end Euler

def SatakeBound {E : Type} [Field E] [NumberField E] (T : Set (Place E)) (r : ℕ) (s : ℝ)
    (x : Place E → Fin r → ℂ) : Prop :=
  ∀ w, w ∉ T → ∀ i, ‖x w i‖ ≤ normAt w ^ (((r : ℝ) - 1) / 2 - s)

def twistTerm {F : Type} [Field F] [NumberField F] (ω : Place F → ℂ) (v : Place F) (i : ℕ) : ℂ :=
  ω v ^ i * ((normAt v : ℂ) ^ i)⁻¹

def dPart {F : Type} [Field F] [NumberField F] (S : Set (Place F)) (ω : Place F → ℂ)
    (r t : ℕ) : ℂ :=
  eulerProd S (Finset.Icc (t + 1) (r + t)) (twistTerm ω)

def placesOver {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (S : Set (Place F)) : Set (Place E) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}


open Classical in
def quadSign {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (v : Place F) : ℂ :=
  by
    classical
    exact if (placesOver E ({v} : Set (Place F))).ncard = 2 then 1
      else if (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime then -1 else 0

end

end GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.SchurIrreducible (IrrGK)
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts (delta wtK wtExt wtH IsLowestType IsKIntw)
open GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors (Place eulerProd dPart quadSign SatakeBound)
open scoped TensorProduct

namespace GlobalTheory.BlockSizes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rowsP (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1) : ℕ := ⌊DV.aPlusQ D j τ i⌋₊

def rowsM (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).2) : ℕ :=
  ⌊DV.aMinusQ D j τ ((D.R.sigW j).2 - 1 - i)⌋₊

variable {D : D7} (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

def WindowsLe (L : SizeData₂ D) : Prop := L.etaSz ≤ L.sc.b ∧ L.Sc ≤ L.sc.b

end GlobalTheory.BlockSizes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParam
noncomputable section

namespace GlobalTheory.ParamLabel

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.GLq GlobalTheory.GoodCharsCompare GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

variable {p : ℕ} [Fact p.Prime]

theorem isCusp_psi (θ : Fbar p →* ℂ) (hθ : ∀ x y : Fbar p, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) {d k : ℕ} (hd : 0 < d)
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card (ZMod p) ^ i ≡ k [MOD Nat.card (ZMod p) ^ d - 1]) :
    IsCusp (fun x : Gn p d => (-1) ^ (d - 1) *
      psi (rootSum θ k) (Fin d → ZMod p) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod p)))) := by
  classical
  obtain ⟨hch, hip⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular (ZMod p) θ hθ d k hd hk
  have hadd := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod p) θ k).1
  refine ⟨hd, ?_, fun a ha had => ?_⟩
  · have hs := GlobalTheory.T.star_virtualCharacter_eq_apply_inv _ _ (AddSubgroup.subset_closure (k := {χ | BI.IsChar ℂ ℂ χ}) hch)
    obtain ⟨n, ρ, hρ⟩ := hch
    have hρ' : ∀ x, (FDRep.of ρ).character x = (-1) ^ (d - 1) *
      psi (rootSum θ k) (Fin d → ZMod p) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod p))) :=
      fun x => (hρ x).symm
    refine ⟨FDRep.of ρ, ?_, hρ'⟩
    rw [FDRep.simple_iff_char_is_norm_one]
    rw [(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties (ZMod p) d (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype, glCard] at hip
    rw [← hip]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : ((-1 : ℂ) ^ (d - 1)) * ((-1 : ℂ) ^ (d - 1)) = 1 := by
      rw [← mul_pow]; simp
    rw [hρ', hρ', ← hs x, star_mul', star_pow, star_neg, star_one, mul_mul_mul_comm, h1, one_mul]
  · have h := GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive (ZMod p) d _ (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse (ZMod p) (Fin d → ZMod p) _ hadd) a ha had
    rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
    have h2 := congrArg (fun z : ℂ => (-1 : ℂ) ^ (d - 1) * z) h
    simp only [mul_zero, Finset.mul_sum] at h2
    unfold res
    refine mul_eq_zero_of_right _ (Eq.trans ?_ h2)
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ (Formalism.D.Classical.grUnipBlock d a : Set (GL (Fin d) (ZMod p)))
    · rw [if_pos ((GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).1 hu), Set.indicator_of_mem (by exact hu)]
    · rw [if_neg (mt (GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).2 hu), Set.indicator_of_notMem (by exact hu), mul_zero]

theorem thetaOf_gen (L : LabelDatum p) {d : ℕ} (hd : 0 < d) (k : ℕ) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    thetaOf L d (L.gen d ^ k) z = L.teich z ^ k := by
  have hp : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  haveI : NeZero (p ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨n, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hz
  rw [Model.thetaOf_gen_pow L hd (by rw [← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow]),
    ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem torVal_eq {d : ℕ} (hd : 0 < d) (θ : Tor p d →* ℂˣ) (F : Fbar p → ℂ)
    (h : ∀ u : Tor p d, ((θ u : ℂˣ) : ℂ) = F ((u : (Fbar p)ˣ) : Fbar p)) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    torVal θ z = F z := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (g_pow_sub_pos hd).ne'] at hz
    exact zero_ne_one hz
  let u : Tor p d := ⟨Units.mk0 z hz0, (mem_rootsOfUnity _ _).2 (Units.ext (by simpa using hz))⟩
  have hinj : Function.Injective (fun u : Tor p d => ((u : (Fbar p)ˣ) : Fbar p)) :=
    fun a b e => Subtype.ext (Units.ext e)
  exact (hinj.extend_apply (fun u => ((θ u : ℂˣ) : ℂ)) 0 u).trans (h u)

theorem cuspOn_eq_psi {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι) {ω : Fbar p →*₀ ℂ}
    (hω : Function.Injective ω) (θ : Tor p (Fintype.card ι) →* ℂˣ) (k : ℕ)
    (h : ∀ u : Tor p (Fintype.card ι), ((θ u : ℂˣ) : ℂ) = ω ((u : (Fbar p)ˣ) : Fbar p) ^ k) :
    cuspOn θ = fun y : Gn p (Fintype.card ι) => (-1) ^ (Fintype.card ι - 1) *
      psi (rootSum (ω : Fbar p →* ℂ) k) (Fin (Fintype.card ι) → ZMod p) (Matrix.toLin' y.val) := by
  classical
  funext y
  obtain ⟨x, hx, hx'⟩ := exists_preimage hω hd (z := rootC (p ^ Fintype.card ι - 1) ^ k)
    (by rw [← pow_mul, mul_comm, pow_mul, (rootC_prim (g := p) hd).pow_eq_one, one_pow])
  have hM : (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι)).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self]
    exact y.det_ne_zero
  have e1 : cuspOn θ y = cuspVal ω x (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι)) := by
    unfold cuspOn cuspChar cuspVal
    split_ifs with hh
    · obtain ⟨q, m, hq, hm⟩ := hh
      congr 1
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz1 := root_pow hM hq hm (y := z) (Multiset.mem_toFinset.1 hz)
      obtain ⟨a, ha⟩ := exists_log ω hd hz1
      rw [torVal_eq hd θ (fun z => ω z ^ k) h hz1, labelChar_eq ω hd hx ha, hx', ha, ← pow_mul, ← pow_mul,
        mul_comm a k]
      rfl
    · rfl
  rw [e1, GlobalTheory.CuspFormula.cuspVal_eq_psi ω hd hx hx' _ hM,
    ← GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj _ _ _ _ (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (Fintype.equivFin ι)) (Matrix.toLin' y.val)]
  congr 2
  refine LinearMap.ext fun v => ?_
  show Matrix.toLin' (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm y.val) v = _
  rw [Matrix.toLin'_reindex]
  rfl

theorem isCuspOf_cuspOn (L : LabelDatum p) {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p) (hd : 0 < Fintype.card ι) (hL : LabelsChar L θ x)
    (hx : (minpoly (ZMod p) x).natDegree = Fintype.card ι) : IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) := by
  classical
  obtain ⟨hx1, hθ⟩ := hL
  have hp : IsPrimitiveRoot (L.gen (Fintype.card ι)) (p ^ Fintype.card ι - 1) :=
    L.gen_order _ hd ▸ IsPrimitiveRoot.orderOf _
  haveI : NeZero (p ^ Fintype.card ι - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨k, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx1
  have hι : Function.Injective (Units.map L.teich) := fun a b e =>
    Units.ext (L.teich_inj _ _ a.ne_zero b.ne_zero (congrArg Units.val e))
  let f : Fbar p → ℂ := fun x => if h : x = 0 then 0 else ((Units.map L.teich (Units.mk0 x h) : ℂˣ) : ℂ)
  have hf0 : ∀ x (hx : x ≠ 0), f x = ((Units.map L.teich (Units.mk0 x hx) : ℂˣ) : ℂ) := fun x hx => dif_neg hx
  have hfz : f 0 = 0 := dif_pos rfl
  let ω : Fbar p →*₀ ℂ :=
    { toFun := f
      map_zero' := hfz
      map_one' := by
        show f 1 = 1
        rw [hf0 1 one_ne_zero, Units.mk0_one, map_one, Units.val_one]
      map_mul' := by
        intro a b
        show f (a * b) = f a * f b
        by_cases ha : a = 0
        · rw [ha, zero_mul, hfz, zero_mul]
        by_cases hb : b = 0
        · rw [hb, mul_zero, hfz, mul_zero]
        rw [hf0 a ha, hf0 b hb, hf0 (a * b) (mul_ne_zero ha hb), Units.mk0_mul, map_mul,
          Units.val_mul] }
  have hω : Function.Injective ω := by
    intro a b hab
    change f a = f b at hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · exfalso
      rw [ha, hfz, hf0 b hb] at hab
      exact Units.ne_zero _ hab.symm
    · exfalso
      rw [hb, hfz, hf0 a ha] at hab
      exact Units.ne_zero _ hab
    · rw [hf0 a ha, hf0 b hb] at hab
      have h := hι (Units.ext hab)
      simpa using congrArg Units.val h
  have he : ∀ u : (Fbar p)ˣ, ((Units.map L.teich u : ℂˣ) : ℂ) = ω u := by
    intro u
    show _ = f u
    rw [hf0 u u.ne_zero, Units.mk0_val]
  have he' : ∀ z : Fbar p, z ^ (p ^ Fintype.card ι - 1) = 1 → L.teich z = ω z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (g_pow_sub_pos hd).ne'] at hz
      exact zero_ne_one hz
    exact he (Units.mk0 z hz0)
  have e := cuspOn_eq_psi hd hω θ k fun u => by
    have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ Fintype.card ι - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
    rw [hθ, thetaOf_gen L hd k hu, he' _ hu]
  have hc : Nat.card (ZMod p) = p := Nat.card_zmod p
  refine ⟨⟨minpoly.monic (isInt _), minpoly.irreducible (isInt _),
    minpoly.coeff_zero_ne_zero (isInt _) (pow_ne_zero _ (hp.ne_zero (g_pow_sub_pos hd).ne')), hx⟩, ?_, ?_⟩
  · rw [e]
    exact isCusp_psi _ (fun _ _ _ _ h => hω h) hd
      (GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow (ZMod p) _ k (L.gen _) hd (by rw [hc]; exact L.gen_order _ hd) hx)
  · intro x₀ hx₀ y hy z hz
    obtain ⟨j, rfl⟩ := mem_roots_minpoly.1 hx₀
    have hz1 := root_pow y.det_ne_zero hy (pow_one _).symm hz
    rw [Fintype.card_fin] at hz1
    have h := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible (ZMod p) _ _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod p) (ω : Fbar p →* ℂ) k).1
      (Matrix.toLin' y.val) (by rw [Matrix.charpoly_toLin']; exact hy)
    rw [Matrix.charpoly_toLin'] at h
    rw [e]
    show _ * _ = _
    rw [h]
    congr 1
    change ((Formalism.CyclotomicNorms.rootsBar _).map _).sum = _
    have hnd : y.val.charpoly.natDegree = Fintype.card ι := by simp
    rw [GlobalTheory.GreenExists.rootsBar_eq hy ((mem_rootsBar hy.ne_zero).1 hz), hnd, Multiset.map_map]
    have hs := sum_shift (g := p) (z := ω z) (m := k) (e := Fintype.card ι)
      (by rw [mul_comm, pow_mul, ← map_pow, pow_g_of hz1]) j
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hs.symm.trans (Finset.sum_congr rfl fun i _ => ?_))
    · simp only [Function.comp, MonoidHom.coe_coe, map_pow, ← pow_mul, mul_comm]
    · have hzi : (z ^ p ^ i) ^ (p ^ Fintype.card ι - 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
      rw [← pow_mul (L.gen _), thetaOf_gen L hd _ hzi, he' _ hzi, map_pow, ← pow_mul, ← pow_mul]
      congr 1
      ring

theorem isCuspOf_cuspOn_of_green : GlobalTheory.GLq.Green → ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p), 5 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p), 0 < Fintype.card ι → LabelsChar L θ x → (minpoly (ZMod p) x).natDegree = Fintype.card ι → GlobalTheory.GLq.IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) :=
  fun _ _ _ L _ _ _ _ θ x hd hL hx => isCuspOf_cuspOn L θ x hd hL hx

end GlobalTheory.ParamLabel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropic
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

def LaurentConst (h : ℂ → ℂ) (s₀ c : ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Tendsto (fun s => h s - p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 c)


section Interface

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)


variable {O}

end Interface

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Towers

variable (T : ThetaX D)

end Towers

variable (Z : DivX D) (T : ThetaX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)


end GlobalTheory.ThetaInner

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetSeparatingFiniteDimensionalFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetSeparatingFiniteDimensionalFunctions
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory

theorem finiteDim_functions_detected_by_finset (K : Type) (W : Submodule ℂ (K → ℂ))
    (hW : FiniteDimensional ℂ W) :
    ∃ s : Finset K, ∀ w ∈ W, (∀ k ∈ s, w k = 0) → w = 0 := by
  classical
  haveI := hW
  let N : Finset K → Submodule ℂ (K → ℂ) := fun s =>
    W ⊓ ⨅ k ∈ s, LinearMap.ker (LinearMap.proj k : (K → ℂ) →ₗ[ℂ] ℂ)
  have memN : ∀ s w, w ∈ N s ↔ w ∈ W ∧ ∀ k ∈ s, w k = 0 := by
    intro s w
    simp [N, Submodule.mem_iInf]
  have hex : ∃ n, ∃ s : Finset K, Module.finrank ℂ (N s) = n := ⟨_, ∅, rfl⟩
  obtain ⟨s0, hs0⟩ := Nat.find_spec hex
  have hmin : ∀ s : Finset K, Nat.find hex ≤ Module.finrank ℂ (N s) :=
    fun s => Nat.find_min' hex ⟨s, rfl⟩
  have hfin : ∀ s, FiniteDimensional ℂ (N s) := fun s =>
    Submodule.finiteDimensional_of_le (inf_le_left)
  refine ⟨s0, fun w hw hvan => ?_⟩
  have hwN : w ∈ N s0 := (memN s0 w).2 ⟨hw, hvan⟩
  funext k
  have hle : N (insert k s0) ≤ N s0 := by
    intro v hv
    rw [memN] at hv ⊢
    exact ⟨hv.1, fun j hj => hv.2 j (Finset.mem_insert_of_mem hj)⟩
  have heq : N (insert k s0) = N s0 :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hs0]; exact hmin _)
  rw [← heq, memN] at hwN
  exact hwN.2 k (Finset.mem_insert_self k s0)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetSeparatingFiniteDimensionalFunctionsStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_separating_finiteDimensional_functions : ∀ (K : Type) (W : Submodule ℂ (K → ℂ)), FiniteDimensional ℂ W → ∃ s : Finset K, ∀ w ∈ W, (∀ k ∈ s, w k = 0) → w = 0 := by
  first | exact @GlobalTheory.finiteDim_functions_detected_by_finset | exact GlobalTheory.finiteDim_functions_detected_by_finset | (intros; apply GlobalTheory.finiteDim_functions_detected_by_finset <;> assumption)
end
end
