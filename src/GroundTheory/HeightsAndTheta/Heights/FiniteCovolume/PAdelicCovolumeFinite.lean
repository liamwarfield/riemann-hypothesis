module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StReducedBasisBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoerciveOfPositiveDefinite

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicCovolumeFinite
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem archEmbed_injective (h : HermitianForm F E W) (v : Basis ι E W) :
    Function.Injective (archEmbed h v) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have h1 : ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E).map w.embedding = 1 :=
    congrArg
      (fun g : archUnitary h v => (((g : InfinitePlace E → GL ι ℂ) w : GL ι ℂ) : Matrix ι ι ℂ)) hγ
  have h2 : ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) = 1 := by
    ext i j
    have := congrFun (congrFun h1 i) j
    rw [Matrix.map_apply] at this
    apply w.embedding.injective
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : unitaryGroupEquivMatrix h v γ = 1 := Subtype.ext (Units.ext h2)
  rwa [MulEquiv.map_eq_one_iff] at h3

theorem countable_unitaryGroup (h : HermitianForm F E W) (v : Basis ι E W) :
    Countable h.unitaryGroup := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix ι ι E) := inferInstanceAs (Countable (ι → ι → E))
  refine Function.Injective.countable (f := fun γ : h.unitaryGroup =>
    ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E)) ?_
  intro a b hab
  exact (unitaryGroupEquivMatrix h v).injective (Subtype.ext (Units.ext hab))

theorem AdelicCovolumeFinite.proof (h : HermitianForm F E W) (v : Basis ι E W)
    [FiniteDimensional E W] (h₁ : LatticeOrbitsFinite.Statement h)
    (h₂ : ArithmeticCovolumeFinite.Statement h v) (h₃ : ArchimedeanUnitaryEquiv.Statement h v)
    (h₄ : AdelicLatticeDictionary.Statement h v)
    (h₅ : DoubleCosetCovolume.Statement (unitaryPoints F E (gram h.toSesq v) 𝔸[F])
      (archUnitary h v) (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) :
    AdelicCovolumeFinite.Statement h v := by
  classical
  intro μ _
  obtain ⟨ψ, hψ⟩ := h₃
  obtain ⟨K, D, L, hKc, hKo, hLD, hLeq, hLinj⟩ := h₄
  let e : unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ×
      unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) ≃ₜ*
      archUnitary h v × unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) :=
    { toMulEquiv := MulEquiv.prodCongr ψ.toMulEquiv (MulEquiv.refl _)
      continuous_toFun := (ψ.continuous.comp continuous_fst).prodMk continuous_snd
      continuous_invFun := (ψ.symm.continuous.comp continuous_fst).prodMk continuous_snd }
  let Φ := (adeleSplit h v).trans e
  have hΦ₁ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).1 = archEmbed h v γ :=
    fun γ => hψ γ
  have hΦ₂ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).2 =
      (adeleSplit h v (hermitianDiagonal h v γ)).2 := fun γ => rfl
  haveI := countable_unitaryGroup h v
  haveI : Countable (hermitianDiagonal h v).range := by
    refine Function.Surjective.countable (f := fun γ : h.unitaryGroup =>
      (⟨hermitianDiagonal h v γ, γ, rfl⟩ : (hermitianDiagonal h v).range)) ?_
    rintro ⟨_, γ, rfl⟩
    exact ⟨γ, rfl⟩

  obtain ⟨S₀, hS₀, hS₀cov⟩ := h₁ D
  let r : AddSubgroup W → unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) := fun L₀ => if hL : ∃ y, L y = L₀ then hL.choose else 1
  have hr : ∀ y, L (r (L y)) = L y := fun y => by
    have hL : ∃ y', L y' = L y := ⟨y, rfl⟩
    simp only [r, dif_pos hL]
    exact hL.choose_spec

  have hstab : ∀ (γ : h.unitaryGroup) (s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F)),
      γ ∈ latticeStab h (L s) ↔ s⁻¹ * (Φ (hermitianDiagonal h v γ)).2 * s ∈ K := by
    intro γ s
    rw [latticeStab, MulAction.mem_stabilizer_iff, hΦ₂, ← hLeq, eq_comm, hLinj, mul_assoc]
  have hslice : ∀ s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F), sliceGroup Φ (hermitianDiagonal h v).range K s =
      archLatticeGroup h v (L s) := by
    intro s
    ext x
    rw [mem_sliceGroup, archLatticeGroup, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨γ, rfl⟩, hk, rfl⟩
      exact ⟨γ, (hstab γ s).2 hk, (hΦ₁ γ).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨hermitianDiagonal h v γ, ⟨γ, rfl⟩, (hstab γ s).1 hγ, hΦ₁ γ⟩
  obtain ⟨FD, hFD, hfin⟩ := h₅ Φ (hermitianDiagonal h v).range K (hS₀.toFinset.image r) hKc hKo
    (by
      rintro _ ⟨γ, rfl⟩ h1
      rw [hΦ₁, ← (archEmbed h v).map_one] at h1
      rw [archEmbed_injective h v h1, map_one])
    (by
      intro y
      obtain ⟨L₀, hL₀, g, hg⟩ := hS₀cov (L y) (hLD y)
      have hL₀' : L₀ = L ((adeleSplit h v (hermitianDiagonal h v g⁻¹)).2 * y) := by
        rw [hLeq, ← hg, smul_smul, inv_mul_cancel, one_smul]
      have hs : L (r L₀) = L₀ := by rw [hL₀']; exact hr _
      have hk : ((Φ (hermitianDiagonal h v g)).2 * r L₀)⁻¹ * y ∈ K := by
        rw [← hLinj, hΦ₂, hLeq, hs, hg]
      refine ⟨hermitianDiagonal h v g, ⟨g, rfl⟩, r L₀, ?_, _, hk, ?_⟩
      · exact Finset.mem_image_of_mem r (hS₀.mem_toFinset.2 hL₀)
      · group)
    (by
      intro s _ μ₁ _
      rw [hslice s]
      exact h₂ μ₁ D (L s) (hLD s))
    μ
  exact ⟨FD, hFD, hfin⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticePointsBelowFinite
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

theorem exists_coercive_of_posDef {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ι → ℂ) (j : ι), c * ‖z j‖ ^ 2 ≤ (star z ⬝ᵥ (P *ᵥ z)).re :=
  _root_.UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef hP

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem exists_coord_le_len {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (g : archUnitary h v) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : InfinitePlace E → ι → ℂ) w i,
      ‖y w i‖ ≤ K * M.len (invApply g y) := by
  choose c hc hcoer using fun w => exists_coercive_of_posDef (M.posDef w)
  set G : InfinitePlace E → Matrix ι ι ℂ := fun w =>
    (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) with hG
  refine ⟨∑ w, ∑ i, ∑ j, ‖G w i j‖ / Real.sqrt (c w), by positivity, fun y w i => ?_⟩
  set z := invApply g y with hz
  have hre : ∀ w', 0 ≤ (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re := fun w' =>
    (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (z w'))).1
  have hinv : G w * (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
    simp [hG]
  have hy : y w = G w *ᵥ z w := by
    rw [hz, invApply, mulVec_mulVec, hinv, one_mulVec]
  have hzj : ∀ j, ‖z w j‖ ≤ M.len z / Real.sqrt (c w) := by
    intro j
    have hsq : 0 < Real.sqrt (c w) := Real.sqrt_pos.2 (hc w)
    rw [le_div_iff₀ hsq]
    have h1 : c w * ‖z w j‖ ^ 2 ≤ ∑ w', (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re :=
      (hcoer w (z w) j).trans (Finset.single_le_sum (fun w' _ => hre w') (Finset.mem_univ w))
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_mul (hc w).le, Real.sqrt_sq (norm_nonneg _)] at h2
    unfold Majorant.len
    linarith
  have hlen : 0 ≤ M.len z := Real.sqrt_nonneg _
  calc ‖y w i‖ = ‖∑ j, G w i j * z w j‖ := by rw [hy]; rfl
    _ ≤ ∑ j, ‖G w i j‖ * ‖z w j‖ := (norm_sum_le _ _).trans (by simp)
    _ ≤ ∑ j, ‖G w i j‖ / Real.sqrt (c w) * M.len z := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [div_mul_eq_mul_div, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hzj j) (norm_nonneg _)
    _ = (∑ j, ‖G w i j‖ / Real.sqrt (c w)) * M.len z := by rw [Finset.sum_mul]
    _ ≤ (∑ w', ∑ i', ∑ j, ‖G w' i' j‖ / Real.sqrt (c w')) * M.len z := by
        refine mul_le_mul_of_nonneg_right ?_ hlen
        refine le_trans ?_ (Finset.single_le_sum (f := fun w' => ∑ i', ∑ j,
          ‖G w' i' j‖ / Real.sqrt (c w')) (fun _ _ => by positivity) (Finset.mem_univ w))
        exact Finset.single_le_sum (f := fun i' => ∑ j, ‖G w i' j‖ / Real.sqrt (c w))
          (fun _ _ => by positivity) (Finset.mem_univ i)


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LatticePointsBelowFinite.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    LatticePointsBelowFinite.Statement h v := by
  classical
  intro M La g t hLa
  obtain ⟨S, hS⟩ := hLa.fg

  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)
  let T : AddSubgroup W :=
    { carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)}
      add_mem' := fun {a b} ha hb i => by
        simpa only [map_add (f := _), Finsupp.add_apply, smul_add] using (ha i).add (hb i)
      zero_mem' := fun i => by
        simpa only [map_zero, Finsupp.zero_apply, smul_zero] using isIntegral_zero
      neg_mem' := fun {a} ha i => by
        simpa only [map_neg, Finsupp.neg_apply, smul_neg] using (ha i).neg }
  have hLaT : La ≤ T := by
    have hall : ∀ s : La, (s : W) ∈ T := by
      intro s
      have hmem : s ∈ AddSubsemigroup.closure (S : Set La) := by
        rw [hS]
        trivial
      induction hmem using AddSubsemigroup.closure_induction with
      | mem s hs =>
        intro i
        exact hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
      | add a b _ _ ha hb => exact T.add_mem ha hb
    intro x hx
    exact hall ⟨x, hx⟩
  have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.2 hd0

  obtain ⟨K, hK0, hK⟩ := exists_coord_le_len M g
  set B : ℝ := |(d : ℝ)| * (K * t) with hB
  set A : Set E := {a | IsIntegral ℤ a ∧ ∀ φ : E →+* ℂ, ‖φ a‖ ≤ B} with hA
  have hAfin : A.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ B
  set φ : W → ι → E := fun x i => d • v.repr x i with hφ
  have hinj : Function.Injective φ := by
    intro x y hxy
    refine v.repr.injective (Finsupp.ext fun i => ?_)
    have := congrFun hxy i
    simp only [hφ, zsmul_eq_mul] at this
    exact mul_left_cancel₀ hdE this
  refine ((Set.Finite.pi (t := fun _ : ι => A) fun _ => hAfin).preimage hinj.injOn).subset ?_
  rintro x ⟨hx, hxt⟩ i -
  refine ⟨hLaT hx i, fun ψ => ?_⟩
  have hw : ‖ψ (v.repr x i)‖ = ‖(InfinitePlace.mk ψ).embedding (v.repr x i)‖ := by
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
  have hb := hK (vecAt v x) (InfinitePlace.mk ψ) i
  change ‖ψ (d • v.repr x i)‖ ≤ B
  rw [zsmul_eq_mul, map_mul, map_intCast, norm_mul, Complex.norm_intCast, hw, hB]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_left hxt.le hK0)

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArithmeticCovolumeFinite
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_len_invApply {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (invApply g y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => invApply g y w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_)
  exact (hw w).star.dotProduct (continuous_const.matrix_mulVec (hw w))

theorem ArithmeticCovolumeFinite.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ScalingLaw.Statement h v) (h₂ : MahlerCompactness.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : ShortestVectorIndex.Statement h v)
    (h₅ : IntegralFamilyBound.Statement E) (h₆ : MajorantExists.Statement h v)
    (h₈ : ArchLatticeDiscrete.Statement h v) (h₉ : LatticePointsBelowFinite.Statement h v) :
    ArithmeticCovolumeFinite.Statement h v := by
  classical
  intro μ _ D La hLa
  obtain ⟨M⟩ := h₆

  obtain ⟨r, a, ha, har⟩ := h₅
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]
  have ha' : ∃ b : Fin (2 * finrank ℚ F) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg.symm, ha.comp _ (Fin.cast_injective _), fun i σ => har _ σ⟩
  set C₀ : ℕ := ⌊(r * Real.sqrt (2 * finrank ℚ F)) ^ (2 * finrank ℚ F)⌋₊ with hC₀

  set VV : Set W := {x | x ∈ La ∧ x ≠ 0 ∧ h.toSesq x x = 0 ∧ lineIndex E La x ≤ C₀} with hVV
  have hstable : ∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV := by
    intro γ hγ x hx
    have hγ' : γ • La = La := MulAction.mem_stabilizer_iff.1 hγ
    refine ⟨?_, fun h0 => hx.2.1 ((smul_eq_zero_iff_eq γ).1 h0), ?_, ?_⟩
    · have h1 : γ • x ∈ γ • La := AddSubgroup.smul_mem_pointwise_smul _ _ _ hx.1
      rwa [hγ'] at h1
    · rw [← hx.2.2.1]
      exact HermitianForm.mem_unitaryGroup.1 γ.2 x x
    · rw [GaussianPlane.lineIndex_smul hγ']
      exact hx.2.2.2
  obtain ⟨FD, hFD, hm⟩ := h₁ M μ D La VV hLa (fun x hx => hx.1) (fun x hx => ⟨hx.2.1, hx.2.2.1⟩)
    hstable ⟨C₀, fun x hx => hx.2.2.2⟩
  refine ⟨FD, hFD, ?_⟩

  set B : Set (archUnitary h v) :=
    ⋃ x : W, ⋃ (_ : x ∈ La ∧ x ≠ 0), {g | M.len (invApply g (vecAt v x)) < 1} with hB
  have hBmeas : MeasurableSet B :=
    (isOpen_iUnion fun x => isOpen_iUnion fun _ =>
      isOpen_lt (continuous_len_invApply M _) continuous_const).measurableSet
  have hBle : μ (FD ∩ B) ≤ massBelow M μ FD VV 1 := by
    rw [Set.inter_comm, ← Measure.restrict_apply hBmeas, ← lintegral_indicator_one hBmeas]
    refine lintegral_mono fun g => ?_
    by_cases hg : g ∈ B
    · rw [Set.indicator_of_mem hg, Pi.one_apply]
      obtain ⟨x₁, hx₁⟩ := Set.mem_iUnion.1 hg
      obtain ⟨⟨hx₁La, hx₁0⟩, hx₁lt⟩ := Set.mem_iUnion.1 hx₁
      set S : Set W := {x | x ∈ La ∧ M.len (invApply g (vecAt v x)) < 1} ∩ {x | x ≠ 0}
      have hSfin : S.Finite := (h₉ M La g 1 hLa.isLattice).inter_of_left _
      obtain ⟨x, hxS, hxmin⟩ := Set.exists_min_image S (fun x => M.len (invApply g (vecAt v x)))
        hSfin ⟨x₁, ⟨hx₁La, hx₁lt⟩, hx₁0⟩
      obtain ⟨⟨hxLa, hxlt⟩, hx0⟩ := hxS
      have hshort : ∀ y ∈ La, y ≠ 0 →
          M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y)) := by
        intro y hy hy0
        by_cases hylt : M.len (invApply g (vecAt v y)) < 1
        · exact hxmin y ⟨⟨hy, hylt⟩, hy0⟩
        · exact hxlt.le.trans (not_lt.1 hylt)
      have hxVV : x ∈ VV := by
        refine ⟨hxLa, hx0, h₃ M D La g x hLa hxLa hxlt, ?_⟩
        exact Nat.le_floor (h₄ M r ha' D La g x hLa hxLa hx0 hshort)
      have hne : ({y ∈ VV | M.len (invApply g (vecAt v y)) < 1}).Nonempty := ⟨x, hxVV, hxlt⟩
      unfold countBelow
      rw [← ENat.toENNReal_one, ENat.toENNReal_le]
      exact Set.one_le_encard_iff_nonempty.2 hne
    · rw [Set.indicator_of_notMem hg]
      exact bot_le

  obtain ⟨S, hS, K, hK, hMah⟩ := h₂ M D 1 one_pos
  have : DiscreteTopology (archLatticeGroup h v La) := h₈ La hLa.isLattice
  have : Countable (archLatticeGroup h v La) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let c : AddSubgroup W → h.unitaryGroup := fun L =>
    if hL : ∃ γ : h.unitaryGroup, γ • La = L then hL.choose else 1
  set K' : Set (archUnitary h v) :=
    ⋃ L ∈ S, (fun k => (archEmbed h v (c L))⁻¹ * k) '' K with hK'
  have hK'c : IsCompact K' :=
    hS.isCompact_biUnion fun L _ => hK.image (continuous_const.mul continuous_id)
  have hcover : FD ∩ Bᶜ ⊆ ⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD := by
    rintro g ⟨hgFD, hgB⟩
    have hlam : ∀ x ∈ La, x ≠ 0 → (1 : ℝ) ≤ M.len (invApply g (vecAt v x)) := by
      intro x hx hx0
      by_contra hlt
      exact hgB (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨⟨hx, hx0⟩, not_le.1 hlt⟩⟩)
    obtain ⟨γ, hγS, hγK⟩ := hMah La g hLa hlam
    have hL : ∃ γ' : h.unitaryGroup, γ' • La = γ • La := ⟨γ, rfl⟩
    have hcL : c (γ • La) • La = γ • La := by
      simp only [c, dif_pos hL]
      exact hL.choose_spec
    have hstab : γ⁻¹ * c (γ • La) ∈ latticeStab h La := by
      change (γ⁻¹ * c (γ • La)) • La = La
      rw [mul_smul, hcL, inv_smul_smul]
    refine Set.mem_iUnion.2 ⟨⟨archEmbed h v (γ⁻¹ * c (γ • La)), Subgroup.mem_map_of_mem _ hstab⟩,
      ?_, hgFD⟩
    refine Set.mem_smul_set.2 ⟨(archEmbed h v (c (γ • La)))⁻¹ * (archEmbed h v γ * g),
      Set.mem_biUnion hγS ⟨_, hγK, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, smul_eq_mul]
    simp only [map_mul, map_inv]
    group
  have hAlt : μ (FD ∩ Bᶜ) < ⊤ := by
    calc μ (FD ∩ Bᶜ) ≤ μ (⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD) := measure_mono hcover
      _ ≤ ∑' δ : archLatticeGroup h v La, μ (δ • K' ∩ FD) := measure_iUnion_le _
      _ = μ K' := (hFD.measure_eq_tsum K').symm
      _ < ⊤ := hK'c.measure_lt_top
  calc μ FD = μ ((FD ∩ B) ∪ (FD ∩ Bᶜ)) := by rw [Set.inter_union_compl]
    _ ≤ μ (FD ∩ B) + μ (FD ∩ Bᶜ) := measure_union_le _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hBle.trans_lt (hm 1 one_pos).1, hAlt⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantTransport
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped MatrixOrder ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MajorantTransport

theorem exists_conjTranspose_mul_self {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ X : Matrix ι ι ℂ, Xᴴ * X = P := by
  refine ⟨CFC.sqrt P, ?_⟩
  rw [(CFC.sqrt_nonneg P).posSemidef.isHermitian.eq]
  exact CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg

theorem measurePreserving_mulVec {A : Matrix ι ι ℂ} (hA : Complex.normSq A.det = 1) :
    MeasurePreserving (fun z : ι → ℂ => A *ᵥ z) volume volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' A).restrictScalars ℝ
  have hdet : LinearMap.det f = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hA]
  have hcoe : (⇑f) = fun z : ι → ℂ => A *ᵥ z := by
    funext z; simp [f]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (ι → ℂ)))
    (f := f) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, hcoe] at hmap
  have hm := (LinearMap.continuous_of_finiteDimensional f).measurable
  rw [hcoe] at hm
  refine ⟨hm, ?_⟩
  simpa using hmap


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem normSq_det (h : HermitianForm F E W) (v : Basis ι E W) (g : archUnitary h v)
    (w : InfinitePlace E) : Complex.normSq ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ).det = 1 := by
  have hg := mem_archUnitary.mp g.2 w
  have hH : (gramAt h v w).det ≠ 0 := by
    simp only [gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact ((isUnit_det_gram h v).map w.embedding).ne_zero
  set G : Matrix ι ι ℂ := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  rw [show (G.map ⇑(starRingEnd ℂ))ᵀ = Gᴴ from rfl] at hg
  have h1 := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_conjTranspose, show star G.det = starRingEnd ℂ G.det from rfl] at h1
  have h2 : starRingEnd ℂ G.det * G.det = 1 := by
    apply mul_right_cancel₀ hH
    linear_combination h1
  have h3 : (Complex.normSq G.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self, h2]
  exact_mod_cast h3

def sqrtMap (Q : InfinitePlace E → Matrix ι ι ℂ) :
    (InfinitePlace E → ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (InfinitePlace E × ι) where
  toFun y := WithLp.toLp 2 (fun p => (Q p.1 *ᵥ y p.1) p.2)
  map_add' y z := by ext p; simp [mulVec_add]
  map_smul' c y := by ext p; simp [mulVec_smul]


omit [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem norm_sq_sqrtMap (Q : InfinitePlace E → Matrix ι ι ℂ) (y : InfinitePlace E → ι → ℂ) :
    ‖sqrtMap Q y‖ ^ 2 = ∑ w, (star (y w) ⬝ᵥ (((Q w)ᴴ * Q w) *ᵥ y w)).re := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [sqrtMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, dotProduct, Pi.star_apply,
    Complex.re_sum, Complex.star_def, Complex.conj_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_cast


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem exists_isometry {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v) :
    ∃ (d : ℕ) (S : (InfinitePlace E → ι → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin d)),
      ∀ y, ‖S y‖ = M.len y := by
  choose Q hQ using fun w => exists_conjTranspose_mul_self (M.posDef w)
  have hnorm : ∀ y, ‖sqrtMap Q y‖ = M.len y := by
    intro y
    rw [Majorant.len, ← Real.sqrt_sq (norm_nonneg (sqrtMap Q y)), norm_sq_sqrtMap]
    simp only [hQ]
  have hinj : Function.Injective (sqrtMap Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∑ w, (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re = 0 := by
      have := norm_sq_sqrtMap Q y
      simp only [hQ, hy, norm_zero] at this
      linarith
    have hnn : ∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re := fun w =>
      (Complex.nonneg_iff.mp ((M.posDef w).posSemidef.dotProduct_mulVec_nonneg (y w))).1
    funext w
    by_contra hw
    have hpos := (Complex.lt_def.mp ((M.posDef w).dotProduct_mulVec_pos hw)).1
    have := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hnn w).mp h0 w (Finset.mem_univ _)
    simp only [Complex.zero_re] at hpos
    linarith
  have hdim : finrank ℂ (InfinitePlace E → ι → ℂ) =
      finrank ℂ (EuclideanSpace ℂ (InfinitePlace E × ι)) := by
    simp [Module.finrank_pi_fintype, finrank_euclideanSpace, Fintype.card_prod]
  let e : (InfinitePlace E → ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (InfinitePlace E × ι) :=
    LinearEquiv.ofBijective (sqrtMap Q)
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℂ (InfinitePlace E × ι))
  refine ⟨_, (e.restrictScalars ℝ).toContinuousLinearEquiv.trans b.repr.toContinuousLinearEquiv,
    fun y => ?_⟩
  simp only [ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map]
  exact hnorm y

def invApplyEquiv {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v) :
    (InfinitePlace E → ι → ℂ) ≃L[ℝ] (InfinitePlace E → ι → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := invApply g
      invFun := invApply g⁻¹
      map_add' := fun y z => by funext w; simp [invApply, mulVec_add]
      map_smul' := fun c y => by funext w; simp [invApply, mulVec_smul]
      left_inv := fun y => by funext w; simp [invApply, mulVec_mulVec]
      right_inv := fun y => by funext w; simp [invApply, mulVec_mulVec] }


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem measurePreserving_invApply {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) : MeasurePreserving (invApply g) volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume)
    (fun w => measurePreserving_mulVec (normSq_det h v g⁻¹ w))

end MajorantTransport


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantTransport.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantTransport.Statement h v := by
  intro M
  have : (volume : Measure (InfinitePlace E → ι → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  obtain ⟨d, S, hS⟩ := MajorantTransport.exists_isometry M
  set c := Measure.addHaarScalarFactor (Measure.map S.symm volume)
    (volume : Measure (InfinitePlace E → ι → ℂ))
  have hc : Measure.map S.symm volume = c • (volume : Measure (InfinitePlace E → ι → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul (Measure.map S.symm volume) volume
  refine ⟨d, c, fun g => ⟨(MajorantTransport.invApplyEquiv g).trans S, fun y => hS _,
    fun L _ _ => ?_⟩⟩
  set T := (MajorantTransport.invApplyEquiv g).trans S
  have hT : MeasurePreserving T.symm volume (Measure.map T.symm volume) :=
    T.symm.continuous.measurable.measurePreserving _
  rw [ZLattice.covolume_comap L (Measure.map T.symm volume) volume hT]
  have hsymm : ⇑(MajorantTransport.invApplyEquiv g).symm = invApply g⁻¹ := rfl
  have hmap : Measure.map T.symm volume = c • (volume : Measure (InfinitePlace E → ι → ℂ)) := by
    have hcomp : ⇑T.symm = (MajorantTransport.invApplyEquiv g).symm ∘ S.symm := rfl
    rw [hcomp, ← Measure.map_map (MajorantTransport.invApplyEquiv g).symm.continuous.measurable
      S.symm.continuous.measurable, hc,
      Measure.map_smul c (MajorantTransport.invApplyEquiv g).symm.continuous.measurable.aemeasurable, hsymm,
      (MajorantTransport.measurePreserving_invApply g⁻¹).map_eq]
  let b := Module.Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L _ (ZLattice.isAddFundamentalDomain b _),
    ZLattice.covolume_eq_measure_fundamentalDomain L volume
      (ZLattice.isAddFundamentalDomain b volume), hmap, measureReal_nnreal_smul_apply]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIsotropicScaling
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

namespace IsotropicScaling

section Maps

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def scalingMap (h : HermitianForm F E W) (v w : W) (α β : E) : W →ₗ[E] W :=
  LinearMap.id + α • (h.toSesq w).smulRight v + β • (h.toSesq v).smulRight w

variable (h : HermitianForm F E W) {v w : W}

theorem scalingMap_apply (α β : E) (x : W) :
    scalingMap h v w α β x = x + (α * h.toSesq w x) • v + (β * h.toSesq v x) • w := by
  simp [scalingMap, mul_smul]

theorem scalingMap_zero : scalingMap h v w 0 0 = LinearMap.id := by
  simp [scalingMap]

theorem pairing_left (hww : h.toSesq w w = 0) (hwv : h.toSesq w v = 1) (α β : E) (x : W) :
    h.toSesq w (scalingMap h v w α β x) = (1 + α) * h.toSesq w x := by
  rw [scalingMap_apply, map_add (f := _), map_add (f := _), map_smul, map_smul, hwv, hww, smul_eq_mul, smul_eq_mul]
  ring

theorem pairing_right (hvv : h.toSesq v v = 0) (hvw : h.toSesq v w = 1) (α β : E) (x : W) :
    h.toSesq v (scalingMap h v w α β x) = (1 + β) * h.toSesq v x := by
  rw [scalingMap_apply, map_add (f := _), map_add (f := _), map_smul, map_smul, hvv, hvw, smul_eq_mul, smul_eq_mul]
  ring

variable (hvv : h.toSesq v v = 0) (hww : h.toSesq w w = 0) (hvw : h.toSesq v w = 1)
  (hwv : h.toSesq w v = 1)
include hvv hww hvw hwv

theorem scalingMap_comp (α β α' β' : E) :
    scalingMap h v w α β ∘ₗ scalingMap h v w α' β' =
      scalingMap h v w (α + α' + α * α') (β + β' + β * β') := by
  ext x
  rw [LinearMap.comp_apply, scalingMap_apply h α β, pairing_left h hww hwv,
    pairing_right h hvv hvw, scalingMap_apply, scalingMap_apply]
  module

theorem scalingMap_isometry {α β : E} (hαβ : α + conj F E β + α * conj F E β = 0) (x y : W) :
    h.toSesq (scalingMap h v w α β x) (scalingMap h v w α β y) = h.toSesq x y := by
  have hαβ' : conj F E α + β + conj F E α * β = 0 := by
    simpa [conj_conj] using congrArg (conj F E) hαβ
  have hc : ∀ z, conjHom F E z = conj F E z := fun _ => rfl
  have hxv : h.toSesq x v = conj F E (h.toSesq v x) := (h.isSymm.eq v x).symm
  have hxw : h.toSesq x w = conj F E (h.toSesq w x) := (h.isSymm.eq w x).symm
  rw [scalingMap_apply, scalingMap_apply]
  simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hvv, hww, hvw, hwv, hxv, hxw, hc, map_mul]
  linear_combination (h.toSesq w y * conj F E (h.toSesq v x)) * hαβ +
    (h.toSesq v y * conj F E (h.toSesq w x)) * hαβ'

end Maps

theorem sub_one_add_inv_sub_one_add_mul_eq_zero {E : Type*} [Field E] {u : E} (hu : u ≠ 0) :
    u - 1 + (u⁻¹ - 1) + (u - 1) * (u⁻¹ - 1) = 0 := by
  field_simp
  ring

section Lattice

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem exists_nsmul_mem {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ La := by
  let S : Submodule E W :=
    { carrier := {w | ∃ N : ℕ, 0 < N ∧ N • w ∈ La}
      add_mem' := by
        rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
        refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
        rw [smul_add, mul_smul, mul_comm, mul_smul]
        exact add_mem (La.nsmul_mem ha N) (La.nsmul_mem hb M)
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c a ⟨N, hN, ha⟩
        have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
        obtain ⟨m, s, hm, hs⟩ := hc.exists_nsmul_eq (𝓞 E)
        refine ⟨m * N, Nat.mul_pos (Nat.pos_of_ne_zero hm) hN, ?_⟩
        have : (m * N) • (c • a) = (algebraMap (𝓞 E) E s) • (N • a) := by
          rw [← hs]
          module
        rw [this]
        exact hLa.smul_mem s _ ha }
  have hS : Submodule.span E (La : Set W) ≤ S :=
    Submodule.span_le.2 fun x hx => ⟨1, one_pos, by simpa using hx⟩
  exact (hS (hLa.span_eq_top ▸ Submodule.mem_top : w ∈ Submodule.span E (La : Set W)))

omit [NumberField E] in
theorem conj_mem_integralClosure {z : E}
    (hz : z ∈ integralClosure ℤ E) : conj F E z ∈ integralClosure ℤ E :=
  IsIntegral.map ((conj F E : E ≃ₐ[F] E) : E →+* E).toIntAlgHom hz


omit [NumberField E] in
theorem scalingMap_mem (h : HermitianForm F E W) {La : AddSubgroup W} (hLa : IsLattice E La)
    (hint : IsIntegralOn h La) {v w : W} (hv : v ∈ La) {N : ℕ} (hNw : N • w ∈ La)
    {u : (𝓞 E)ˣ} (hu : u ∈ congruenceUnits E N) {x : W} (hx : x ∈ La) :
    scalingMap h v w (((u : 𝓞 E) : E) - 1) ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) x ∈ La := by
  have smem : ∀ z ∈ integralClosure ℤ E, ∀ y ∈ La, z • y ∈ La :=
    fun z hz y hy => hLa.smul_mem ⟨z, hz⟩ y hy
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (mem_congruenceUnits.1 hu)
  have ht' : ((u : 𝓞 E) : E) - 1 = (t : E) * N := by exact_mod_cast ht.symm
  have hu0 : conj F E ((u : 𝓞 E) : E) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast u.ne_zero
  have hinv : (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((u : 𝓞 E) : E)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    exact_mod_cast u.inv_mul
  have hN : h.toSesq (N • w) x = N * h.toSesq w x := by
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  have e2 : ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) * h.toSesq v x =
      (-conj F E (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * conj F E (t : E) * h.toSesq v x) * N := by
    have hct : conj F E ((u : 𝓞 E) : E) - 1 = conj F E (t : E) * N := by
      rw [← map_one (conj F E), ← map_sub, ht', map_mul, map_natCast]
    rw [hinv, map_inv₀]
    field_simp
    linear_combination (-h.toSesq v x) * hct
  have key : scalingMap h v w (((u : 𝓞 E) : E) - 1) ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) x =
      x + ((t : E) * h.toSesq (N • w) x) • v +
        (-conj F E (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * conj F E (t : E) * h.toSesq v x) • (N • w) := by
    rw [scalingMap_apply, e2, ht', hN, ← Nat.cast_smul_eq_nsmul E]
    module
  rw [key]
  refine add_mem (add_mem hx (smem _ ?_ v hv)) (smem _ ?_ _ hNw)
  · exact mul_mem t.2 (hint _ hNw x hx)
  · exact mul_mem (mul_mem (neg_mem (conj_mem_integralClosure (u⁻¹ : (𝓞 E)ˣ).val.2))
      (conj_mem_integralClosure t.2)) (hint v hv x hx)

end Lattice

section Main

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem proof (h : HermitianForm F E W) (h₁ : WittPartner.Statement h) :
    IsotropicScaling.Statement h := by
  intro La x₀ hLa hint hx₀ hne hiso
  obtain ⟨w₀, hvw, hww⟩ := h₁ x₀ hne hiso
  have hwv : h.toSesq w₀ x₀ = 1 := by rw [← h.isSymm.eq x₀ w₀, hvw, map_one]
  obtain ⟨N, hN, hNw⟩ := exists_nsmul_mem hLa w₀
  refine ⟨N, hN, fun ε hε => ?_⟩
  have he : ((ε : 𝓞 E) : E) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hce : conj F E ((ε : 𝓞 E) : E) ≠ 0 := (map_ne_zero _).2 he
  have hinv : (((ε⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((ε : 𝓞 E) : E)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by exact_mod_cast ε.inv_mul)
  set e : E := ((ε : 𝓞 E) : E)
  have hcinv : (conj F E e⁻¹)⁻¹ = conj F E e := by rw [map_inv₀, inv_inv]
  have k1 : e - 1 + (e⁻¹ - 1) + (e - 1) * (e⁻¹ - 1) = 0 := sub_one_add_inv_sub_one_add_mul_eq_zero he
  have k2 : (conj F E e)⁻¹ - 1 + (conj F E e - 1) + ((conj F E e)⁻¹ - 1) * (conj F E e - 1) = 0 := by
    have := sub_one_add_inv_sub_one_add_mul_eq_zero (inv_ne_zero hce); rwa [inv_inv] at this
  have k3 : e⁻¹ - 1 + (e - 1) + (e⁻¹ - 1) * (e - 1) = 0 := by
    have := sub_one_add_inv_sub_one_add_mul_eq_zero (inv_ne_zero he); rwa [inv_inv] at this
  have k4 : conj F E e - 1 + ((conj F E e)⁻¹ - 1) + (conj F E e - 1) * ((conj F E e)⁻¹ - 1) = 0 :=
    sub_one_add_inv_sub_one_add_mul_eq_zero hce
  have h1 : scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) ∘ₗ
      scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) = LinearMap.id := by
    rw [scalingMap_comp h hiso hww hvw hwv, k1, k2, scalingMap_zero]
  have h2 : scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) ∘ₗ
      scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) = LinearMap.id := by
    rw [scalingMap_comp h hiso hww hvw hwv, k3, k4, scalingMap_zero]
  let γ : W ≃ₗ[E] W := LinearEquiv.ofLinearMap _ _ h1 h2
  have hγU : γ ∈ h.unitaryGroup := HermitianForm.mem_unitaryGroup.2 fun x y =>
    scalingMap_isometry h hiso hww hvw hwv
      (by rw [map_sub, map_inv₀, conj_conj, map_one]; exact k1) x y
  have memT : ∀ x ∈ La, scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) x ∈ La :=
    fun x hx => scalingMap_mem h hLa hint hx₀ hNw hε hx
  have memT' : ∀ x ∈ La, scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) x ∈ La := fun x hx => by
    have := scalingMap_mem h hLa hint hx₀ hNw (inv_mem hε) hx
    rwa [hinv, hcinv] at this
  refine ⟨⟨γ, hγU⟩, ?_, ?_⟩
  · rw [latticeStab, MulAction.mem_stabilizer_iff]
    ext y
    refine ⟨fun hy => ?_, fun hy => ⟨_, memT' y hy, ?_⟩⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      exact memT x hx
    change scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1)
      (scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) y) = y
    rw [← LinearMap.comp_apply, h1, LinearMap.id_apply]
  · change scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) x₀ = e • x₀
    rw [scalingMap_apply, hwv, hiso]
    module

end Main

end IsotropicScaling

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
