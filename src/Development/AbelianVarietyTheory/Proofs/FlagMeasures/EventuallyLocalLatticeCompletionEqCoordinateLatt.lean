module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExistsHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicU.Cofinite

open Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_mem_intLoc_iff_repr {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] E, y ∈ intLoc F E v ↔
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F := by
  classical
  set ω := Module.Free.chooseBasis ℤ (𝓞 E) with hω
  have hI : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E), z ∈ intLoc F E v ↔
      z ∈ AddSubgroup.closure {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E,
        z = a ⊗ₜ[F] (x : E)} := fun _ _ => Iff.rfl
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ j k,
      algebraMap F (Fv F v) (b.repr ((ω j : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    intro j k
    exact eventually_algebraMap_mem_integers _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ k,
      (1 : Fv F v) ⊗ₜ[F] b k ∈ intLoc F E v := by
    rw [Filter.eventually_all]
    intro k
    exact eventually_one_tmul_mem_intLoc _
  filter_upwards [h1, h2] with v h1 h2 y
  have key : ∀ (x : 𝓞 E) (k : Fin d),
      algebraMap F (Fv F v) (b.repr (x : E) k) ∈ v.adicCompletionIntegers F := by
    intro x k
    have hx : (x : E) = ∑ j, (ω.repr x j) • ((ω j : 𝓞 E) : E) := by
      have := congrArg (algebraMap (𝓞 E) E) (ω.sum_repr x)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simp only [map_zsmul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (h1 j k) _
  constructor
  · intro hy
    rw [hI] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      intro k
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul]
      exact mul_mem ha (key x k)
    | zero => intro k; simp
    | add z w _ _ hz hw =>
      intro k
      rw [map_add (f := _), Finsupp.add_apply]
      exact add_mem (hz k) (hw k)
    | neg z _ hz =>
      intro k
      rw [map_neg, Finsupp.neg_apply]
      exact neg_mem (hz k)
  · intro hy
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
    refine sum_mem fun k _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.smul_def]
    refine mul_mem ?_ (h2 k)
    rw [hI]
    refine AddSubgroup.subset_closure ⟨_, hy k, 1, ?_⟩
    simp [Algebra.TensorProduct.algebraMap_apply]

theorem eventually_latLoc_eq_latV :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
      (b : Module.Basis (Fin d) F E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L →
      ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} = latV b v := by
  intro F E _ _ _ _ _ n d b L hL
  have : Submodule.IsFullLattice E L := hL
  have : Submodule.IsFullLattice E (stdLattice E n) := isLattice_stdLattice
  filter_upwards [eventually_latLoc_eq F L (stdLattice E n), eventually_mem_intLoc_iff_repr b]
    with v hv h1
  have hI : ∀ z : Fv F v ⊗[F] E, z ∈ intLoc F E v ↔
      z ∈ AddSubgroup.closure {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E,
        z = a ⊗ₜ[F] (x : E)} := fun _ => Iff.rfl
  have hS : ∀ y : Fin n → Fv F v ⊗[F] E, y ∈ latLoc F (stdLattice E n) v ↔
      y ∈ AddSubgroup.closure {y : Fin n → Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F,
        ∃ x ∈ stdLattice E n, y = fun i => a ⊗ₜ[F] x i} := fun _ => Iff.rfl
  have hstd : ∀ x : Fin n → E, x ∈ stdLattice E n ↔ ∀ i, ∃ z : 𝓞 E, (z : E) = x i := by
    intro x
    unfold stdLattice Formalism.UG.stdLat
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
      Algebra.linearMap_apply]
  have hloc : ∀ y, y ∈ latLoc F (stdLattice E n) v ↔ ∀ i, y i ∈ intLoc F E v := by
    intro y
    constructor
    · intro hy i
      rw [hS] at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        obtain ⟨w, hw⟩ := (hstd x).1 hx i
        rw [hI]
        exact AddSubgroup.subset_closure ⟨a, ha, w, by rw [hw]⟩
      | zero => exact zero_mem _
      | add z w _ _ hz hw => exact add_mem hz hw
      | neg z _ hz => exact neg_mem hz
    · intro hy
      rw [← Finset.univ_sum_single y, hS]
      refine sum_mem fun i _ => ?_
      have hyi := hy i
      rw [hI] at hyi
      revert hyi
      generalize y i = z0
      intro hyi
      induction hyi using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : E), (hstd _).2 fun j => ?_, ?_⟩
        · by_cases h : j = i
          · subst h
            exact ⟨x, by simp⟩
          · exact ⟨0, by simp [h]⟩
        · funext j
          by_cases h : j = i
          · subst h
            simp
          · simp [h]
      | zero => simp
      | add z w _ _ hz hw =>
        rw [Pi.single_add]
        exact add_mem hz hw
      | neg z _ hz =>
        rw [Pi.single_neg]
        exact neg_mem hz
  ext X
  unfold latV
  simp only [Set.mem_ofPred_eq, hv, hloc, h1, Fin.forall_fin_one]

end GlobalTheory.AdelicU.Cofinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLattStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_localLatticeCompletion_eq_coordinateLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (b : Module.Basis (Fin d) F E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} = latV b v := by
  first
  | exact @GlobalTheory.AdelicU.Cofinite.eventually_latLoc_eq_latV
  | intro F E _ _ _ _ _ n d b L hL
    exact GlobalTheory.AdelicU.Cofinite.eventually_latLoc_eq_latV F E n d b L hL.toIsLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuous
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.TwoSided

open GlobalTheory.Mom.LowVec

theorem exists_coord {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (a : Fin (r + 1)) :
    ∃ i : Fin (2 * r + k + 1), a.val ≤ i.val ∧ fvec k r z a i ≠ 0 := by
  by_cases ha : a.val < r
  · refine ⟨eI k r ⟨a.val, ha⟩, le_of_eq rfl, ?_⟩
    simp only [fvec, dif_pos ha, bvec, Pi.single_eq_same]
    exact one_ne_zero
  ·
    have hz0 : ∃ i, z i ≠ 0 := by
      by_contra h
      push_neg at h
      have : z = 0 := funext h
      subst this
      simp [Tz, herm] at hT
    obtain ⟨i, hi⟩ := hz0
    have hri : r ≤ i.val := by
      by_contra h
      exact hi (hz i (Or.inl (Nat.lt_of_not_le h)))
    refine ⟨i, le_trans (Nat.le_of_lt_succ a.isLt) hri, ?_⟩
    simp only [fvec, dif_neg ha]
    exact hi

theorem lA_pos {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {x : Mat k r} (hx : x ∈ GG k r) (a : Fin (r + 1)) : 0 < lA k r z x a := by
  obtain ⟨i, hai, hi⟩ := exists_coord hz hT a
  have hu : IsUnit x.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx
  have hc : 0 < ∑ j, ‖x i j‖ + 1 := by positivity

  have key : ∀ y ∈ Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} =>
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1)),
      ‖fvec k r z a i‖ / (∑ j, ‖x i j‖ + 1) ≤ eucl (x⁻¹ *ᵥ (fvec k r z a - y)) := by
    intro y hy
    have hy' : y ∈ GlobalTheory.Mom.LowVec.flagSpan k r a := hy
    have hyi : y i = 0 := (GlobalTheory.Mom.LowVec.mem_flagSpan.1 hy') i hai
    set w := x⁻¹ *ᵥ (fvec k r z a - y) with hw
    have hv : fvec k r z a - y = x *ᵥ w := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hu, Matrix.one_mulVec]
    have hvi : fvec k r z a i = ∑ j, x i j * w j := by
      have := congrFun hv i
      simp only [Pi.sub_apply, hyi, sub_zero] at this
      rw [this]
      rfl
    have hwe : 0 ≤ eucl w := Real.sqrt_nonneg _
    have hle : ‖fvec k r z a i‖ ≤ (∑ j, ‖x i j‖ + 1) * eucl w := by
      rw [hvi]
      calc ‖∑ j, x i j * w j‖ ≤ ∑ j, ‖x i j * w j‖ := norm_sum_le _ _
        _ = ∑ j, ‖x i j‖ * ‖w j‖ := by simp only [norm_mul]
        _ ≤ ∑ j, ‖x i j‖ * eucl w := by
          gcongr with j
          exact GlobalTheory.Amp.LInv.norm_le_eucl w j
        _ = (∑ j, ‖x i j‖) * eucl w := by rw [Finset.sum_mul]
        _ ≤ (∑ j, ‖x i j‖ + 1) * eucl w := by nlinarith
    rw [div_le_iff₀ hc]
    linarith
  unfold lA
  refine lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hi) hc) ?_
  refine le_csInf ⟨_, 0, Submodule.zero_mem _, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact key y hy

theorem Sg2_invariant_continuousOn_one_le_bounds : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → (∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a) ∧ (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Sg2 k r z (s * x * κ) = Sg2 k r z x) ∧ ContinuousOn (Sg2 k r z) (GG k r) ∧ ∀ x, 1 ≤ Sg2 k r z x ∧ Sg k r z x ≤ Sg2 k r z x ∧ (∀ a, lA k r z x a ≤ Sg2 k r z x ∧ (lA k r z x a)⁻¹ ≤ Sg2 k r z x) ∧ (Sg2 k r z x = 1 ∨ ∃ a, Sg2 k r z x = max (lA k r z x a) (lA k r z x a)⁻¹) := by
  intro k r z hz hT
  have hpos : ∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a := fun x hx a => lA_pos hz hT hx a
  obtain ⟨hinv, -, hSg⟩ := GlobalTheory.Amp.LInv.lengths_basic k r z hz
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro x hx s hs κ hκ
    have h := (hinv x hx s hs κ hκ).1
    simp only [Sg2, h]
  · have hc := (GlobalTheory.Amp.LenCont.lA_Sg_continuousOn k r z).1
    exact GlobalTheory.Amp.LenCont.fold_continuousOn (GG k r) (fun a x => max (lA k r z x a) (lA k r z x a)⁻¹)
      (fun a => continuous_max.comp_continuousOn (ContinuousOn.prodMk (hc a) (ContinuousOn.inv₀ (hc a) fun x hx => (hpos x hx a).ne'))) Finset.univ
  · intro x
    have hle : ∀ a, max (lA k r z x a) (lA k r z x a)⁻¹ ≤ Sg2 k r z x := fun a =>
      (Finset.le_fold_max _).2 (Or.inr ⟨a, Finset.mem_univ _, le_rfl⟩)
    have h1 : 1 ≤ Sg2 k r z x := (Finset.le_fold_max _).2 (Or.inl le_rfl)
    refine ⟨h1, ?_, fun a => ⟨(le_max_left _ _).trans (hle a), (le_max_right _ _).trans (hle a)⟩, ?_⟩
    · exact (Finset.fold_max_le _).2 ⟨h1, fun a _ => (le_max_left _ _).trans (hle a)⟩
    ·
      have key : ∀ s : Finset (Fin (r + 1)), s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹) = 1 ∨
          ∃ a, s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹) = max (lA k r z x a) (lA k r z x a)⁻¹ := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · left
          simp
        · intro a s ha ih
          rw [Finset.fold_insert ha]
          rcases max_choice (max (lA k r z x a) (lA k r z x a)⁻¹)
              (s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹)) with h | h
          · exact Or.inr ⟨a, h⟩
          · rw [h]
            exact ih
      exact key Finset.univ

end GlobalTheory.Amp.TwoSided
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuousStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_sided_size_function_pos_invariant_continuous : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → (∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a) ∧ (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Sg2 k r z (s * x * κ) = Sg2 k r z x) ∧ ContinuousOn (Sg2 k r z) (GG k r) ∧ ∀ x, 1 ≤ Sg2 k r z x ∧ Sg k r z x ≤ Sg2 k r z x ∧ (∀ a, lA k r z x a ≤ Sg2 k r z x ∧ (lA k r z x a)⁻¹ ≤ Sg2 k r z x) ∧ (Sg2 k r z x = 1 ∨ ∃ a, Sg2 k r z x = max (lA k r z x a) (lA k r z x a)⁻¹) := by
  first | exact @GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds | exact GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds | (intros; apply GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProof
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProof
noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frameExp_cast (r l : ℕ) (hl : l ≤ r + 1) :
    ((frameExp r l : ℕ) : ℤ) = ∑ a ∈ Finset.range l, ((r : ℤ) - a) := by
  induction l with
  | zero => simp [frameExp]
  | succ l ih =>
    have h1 : frameExp r (l + 1) = frameExp r l + (r + 1 - (l + 1)) := by
      unfold frameExp
      rw [Finset.sum_Icc_succ_top (by omega)]
    have h2 : ((r + 1 - (l + 1) : ℕ) : ℤ) = (r : ℤ) - l := by omega
    rw [h1, Nat.cast_add, ih (by omega), Finset.sum_range_succ, h2]

theorem nloc_eq (D : D7) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) =
      |((Algebra.norm ℚ x : ℚ) : ℝ)| * (Ideal.absNorm (dI D) : ℝ) ^ (-(2 * (frameExp r l : ℤ))) := by
  unfold Nloc
  rw [map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 D.host.E), map_zpow₀,
    show ddS D = ((dI D : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) from rfl,
    FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rfl

theorem norm_star (D : D7) (x : D.host.E) : Algebra.norm ℚ (star x) = Algebra.norm ℚ x := by
  have := Algebra.norm_eq_of_algEquiv ((starRingAut : D.host.E ≃+* D.host.E).toRatAlgEquiv) x
  simpa using this

theorem nloc_ne_zero (D : D7) (hd : dI D ≠ ⊥) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) ≠ 0 ↔ x ≠ 0 := by
  have hA : (Ideal.absNorm (dI D) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hd)
  rw [nloc_eq, mul_ne_zero_iff, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
  simp only [ne_eq, zpow_neg, inv_eq_zero, and_iff_left_iff_imp]
  intro _
  exact zpow_ne_zero _ hA

theorem T_eq {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (F G : Formalism.HermitianLatticeCounting.S6.FlagD H r) (h : G.e (Fin.last r) - F.e (Fin.last r) ∈ F.X) : G.T = F.T := by
  have hX : ∀ w : V, (∀ a : Fin r, H.B (F.e a.castSucc) w = 0) → ∀ y ∈ F.X, H.B y w = 0 := by
    intro w hw y hy
    have hle : F.X ≤ LinearMap.ker (H.B.flip w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, -, rfl⟩
      simpa using hw b
    simpa using hle hy
  set x := G.e (Fin.last r) - F.e (Fin.last r) with hxdef
  have hxz : H.B x (F.e (Fin.last r)) = 0 := hX _ F.zperp x h
  have hzx : H.B (F.e (Fin.last r)) x = 0 := by rw [← H.herm, hxz, star_zero]
  have hxx : H.B x x = 0 := by
    refine hX x (fun a => ?_) x h
    have := hX (F.e a.castSucc) (fun b => F.iso b a) x h
    rw [← H.herm, this, star_zero]
  have hG : G.e (Fin.last r) = F.e (Fin.last r) + x := by rw [hxdef]; abel
  have h1 := G.zz
  rw [hG] at h1
  simp only [map_add (f := _), LinearMap.add_apply, hxz, hzx, hxx, F.zz, add_zero] at h1
  exact (neg_inj.1 h1).symm

end GlobalTheory.TypeAsm.HasLabelling

namespace GlobalTheory.TypeAsm
open GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem labC : LabC := by
  intro D large₂ X Y u hS t N hN
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := by
    obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩ := hS
    exact hH.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hj, hDl, -, -, -⟩ :=
    GlobalTheory.DegAsm.adapt_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (Ft t) (dI D) N hN
  have hII : Formalism.HermitianLatticeCounting.S6.II (F0 X u) (Ft t) = Isp (lf D (X.Fu u)).fl (frq X t.rep).fl := nf_II _ _ _ _
  have hjT : N.j = jT t := by rw [hj, hII]; rfl
  have hjle : jT t ≤ D.R.rS := by unfold jT; omega
  have hnf : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl) :=
    fun l hl => nf_Dl _ _ _ _ l hl
  have hd : N.𝔡 = dI D := hN.1
  have hdne : dI D ≠ ⊥ := hd ▸ N.𝔡_ne
  have key : ∀ l, l ≤ jT t → N.nD l = ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) := by
    intro l hl
    have hl' : l ≤ D.R.rS + 1 := by omega
    have hlab : labT t l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl') := by
      simp only [labT, if_pos hl]
      exact hnf l hl'
    unfold GlobalTheory.DegCnt.NF.nD
    rw [dite_eq_left hl', hDl l hl', nloc_eq, hlab, norm_star, hd, frameExp_cast _ _ hl']
  refine ⟨hjT, ?_, ?_, ?_, ?_⟩
  · have hz : N.F.e (Fin.last D.R.rS) - (F0 X u).e (Fin.last D.R.rS) ∈ (F0 X u).X := hN.2.1 (Fin.last _)
    have h1 : ((N.T : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := by
      rw [← N.hT, T_eq (F0 X u) N.F hz]
      rfl
    exact_mod_cast h1
  · unfold GlobalTheory.DegCnt.NF.Del
    rw [hjT, key _ le_rfl]
    rfl
  · unfold GlobalTheory.DegCnt.NF.Db DbL
    rw [hjT]
    have hset : (Finset.Icc 1 (jT t)).filter (fun l => N.nD l ≠ 0) = k2ends D (jT t) (labT t) := by
      ext l
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2] at h3
        exact (nloc_ne_zero D hdne _ _ _).1 h3
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2]
        exact (nloc_ne_zero D hdne _ _ _).2 h3
    rw [hset]
    refine Finset.prod_congr rfl fun l hl => ?_
    have h2 : l ≤ jT t := by
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc] at hl
      exact hl.1.2
    exact key l h2
  · funext l
    unfold GlobalTheory.DegAsm.lab
    by_cases hl : l ≤ jT t
    · have hl' : l ≤ D.R.rS + 1 := by omega
      rw [dite_eq_left ⟨hl, hl'⟩]
      simp only [labT, if_pos hl]
      rw [hnf l hl', star_star]
    · rw [dite_eq_right (fun h => hl h.1)]
      simp only [labT, if_neg hl, star_zero]

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label : GlobalTheory.TypeAsm.LabC := by
  first | exact @GlobalTheory.TypeAsm.labC | exact GlobalTheory.TypeAsm.labC | (intros; apply GlobalTheory.TypeAsm.labC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHolds
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHolds
noncomputable section
open scoped Classical Pointwise
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm

namespace GlobalTheory.TypeAsm.LatticeOrthogonalComplement

section Gen
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W} {r : ℕ}

theorem B_swap {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem X_B_e (F : FlagD H r) (a : Fin (r + 1)) (x : V) (hx : x ∈ F.X) : H.B x (F.e a) = 0 := by
  have key : ∀ b : Fin r, H.B (F.e b.castSucc) (F.e a) = 0 := by
    intro b
    induction a using Fin.lastCases with
    | last => exact F.zperp b
    | cast c => exact F.iso b c
  have : F.X ≤ LinearMap.ker (H.B.flip (F.e a)) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using key b
  simpa using this hx

theorem X_B_perp (F : FlagD H r) {v : V} (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) (x : V) (hx : x ∈ F.X) :
    H.B x v = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip v) := by
    unfold FlagD.X FlagD.Xa
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simpa using hv b.castSucc
  simpa using this hx

theorem flag_vector_mem_base_lattice (F : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F := by
  unfold V0
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  | cast c => exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨c, c.2, rfl⟩))

theorem mem_wSp (F : FlagD H r) (v : V) : v ∈ wSp F F ↔ ∀ a, H.B (F.e a) v = 0 := by
  rw [wSp, mem_perp_iff]
  constructor
  · intro h a
    exact B_swap (h _ (flag_vector_mem_base_lattice F a))
  · intro h x hx
    apply B_swap
    have : V0 F F ≤ LinearMap.ker (H.B.flip v) := by
      unfold V0
      refine sup_le (sup_le ?_ ?_) (Submodule.span_le.2 ?_)
      · intro y hy; simpa using X_B_perp F h y hy
      · intro y hy; simpa using X_B_perp F h y hy
      · rintro _ (rfl | rfl) <;> simpa [FlagD.z] using h (Fin.last r)
    simpa using this hx

theorem mem_perp_lattice_flag_iff (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (v : V) :
    v ∈ flagPairDefinitePartLattice F F Λ ↔ v ∈ Λ ⊔ rs (𝓞 K) F.X ∧ v ∈ wSp F F := by
  simp only [flagPairDefinitePartLattice, latL, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1⟩, h2⟩
    rw [uPerp, mem_perp_iff]
    rw [wSp, mem_perp_iff] at h2
    exact fun x hx => h2 x ((le_sup_left : F.X ⊔ F.X ≤ V0 F F) hx)

variable {F : FlagD H r} {e : W →ₗ[K] V}

theorem e_perp (hE : IsEmb F HW e) (w : W) (a : Fin (r + 1)) : H.B (F.e a) (e w) = 0 :=
  (hE.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩) a

theorem e_wSp (hE : IsEmb F HW e) (w : W) : e w ∈ wSp F F := (mem_wSp F _).2 (e_perp hE w)

theorem X_wSp (x : V) (hx : x ∈ F.X) : x ∈ wSp F F :=
  (mem_wSp F _).2 fun a => B_swap (X_B_e F a x hx)

theorem decomp (hE : IsEmb F HW e) {v : V} (hv : v ∈ wSp F F) : ∃ w, v - e w ∈ F.X := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, h⟩ := Submodule.mem_sup.1 ((hE.2 v).1 ((mem_wSp F v).1 hv))
  exact ⟨w, by rw [← h]; simpa using hz⟩

theorem XB_e (hE : IsEmb F HW e) (x : V) (hx : x ∈ F.X) (w : W) : H.B x (e w) = 0 :=
  X_B_perp F (e_perp hE w) x hx

theorem memL_e (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V) (w : W) :
    e w ∈ flagPairDefinitePartLattice F F Λ ↔ w ∈ lat0 F e Λ :=
  (mem_perp_lattice_flag_iff F Λ _).trans ⟨fun h => h.1, fun h => ⟨h, e_wSp hE w⟩⟩

theorem X_L (Λ : Submodule (𝓞 K) V) (x : V) (hx : x ∈ F.X) : x ∈ flagPairDefinitePartLattice F F Λ :=
  (mem_perp_lattice_flag_iff F Λ x).2 ⟨Submodule.mem_sup_right hx, X_wSp x hx⟩

theorem quotEquiv (hE : IsEmb F HW e) (Λ : Submodule (𝓞 K) V)
    (hspan : Submodule.span K (flagPairDefinitePartLattice F F Λ : Set V) = wSp F F) :
    Nonempty ((↥(Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)) ⧸
        (lat0 F e Λ).comap (Formalism.HermitianLatticesTheory.dual HW.B.flip (lat0 F e Λ)).subtype) ≃ₗ[𝓞 K]
      (↥(dual H (flagPairDefinitePartLattice F F Λ)) ⧸ (flagPairDefinitePartLattice F F Λ).comap (dual H (flagPairDefinitePartLattice F F Λ)).subtype)) := by
  set L := flagPairDefinitePartLattice F F Λ with hL
  set M := lat0 F e Λ with hM
  set DW := Formalism.HermitianLatticesTheory.dual HW.B.flip M with hDW
  set DV := dual H L with hDV
  have hmemW : ∀ w, w ∈ DW ↔ ∀ y ∈ M, HW.B w y ∈ (1 : Submodule (𝓞 K) K) := fun w => by
    rw [hDW, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    simp only [LinearMap.flip_apply]
  have hin : ∀ w : DW, e w ∈ DV := by
    rintro ⟨w, hw⟩
    rw [hDV, mem_dual_iff, hspan]
    refine ⟨e_wSp hE w, fun x hx => ?_⟩
    obtain ⟨w', hw'⟩ := decomp hE ((mem_perp_lattice_flag_iff F Λ x).1 hx).2
    have hw'M : w' ∈ M := (memL_e hE Λ w').1 (by simpa using L.sub_mem hx (X_L Λ _ hw'))
    have h1 : H.B (e w) x = HW.B w w' := by
      have e1 : x = e w' + (x - e w') := by abel
      rw [e1, map_add (f := _), B_swap (XB_e hE _ hw' w), add_zero, hE.1]
    rw [h1]
    exact (hmemW w).1 hw w' hw'M
  let f : DW →ₗ[𝓞 K] DV :=
    LinearMap.codRestrict DV ((e.restrictScalars (𝓞 K)).comp DW.subtype) (fun w => hin w)
  let Φ := (L.comap DV.subtype).mkQ ∘ₗ f
  have hker : LinearMap.ker Φ = M.comap DW.subtype := by
    ext w
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    exact memL_e hE Λ w
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    have hv' := (mem_dual_iff H L v).1 hv
    rw [hspan] at hv'
    obtain ⟨w, hw⟩ := decomp hE hv'.1
    have hwD : w ∈ DW := (hmemW w).2 fun y hy => by
      have h1 : HW.B w y = H.B v (e y) := by
        rw [← hE.1]
        have e1 : v = e w + (v - e w) := by abel
        conv_rhs => rw [e1]
        rw [map_add (f := _), LinearMap.add_apply, XB_e hE (v - e w) hw y, add_zero]
      rw [h1]
      exact hv'.2 _ ((memL_e hE Λ y).2 hy)
    refine ⟨⟨w, hwD⟩, ?_⟩
    show Submodule.Quotient.mk (f ⟨w, hwD⟩) = Submodule.Quotient.mk ⟨v, hv⟩
    rw [Submodule.Quotient.eq]
    show e w - v ∈ L
    have := L.neg_mem (X_L Λ _ hw)
    simpa using this
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)⟩

end Gen

end GlobalTheory.TypeAsm.LatticeOrthogonalComplement

open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm
open LatticeOrthogonalComplement
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lat0C : LatticeNormalizationCondition := by
  intro D large₂ X Y u hS W HW hE Λ hΛ
  obtain ⟨hCM, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N, hF, hF', -, hT, -, hTerm, -, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hS Λ (Or.inl hΛ)
  have hg1 : 1 ≤ gS D := by omega
  obtain ⟨-, -, -, hLat, -, hNe⟩ := GlobalTheory.DegCnt.PrimPerp.main _ _ (HV D) hCM D.R.rS N (gS D) Λ hg1 hTerm
  rw [hF, hF'] at hLat hNe
  rw [hT] at hNe
  have hAd : Adapt (F0 X u) (F0 X u) N.𝔡 N := by
    have := adapt_self N
    rwa [hF, hF'] at this
  obtain ⟨⟨hInt, -⟩, -⟩ := GlobalTheory.DegAsm.isDat_datOf _ _ _ (HV D) HW W.subtype hCM D.R.rS (F0 X u) (F0 X u) N.𝔡 N
    (gS D) Λ hg1 hE hAd hTerm
  have hd : (datOf (F0 X u) (F0 X u) W.subtype (gS D) Λ).1 = lat0 (F0 X u) W.subtype Λ := by
    ext w
    change W.subtype w ∈ flagPairDefinitePartLattice (F0 X u) (F0 X u) Λ ⊔ rs _ (F0 X u).X ↔ w ∈ lat0 (F0 X u) W.subtype Λ
    rw [sup_eq_left.2 (fun x hx => X_L Λ x hx), memL_e hE Λ]
  refine ⟨hd ▸ hInt, ?_⟩
  obtain ⟨q⟩ := quotEquiv hE Λ hLat.2
  obtain ⟨i⟩ := hNe
  exact ⟨q.trans i⟩

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_lattice_construction_holds : GlobalTheory.TypeAsm.LatticeNormalizationCondition := by
  first | exact @GlobalTheory.TypeAsm.lat0C | exact GlobalTheory.TypeAsm.lat0C | (intros; apply GlobalTheory.TypeAsm.lat0C <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocal
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicU

theorem eventually_vecLoc_mem_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) (y : Fin n → Af F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, vecLoc v y ∈ latLoc F L v := by
  letI := hL
  haveI := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_latLoc_eq F L (stdLattice E n),
    Filter.eventually_all.2 fun i => eventually_map_evalV_mem_intLoc (y i)] with v h h1
  rw [h, mem_latLoc_stdLattice]
  exact h1

theorem indicator_latHat_eq_finprod :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E,
      {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator
        (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  intro F E _ _ _ _ _ n L hL X
  have key : ∀ v : HeightOneSpectrum (𝓞 F), vecLoc v (X 0) ∈ latLoc F L v →
      {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) = 1 := fun v hv =>
    Set.indicator_of_mem (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
  by_cases h : X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))
  · rw [Set.indicator_of_mem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h,
      finprod_congr fun v => key v ((mem_latHat_iff hL.fg _).1 h v), finprod_one]
    rfl
  · rw [Set.indicator_of_notMem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h]
    rw [mem_latHat_iff hL.fg, not_forall] at h
    obtain ⟨v, hv⟩ := h
    refine (finprod_eq_zero _ v ?_ ?_).symm
    · exact Set.indicator_of_notMem
        (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
    · exact Set.Finite.subset (Filter.eventually_cofinite.1 (eventually_vecLoc_mem_latLoc L hL (X 0)))
        fun u hu hu' => hu (key u hu')

end GlobalTheory.AdelicU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocalStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_completedLattice_eq_finprod_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E, {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X = ∏ᶠ v : HeightOneSpectrum (𝓞 F), {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  first | exact @GlobalTheory.AdelicU.indicator_latHat_eq_finprod | exact GlobalTheory.AdelicU.indicator_latHat_eq_finprod | (intros; apply GlobalTheory.AdelicU.indicator_latHat_eq_finprod <;> first | assumption | exact Submodule.IsFullLattice.toIsLattice)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsDerLowKSub
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DerEx


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothOnG_comb {n : ℕ} {ε : Fin n → Bool} {f g : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hg : SmoothOnG ε g) : SmoothOnG ε (fun x => c * f x + g x) := by
  intro x hx
  obtain ⟨U, F, hU, hxU, hF, hFf⟩ := hf x hx
  obtain ⟨U', G, hU', hxU', hG, hGg⟩ := hg x hx
  refine ⟨U ∩ U', fun y => c * F y + G y, hU.inter hU', ⟨hxU, hxU'⟩,
    (contDiffOn_const.mul (hF.mono Set.inter_subset_left)).add (hG.mono Set.inter_subset_right), ?_⟩
  intro y hy hyJ
  simp only [hFf y hy.1 hyJ, hGg y hy.2 hyJ]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothOnG_zero {n : ℕ} (ε : Fin n → Bool) : SmoothOnG ε (fun _ => 0) := fun _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem exists_isDer_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsDer ε σ V E ∧ lowKSub ε lam σ ≤ V := by
  intro n ε lam H _ _ _ σ hσ hK
  let S : Set H := {v | ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), SmoothOnG ε α ∧
    HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
    ∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ}
  have hder : ∀ v ∈ Submodule.span ℂ S, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X →
      ∃ v' ∈ Submodule.span ℂ S,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
    intro v hv X hX
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      obtain ⟨β, v', k1, k2, k3, k4⟩ :=
        (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).2 X hX
      exact ⟨v', Submodule.subset_span ⟨β, s, k1, k2, k3⟩, k4⟩
    | zero => exact ⟨0, zero_mem _, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', hda⟩ := ha
      obtain ⟨b', hb', hdb⟩ := hb
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      simp only [map_add (f := _)]
      exact hda.add hdb
    | smul c a _ ha =>
      obtain ⟨a', ha', hda⟩ := ha
      refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
      simp only [map_smul]
      exact hda.const_smul c
  have hzero := smoothOnG_zero ε
  have hsm : ∀ v ∈ Submodule.span ℂ S, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ) := by
    intro v hv y
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      exact (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).1 y
    | zero => simpa using hzero
    | add a b _ _ ha hb => simpa [inner_add_right] using smoothOnG_comb 1 ha hb
    | smul c a _ ha => simpa [inner_smul_right] using smoothOnG_comb c ha hzero
  obtain ⟨E, hE⟩ := GlobalTheory.DerOf.exists_isDer n ε H σ (Submodule.span ℂ S) hσ hder hsm
  obtain ⟨α, h1, h2, h3⟩ := GlobalTheory.exists_smooth_fix_lowKSub n ε lam H σ hσ hK
  exact ⟨_, E, hE, fun s hs => Submodule.subset_span ⟨α, s, h1, h2, h3 s hs⟩⟩

end GlobalTheory.DerEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilUnitaryConvergentOfSiegelWeilConvergen
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain MeasureTheory Topology
open HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.SiegelWeilConvCompare

theorem exists_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  let e1 : (κ → X) ≃ₜ (κ → Fin k → ℝ) := Homeomorph.piCongrRight fun _ => e
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext i; exact he (x i) (y i)
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := κ → Fin k → ℝ)
    (F := Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add (f := _)]

theorem exists_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  let e1 : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).map_add _ _
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := InfinitePlace F → ℝ)
    (F := Fin (Module.finrank ℝ (InfinitePlace F → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add (f := _)]

theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  let R := Ainf F
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let eL : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  let e0 : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
    { toEquiv := eL.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap }
  obtain ⟨k0, eA, hA⟩ := exists_coord_Ainf F
  obtain ⟨k, e1, h1⟩ := exists_coord_pi eA hA (Module.Free.ChooseBasisIndex R (R ⊗[F] E))
  refine ⟨k, e0.trans e1, fun x y => ?_⟩
  show e1 (e0 (x + y)) = e1 (e0 x) + e1 (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from eL.map_add x y, h1]

section Zero

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [Subsingleton V]

end Zero

theorem measure_fundamentalDomain_pos (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ) (hμ : IsHaarH F E σ M J μ)
    (𝓕) (h : IsFDH F E σ M J μ 𝓕) : 0 < μ 𝓕 := by
  haveI : μ.IsHaarMeasure := hμ
  haveI : Countable E := (Module.Free.chooseBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  haveI : Countable (HFin (AF F) σ J) := by
    have : ((HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
        Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      unfold HFin; rw [Subgroup.coe_map]; exact (Set.to_countable _).image _
    exact this
  haveI : Countable (HFinIn (AF F) σ J) := by
    have : Function.Injective (fun x : HFinIn (AF F) σ J => (⟨x.1.1, x.2⟩ : HFin (AF F) σ J)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : HFin (AF F) σ J => z.1) hxy))
    exact this.countable
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
    ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
  exact pos_iff_ne_zero.2 (IsFundamentalDomain.measure_ne_zero (NeZero.ne μ) h)

section HermTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def tensHomeo {κ : Type} [Finite κ] (b : Module.Basis κ F E) : R ⊗[F] E ≃ₜ (κ → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

end HermTop


end GlobalTheory.SiegelWeilConvCompare
end
end
