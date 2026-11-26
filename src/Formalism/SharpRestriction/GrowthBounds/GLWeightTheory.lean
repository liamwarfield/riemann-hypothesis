module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MahPadicGeOfDvd
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemBoundedDegreeExponentsIff
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.FrameChangePreservesMultidegree
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicLatticeCorollary
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedWeightLemmaOfReducibility
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolynomialsEnvelopingStable
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightEntryRestrictionMem
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.SumFinsuppAntidiagEqSumPiFinset
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringSpanHighestComponentIntegral
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.LatticeTheoremSingleRepLinf
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DenominatorLemmaWithoutProjector

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaPartB
noncomputable section

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem generated_module_weight_lemma_part_b : GeneratedModuleWeightDescription :=
  generated_module_weight_lemma_of_interfaces transvectionExpansion torus_acts_through_weight binomial_stable_contains_components twist_exponents_are_weight_entries generic_monomials_specialise

theorem valuationsAdditive_D7 (D : Formalism.BasicNotions.D7) : ValuationsAdditive D := valuations_additive_of_generated_weight_description D generated_module_weight_lemma_part_b

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.LinfAdjointLeEllWtHighest
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem linf_adjoint_le_ellWt_highest [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) : linf (adjointEndAction E) ⊤ ≤ ellWt lam := by
  refine csSup_le' ?_
  rintro k ⟨ka, hk, -, a, rfl⟩
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hk
  have hfw := hf.1
  obtain ⟨nu, x, hx, hfx⟩ : ∃ nu x, x ∈ weightSp E nu ∧ f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf0
    have hk : (⊤ : Submodule (KK O) V) ≤ LinearMap.ker f := by
      rw [← hI.1.2.2]
      exact iSup_le fun nu x hx => hcon nu x hx
    exact LinearMap.ext fun x => hk Submodule.mem_top
  have hx0 : x ≠ 0 := by rintro rfl; simp at hfx
  have hfxw : f x ∈ weightSp E (nu + ka) := by
    rw [mem_weightSpace_iff_diag_scalar]
    intro c
    have h1 := congrArg (fun T : Module.End (KK O) V => T x) (mem_weightSpace_iff_diag_scalar.1 hfw c)
    simp only [adjointEndAction_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h1
    rw [mem_weightSpace_iff_diag_scalar.1 hx c, map_smul] at h1
    rw [sub_eq_iff_eq_add.1 h1, ← add_smul]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  have h1 := weight_entries_between_extreme_highest hI hfxw hfx a
  have h2 := weight_entries_between_extreme_highest hI hx hx0 a
  simp only [Pi.add_apply] at h1
  unfold ellWt
  omega

end hw

theorem restA_of_linf_integrality (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorLinftyBound) (hK : HighestWeightVectorIntegrality) : LatticeNablaDeltaBound := by
  intro p n' O _ _ _ S hR n _ lam V _ _ _ _ E v hI x hx
  have := dvr_fraction_field_char_zero_prime S hR.prime
  have := irreducible_highest_weight_findim hI
  have hCR := h2 (KK O) V n E hI.1
  obtain ⟨xi, x1, x2, x3⟩ := exists_highest_coordinate_functional hI
  have hKv := hK p n' O S hR n lam V E v hI
  have hlat : UZLattice (O := O) (adjointEndAction E) (nablaToDeltaMaps (O := O) E lam v) :=
    ⟨nabla_to_delta_maps_stable hI.1 lam v, nabla_to_delta_maps_fg hI hCR x1 x2 x3 hKv⟩
  have hMQ := nabla_to_delta_maps_span_top (O := O) hI (nabla_finitely_generated hI hCR x1 x2 x3)
  have key := h p n' O S hR n (Module.End (KK O) V) (adjointEndAction E) (adjoint_end_isGLRep hI.1) _ hlat hMQ
    (traceInvariantProjection O V) (trace_projection_isInvProj hI) (xi.smulRight v) (coordinate_rank_one_mem_maps x1 x2 x3)
  rw [hMQ] at key
  have hd : (Module.finrank (KK O) V : KK O) ≠ 0 := by
    have : Nontrivial V := ⟨⟨v, 0, hI.2.2.1.1⟩⟩
    exact_mod_cast (Module.finrank_pos (R := KK O) (M := V)).ne'
  have hInv : traceInvariantProjection O V (xi.smulRight v) = ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V) := by
    rw [traceInvariantProjection, LinearMap.smulRight_apply, LinearMap.trace_smulRight, x1, one_smul]
  rw [hInv] at key
  set D' := N0 n * deF p n (linf (adjointEndAction E) ⊤) with hD'
  set D0 := N0 n * deF p n (ellWt lam) with hD0
  have hle : D' ≤ D0 := by
    refine Nat.mul_le_mul_left _ ?_
    unfold deF
    exact Nat.log_mono_right (by have := linf_adjoint_le_ellWt_highest hI; omega)
  have h3 : ((Module.finrank (KK O) V : ℕ) : O) • ((p : O) ^ (D0 - D')) •
      ((p : O) ^ D' • ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)) ∈ nablaToDeltaMaps (O := O) E lam v :=
    Submodule.smul_mem _ _ (Submodule.smul_mem _ _ key)
  have h4 : ((Module.finrank (KK O) V : ℕ) : O) • ((p : O) ^ (D0 - D')) •
      ((p : O) ^ D' • ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)) =
      (p : O) ^ D0 • (1 : Module.End (KK O) V) := by
    rw [smul_smul ((p : O) ^ (D0 - D')), ← pow_add, Nat.sub_add_cancel hle, smul_comm,
      ← algebraMap_smul (KK O) ((Module.finrank (KK O) V : ℕ) : O), smul_smul, map_natCast, mul_inv_cancel₀ hd,
      one_smul]
  rw [h4] at h3
  have := h3 x hx
  simpa using this

theorem integral_form_of_linf_lemma (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorLinftyBound) : NablaDeltaComparisonField D :=
  highest_weight_lattice_of_first_part D (restA_of_linf_integrality D h2 h highest_vector_integrality)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.AlgHomFixesSupportedPolynomials
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem det_mem_subalgebra_of_entries {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] (T : Subalgebra R P) {n : ℕ}
    (N : Matrix (Fin n) (Fin n) P) (h : ∀ i j, N i j ∈ T) : N.det ∈ T := by
  let M : Matrix (Fin n) (Fin n) T := Matrix.of fun i j => ⟨N i j, h i j⟩
  have hM : (T.val.toRingHom).mapMatrix M = N := by ext i j; rfl
  rw [← hM, ← RingHom.map_det]
  exact M.det.2

theorem divisor_supported_of_supported {R σ : Type*} [CommRing R] [IsDomain R] {s : Set σ} {f q : MvPolynomial σ R}
    (hf : f ≠ 0) (hs : f ∈ supported R s) (hq : q ∣ f) : q ∈ supported R s := by
  rw [mem_supported] at hs ⊢
  obtain ⟨g, rfl⟩ := hq
  have hq0 : q ≠ 0 := by rintro rfl; simp at hf
  have hg0 : g ≠ 0 := by rintro rfl; simp at hf
  intro v hv
  by_contra hvs
  have h1 : degreeOf v (q * g) = degreeOf v q + degreeOf v g := degreeOf_mul_eq hq0 hg0
  have h2 : degreeOf v (q * g) = 0 := by
    rw [degreeOf_eq_sup]
    refine Nat.le_zero.mp (Finset.sup_le fun m hm => ?_)
    by_contra hmv
    exact hvs (hs ((mem_vars_iff_mem_support v).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr (by omega)⟩))
  have h3 : degreeOf v q ≠ 0 := mem_vars_iff_degreeOf_ne_zero.mp hv
  omega

theorem algHom_fixes_supported_polynomials {R σ : Type*} [CommRing R] {s : Set σ} (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (h : ∀ v ∈ s, φ (X v) = X v) {q : MvPolynomial σ R} (hq : q ∈ supported R s) : φ q = q := by
  rw [supported_eq_adjoin_X] at hq
  have hle : Algebra.adjoin R (X '' s) ≤ AlgHom.equalizer φ (AlgHom.id R _) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  exact hle hq

def cofactorMatrix (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  (matA R A).updateRow (lastIdx r) (Pi.single a 1)

def cofactorMatrixColumnCleared (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  Matrix.of fun i j => if i = lastIdx r then (if j = a then 1 else 0) else (if j = a then 0 else X (A i, j))

theorem adjugate_last_row_eq_cofactor_det (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (matA R A).adjugate a (lastIdx r) = (cofactorMatrix R A a).det := by
  rw [Matrix.adjugate_apply]; rfl

theorem cofactor_det_eq_cleared_det (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (cofactorMatrix R A a).det = (cofactorMatrixColumnCleared R A a).det := by
  symm
  classical
  refine Matrix.det_eq_of_forall_row_eq_smul_add_const
    (fun i => if i = lastIdx r then 0 else -X (A i, a)) (lastIdx r) (by simp) ?_
  intro i j
  by_cases hi : i = lastIdx r
  · subst hi
    simp [cofactorMatrix, cofactorMatrixColumnCleared, Matrix.updateRow_self, Pi.single_apply]
  · by_cases hj : j = a
    · subst hj
      simp [cofactorMatrix, cofactorMatrixColumnCleared, hi, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA]
    · simp [cofactorMatrix, cofactorMatrixColumnCleared, hi, hj, Matrix.updateRow_ne hi, Matrix.updateRow_self, matA, Pi.single_apply]

def cofactorVariables {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) : Set (ι × Fin r) :=
  {v | (∃ i, i ≠ lastIdx r ∧ v.1 = A i) ∧ v.2 ≠ a}

theorem cofactor_last_row_supported (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    (matA R A).adjugate a (lastIdx r) ∈ supported R (cofactorVariables A a) := by
  rw [adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]
  apply det_mem_subalgebra_of_entries
  intro i j
  simp only [cofactorMatrixColumnCleared, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _
  · exact Subalgebra.zero_mem _
  · rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨_, ⟨⟨i, h1, rfl⟩, h3⟩, rfl⟩


open Classical in
theorem adjugate_last_row_ne_zero (R : Type) [CommRing R] [Nontrivial R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι)
    (hA : Function.Injective A) (a : Fin r) : (matA R A).adjugate a (lastIdx r) ≠ 0 := by
  rw [adjugate_last_row_eq_cofactor_det, cofactor_det_eq_cleared_det]
  intro h0
  set σ : Equiv.Perm (Fin r) := Equiv.swap a (lastIdx r) with hσ
  let g : ι × Fin r → R := fun v => if ∃ i, v = (A i, σ i) then 1 else 0
  have hmap : (eval g).mapMatrix (cofactorMatrixColumnCleared R A a) = σ.permMatrix R := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, cofactorMatrixColumnCleared, Matrix.of_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq]
    by_cases hi : i = lastIdx r
    · subst hi
      by_cases hj : j = a
      · subst hj; simp [hσ, Equiv.swap_apply_right]
      · have : σ (lastIdx r) ≠ j := by rw [hσ, Equiv.swap_apply_right]; exact Ne.symm hj
        simp [hj, this]
    · have hσi : σ i ≠ a := by
        intro h
        apply hi
        have := congrArg σ h
        rwa [hσ, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have key : (∃ i', A i = A i' ∧ j = σ i') ↔ σ i = j := by
        constructor
        · rintro ⟨i', h1, h2⟩
          rw [hA h1]; exact h2.symm
        · intro h; exact ⟨i, rfl, h.symm⟩
      by_cases hj : j = a
      · subst hj; simp [hi, hσi]
      · simp [hi, hj, g, key]
  have hdet := congrArg (eval g) h0
  rw [RingHom.map_det, hmap, Matrix.det_permutation, map_zero] at hdet
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs] at hdet


open Classical in
def lastRowSubstitution (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι) (a : Fin r) :
    MvPolynomial (ι × Fin r) R →ₐ[R] MvPolynomial (ι × Fin r) R :=
  aeval fun v => if v.1 = A (lastIdx r) then (if v.2 = a then 1 else 0) else X v

theorem substitution_det_eq_adjugate (R : Type) [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (A : Fin r → ι)
    (hA : Function.Injective A) (a : Fin r) :
    lastRowSubstitution R A a (detA (R := R) A) = (matA R A).adjugate a (lastIdx r) := by
  rw [adjugate_last_row_eq_cofactor_det]
  unfold detA
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, cofactorMatrix, lastRowSubstitution, aeval_X, matA]
  by_cases hi : i = lastIdx r
  · subst hi
    simp [Matrix.updateRow_self, Pi.single_apply]
  · have : A i ≠ A (lastIdx r) := hA.ne hi
    simp [this, Matrix.updateRow_ne hi, matA]

theorem hCop_proved : HCop := by
  intro R _ ι r _ A hA
  have hC := adjugate_last_row_ne_zero R A hA (lastIdx r)
  refine ⟨hC, ?_⟩
  intro d hd1 hd2
  have hd0 : d ≠ 0 := by rintro rfl; exact hC (zero_dvd_iff.mp hd2)
  have hsL : d ∈ supported R (cofactorVariables A (lastIdx r)) :=
    divisor_supported_of_supported hC (cofactor_last_row_supported R A _) hd2
  have hall : ∀ a, d ∈ supported R (cofactorVariables A a) := by
    intro a
    have hfix : lastRowSubstitution R A a d = d := by
      refine algHom_fixes_supported_polynomials _ ?_ hsL
      rintro v ⟨⟨i, hi, hv⟩, -⟩
      have : v.1 ≠ A (lastIdx r) := by rw [hv]; exact hA.ne hi
      simp [lastRowSubstitution, this]
    have hdv : d ∣ (matA R A).adjugate a (lastIdx r) := by
      rw [← substitution_det_eq_adjugate R A hA a, ← hfix]; exact map_dvd _ hd1
    exact divisor_supported_of_supported (adjugate_last_row_ne_zero R A hA a) (cofactor_last_row_supported R A a) hdv
  have hsub : (d.vars : Set (ι × Fin r)) ⊆ ∅ := by
    intro v hv
    exact ((mem_supported.mp (hall v.2)) hv).2 rfl
  have h0 : d ∈ supported R (∅ : Set (ι × Fin r)) := mem_supported.mpr hsub
  rw [supported_empty, Algebra.mem_bot] at h0
  obtain ⟨c, rfl⟩ := h0
  have hc : c ≠ 0 := by rintro rfl; exact hd0 (map_zero _)
  exact (IsUnit.mk0 c hc).map (algebraMap R _)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.PositivityConditionHolds
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.PieAltApply
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def pie_cnt {n b : ℕ} (s : Sym (Fin n) b) : Fin n → ℕ := fun i => (s : Multiset (Fin n)).count i

theorem pie_hsymm (n b : ℕ) : hsymm (Fin n) ℤ b =
    ∑ s : Sym (Fin n) b, ∏ i, (X i : MvPolynomial (Fin n) ℤ) ^ pie_cnt s i := by
  rw [MvPolynomial.hsymm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_multiset_map_count]
  simp only [pie_cnt]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Multiset.mem_toFinset] at hi
  rw [Multiset.count_eq_zero.mpr hi, pow_zero]

theorem pie_alt_apply (n : ℕ) (al : Fin n → ℕ) : alt n al =
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, (X (σ i) : MvPolynomial (Fin n) ℤ) ^ al i := by
  unfold alt
  rw [Matrix.det_apply]
  rfl

private theorem pie_cnt_map_equiv {n b : ℕ} (e : Fin n ≃ Fin n) (s : Sym (Fin n) b) (i : Fin n) :
    pie_cnt (s.map e) i = pie_cnt s (e.symm i) := by
  unfold pie_cnt
  rw [Sym.coe_map]
  conv_lhs => rw [← e.apply_symm_apply i]
  exact Multiset.count_map_eq_count' e _ e.injective _

theorem pie_step1 (n b : ℕ) (al : Fin n → ℕ) : alt n al * hsymm (Fin n) ℤ b =
    ∑ s : Sym (Fin n) b, alt n (al + pie_cnt s) := by
  rw [pie_alt_apply, pie_hsymm, Finset.sum_mul]
  simp_rw [pie_alt_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_mul_assoc, Finset.mul_sum, ← Finset.smul_sum]
  congr 1
  refine Finset.sum_nbij' (fun s => s.map σ.symm) (fun s => s.map σ) (by simp) (by simp) ?_ ?_ ?_
  · intro s _
    first
    | simp [Sym.map_map]
    | (apply Sym.ext; simp [Sym.coe_map, Multiset.map_map])
  · intro s _
    first
    | simp [Sym.map_map]
    | (apply Sym.ext; simp [Sym.coe_map, Multiset.map_map])
  · intro s _
    rw [← Equiv.prod_comp σ (fun i => (X i : MvPolynomial (Fin n) ℤ) ^ pie_cnt s i),
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Pi.add_apply, pow_add, pie_cnt_map_equiv, Equiv.symm_symm]

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def pie_pr {n : ℕ} (j : Fin n) : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩

def pie_sw {n : ℕ} (mu : Fin n → ℕ) (j : Fin n) : Fin n → ℕ :=
  Function.update (Function.update mu (pie_pr j) (mu j - 1)) j (mu (pie_pr j) + 1)

def pie_B {n : ℕ} (lam mu : Fin n → ℕ) : Finset (Fin n) :=
  univ.filter fun j => 0 < j.val ∧ lam (pie_pr j) < mu j

theorem pie_pr_ne {n : ℕ} {j : Fin n} (h : 0 < j.val) : pie_pr j ≠ j := by
  intro hc
  have h2 : j.val - 1 = j.val := congrArg Fin.val hc
  omega

theorem pie_sw_self {n : ℕ} (mu : Fin n → ℕ) (j : Fin n) : pie_sw mu j j = mu (pie_pr j) + 1 := by
  unfold pie_sw
  first
  | rw [Function.update_self]
  | rw [Function.update_same]
  | simp

theorem pie_sw_pr {n : ℕ} (mu : Fin n → ℕ) {j : Fin n} (h : 0 < j.val) :
    pie_sw mu j (pie_pr j) = mu j - 1 := by
  unfold pie_sw
  first
  | rw [Function.update_of_ne (pie_pr_ne h), Function.update_self]
  | rw [Function.update_noteq (pie_pr_ne h), Function.update_same]

theorem pie_sw_other {n : ℕ} (mu : Fin n → ℕ) {j k : Fin n} (hk : k ≠ j) (hk' : k ≠ pie_pr j) :
    pie_sw mu j k = mu k := by
  unfold pie_sw
  first
  | rw [Function.update_of_ne hk, Function.update_of_ne hk']
  | rw [Function.update_noteq hk, Function.update_noteq hk']

theorem pie_sw_rho {n : ℕ} (mu : Fin n → ℕ) {j : Fin n} (h : 0 < j.val) (h1 : 1 ≤ mu j) :
    pie_sw mu j + rhoN n = (mu + rhoN n) ∘ Equiv.swap (pie_pr j) j := by
  funext k
  simp only [Pi.add_apply, Function.comp_apply, rhoN]
  have hj := j.isLt
  have hpr : (pie_pr j).val = j.val - 1 := rfl
  by_cases hkj : k = j
  · subst hkj
    rw [Equiv.swap_apply_right, pie_sw_self]
    omega
  · by_cases hkp : k = pie_pr j
    · subst hkp
      rw [Equiv.swap_apply_left, pie_sw_pr mu h]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hkp hkj, pie_sw_other mu hkj hkp]

theorem pie_alt_swap (n : ℕ) (ga : Fin n → ℕ) {i j : Fin n} (hij : i ≠ j) :
    alt n (ga ∘ Equiv.swap i j) = - alt n ga := by
  unfold alt
  have e : (Matrix.of fun a b : Fin n => (X a : MvPolynomial (Fin n) ℤ) ^ (ga ∘ Equiv.swap i j) b) =
      (Matrix.of fun a b : Fin n => (X a : MvPolynomial (Fin n) ℤ) ^ ga b).submatrix id (Equiv.swap i j) := by
    ext a b
    rfl
  rw [e, Matrix.det_permute', Equiv.Perm.sign_swap hij]
  simp

theorem pie_alt_zero (n : ℕ) (ga : Fin n → ℕ) {i j : Fin n} (hij : i ≠ j) (h : ga i = ga j) :
    alt n ga = 0 := by
  unfold alt
  exact Matrix.det_zero_of_column_eq hij fun k => by simp [h]


open Classical in
def pie_S {n : ℕ} (lam : Fin n → ℕ) (b : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (∑ j, lam j + b + 1)).filter
    fun mu => (∀ j, lam j ≤ mu j) ∧ ∑ j, mu j = ∑ j, lam j + b

theorem pie_mem_S {n : ℕ} {lam : Fin n → ℕ} {b : ℕ} {mu : Fin n → ℕ} :
    mu ∈ pie_S lam b ↔ (∀ j, lam j ≤ mu j) ∧ ∑ j, mu j = ∑ j, lam j + b := by
  unfold pie_S
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, h1, h2⟩
    rw [Finset.mem_range]
    have := Finset.single_le_sum (f := mu) (fun i _ => Nat.zero_le (mu i)) (Finset.mem_univ j)
    omega

private lemma sum_pie_cnt_eq {n b : ℕ} (s : Sym (Fin n) b) : ∑ j, pie_cnt s j = b := by
  unfold pie_cnt
  first
  | (rw [Multiset.sum_count_eq_card]
     all_goals first
       | exact s.2
       | exact fun a _ => Finset.mem_univ a)
  | (rw [← s.2, ← Multiset.toFinset_sum_count_eq]
     exact (Finset.sum_subset (Finset.subset_univ _)
       fun x _ hx => Multiset.count_eq_zero.2 (by simpa using hx)).symm)

private lemma pie_cnt_injective {n b : ℕ} {s1 s2 : Sym (Fin n) b} (h : pie_cnt s1 = pie_cnt s2) :
    s1 = s2 := by
  apply Subtype.ext
  first
  | exact Multiset.ext' fun a => congrFun h a
  | exact Multiset.ext.2 fun a => congrFun h a

theorem pie_step2 (n b : ℕ) (lam : Fin n → ℕ) :
    ∑ s : Sym (Fin n) b, alt n (lam + rhoN n + pie_cnt s) = ∑ mu ∈ pie_S lam b, alt n (mu + rhoN n) := by
  classical
  refine Finset.sum_bij (fun s _ => lam + pie_cnt s) ?_ ?_ ?_ ?_
  · intro s _
    show lam + pie_cnt s ∈ pie_S lam b
    rw [pie_mem_S]
    refine ⟨fun j => Nat.le_add_right _ _, ?_⟩
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, sum_pie_cnt_eq s]
  · intro s1 _ s2 _ h12
    apply pie_cnt_injective
    funext j
    have h3 := congrFun h12 j
    simp only [Pi.add_apply] at h3
    omega
  · intro mu hmu
    rw [pie_mem_S] at hmu
    obtain ⟨hle, hsum⟩ := hmu
    let M : Multiset (Fin n) := ∑ j, Multiset.replicate (mu j - lam j) j
    have hcount : ∀ i, Multiset.count i M = mu i - lam i := by
      intro i
      simp [M, Multiset.count_sum', Multiset.count_replicate]
    have hcard : Multiset.card M = b := by
      simp only [M, Multiset.card_sum, Multiset.card_replicate]
      have h2 : ∑ j, (mu j - lam j) + ∑ j, lam j = ∑ j, mu j := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hle j)
      omega
    refine ⟨⟨M, hcard⟩, Finset.mem_univ _, ?_⟩
    funext i
    show lam i + Multiset.count i M = mu i
    rw [hcount i]
    have := hle i
    omega
  · intro s _
    show alt n (lam + rhoN n + pie_cnt s) = alt n (lam + pie_cnt s + rhoN n)
    rw [add_right_comm]

theorem pie_sw_sum {n : ℕ} (mu : Fin n → ℕ) {j : Fin n} (h : 0 < j.val) (h1 : 1 ≤ mu j) :
    ∑ k, pie_sw mu j k = ∑ k, mu k := by
  have e : ∑ k, (pie_sw mu j + rhoN n) k = ∑ k, (mu + rhoN n) k := by
    rw [pie_sw_rho mu h h1]
    exact Equiv.sum_comp (Equiv.swap (pie_pr j) j) (mu + rhoN n)
  simp only [Pi.add_apply, Finset.sum_add_distrib] at e
  omega

theorem pie_sw_sw {n : ℕ} (mu : Fin n → ℕ) {j : Fin n} (h : 0 < j.val) (h1 : 1 ≤ mu j) :
    pie_sw (pie_sw mu j) j = mu := by
  funext k
  by_cases hkj : k = j
  · subst hkj
    rw [pie_sw_self, pie_sw_pr mu h]
    omega
  · by_cases hkp : k = pie_pr j
    · subst hkp
      rw [pie_sw_pr _ h, pie_sw_self]
      omega
    · rw [pie_sw_other _ hkj hkp, pie_sw_other _ hkj hkp]

theorem pie_mem_B {n : ℕ} {lam mu : Fin n → ℕ} {j : Fin n} :
    j ∈ pie_B lam mu ↔ 0 < j.val ∧ lam (pie_pr j) < mu j := by
  unfold pie_B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem pie_B_sw {n : ℕ} {lam mu : Fin n → ℕ} {j : Fin n} (hj : j ∈ pie_B lam mu)
    (hmax : ∀ k ∈ pie_B lam mu, k ≤ j) (hle : lam (pie_pr j) ≤ mu (pie_pr j)) :
    ∃ h' : (pie_B lam (pie_sw mu j)).Nonempty, (pie_B lam (pie_sw mu j)).max' h' = j := by
  have hj' := pie_mem_B.1 hj
  have hjB : j ∈ pie_B lam (pie_sw mu j) := by
    rw [pie_mem_B, pie_sw_self]
    exact ⟨hj'.1, by omega⟩
  refine ⟨⟨j, hjB⟩, ?_⟩
  apply le_antisymm
  · apply Finset.max'_le
    intro k hk
    by_contra hlt
    push_neg at hlt
    have hkj : k ≠ j := hlt.ne'
    have hkp : k ≠ pie_pr j := by
      intro e
      have h2 : k.val = j.val - 1 := congrArg Fin.val e
      have h3 : j.val < k.val := hlt
      omega
    have hk' := pie_mem_B.1 hk
    rw [pie_sw_other mu hkj hkp] at hk'
    have h4 := hmax k (pie_mem_B.2 hk')
    exact absurd h4 (not_le.2 hlt)
  · exact Finset.le_max' _ j hjB

def pie_g {n : ℕ} (lam mu : Fin n → ℕ) : Fin n → ℕ :=
  if h : (pie_B lam mu).Nonempty then pie_sw mu ((pie_B lam mu).max' h) else mu

open Classical in
theorem pie_bad_zero (n b : ℕ) (lam : Fin n → ℕ) (hlam : Antitone lam) :
    ∑ mu ∈ (pie_S lam b).filter (fun mu => (pie_B lam mu).Nonempty), alt n (mu + rhoN n) = 0 := by
  have key : ∀ mu : Fin n → ℕ, (∀ j, lam j ≤ mu j) → (pie_B lam mu).Nonempty →
      ∃ j : Fin n, 0 < j.val ∧ 1 ≤ mu j ∧ pie_g lam mu = pie_sw mu j ∧ (∀ k, lam k ≤ pie_sw mu j k) ∧
        ∃ h' : (pie_B lam (pie_sw mu j)).Nonempty, (pie_B lam (pie_sw mu j)).max' h' = j := by
    intro mu hle hB
    obtain ⟨j, hjdef⟩ : ∃ j, (pie_B lam mu).max' hB = j := ⟨_, rfl⟩
    have hjB : j ∈ pie_B lam mu := by
      rw [← hjdef]
      exact Finset.max'_mem _ _
    have hmax : ∀ k ∈ pie_B lam mu, k ≤ j := fun k hk => by
      rw [← hjdef]
      exact Finset.le_max' _ k hk
    have hj := pie_mem_B.1 hjB
    have hj2 := hj.2
    have hprj : pie_pr j ≤ j := by
      show (pie_pr j).val ≤ j.val
      exact Nat.sub_le _ _
    have hl : lam j ≤ lam (pie_pr j) := hlam hprj
    have hg : pie_g lam mu = pie_sw mu j := by
      unfold pie_g
      rw [dite_eq_left hB, hjdef]
    refine ⟨j, hj.1, by omega, hg, ?_, pie_B_sw hjB hmax (hle _)⟩
    intro k
    by_cases hkj : k = j
    · rw [hkj, pie_sw_self]
      have := hle (pie_pr j)
      omega
    · by_cases hkp : k = pie_pr j
      · rw [hkp, pie_sw_pr mu hj.1]
        omega
      · rw [pie_sw_other mu hkj hkp]
        exact hle k
  refine Finset.sum_involution (fun mu _ => pie_g lam mu) ?_ ?_ ?_ ?_
  · intro mu hmu
    have hmu' := hmu
    rw [Finset.mem_filter, pie_mem_S] at hmu'
    obtain ⟨⟨hle, -⟩, hB⟩ := hmu'
    obtain ⟨j, hj0, hj1, hg, -, -⟩ := key mu hle hB
    show alt n (mu + rhoN n) + alt n (pie_g lam mu + rhoN n) = 0
    rw [hg, pie_sw_rho mu hj0 hj1, pie_alt_swap n _ (pie_pr_ne hj0)]
    first
    | exact add_neg_cancel _
    | exact add_right_neg _
    | simp
  · intro mu hmu hne
    have hmu' := hmu
    rw [Finset.mem_filter, pie_mem_S] at hmu'
    obtain ⟨⟨hle, -⟩, hB⟩ := hmu'
    obtain ⟨j, hj0, hj1, hg, -, -⟩ := key mu hle hB
    show pie_g lam mu ≠ mu
    rw [hg]
    intro heq
    apply hne
    have e := pie_sw_rho mu hj0 hj1
    rw [heq] at e
    have e2 := congrFun e j
    simp only [Function.comp_apply, Equiv.swap_apply_right] at e2
    exact pie_alt_zero n _ (pie_pr_ne hj0) e2.symm
  · intro mu hmu
    have hmu' := hmu
    rw [Finset.mem_filter, pie_mem_S] at hmu'
    obtain ⟨⟨hle, hsum⟩, hB⟩ := hmu'
    obtain ⟨j, hj0, hj1, hg, hle', hne', -⟩ := key mu hle hB
    show pie_g lam mu ∈ (pie_S lam b).filter (fun mu => (pie_B lam mu).Nonempty)
    rw [hg, Finset.mem_filter, pie_mem_S]
    exact ⟨⟨hle', by rw [pie_sw_sum mu hj0 hj1, hsum]⟩, hne'⟩
  · intro mu hmu
    have hmu' := hmu
    rw [Finset.mem_filter, pie_mem_S] at hmu'
    obtain ⟨⟨hle, -⟩, hB⟩ := hmu'
    obtain ⟨j, hj0, hj1, hg, -, hne', hmax'⟩ := key mu hle hB
    show pie_g lam (pie_g lam mu) = mu
    rw [hg]
    unfold pie_g
    rw [dite_eq_left hne', hmax', pie_sw_sw mu hj0 hj1]

theorem pie_good_iff {n : ℕ} (lam mu : Fin n → ℕ) :
    ¬ (pie_B lam mu).Nonempty ↔ ∀ i j : Fin n, i.val + 1 = j.val → mu j ≤ lam i := by
  constructor
  · intro hn i j hij
    by_contra hc
    push_neg at hc
    apply hn
    have hpr : pie_pr j = i := Fin.ext (by show j.val - 1 = i.val; omega)
    exact ⟨j, pie_mem_B.2 ⟨by omega, by rw [hpr]; exact hc⟩⟩
  · rintro h ⟨j, hj⟩
    obtain ⟨hj0, hj1⟩ := pie_mem_B.1 hj
    have h2 := h (pie_pr j) j (by show j.val - 1 + 1 = j.val; omega)
    omega

theorem positivity_condition_holds (D : Formalism.BasicNotions.D7) : adm1 D := by
  classical
  unfold adm1
  intro n lam hlam b
  have hset : (pie_S lam b).filter (fun mu => ¬ (pie_B lam mu).Nonempty) =
      (Fintype.piFinset fun _ : Fin n => Finset.range (∑ j, lam j + b + 1)).filter
        (fun mu => Interlace lam mu ∧ ∑ j, mu j = ∑ j, lam j + b) := by
    ext mu
    rw [Finset.mem_filter, Finset.mem_filter, pie_mem_S, pie_good_iff]
    unfold Interlace
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hm : mu ∈ pie_S lam b := pie_mem_S.2 ⟨h1, h2⟩
      unfold pie_S at hm
      exact ⟨(Finset.mem_filter.1 hm).1, ⟨h1, h3⟩, h2⟩
    · rintro ⟨-, ⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  rw [pie_step1, pie_step2,
    ← Finset.sum_filter_add_sum_filter_not (pie_S lam b) (fun mu => (pie_B lam mu).Nonempty),
    pie_bad_zero n b lam hlam, zero_add, hset]

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem exponent_condition_holds (D : Formalism.BasicNotions.D7) : adm3 D := by
  intro p hp m k b hkm hb
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.padicValNat_def]
  exact multiplicity_choose hkm hb

theorem key_positivity_condition (D : Formalism.BasicNotions.D7) : ArchimedeanSignatureMatching D := by
  intro A _ _ _ σ w hw F G h
  have hp : Prime w := UniqueFactorizationMonoid.irreducible_iff_prime.mp hw
  haveI : (Ideal.span {w}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp

  have key : ∀ H : MvPolynomial σ A,
      C w ∣ H ↔ MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {w})) H = 0 := by
    intro H
    rw [MvPolynomial.C_dvd_iff_dvd_coeff, MvPolynomial.ext_iff]
    simp only [MvPolynomial.coeff_map]
    change (∀ i, w ∣ H.coeff i) ↔ ∀ m, (Ideal.Quotient.mk (Ideal.span {w})) (H.coeff m) = 0
    simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [key] at h
  rw [map_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl ((key F).mpr h1)
  · exact Or.inr ((key G).mpr h1)

private theorem sub_one_mod_eq_ite (a n : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a) :
    (a - 1) % n = if 1 ≤ a % n then a % n - 1 else n - 1 := by
  have hdiv := Nat.div_add_mod a n
  have hlt := Nat.mod_lt a (by omega : n > 0)
  generalize a % n = r at hdiv hlt ⊢
  generalize a / n = q at hdiv
  generalize hx : n * q = x at hdiv
  split_ifs with hr
  · have e : a - 1 = (r - 1) + x := by omega
    rw [e, ← hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · have hq : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hx
      omega
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    have hx' : x = n * q' + n := by rw [← hx, Nat.mul_succ]
    generalize hy : n * q' = y at hx'
    have e : a - 1 = (n - 1) + y := by omega
    rw [e, ← hy, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem true_derivative_digit_class (D : Formalism.BasicNotions.D7) : TrueDerivativeDigitClass D := by
  classical
  intro R _ σ P hP rho k F hF
  have hF' : ∀ m ∈ F.support, digitOfL P m = rho := fun m hm =>
    (show (↑F.support : Set (σ →₀ ℕ)) ⊆ {m | digitOfL P m = rho} from hF) hm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [F.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.pderiv_monomial, DigitClassL, MvPolynomial.monomial_mem_restrictSupport]
  by_cases hmk : m k = 0
  · right
    simp [hmk]
  · left
    have hd := hF' m hm
    show digitOfL P (m - Finsupp.single k 1) = _
    funext j
    have hdj := congrFun hd j
    simp only [digitOfL] at hdj ⊢
    by_cases hjk : j = k
    · subst hjk
      rw [Function.update_self, Finsupp.tsub_apply, Finsupp.single_eq_same,
        sub_one_mod_eq_ite (m j) (P j) (hP j) (Nat.one_le_iff_ne_zero.mpr hmk), hdj]
    · rw [Function.update_of_ne hjk, Finsupp.tsub_apply]
      simp [Ne.symm hjk, hdj]

theorem unit_function_expansion (D : Formalism.BasicNotions.D7) : UnitFunctionExpansion D := mahler_decay_products_of D (fun p hp => hDec_of hp (hdU_proved hp)) (fun p hp => hMul_proved hp)

theorem lemma_five_two_first_holds (D : Formalism.BasicNotions.D7) : FactorialUnitDecomposition D := unit_function_mahler_decay_of D (fun p hp => hDec_of hp (hdU_proved hp)) (fun p hp => hMul_proved hp)
    (fun p hp => hUnit_of hp (hdU_proved hp))

theorem support_coprimality_lemma_holds (D : Formalism.BasicNotions.D7) : ConclusionE D := prvE_of_gl_operators_form_representation D (height_bound_of_weights hSupp_proved hCop_proved)

theorem section_five_lemmas_hold (D : Formalism.BasicNotions.D7) : UnitProductLemmas D := ⟨unit_function_expansion D, show FactorialUnitDecomposition D ∧ DegreeTruncationLemma D from ⟨lemma_five_two_first_holds D, degree_truncation D⟩⟩

theorem lattice_index_lemma_holds (D : Formalism.BasicNotions.D7) : DerivativeLemmaField D := show DerivativeValuationBound D ∧ DerivativeDigitExpansion D ∧ TrueDerivativeDigitClass D from ⟨derivative_valuation_bound D, derivative_digit_expansion D, true_derivative_digit_class D⟩

theorem valuation_field_of_adm2 (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : ValuationLemmaField D := show ValuationsAdditive D ∧ ShaLengthVersionTwo D from ⟨valuationsAdditive_D7 D, generated_weight_lemma_of_reducibility D h2 (valuationsAdditive_D7 D)⟩

theorem valuation_field (D : Formalism.BasicNotions.D7) : ValuationLemmaField D := valuation_field_of_adm2 D (weight_condition_from_integral_form D)

theorem invariant_projection_sup_norm_denominator (D : Formalism.BasicNotions.D7) : InvariantDenominatorLinftyBound := linf_lemma_without_projector D (weight_condition_from_integral_form D)

theorem invariantProjectionDenominator (D : Formalism.BasicNotions.D7) : InvariantProjectionDenominator := denominator_lemma_without_projector D (weight_condition_from_integral_form D)

theorem nabla_delta_comparison_field (D : Formalism.BasicNotions.D7) : NablaDeltaComparisonField D := integral_form_of_linf_lemma D (weight_condition_from_integral_form D) (invariant_projection_sup_norm_denominator D)

theorem isotypic_projector_theorem_field (D : Formalism.BasicNotions.D7) : IsotypicProjectorTheoremField D := isotypicProjectorTheoremField_of_linfty_bound D (weight_condition_from_integral_form D) (invariant_projection_sup_norm_denominator D)

theorem translate_corollary_field (D : Formalism.BasicNotions.D7) : TranslateCorollaryField D := isotypic_lattice_corollary D (weight_condition_from_integral_form D) (nabla_delta_comparison_field D)

theorem filtered_projector_corollary_field (D : Formalism.BasicNotions.D7) : FilteredProjectorCorollaryField D := polynomial_isotypic_lattice_corollary D (weight_condition_from_integral_form D) (isotypic_projector_theorem_field D)

def InvariantProductFormula : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        (∀ π : Module.End (KK O) V, IsWtProj E 0 π → ∀ ord, NormalOrder n ord →
          ∀ T : ℕ, Module.finrank (KK O) V ≤ T → Inv = pp E 0 ord T * π)

theorem invariant_projection_of_product_formula (D : Formalism.BasicNotions.D7) (h : InvariantProductFormula) : InvariantProjectionField D := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv
  exact ⟨h p n' O S hG n V E hE M hM hMQ Inv hInv, invariantProjectionDenominator D p n' O S hG n V E hE M hM hMQ Inv hInv⟩

theorem product_formula_of_extremal_projector (D : Formalism.BasicNotions.D7) (h5 : adm5 D) : InvariantProductFormula := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv π hπ ord hord T hT
  haveI := dvr_fraction_field_charZero_prime S hG.prime
  exact invariant_projection_extremal_formula D (weight_condition_from_integral_form D) h5 E hE Inv hInv π hπ ord hord T hT

theorem counting_statement_of_block_form (D : Formalism.BasicNotions.D7) (h : InvariantProductFormula) : Conclusion1 D := show ProjectionTheorems D ∧ ValuationLemmaField D ∧ ConclusionE D ∧ UnitProductLemmas D ∧ DerivativeLemmaField D from
    ⟨show InvariantProjectionField D ∧ NablaDeltaComparisonField D ∧ IsotypicProjectorTheoremField D ∧ TranslateCorollaryField D ∧ FilteredProjectorCorollaryField D from
      ⟨invariant_projection_of_product_formula D h, nabla_delta_comparison_field D, isotypic_projector_theorem_field D, translate_corollary_field D, filtered_projector_corollary_field D⟩,
     valuation_field D, support_coprimality_lemma_holds D, section_five_lemmas_hold D, lattice_index_lemma_holds D⟩

theorem part_one_of_extremal_projector (D : Formalism.BasicNotions.D7) (h5 : adm5 D) : Conclusion1 D := counting_statement_of_block_form D (product_formula_of_extremal_projector D h5)

theorem problem_holds (D : Formalism.BasicNotions.D7) : IntegralityFromMetric D := fun hA => part_one_of_extremal_projector D (show admitted D from hA).2.2.2.2

end Formalism.MainNotions.G.GLWeightTheory
