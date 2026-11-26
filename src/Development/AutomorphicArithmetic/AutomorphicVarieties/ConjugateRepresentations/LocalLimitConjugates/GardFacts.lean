module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HasDerivAtConv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLatticeGLConjLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalGLBoundedSizeCompactFinitePolynomialCoun
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalBoundedInfiniteCompactFinitePolyCount
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLe
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory.IntCount

theorem exists_abs_repr_le_mul_house (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  let L := (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun x j => ?_⟩
  have h1 := L.le_opNorm (canonicalEmbedding E x)
  have h2 := norm_le_pi_norm (L (canonicalEmbedding E x)) j
  have h3 : L (canonicalEmbedding E x) j = (((RingOfIntegers.basis E).repr x j : ℤ) : ℂ) := by
    have := canonicalEmbedding.integralBasis_repr_apply E (x : E) j
    rw [NumberField.integralBasis_repr_apply] at this
    simpa [L] using this
  rw [h3, Complex.norm_intCast] at h2
  exact h2.trans h1

theorem card_bounded_integers_le (E : Type) [Field E] [NumberField E] :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.Finite ∧
      ({ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.ncard : ℝ) ≤ C * T ^ m := by
  classical
  obtain ⟨c, hc, hb⟩ := exists_abs_repr_le_mul_house E
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  refine ⟨Fintype.card ι, (2 * c + 3) ^ Fintype.card ι, by positivity, fun T hT => ?_⟩
  set S := {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T} with hS
  let M : ℕ := ⌈c * T⌉₊
  let s : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
  let f : 𝓞 E → (ι → ℤ) := fun ξ j => (RingOfIntegers.basis E).repr ξ j
  have hf : Function.Injective f := fun ξ η h =>
    (RingOfIntegers.basis E).ext_elem fun j => congrFun h j
  have hmaps : ∀ ξ ∈ S, f ξ ∈ s := by
    intro ξ hξ
    refine Fintype.mem_piFinset.2 fun j => Finset.mem_Icc.2 (abs_le.1 ?_)
    have hh : house (ξ : E) ≤ T := by
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun φ => ?_
      have := hξ (InfinitePlace.mk φ)
      rwa [InfinitePlace.apply] at this
    have h1 := hb ξ j
    have h2 : c * house (ξ : E) ≤ (M : ℝ) :=
      (mul_le_mul_of_nonneg_left hh hc).trans (Nat.le_ceil _)
    exact_mod_cast h1.trans h2
  have hsub : S ⊆ f ⁻¹' (s : Set (ι → ℤ)) := fun ξ hξ => hmaps ξ hξ
  have hfin : S.Finite := ((s.finite_toSet).preimage hf.injOn).subset hsub
  refine ⟨hfin, ?_⟩
  have hcard : S.ncard ≤ s.card := by
    rw [← Set.ncard_coe_finset s]
    exact Set.ncard_le_ncard_of_injOn f (fun ξ hξ => hmaps ξ hξ) hf.injOn s.finite_toSet
  have hs : (s.card : ℝ) = (2 * (M : ℝ) + 1) ^ Fintype.card ι := by
    simp only [s, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    push_cast
    congr 1
    have : (↑M + 1 - -↑M : ℤ).toNat = 2 * M + 1 := by omega
    rw [this]; push_cast; ring
  have hM : (M : ℝ) ≤ c * T + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hbase : 2 * (M : ℝ) + 1 ≤ (2 * c + 3) * T := by nlinarith
  calc (S.ncard : ℝ) ≤ s.card := by exact_mod_cast hcard
    _ = (2 * (M : ℝ) + 1) ^ Fintype.card ι := hs
    _ ≤ ((2 * c + 3) * T) ^ Fintype.card ι := by gcongr
    _ = (2 * c + 3) ^ Fintype.card ι * T ^ Fintype.card ι := mul_pow _ _ _

end GlobalTheory.IntCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLeStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le : ∀ (E : Type) [Field E] [NumberField E], ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.Finite ∧ ({ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.IntCount.card_bounded_integers_le | exact GlobalTheory.IntCount.card_bounded_integers_le | (intros; apply GlobalTheory.IntCount.card_bounded_integers_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalBoundedInfiniteCompactFinitePolyCount
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem place_le_norm_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (ξ : E)
    (w : InfinitePlace E) : w ξ ≤ ‖pInf E (algebraMap E (Ad E) ξ)‖ := by
  have h := norm_le_pi_norm (pInf E (algebraMap E (Ad E) ξ)) w
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq] at h
  exact h

theorem rat_bounded_compact_polynomial : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ∃ m : ℕ,
    ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧
      ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ)
        ≤ C * T ^ m := by
  intro E _ _ _
  obtain ⟨m, C₀, hC₀, hcount⟩ := GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le E
  refine ⟨m, fun Kf hKf => ?_⟩
  obtain ⟨n, hn, hint⟩ := GlobalTheory.T.exists_common_denominator_compact_finiteAdeles E Kf hKf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨C₀ * (n : ℝ) ^ m, by positivity, fun T hT => ?_⟩
  have hnT : (1 : ℝ) ≤ n * T := by nlinarith
  obtain ⟨hAfin, hAcard⟩ := hcount (n * T) hnT
  set A := {x : 𝓞 E | ∀ w : InfinitePlace E, w (x : E) ≤ n * T}
  set S := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  have hsub : S ⊆ (fun x : 𝓞 E => (x : E) / n) '' A := by
    intro ξ hξ
    have hi : IsIntegral ℤ ((n : E) * ξ) := hint ξ hξ.2
    refine ⟨⟨(n : E) * ξ, hi⟩, fun w => ?_, ?_⟩
    · show w ((n : E) * ξ) ≤ n * T
      rw [← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul, Complex.norm_natCast,
        InfinitePlace.norm_embedding_eq]
      exact mul_le_mul_of_nonneg_left ((place_le_norm_pInf ξ w).trans hξ.1) (Nat.cast_nonneg n)
    · show (n : E) * ξ / n = ξ
      field_simp
  have hSfin : S.Finite := (hAfin.image _).subset hsub
  refine ⟨hSfin, ?_⟩
  have h1 : S.ncard ≤ A.ncard :=
    (Set.ncard_le_ncard hsub (hAfin.image _)).trans (Set.ncard_image_le hAfin)
  calc (S.ncard : ℝ) ≤ A.ncard := by exact_mod_cast h1
    _ ≤ C₀ * (n * T) ^ m := hAcard
    _ = C₀ * (n : ℝ) ^ m * T ^ m := by rw [mul_pow]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalBoundedInfiniteCompactFinitePolyCountStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ∃ m : ℕ, ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧ ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.rat_bounded_compact_polynomial | exact GlobalTheory.rat_bounded_compact_polynomial | (intros; apply GlobalTheory.rat_bounded_compact_polynomial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalGLBoundedSizeCompactFinitePolynomialCoun
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem ratGL_bounded_count : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  intro E _ _ _ a
  obtain ⟨m, hm⟩ := GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount E
  refine ⟨m * (a * a), fun Kf hKf => ?_⟩
  let Kf' : Set (Af E) := ⋃ i : Fin a, ⋃ j : Fin a, (fun g : GL (Fin a) (Af E) => g.val i j) '' Kf
  have hc : IsCompact Kf' := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hKf.image ?_
    exact (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨C, hC0, hC⟩ := hm Kf' hc
  refine ⟨C ^ (a * a), pow_nonneg hC0 _, fun T hT => ?_⟩
  obtain ⟨hNf, hNc⟩ := hC T hT
  let N : Set E := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf'}
  let S : Set (GL (Fin a) E) := {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}
  change S.Finite ∧ (S.ncard : ℝ) ≤ C ^ (a * a) * T ^ (m * (a * a))
  have hsub : ∀ γ ∈ S, ∀ i j, γ.val i j ∈ N := by
    intro γ hγ i j
    obtain ⟨h1, h2⟩ := hγ
    refine ⟨?_, ?_⟩
    · have he : pInf E (algebraMap E (Ad E) (γ.val i j)) = (toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val) i j := rfl
      rw [he]
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans h1
    · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨_, h2, rfl⟩⟩⟩
  classical
  let F : Finset E := hNf.toFinset
  let P : Finset (Fin a → Fin a → E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  let f : GL (Fin a) E → (Fin a → Fin a → E) := fun γ => γ.val
  have hf : Function.Injective f := fun x y h => Units.ext h
  have himg : f '' S ⊆ (P : Set (Fin a → Fin a → E)) := by
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [P, F, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i j => hsub γ hγ i j
  have hSfin : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset himg) hf.injOn
  refine ⟨hSfin, ?_⟩
  have hcardP : P.card = (F.card ^ a) ^ a := by
    simp [P, Fintype.card_piFinset, Finset.prod_const]
  have hS : S.ncard ≤ (F.card ^ a) ^ a := by
    rw [← Set.ncard_image_of_injective S hf, ← hcardP, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg P.finite_toSet
  have hF : (F.card : ℝ) ≤ C * T ^ m := by
    rw [← Set.ncard_eq_toFinset_card N hNf]; exact hNc
  calc (S.ncard : ℝ) ≤ ((F.card ^ a) ^ a : ℕ) := by exact_mod_cast hS
    _ = (F.card : ℝ) ^ (a * a) := by push_cast; rw [← pow_mul]
    _ ≤ (C * T ^ m) ^ (a * a) := pow_le_pow_left₀ (Nat.cast_nonneg _) hF _
    _ = C ^ (a * a) * T ^ (m * (a * a)) := by rw [mul_pow, ← pow_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalGLBoundedSizeCompactFinitePolynomialCounStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalGL_boundedSize_compactFinite_polynomialCount : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.ratGL_bounded_count | exact GlobalTheory.ratGL_bounded_count | (intros; apply GlobalTheory.ratGL_bounded_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsSplitCentreExponentLeOfConjMemCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsSplitCentreExponentLeOfConjMemCompact
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CentralExponent

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.UnitaryBC

theorem abs_le_of_conj_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ W : Set (GA E a), IsCompact W → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (g : GA E a),
      g⁻¹ * (ratGL E a γ * GlobalTheory.UnitaryBC.splitCentre E a 1 ^ n) * g ∈ W → |n| ≤ n₀ := by
  intro E _ _ _ a ha W hW
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  have hc : Continuous fun x : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det x)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨C, hC⟩ := hW.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊, fun γ n g hmem => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have e : GeneralLinearGroup.det (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g) =
      diag E (GeneralLinearGroup.det γ) * eIdele E ^ ((a : ℤ) * n) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, ← zpow_natCast, ← _root_.zpow_mul,
      mul_comm _ (GeneralLinearGroup.det g), mul_inv_cancel_left]
  have key : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g))) =
      ((a : ℤ) * n : ℤ) * Real.log (ideleNorm (E := E) (eIdele E)) := by
    rw [e, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul, map_zpow,
      Real.log_zpow]
  have h1 := hC _ hmem
  rw [key, Real.norm_eq_abs, abs_mul, abs_of_pos hL] at h1
  have h2 : (|n| : ℝ) ≤ |(((a : ℤ) * n : ℤ) : ℝ)| := by
    push_cast
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast ha)
  have h3 : (|n| : ℝ) ≤ ⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊ :=
    (h2.trans ((le_div_iff₀ hL).2 h1)).trans (Nat.le_ceil _)
  exact_mod_cast h3

end GlobalTheory.CentralExponent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsSplitCentreExponentLeOfConjMemCompactStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_splitCentre_exponent_le_of_conj_mem_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ W : Set (GA E a), IsCompact W → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (g : GA E a), g⁻¹ * (ratGL E a γ * GlobalTheory.UnitaryBC.splitCentre E a 1 ^ n) * g ∈ W → |n| ≤ n₀ := by
  first | exact @GlobalTheory.CentralExponent.abs_le_of_conj_mem | exact GlobalTheory.CentralExponent.abs_le_of_conj_mem | (intros; apply GlobalTheory.CentralExponent.abs_le_of_conj_mem <;> assumption)
end
end

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem card_latticeGL_conj_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ A : ℕ,
    ∀ W : Set (GA E a), IsCompact W → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GL (Fin a) (Cinf E),
      {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.Finite ∧
      ({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℝ) ≤
        C * height y ^ (2 * A) := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨0, fun W _ => ⟨1, zero_le_one, fun y => ?_⟩⟩
    have hs : ∀ s : Set (GlobalTheory.UnitaryBC.latticeGL E 0), s.Subsingleton := fun s x _ z _ =>
      Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))
    refine ⟨(hs _).finite, ?_⟩
    rw [pow_zero, mul_one]
    exact_mod_cast (Set.ncard_le_one_iff (hs _).finite).2 fun h1 h2 => hs _ h1 h2
  obtain ⟨m, hm⟩ := GlobalTheory.T.rationalGL_boundedSize_compactFinite_polynomialCount E a
  refine ⟨m, fun W hW => ?_⟩
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.abs_splitCentre_exponent_le_of_conj_mem_compact E a ha W hW
  obtain ⟨hInf, hFin, -, -⟩ := GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a
  set e : GA E a := GlobalTheory.UnitaryBC.splitCentre E a 1 with he
  set W' : Set (GA E a) := ⋃ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, (fun g => g * (e ^ n)⁻¹) '' W with hW'
  have hW'c : IsCompact W' := (Finset.Icc (-(n₀ : ℤ)) n₀).isCompact_biUnion fun n _ =>
    hW.image (continuous_mul_const _)
  set Kf : Set (GL (Fin a) (Af E)) := (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) '' W' with hKf
  have hKfc : IsCompact Kf := hW'c.image hFin
  have hv : Continuous fun g : GA E a =>
      ((Matrix.GeneralLinearGroup.map (pInf E) g : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_val.comp hInf
  have ht : Continuous (toL : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a) := continuous_id
  have hcn : Continuous fun g : GA E a => ‖toL (Matrix.GeneralLinearGroup.map (pInf E) g).val‖ :=
    continuous_norm.comp (ht.comp hv)
  obtain ⟨B₀, hB₀⟩ := hW'c.exists_bound_of_continuousOn hcn.continuousOn
  set B : ℝ := max 0 B₀ with hB
  have hB0 : 0 ≤ B := le_max_left _ _
  have hBb : ∀ w ∈ W', ‖toL (Matrix.GeneralLinearGroup.map (pInf E) w).val‖ ≤ B := fun w hw =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₀ w hw).trans (le_max_right _ _))
  obtain ⟨C₁, hC₁0, hC₁⟩ := hm Kf hKfc
  set N : ℝ := ((Set.Icc (-(n₀ : ℤ)) n₀).ncard : ℝ) with hN
  set c : ℝ := 1 + (a : ℝ) ^ 2 * B with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) ^ 2 * B := by positivity
    linarith
  refine ⟨C₁ * c ^ m * N, by positivity, fun y => ?_⟩
  set T : ℝ := c * height y ^ 2 with hT
  have hh := one_le_height y
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hh)
  obtain ⟨hfin, hcard⟩ := hC₁ T hT1
  set S := {δ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ)).val‖ ≤ T ∧
    Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) ∈ Kf} with hS
  let f : GL (Fin a) E × ℤ → GlobalTheory.UnitaryBC.latticeGL E a := fun p =>
    ⟨ratGL E a p.1 * e ^ p.2, GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.2 ⟨p.1, p.2, rfl⟩⟩
  have hsub : {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W} ⊆
      f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀) := by
    rintro ⟨γ, hγ⟩ hγW
    obtain ⟨δ, n, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ
    change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y ∈ W at hγW
    have hn : |n| ≤ n₀ := hn₀ δ n _ hγW
    have hn' : n ∈ Set.Icc (-(n₀ : ℤ)) n₀ := abs_le.1 hn
    set w := (infGL E a y)⁻¹ * ratGL E a δ * infGL E a y with hw
    have hcomm : Commute (e ^ n) (infGL E a y) :=
      (Commute.zpow_left (GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm 1 (infGL E a y)) n)
    have hwW : w ∈ W' := by
      refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_Icc.2 hn')) ⟨_, hγW, ?_⟩
      change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y * (e ^ n)⁻¹ = w
      simp only [mul_assoc]
      rw [← mul_assoc (e ^ n) (infGL E a y), hcomm.eq, mul_inv_cancel_right]
      all_goals simp only [hw, mul_assoc]
    have hδ : ratGL E a δ = infGL E a y * w * (infGL E a y)⁻¹ := by rw [hw]; group
    refine ⟨(δ, n), ⟨⟨?_, ?_⟩, hn'⟩, rfl⟩
    · have e1 : Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ) =
          y * Matrix.GeneralLinearGroup.map (pInf E) w * y⁻¹ := by
        rw [hδ, map_mul, map_mul, map_inv, pInf_infGL]
      rw [e1, Units.val_mul, Units.val_mul]
      have hw' := hBb w hwW
      have p1 := GlobalTheory.AutGrowth.norm_toL_mul_le (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val) (y⁻¹).val
      have p2 := GlobalTheory.AutGrowth.norm_toL_mul_le y.val (Matrix.GeneralLinearGroup.map (pInf E) w).val
      have hy1 : ‖toL y.val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
      have hy2 : ‖toL (y⁻¹).val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL y.val)]
      have n1 := norm_nonneg (toL y.val)
      have n2 := norm_nonneg (toL (y⁻¹).val)
      have n3 := norm_nonneg (toL (Matrix.GeneralLinearGroup.map (pInf E) w).val)
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have q1 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val)‖ ≤ a * (height y * B) :=
        p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul hy1 hw' n3 (by linarith)) ha0)
      have q2 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val * (y⁻¹).val)‖ ≤
          a * ((a * (height y * B)) * height y) :=
        p1.trans (mul_le_mul_of_nonneg_left (mul_le_mul q1 hy2 n2 (by positivity)) ha0)
      refine q2.trans ?_
      rw [hT, hc]
      have : 0 ≤ height y ^ 2 := by positivity
      nlinarith
    · have e2 : Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) =
          Matrix.GeneralLinearGroup.map (pFin E) w := by
        rw [hδ, map_mul, map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]
      rw [e2]
      exact ⟨w, hwW, rfl⟩
  have hfin2 : (f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀)).Finite := (hfin.prod (Set.finite_Icc _ _)).image f
  refine ⟨hfin2.subset hsub, ?_⟩
  have k1 := Set.ncard_le_ncard hsub hfin2
  have k2 := Set.ncard_image_le (f := f) (hfin.prod (Set.finite_Icc (-(n₀ : ℤ)) n₀))
  rw [Set.ncard_prod] at k2
  have k3 : (({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℕ) : ℝ) ≤
      (S.ncard : ℝ) * N := by rw [hN]; exact_mod_cast k1.trans k2
  refine k3.trans ?_
  have hN0 : 0 ≤ N := by positivity
  calc (S.ncard : ℝ) * N ≤ C₁ * T ^ m * N := mul_le_mul_of_nonneg_right hcard hN0
    _ = C₁ * c ^ m * N * height y ^ (2 * m) := by rw [hT, mul_pow, ← pow_mul, mul_comm 2 m]; ring

end GlobalTheory
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvGrow
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LatCount
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.latCount :
    UpperTheory.V.Cj.H.LatCount := by
  intro E _ _ _ a _ S hS g
  obtain ⟨A, hA⟩ := GlobalTheory.card_latticeGL_conj_le E a
  set c : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g with hc
  set f : GA E a := finGL E a (GeneralLinearGroup.map (pFin E) g) with hf
  obtain ⟨C, hC0, hC⟩ := hA ((fun s => f * s * f⁻¹) '' S) (hS.image (by fun_prop))
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c))
  refine ⟨C * B ^ (2 * A), 2 * A, fun y => ?_⟩
  obtain ⟨hfin, hle⟩ := hC (c * y)
  have hg : g * infGL E a y = infGL E a (c * y) * f := by
    refine ga_ext ?_ ?_
    · simp only [map_mul, hf, pInf_infGL, pInf_finGL, mul_one, hc]
    · simp only [map_mul, hf, pFin_infGL, pFin_finGL, mul_one, one_mul]
  refine ⟨_, hle.trans ?_, ?_⟩
  · have h0 : 0 ≤ GlobalTheory.CuspRep.height (c * y) := zero_le_one.trans (one_le_height _)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hB c rfl y) _) hC0
  · rw [hfin.cast_ncard_eq]
    refine Set.encard_le_encard fun γ hγ => ⟨_, hγ, ?_⟩
    rw [hg]
    group
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.cvGrow :
    UpperTheory.V.Cj.H.CvGrow := by
  intro E _ _ _ a ha μ _ _ ψ hψc hψs F g
  obtain ⟨B, hB0, hB⟩ := cvCount (GA E a) (latticeGL E a) μ ψ hψc hψs
  have hKc : IsCompact (tsupport ψ) := hψs.isCompact
  obtain ⟨C, N, hC⟩ := latCount E a ha ((tsupport ψ)⁻¹ * tsupport ψ) (hKc.inv.mul hKc) g
  refine ⟨B * ‖F‖ * C, N, fun y => ?_⟩
  obtain ⟨M, hM, hcard⟩ := hC y
  have key : ∀ h : GA E a,
      {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.encard ≤ (M : ℕ∞) := by
    intro h
    by_cases hne : {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.Nonempty
    · obtain ⟨γ₀, hγ₀⟩ := hne
      refine le_trans (Set.encard_le_encard_of_injOn (f := fun γ => γ * γ₀⁻¹) ?_ ?_) hcard
      · intro γ hγ
        simp only [Set.mem_setOf_eq] at hγ hγ₀ ⊢
        have h₁ := subset_tsupport ψ hγ
        have h₂ := subset_tsupport ψ hγ₀
        have e : (g * infGL E a y)⁻¹ * ↑(γ * γ₀⁻¹) * (g * infGL E a y)
            = ((↑γ * h)⁻¹ * (g * infGL E a y))⁻¹ * ((↑γ₀ * h)⁻¹ * (g * infGL E a y)) := by
          push_cast
          group
        rw [e]
        exact Set.mul_mem_mul (Set.inv_mem_inv.mpr h₁) h₂
      · intro γ _ δ _ hγδ
        simpa using hγδ
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hx := hB (g * infGL E a y) M key F
  calc ‖cv ψ F (g * infGL E a y)‖ ≤ B * M * ‖F‖ := hx
    _ = B * ‖F‖ * M := by ring
    _ ≤ B * ‖F‖ * (C * height y ^ N) :=
        mul_le_mul_of_nonneg_left hM (mul_nonneg hB0 (norm_nonneg _))
    _ = B * ‖F‖ * C * height y ^ N := by ring
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem grow_lin {φ ψ : GA E a → ℂ} (hφ : Grow φ) (hψ : Grow ψ) : Grow (φ + ψ) := by
  intro g
  obtain ⟨C, N, h⟩ := hφ g
  obtain ⟨C', N', h'⟩ := hψ g
  refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
  have h1 := GlobalTheory.CuspRep.one_le_height y
  have h0 : 0 ≤ GlobalTheory.CuspRep.height y := zero_le_one.trans h1
  have e1 : C * GlobalTheory.CuspRep.height y ^ N ≤ |C| * GlobalTheory.CuspRep.height y ^ (N + N') :=
    mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right _ _)) (pow_nonneg h0 _) (abs_nonneg C)
  have e2 : C' * GlobalTheory.CuspRep.height y ^ N' ≤ |C'| * GlobalTheory.CuspRep.height y ^ (N + N') :=
    mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left _ _)) (pow_nonneg h0 _) (abs_nonneg C')
  rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add ((h y).trans e1) ((h' y).trans e2))

private theorem grow_smul (s : ℂ) {φ : GA E a → ℂ} (hφ : Grow φ) : Grow (s • φ) := by
  intro g
  obtain ⟨C, N, h⟩ := hφ g
  refine ⟨‖s‖ * C, N, fun y => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg s)

private theorem lev_of {φ : Sm E a} {S : Set (GL (Fin a) (Af E))} (hS : S ∈ 𝓝 1)
    (h : ∀ k ∈ S, act (.fin k) φ = φ) : HasLev φ :=
  isOpen_stab_of_mem_nhds (finRep E a) φ (Filter.mem_of_superset hS h)

private theorem lev_nhds {φ : Sm E a} (h : HasLev φ) : {k : GL (Fin a) (Af E) | act (.fin k) φ = φ} ∈ 𝓝 1 := by
  refine h.mem_nhds ?_
  change finRep E a 1 φ = φ
  rw [map_one]; rfl

private theorem rt_cv (μ : Measure (GA E a)) {φ ψ : Sm E a} {F : HL μ} (e : φ.1 = cv ψ.1 F) (g : GA E a) :
    (rt E a g φ).1 = cv (rt E a g ψ).1 F := by
  funext x
  change φ.1 (x * g) = ∫ y, GlobalTheory.AutomorphicL2Unitary.lift _ F y * ψ.1 (y⁻¹ * x * g) ∂μ
  rw [e]
  simp only [cv, mul_assoc]

end

theorem UpperTheory.V.Cj.H.gardFacts :
    UpperTheory.V.Cj.H.GardFacts := by
  intro E _ _ _ a ha μ _ _ φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ψ, F, hψ, e⟩ := h
    obtain ⟨t1, t2⟩ := testOps E a ψ
    have hc : Continuous ψ.1 := (t1 hψ.2).1
    refine ⟨lev_of (lev_nhds hψ.2) fun k hk => ?_, ?_, ?_, fun X => ?_, fun g => ?_⟩
    · have hk' : rt E a (finGL E a k) ψ = ψ := hk
      apply Subtype.ext
      change (rt E a (finGL E a k) φ).1 = φ.1
      rw [rt_cv μ e, hk', e]
    · obtain ⟨h, -⟩ := convolution_L2_class (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1 F
      unfold InL
      rw [e]
      exact h
    · rw [e]
      exact cvGrow E a ha μ ψ.1 hc hψ.1 F
    · exact Submodule.subset_span ⟨_, F, (t2 hψ).1 X, cvLie E a μ ψ φ hψ F e X⟩
    · exact Submodule.subset_span ⟨_, F, (t2 hψ).2 g, rt_cv μ e g⟩
  | zero =>
    refine ⟨lev_of Filter.univ_mem fun k _ => map_zero _, ⟨fun _ _ _ => rfl, ?_⟩, fun g => ⟨0, 0, fun y => by simp⟩,
      fun X => by rw [map_zero]; exact zero_mem _, fun g => by rw [map_zero]; exact zero_mem _⟩
    exact MemLp.zero
  | add φ ψ _ _ h h' =>
    refine ⟨lev_of (Filter.inter_mem (lev_nhds h.1) (lev_nhds h'.1)) fun k hk => ?_, ?_, grow_lin h.2.2.1 h'.2.2.1,
      fun X => by rw [map_add]; exact add_mem (h.2.2.2.1 X) (h'.2.2.2.1 X),
      fun g => by rw [map_add]; exact add_mem (h.2.2.2.2 g) (h'.2.2.2.2 g)⟩
    · rw [map_add (f := _), hk.1, hk.2]
    · simpa only [one_smul] using ((clFacts E a μ).1 φ ψ 1 1 h.2.1 h'.2.1).1
  | smul s φ _ h =>
    refine ⟨lev_of (lev_nhds h.1) fun k hk => ?_, ?_, grow_smul s h.2.2.1,
      fun X => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.1 X),
      fun g => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.2 g)⟩
    · rw [map_smul, hk]
    · simpa only [zero_smul, add_zero] using ((clFacts E a μ).1 φ φ s 0 h.2.1 h.2.1).1
