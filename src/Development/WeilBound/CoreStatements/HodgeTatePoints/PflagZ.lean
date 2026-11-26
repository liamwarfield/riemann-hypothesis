module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb
public import Development.WeilBound.CoreStatements.IdealCycleValues.IntersectionNumbersPermInvariant
public import Development.WeilBound.CoreStatements.IdealCycleValues.IntNumLCons
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HasExpansionOfMemSpan
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

def negReal (N : ℕ) : MvPolynomial (Fin N) ℤ →ₐ[ℤ] MvPolynomial (Fin N) ℝ :=
  aeval fun i => (-X i : MvPolynomial (Fin N) ℝ)

theorem negReal_hsymm (N a : ℕ) :
    negReal N (hsymm (Fin N) ℤ a) =
      aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [negReal, hsymm, map_sum, map_multiset_prod, Multiset.map_map, Function.comp_def, aeval_X]

theorem negReal_isHomogeneous {N n : ℕ} {P : MvPolynomial (Fin N) ℤ} (hP : P.IsHomogeneous n) :
    (negReal N P).IsHomogeneous n := by
  have h := hP.aeval (S := ℝ) (n := 1) (fun i => (-X i : MvPolynomial (Fin N) ℝ))
    (fun i => (isHomogeneous_X ℝ i).neg)
  simpa [negReal] using h

theorem negReal_psum (N k : ℕ) :
    negReal N (psum (Fin N) ℤ k) = (-1) ^ k * ∑ i, (X i ^ k : MvPolynomial (Fin N) ℝ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [negReal, psum, map_sum, map_pow, aeval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow]

def HasExpansion (N k : ℕ) (G : MvPolynomial (Fin N) ℤ) : Prop :=
  ∃ R : ℕ → MvPolynomial (Fin N) ℝ, (∀ a, (R a).IsHomogeneous (k - a)) ∧
    negReal N G = ∑ a ∈ Finset.Icc 1 k,
      aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) * R a

theorem hasExpansion_hsymmPart {N k : ℕ} (hk : 1 ≤ k) (μ : k.Partition) :
    HasExpansion N k (hsymmPart (Fin N) ℤ μ) := by
  classical
  have hne : μ.parts ≠ 0 := by
    intro h
    have := μ.parts_sum
    rw [h] at this
    simp at this
    omega
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
  have hsum : a + t.sum = k := by
    have := μ.parts_sum
    rwa [ht, Multiset.sum_cons] at this
  have hpos : 0 < a := μ.parts_pos ha
  have hmem : a ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hpos, by omega⟩
  refine ⟨Pi.single a (negReal N (t.map (hsymm (Fin N) ℤ)).prod), fun b => ?_, ?_⟩
  · by_cases hb : b = a
    · subst hb
      rw [Pi.single_eq_same]
      have h := negReal_isHomogeneous (SymmetricSpanHsymm.isHomogeneous_prod_map_hsymm (σ := Fin N) t)
      rwa [show t.sum = k - b by omega] at h
    · rw [Pi.single_eq_of_ne hb]
      exact isHomogeneous_zero _ _ _
  · rw [Finset.sum_eq_single_of_mem a hmem
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])]
    rw [Pi.single_eq_same, hsymmPart, ht, Multiset.map_cons, Multiset.prod_cons, map_mul,
      negReal_hsymm]

theorem hasExpansion_of_mem_span {N k : ℕ} (hk : 1 ≤ k) {G : MvPolynomial (Fin N) ℤ}
    (hG : G ∈ Submodule.span ℤ (Set.range fun μ : k.Partition => hsymmPart (Fin N) ℤ μ)) :
    HasExpansion N k G := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    exact hasExpansion_hsymmPart hk μ
  | zero => exact ⟨0, fun a => isHomogeneous_zero _ _ _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨R, hR, e⟩ := hx
    obtain ⟨S, hS, f⟩ := hy
    refine ⟨R + S, fun a => (hR a).add (hS a), ?_⟩
    simp only [map_add (f := _), e, f, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨R, hR, e⟩ := hx
    refine ⟨fun a => C (c : ℝ) * R a, fun a => ?_, ?_⟩
    · simpa using (isHomogeneous_C (Fin N) (c : ℝ)).mul (hR a)
    · rw [map_zsmul, e, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [zsmul_eq_mul, show ((c : MvPolynomial (Fin N) ℝ)) = C (c : ℝ) by simp]
      ring

theorem psum_eq_sum_hsymm_neg :
    ∀ (N k : ℕ), 1 ≤ k → ∃ R : ℕ → MvPolynomial (Fin N) ℝ, (∀ a, (R a).IsHomogeneous (k - a)) ∧
      (∑ i, X i ^ k : MvPolynomial (Fin N) ℝ) = ∑ a ∈ Finset.Icc 1 k,
        aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) * R a := by
  intro N k hk
  obtain ⟨R, hR, e⟩ := hasExpansion_of_mem_span hk
    (SymmetricSpanHsymm.full N k (psum (Fin N) ℤ k) (isHomogeneous_psum N k) (psum_isSymmetric _ _ _))
  refine ⟨fun a => C ((-1) ^ k) * R a, fun a => ?_, ?_⟩
  · simpa using (isHomogeneous_C (Fin N) (((-1 : ℝ)) ^ k)).mul (hR a)
  · have h1 : ((-1 : MvPolynomial (Fin N) ℝ) ^ k) * (-1) ^ k = 1 := by
      rw [← mul_pow]; simp
    rw [negReal_psum] at e
    calc (∑ i, X i ^ k : MvPolynomial (Fin N) ℝ)
        = (-1) ^ k * ((-1) ^ k * ∑ i, (X i ^ k : MvPolynomial (Fin N) ℝ)) := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by
          rw [e, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [map_pow, map_neg, map_one]
          ring

end

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumLinearSubst
section -- merged from Development.WeilBound.CoreStatements.IdealCycleValues.GenNumLinearChangeClasses
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.genNum_linear_change_classes : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime V → ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → genNum F V (fun t => ∑ i, M t i • cls i) H Q = genNum F V cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  intro F _ K _ _ ι _ V d hV hd σ σ' _ cls M H m hH Q hQ
  unfold genNum classList
  rw [BaseChangeColon.evL_eq (H := aeval _ H)]
  exact BaseChangeColon.subst_abs d (fun l => (intNumL F V l : ℝ))
    (fun l l' h => by rw [BaseChangeColon.intersection_numbers_perm_invariant.1 F K ι V l l' h])
    (fun b b' l hl => by
      rw [BaseChangeColon.intNumL_add F K ι V d hV hd b b' l hl, Int.cast_add]) cls M H m hH Q hQ
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_linear_subst : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime V → ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → genNum F V (fun t => ∑ i, M t i • cls i) H Q = genNum F V cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  exact @BaseChangeColon.genNum_linear_change_classes

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HsymmDualRootsTrivNumZero
section -- merged from Development.WeilBound.CoreStatements.IdealCycleValues.FlagFrameOfPointIdeal
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace BaseChangeColon

theorem foldr_diffStep_zero {K : Type} (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l) (h : (K → ℤ) → ℤ) :
    l.foldr diffStep h = 0 := by
  induction l with
  | nil => simp at hl
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hl with hb | hb
    · subst hb
      funext m
      simp [diffStep]
    · rw [ih hb]
      funext m
      simp [diffStep]

theorem intNumL_of_zero_mem {F : Type} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (V : Ideal (MRing ι F)) (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l) : intNumL F V l = 0 := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get, foldr_diffStep_zero l hl]
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, hm⟩ := h.choose_spec.exists
    exact hm.symm
  · rfl

theorem flag_frame_of_point_ideal : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ a : ℕ, 1 ≤ a → ∀ Y : List (K → ℤ), a + Y.length = e → ∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F (pointIdeal F y) (rootList (fun i => -b i) α ++ Y) = 0 := by
  intro hS F _ Ω _ _ K _ _ ι _ y e hP hd N w b hw a ha Y hY
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact Finset.sum_eq_zero fun α hα => by
      rw [Finset.Nat.mem_antidiagonalTuple] at hα
      simp at hα
  have ht : AlgebraicIndependent Ω
      ((IsScalarTower.toAlgHom Ω (MvPolynomial (Fin N) Ω) (FractionRing (MvPolynomial (Fin N) Ω))) ∘ X) :=
    (MvPolynomial.algebraicIndependent_X (Fin N) Ω).map'
      (IsFractionRing.injective (MvPolynomial (Fin N) Ω) (FractionRing (MvPolynomial (Fin N) Ω)))
  have h1 := hS F Ω K ι y e hP hd N hN _ _ w b hw N 0 _ (isTwistedDualGens_triv F y N) _ _ ht
    (N - 1 + a) Y (by omega)
  have h2 := hS F Ω K ι y e hP hd N hN _ _ _ _ (isFlagFrame_scaledTriv F y N (one_ne_zero (α := Ω))) N 0 _
    (isTwistedDualGens_triv F y N) _ _ ht (N - 1 + a) Y (by omega)
  rw [projIdeal_independent_of_basis F Ω K ι y N N _ w (scaledBasis N (one_ne_zero (α := Ω))) _ _ _ ht, h2,
    if_pos (Nat.le_add_right _ _), if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at h1
  simp only [zero_sub] at h1
  rw [← h1]
  refine Finset.sum_eq_zero fun α hα => intNumL_of_zero_mem _ _ ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hα
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) (by omega)
  refine List.mem_append_left _ ?_
  unfold rootList
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_replicate.mpr ⟨hi, by simp⟩⟩

end BaseChangeColon
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem hsymm_dualRoots_triv_numZero : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ a : ℕ, 1 ≤ a → ∀ Y : List (K → ℤ), a + Y.length = e → ∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F (pointIdeal F y) (rootList (fun i => -b i) α ++ Y) = 0 :=
  BaseChangeColon.flag_frame_of_point_ideal

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumProductExpansion
section -- merged from Development.WeilBound.CoreStatements.IdealCycleValues.GenNumMulExpansion
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.genNum_mul_expansion : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * genNum F V cls H (classList cls μ ++ Q) := by
  intro F _ K _ _ ι _ σ V cls H G Q
  classical
  have key : ∀ (P : MvPolynomial σ ℝ) (L : List (K → ℤ)) (s : Finset (σ →₀ ℕ)), P.support ⊆ s →
      genNum F V cls P L = ∑ κ ∈ s, AddMonoidAlgebra.coeff P κ * (intNumL F V (classList cls κ ++ L) : ℝ) := by
    intro P L s hs
    show ∑ κ ∈ P.support, AddMonoidAlgebra.coeff P κ * (intNumL F V (classList cls κ ++ L) : ℝ) = _
    refine Finset.sum_subset hs (fun κ _ hκ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul]
  have hadd : ∀ P P' : MvPolynomial σ ℝ, genNum F V cls (P + P') Q = genNum F V cls P Q + genNum F V cls P' Q := by
    intro P P'
    rw [key (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add,
      key P Q (P.support ∪ P'.support) Finset.subset_union_left,
      key P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : genNum F V cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 Q ∅ (by simp)]
    simp
  have hsum : ∀ (α : Type) (s : Finset α) (P : α → MvPolynomial σ ℝ),
      genNum F V cls (∑ a ∈ s, P a) Q = ∑ a ∈ s, genNum F V cls (P a) Q := by
    intro α s P
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hmon : ∀ (κ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial κ c) Q = c * (intNumL F V (classList cls κ ++ Q) : ℝ) := by
    intro κ c
    rw [key _ Q {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
  have hperm : ∀ ν μ : σ →₀ ℕ, intNumL F V (classList cls (ν + μ) ++ Q) = intNumL F V (classList cls ν ++ (classList cls μ ++ Q)) := by
    intro ν μ
    have hp : (classList cls (ν + μ)).Perm (classList cls ν ++ classList cls μ) := by
      rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
      simp only [classList, Multiset.coe_toList, Finsupp.toMultiset_add, Multiset.map_add (f := _)]
    rw [← List.append_assoc]
    exact BaseChangeColon.intersection_numbers_perm_invariant.1 F K ι V _ _ (hp.append_right Q)
  conv_lhs => rw [H.as_sum, G.as_sum, Finset.sum_mul_sum]
  rw [hsum]
  simp_rw [hsum, MvPolynomial.monomial_mul, hmon]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [key H (classList cls μ ++ Q) H.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [hperm]
  ring
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_mul_expand : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * genNum F V cls H (classList cls μ ++ Q) :=
  @BaseChangeColon.genNum_mul_expansion

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumLinear
section -- merged from Development.WeilBound.CoreStatements.IdealCycleValues.GenNumLinearInPolynomial
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.genNum_linear_in_polynomial : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, genNum F V cls (H + H') Q = genNum F V cls H Q + genNum F V cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), genNum F V cls (C c * H) Q = c * genNum F V cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), genNum F V cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, genNum F V cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial μ c) Q = c * (intNumL F V (classList cls μ ++ Q) : ℝ) := by
  intro F _ K _ _ ι _ σ V cls Q
  classical
  set g : (σ →₀ ℕ) → ℝ := fun μ => (intNumL F V (classList cls μ ++ Q) : ℝ) with hg
  have key : ∀ (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      genNum F V cls H Q = ∑ μ ∈ s, AddMonoidAlgebra.coeff H μ * g μ := by
    intro H s hs
    show ∑ μ ∈ H.support, AddMonoidAlgebra.coeff H μ * g μ = _
    refine Finset.sum_subset hs (fun μ _ hμ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hμ, zero_mul]
  have hadd : ∀ H H' : MvPolynomial σ ℝ, genNum F V cls (H + H') Q = genNum F V cls H Q + genNum F V cls H' Q := by
    intro H H'
    rw [key (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
      key H (H.support ∪ H'.support) Finset.subset_union_left,
      key H' (H.support ∪ H'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : genNum F V cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 ∅ (by simp)]
    simp
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c H
    have hs : (MvPolynomial.C c * H).support ⊆ H.support := by
      intro μ hμ
      rw [MvPolynomial.mem_support_iff] at hμ ⊢
      rw [MvPolynomial.coeff_C_mul] at hμ
      exact right_ne_zero_of_mul hμ
    rw [key _ H.support hs, key H H.support subset_rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_C_mul, mul_assoc]
  · intro α s H
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  · intro μ c
    rw [key _ {μ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_linear : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, genNum F V cls (H + H') Q = genNum F V cls H Q + genNum F V cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), genNum F V cls (C c * H) Q = c * genNum F V cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), genNum F V cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, genNum F V cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial μ c) Q = c * (intNumL F V (classList cls μ ++ Q) : ℝ) := by
  exact @BaseChangeColon.genNum_linear_in_polynomial

end GlobalTheory.CompanionTheory.Ar.Num
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.HtPt.Pflag

def idxList {N : ℕ} (α : Fin N → ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun i => List.replicate (α i) i

theorem count_idxList {N : ℕ} (α : Fin N → ℕ) (j : Fin N) : (idxList α).count j = α j := by
  classical
  simp only [idxList, List.count_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp [List.count_replicate]

theorem length_idxList {N : ℕ} (α : Fin N → ℕ) : (idxList α).length = ∑ i, α i := by
  simp only [idxList, List.length_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

theorem map_idxList {K : Type} {N : ℕ} (x : Fin N → K → ℤ) (α : Fin N → ℕ) :
    (idxList α).map x = rootList x α := by
  simp [idxList, rootList, List.map_flatMap, List.map_replicate]

theorem prod_map_X {σ : Type} [DecidableEq σ] (s : Multiset σ) :
    ((s.map X).prod : MvPolynomial σ ℝ) = monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add (f := _),
      Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]

theorem length_classList_of_hom {K σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) : (classList cls μ).length = m := by
  classical
  have h := hH (mem_support_iff.mp hμ)
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem isHomogeneous_hsymm_real (N a : ℕ) : (hsymm (Fin N) ℝ a).IsHomogeneous a := by
  classical
  apply IsHomogeneous.sum
  intro s _
  rw [prod_map_X]
  apply isHomogeneous_monomial
  have h := Finsupp.card_toMultiset (Multiset.toFinsupp (s : Multiset (Fin N)))
  rw [Multiset.toFinsupp_toMultiset] at h
  calc Finsupp.degree (Multiset.toFinsupp (s : Multiset (Fin N)))
      = (Multiset.toFinsupp (s : Multiset (Fin N))).sum fun _ => id := rfl
    _ = a := by rw [← h]; simp

section
variable (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
  [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F))

theorem genNum_hsymm {N : ℕ} (x : Fin N → K → ℤ) (a : ℕ) (Q : List (K → ℤ)) :
    genNum F V x (hsymm (Fin N) ℝ a) Q =
      ((∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F V (rootList x α ++ Q) : ℤ) : ℝ) := by
  classical
  rw [hsymm, (genNum_linear F K ι (Fin N) V x Q).2.2.1]
  simp_rw [prod_map_X, (genNum_linear F K ι (Fin N) V x Q).2.2.2, one_mul]
  push_cast
  symm
  refine Finset.sum_bij'
    (fun α hα => (⟨(idxList α : Multiset (Fin N)), by
      rw [Multiset.coe_card, length_idxList, (Finset.Nat.mem_antidiagonalTuple.mp hα)]⟩ : Sym (Fin N) a))
    (fun s _ => fun i => (s : Multiset (Fin N)).count i) ?_ ?_ ?_ ?_ ?_
  · intro α _
    exact Finset.mem_univ _
  · intro s _
    rw [Finset.Nat.mem_antidiagonalTuple]
    rw [← Finset.sum_subset (Finset.subset_univ (s : Multiset (Fin N)).toFinset)]
    · rw [Multiset.toFinset_sum_count_eq]
      exact s.2
    · intro i _ hi
      simpa using hi
  · intro α _
    funext i
    simp [Multiset.coe_count, count_idxList]
  · intro s _
    apply Subtype.ext
    ext i
    simp [Multiset.coe_count, count_idxList]
  · intro α _
    rw [intNumL_perm_of_perm F K ι V (rootList x α ++ Q) _]
    apply List.Perm.append_right
    rw [← map_idxList]
    rw [← Multiset.coe_eq_coe]
    simp [classList, Multiset.toFinsupp_toMultiset]

theorem genNum_neg (d : ℕ) (hV : IsMultiProjPrime V)
    (hd : ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) {N : ℕ}
    (b : Fin N → K → ℤ) (H : MvPolynomial (Fin N) ℝ) (m : ℕ) (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    genNum F V b (aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) H) Q =
      genNum F V (fun i => -b i) H Q := by
  classical
  have h := genNum_linear_subst F K ι V d hV hd (Fin N) (Fin N) b
    (fun t i => if t = i then -1 else 0) H m hH Q hQ
  have e1 : (fun t : Fin N => ∑ i : Fin N, (if t = i then (-1 : ℤ) else 0) • b i) =
      fun t => -b t := by
    funext t
    simp
  have e2 : (fun t : Fin N => ∑ i : Fin N,
      C (((if t = i then (-1 : ℤ) else 0 : ℤ) : ℝ)) * (X i : MvPolynomial (Fin N) ℝ)) =
      fun t => (-X t : MvPolynomial (Fin N) ℝ) := by
    funext t
    simp only [apply_ite (fun z : ℤ => ((z : ℝ))), Int.cast_neg, Int.cast_one, Int.cast_zero,
      apply_ite C, map_neg, map_one, map_zero, ite_mul, neg_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ t (fun i => -(X i : MvPolynomial (Fin N) ℝ))]
    simp
  rw [e1, e2] at h
  exact h.symm

end

end PositivityTheory.HtPt.Pflag
