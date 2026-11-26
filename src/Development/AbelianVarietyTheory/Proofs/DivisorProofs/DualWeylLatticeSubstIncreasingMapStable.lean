module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStable
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

def colPull {k N : ℕ} (τ : Fin k → Fin N) : (Fin N → ℕ) →+ (Fin k → ℕ) where
  toFun g := g ∘ τ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colPull_single_mem {k N : ℕ} {τ : Fin k → Fin N} (hτ : Function.Injective τ) (s : Fin k) :
    colPull τ (Pi.single (τ s) 1) = Pi.single s 1 := by
  funext t
  change (Pi.single (τ s) 1 : Fin N → ℕ) (τ t) = _
  by_cases h : t = s
  · subst h; simp
  · rw [Pi.single_eq_of_ne (fun h' => h (hτ h')), Pi.single_eq_of_ne h]

theorem colPull_single_not {k N : ℕ} {τ : Fin k → Fin N} {y : Fin N} (hy : y ∉ Set.range τ) :
    colPull τ (Pi.single y 1) = 0 := by
  funext t
  change (Pi.single y 1 : Fin N → ℕ) (τ t) = 0
  exact Pi.single_eq_of_ne (fun h => hy ⟨t, h⟩) _

theorem mem_dualWeyl_iff' {R : Type} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, mem_weightedHomogeneousSubmodule,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]

theorem aeval_isWeightedHomogeneous {R σ ι Mo : Type} [CommRing R] [AddCommMonoid Mo] (w : ι → Mo)
    (φ : σ → MvPolynomial ι R) (ω : σ → Mo) (hφ : ∀ v, IsWeightedHomogeneous w (φ v) (ω v))
    (x : MvPolynomial σ R) (κ : Mo) (hx : IsWeightedHomogeneous ω x κ) :
    IsWeightedHomogeneous w (aeval φ x) κ := by
  conv => enter [2, 2]; rw [x.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial, ← hx (mem_support_iff.mp hd), Finsupp.weight_apply, MvPolynomial.algebraMap_eq]
  refine IsWeightedHomogeneous.C_mul ?_ _
  unfold Finsupp.prod Finsupp.sum
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _

theorem isWeightedHomogeneous_map_weight {R σ M M' : Type} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']
    (π : M →+ M') (w : σ → M) (x : MvPolynomial σ R) (κ : M) (hx : IsWeightedHomogeneous w x κ) :
    IsWeightedHomogeneous (fun v => π (w v)) x (π κ) := by
  intro d hd
  rw [← hx hd, Finsupp.weight_apply, Finsupp.weight_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [map_nsmul]

theorem substMem : SubstMem := by
  intro R _ k N τ hτ ψ h1 h2 h3 ν f hf
  rw [mem_dualWeyl_iff'] at hf ⊢
  have hinj := hτ.injective
  refine ⟨?_, fun l j hlj => ?_⟩
  · have hvar : ∀ v : Fin N × Fin N,
        IsWeightedHomogeneous (colW k k) (ψ v) (colPull τ (colW N N v)) := by
      rintro ⟨x, y⟩
      change IsWeightedHomogeneous _ _ (colPull τ (Pi.single y 1))
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        rw [colPull_single_mem hinj]
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1]
          exact isWeightedHomogeneous_X _ _ _
        · rw [h2 x s hx]
          exact isWeightedHomogeneous_zero _ _ _
      · rw [colPull_single_not hy]
        obtain ⟨c, hc⟩ := h3 x y hy
        rw [hc]
        exact isWeightedHomogeneous_C _ _
    exact aeval_isWeightedHomogeneous (colW k k) ψ _ hvar f _
      (isWeightedHomogeneous_map_weight (colPull τ) _ f ν hf.1)
  · let ψO : Option (Fin N × Fin N) → MvPolynomial (Option (Fin k × Fin k)) R :=
      fun o => o.elim (X none) fun v => rename some (ψ v)
    have hA : (aeval ψO).comp (rename some) = (rename some).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      simp [ψO]
    have hB : (aeval ψO).comp (colAddGen R (r := N) (τ l) (τ j)) = (colAddGen R l j).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      obtain ⟨x, y⟩ := v
      simp only [AlgHom.comp_apply, aeval_X]
      rw [colAddGen, aeval_X]
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1, colAddGen, aeval_X]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h1]
          · simp [ψO, h1]
        · rw [h2 x s hx, map_zero]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h2 x _ hx]
          · simp [ψO, h2 x _ hx]
      · obtain ⟨c, hc⟩ := h3 x y hy
        have hyj : y ≠ τ j := fun h => hy ⟨j, h.symm⟩
        rw [if_neg hyj, hc]
        simp [ψO, hc]
    have e1 := congrArg (fun φ => φ f) hA
    have e2 := congrArg (fun φ => φ f) hB
    simp only [AlgHom.comp_apply] at e1 e2
    rw [← e2, hf.2 (τ l) (τ j) (hτ hlj), e1]

end GlobalTheory.LeviCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStableStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_subst_increasing_map_stable : GlobalTheory.LeviCut.SubstMem := by
  first | exact @GlobalTheory.LeviCut.substMem | exact GlobalTheory.LeviCut.substMem | (intros; apply GlobalTheory.LeviCut.substMem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridDenominatorBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridDenominatorBound
open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut.GridIntProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem adj_pow_apply (x U : Module.End ℚ V) (k : ℕ) :
    (adj x ^ k) U = ∑ t ∈ Finset.range (k + 1),
      (((-1 : ℚ) ^ (k - t) * (k.choose t : ℚ)) • (x ^ t * U * x ^ (k - t))) := by
  have hc : Commute (LinearMap.mulLeft ℚ x) ((-1 : ℚ) • LinearMap.mulRight ℚ x) :=
    (LinearMap.commute_mulLeft_right x x).smul_right _
  have h1 : adj x = LinearMap.mulLeft ℚ x + (-1 : ℚ) • LinearMap.mulRight ℚ x := by
    simp [adj, sub_eq_add_neg]
  rw [h1, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℚ, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]

def IntOn (L M : Submodule ℤ V) (c : ℕ) (U : Module.End ℚ V) : Prop := ∀ x ∈ L, ((c : ℕ) : ℤ) • U x ∈ M

theorem intOn_divAdj (L M : Submodule ℤ V) (e : Module.End ℚ V)
    (hL : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (e ^ k) x ∈ L)
    (hM : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (e ^ k) x ∈ M)
    (c : ℕ) (U : Module.End ℚ V) (hU : IntOn L M c U) (k : ℕ) :
    IntOn L M c (((k.factorial : ℚ)⁻¹) • (adj e ^ k) U) := by
  intro y hy
  have hE : ((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj e ^ k) U) y) =
      ∑ t ∈ Finset.range (k + 1), ((-1 : ℤ) ^ (k - t)) • ((t.factorial : ℚ)⁻¹ •
        (e ^ t) (((c : ℕ) : ℤ) • U (((k - t).factorial : ℚ)⁻¹ • (e ^ (k - t)) y))) := by
    rw [LinearMap.smul_apply, adj_pow_apply, LinearMap.sum_apply, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hch := Nat.choose_mul_factorial_mul_factorial ht'
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      LinearMap.sum_apply, Finset.smul_sum]
    congr 1
    have h1 : ((k.choose t : ℕ) : ℚ) * (t.factorial : ℚ) * ((k - t).factorial : ℚ) = (k.factorial : ℚ) := by
      exact_mod_cast hch
    have h2 : (t.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((k - t).factorial : ℚ) ≠ 0 := by positivity
    have h4 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h5 : ((k.choose t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ht').ne'
    rw [← h1]
    push_cast
    field_simp
  rw [hE]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  exact hM t _ (hU _ (hL (k - t) y hy))

theorem intOn_proj (L M : Submodule ℤ V) (X Y : Module.End ℚ V)
    (hLX : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (X ^ k) x ∈ L)
    (hMX : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (X ^ k) x ∈ M)
    (hLY : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (Y ^ k) x ∈ L)
    (hMY : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (Y ^ k) x ∈ M)
    (K j₀ Λ : ℕ) (hΛ : ∀ k ≤ K, (j₀ + k + 1).factorial ∣ Λ * (j₀.factorial * k.factorial))
    (c : ℕ) (U : Module.End ℚ V) (hU : IntOn L M c U) :
    IntOn L M (c * Λ) (proj K j₀ (adj X) (adj Y) U) := by
  intro y hy
  simp only [proj, LinearMap.sum_apply, Finset.smul_sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨m, hm⟩ := hΛ k hkK
  have hE : ((c * Λ : ℕ) : ℤ) • ((coef j₀ k • (adj Y ^ k * adj X ^ k)) U) y =
      ((-1 : ℤ) ^ k * (m : ℤ)) • (((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj Y ^ k)
        ((k.factorial : ℚ)⁻¹ • (adj X ^ k) U)) y)) := by
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    have h2 : (j₀.factorial : ℚ) ≠ 0 := by positivity
    have h3 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((j₀ + k + 1).factorial : ℚ) ≠ 0 := by positivity
    have hΛq : (Λ : ℚ) = ((j₀ + k + 1).factorial : ℚ) * (m : ℚ) / ((j₀.factorial : ℚ) * (k.factorial : ℚ)) := by
      rw [eq_div_iff (by positivity)]
      exact_mod_cast hm
    have hkj : k + j₀ + 1 = j₀ + k + 1 := by omega
    simp only [coef, hkj]
    push_cast
    rw [hΛq]
    field_simp
  rw [hE]
  refine Submodule.smul_mem _ _ ?_
  exact intOn_divAdj L M Y hLY hMY c _ (intOn_divAdj L M X hLX hMX c U hU k) k y hy

theorem intOn_listProd (L M : Submodule ℤ V) (n : ℕ) :
    ∀ (l : List (Module.End ℚ (Module.End ℚ V))), (∀ f ∈ l, ∀ c U, IntOn L M c U → IntOn L M (c * n) (f U)) →
      ∀ c U, IntOn L M c U → IntOn L M (c * n ^ l.length) (l.prod U)
  | [], _, c, U, hU => by simpa using hU
  | f :: l, hf, c, U, hU => by
      rw [List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, ← mul_assoc]
      exact hf f (List.mem_cons_self ..) _ _
        (intOn_listProd L M n l (fun g hg => hf g (List.mem_cons_of_mem _ hg)) c U hU)

end GlobalTheory.LeviCut.GridIntProof

namespace GlobalTheory.LeviCut


open GridIntProof in
theorem gridInt_holds : GridInt := by
  intro V _ _ a b K w Λ e L M hL hM hw hΛ c T hT
  have hstep : ∀ i < a, ∀ j, a ≤ j → j < a + b → ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U →
      IntOn L M (c * Λ) (rootP (fun c d => adj (e c d)) K i j U) := by
    intro i hi j hj1 hj2 c U hU
    have hij : i ≠ j := by omega
    have hji : j ≠ i := by omega
    exact intOn_proj L M (e i j) (e j i) (fun k x hx => hL i (by omega) j hj2 hij k x hx)
      (fun k x hx => hM i (by omega) j hj2 hij k x hx) (fun k x hx => hL j hj2 i (by omega) hji k x hx)
      (fun k x hx => hM j hj2 i (by omega) hji k x hx) K (j - i - 1) Λ (fun k hk => hΛ _ _ (by omega)) c U hU
  have hrow : ∀ i < a, ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U →
      IntOn L M (c * Λ ^ b) (rowP (fun c d => adj (e c d)) K i a b U) := by
    intro i hi c U hU
    have h := intOn_listProd L M Λ ((List.range' a b).map (rootP (fun c d => adj (e c d)) K i)) (by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      rw [List.mem_range'_1] at hj
      exact hstep i hi j hj.1 hj.2) c U hU
    simpa [rowP] using h
  have h := intOn_listProd L M (Λ ^ b) ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b)
    (by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨i, hi, rfl⟩ := hf
      rw [List.mem_reverse, List.mem_range] at hi
      exact hrow i hi) c T hT
  have e1 : (Λ ^ b) ^ ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b).length =
      Λ ^ (a * b) := by
    simp [← pow_mul, mul_comm]
  rw [e1] at h
  exact h

end GlobalTheory.LeviCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridDenominatorBoundStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projector_grid_denominator_bound : GlobalTheory.LeviCut.GridInt := by
  first | exact @GlobalTheory.LeviCut.gridInt_holds | exact GlobalTheory.LeviCut.gridInt_holds | (intros; apply GlobalTheory.LeviCut.gridInt_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylHighestWeightRestrictionBlockDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylHighestWeightRestrictionBlockDiagonal
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

theorem resT_lpMinor_le (p q s : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hs : s ≤ p) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
  have key : lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ s hs hs) := rfl
  rw [key, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  have hi : (Fin.castLE h1 i : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs i) := Fin.ext rfl
  have hj : (Fin.castLE h2 j : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs j) := Fin.ext rfl
  rw [hi, hj, resT, aeval_X]
  simp [resVarT]

theorem resT_lpMinor_ge (p q u : ℕ) (h1 : p + u ≤ p + q) (h2 : p + u ≤ p + q) (hu : u ≤ q) :
    resT ℚ p q (lpMinor ℚ (p + u) h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  have key : lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ p le_rfl le_rfl) *
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := MvPolynomial (Fin p × Fin p) ℚ))
        (lpMinor ℚ u hu hu) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [key, lpMinor, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₂₁ (B := 0)]
  congr 1
  ext (a | a) (b | b)
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q a := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q b := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]

theorem nuNext_natAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (j : Fin q) :
    nuNext ν (Fin.natAdd p j) = nuNext (fun j => ν (Fin.natAdd p j)) j := by
  unfold nuNext
  simp only [Fin.val_natAdd]
  split_ifs with h h' h'
  · congr 1
  · omega
  · omega
  · rfl

theorem nuNext_castAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (i : Fin p) (hi : (i : ℕ) + 1 < p) :
    nuNext ν (Fin.castAdd q i) = nuNext (fun i => ν (Fin.castAdd q i)) i := by
  unfold nuNext
  simp only [Fin.val_castAdd]
  rw [dite_eq_left (by omega), dite_eq_left hi]
  rfl

theorem sum_sub_nuNext (q : ℕ) (μ : Fin (q + 1) → ℕ) (hμ : Antitone μ) :
    ∑ j, (μ j - nuNext μ j) = μ 0 := by
  induction q with
  | zero => simp [nuNext]
  | succ q ih =>
    rw [Fin.sum_univ_succ]
    have h1 : ∀ j : Fin (q + 1), nuNext μ j.succ = nuNext (fun j => μ j.succ) j := by
      intro j
      unfold nuNext
      simp only [Fin.val_succ]
      split_ifs with h h' h' <;> first | omega | rfl
    simp_rw [h1]
    rw [ih (fun j => μ j.succ) (fun a b hab => hμ (Fin.succ_le_succ_iff.mpr hab))]
    have h0 : nuNext μ 0 = μ (Fin.succ 0) := by
      unfold nuNext; rw [dite_eq_left (by simp)]; rfl
    rw [h0]
    have := hμ (Fin.zero_le (Fin.succ 0 : Fin (q + 2)))
    omega

theorem resT_lpMinor_ge' (p q s u : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hu : u ≤ q) (hs : s = p + u) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  subst hs
  exact resT_lpMinor_ge p q u h1 h2 hu

theorem prod_tmul_prod {ι A B : Type} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (s : Finset ι) (a : ι → A) (b : ι → B) :
    ∏ i ∈ s, (a i ⊗ₜ[ℚ] b i) = (∏ i ∈ s, a i) ⊗ₜ[ℚ] (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.TensorProduct.one_def]
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

theorem hw_first (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) :
    (∏ i : Fin p, lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^
        (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) *
      lpMinor ℚ p le_rfl le_rfl ^ (∑ j : Fin q, (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) := by
  rcases p with _ | p
  · simp [hw, lpMinor, Matrix.det_isEmpty]
  · rw [hw, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
    simp only [Fin.val_last]
    rw [← pow_add]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      rw [nuNext_castAdd (p + 1) q ν k.castSucc (by simp)]
    · have hl : nuNext (fun i => ν (Fin.castAdd q i)) (Fin.last p) = 0 := by
        unfold nuNext; rw [dite_eq_right (by simp)]
      rw [hl, Nat.sub_zero]
      congr 1
      simp_rw [nuNext_natAdd]
      rcases q with _ | q
      · simp [nuNext]
      · rw [sum_sub_nuNext q (fun j => ν (Fin.natAdd (p + 1) j))
          (fun a b hab => hν (by rw [Fin.le_def] at hab ⊢; simp only [Fin.val_natAdd]; omega))]
        have h0 : nuNext ν (Fin.castAdd (q + 1) (Fin.last p)) = ν (Fin.natAdd (p + 1) 0) := by
          unfold nuNext; rw [dite_eq_left (by simp <;> omega)]; congr 1
        have := hν (show Fin.castAdd (q + 1) (Fin.last p) ≤ Fin.natAdd (p + 1) 0 by
          simp [Fin.le_def])
        rw [h0]
        omega

theorem resHw_holds : ResHw := by
  intro p q ν hν
  rw [hw, map_prod, Fin.prod_univ_add]
  have e1 : ∀ i : Fin p, resT ℚ p q (lpMinor ℚ ((Fin.castAdd q i : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) =
      (lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^ (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) ⊗ₜ[ℚ]
        (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
    intro i
    rw [map_pow, resT_lpMinor_le p q _ _ _ (by simp <;> omega), Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  have e2 : ∀ j : Fin q, resT ℚ p q (lpMinor ℚ ((Fin.natAdd p j : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      (lpMinor ℚ p le_rfl le_rfl ^ (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) ⊗ₜ[ℚ]
        (lpMinor ℚ ((j : ℕ) + 1) (by omega) (by omega) ^
          ((fun j => ν (Fin.natAdd p j)) j - nuNext (fun j => ν (Fin.natAdd p j)) j)) := by
    intro j
    rw [map_pow, resT_lpMinor_ge' p q _ ((j : ℕ) + 1) _ _ (by omega) (by simp <;> omega),
      Algebra.TensorProduct.tmul_pow, nuNext_natAdd]
  rw [Finset.prod_congr rfl fun i _ => e1 i, Finset.prod_congr rfl fun j _ => e2 j, prod_tmul_prod,
    prod_tmul_prod, Algebra.TensorProduct.tmul_mul_tmul, Finset.prod_const_one, one_mul,
    Finset.prod_pow_eq_pow_sum, hw_first p q ν hν]
  rfl

end GlobalTheory.LeviCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylHighestWeightRestrictionBlockDiagonalStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_highest_weight_restriction_blockDiagonal : GlobalTheory.LeviCut.ResHw := by
  first | exact @GlobalTheory.LeviCut.resHw_holds | exact GlobalTheory.LeviCut.resHw_holds | (intros; apply GlobalTheory.LeviCut.resHw_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvariance
open GlobalTheory.LeviCut

noncomputable section

namespace GlobalTheory.LeviCut.RankTwoProof

variable {W : Type} [AddCommGroup W] [Module ℚ W]

theorem coef_succ_mul (i k : ℕ) :
    coef i (k + 1) * (((k : ℚ) + 1) * ((k : ℚ) + i + 2)) = - coef i k := by
  unfold coef
  rw [show k + 1 + i + 1 = (k + i + 1) + 1 by ring, Nat.factorial_succ (k + i + 1), Nat.factorial_succ k]
  have a1 : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have a2 : (((k + i + 1).factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

theorem pow_succ_apply' (Y : Module.End ℚ W) (k : ℕ) (v : W) : (Y ^ (k + 1)) v = Y ((Y ^ k) v) := by
  rw [pow_succ', Module.End.mul_apply]

theorem comm_sub' (A B X x y : Module.End ℚ W) (h1 : A * X - X * A = x) (h2 : B * X - X * B = y) :
    (A - B) * X - X * (A - B) = x - y := by
  rw [← h1, ← h2]; noncomm_ring

theorem eig_pow (H X : Module.End ℚ W) (d c : ℚ) (hHX : H * X - X * H = d • X) (v : W)
    (hv : H v = c • v) (k : ℕ) : H ((X ^ k) v) = (c + k * d) • (X ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have e := LinearMap.congr_fun hHX ((X ^ k) v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at e
    rw [pow_succ_apply', eq_add_of_sub_eq e, ih, map_smul, ← add_smul]
    congr 1; push_cast; ring

theorem comm_pow_apply (Z Y P : Module.End ℚ W) (h : Z * Y - Y * Z = P) (hP : P * Y = Y * P) (v : W)
    (k : ℕ) : Z ((Y ^ (k + 1)) v) = (Y ^ (k + 1)) (Z v) + ((k : ℚ) + 1) • P ((Y ^ k) v) := by
  induction k with
  | zero =>
    have e := LinearMap.congr_fun h v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, one_smul]
    rw [eq_add_of_sub_eq e]; abel
  | succ k ih =>
    have e := LinearMap.congr_fun h ((Y ^ (k + 1)) v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have hp : P ((Y ^ (k + 1)) v) = Y (P ((Y ^ k) v)) := by
      rw [pow_succ_apply', ← Module.End.mul_apply P Y, hP, Module.End.mul_apply]
    rw [pow_succ_apply' Y (k + 1) v, pow_succ_apply' Y (k + 1) (Z v), eq_add_of_sub_eq e, ih, hp, map_add (f := _), map_smul]
    push_cast
    module

theorem sl2_X_Ypow (X Y H : Module.End ℚ W) (hXY : X * Y - Y * X = H) (hHY : H * Y - Y * H = (-2 : ℚ) • Y)
    (v : W) (c : ℚ) (hv : H v = c • v) (k : ℕ) :
    X ((Y ^ (k + 1)) v) = (Y ^ (k + 1)) (X v) + (((k : ℚ) + 1) * (c - k)) • (Y ^ k) v := by
  induction k with
  | zero =>
    have e := LinearMap.congr_fun hXY v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero, one_mul]
    rw [eq_add_of_sub_eq e, hv]; abel
  | succ k ih =>
    have e := LinearMap.congr_fun hXY ((Y ^ (k + 1)) v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have hH := eig_pow H Y (-2) c hHY v hv (k + 1)
    rw [pow_succ_apply' Y (k + 1) v, pow_succ_apply' Y (k + 1) (X v), eq_add_of_sub_eq e, ih, hH, map_add (f := _),
      map_smul, ← pow_succ_apply' Y k v]
    push_cast
    module

theorem sl2_Xpow_Y (X Y H : Module.End ℚ W) (hXY : X * Y - Y * X = H) (hHX : H * X - X * H = (2 : ℚ) • X)
    (u : W) (c : ℚ) (hu : H u = c • u) (l : ℕ) :
    (X ^ (l + 1)) (Y u) = Y ((X ^ (l + 1)) u) + (((l : ℚ) + 1) * (c + l)) • (X ^ l) u := by
  induction l with
  | zero =>
    have e := LinearMap.congr_fun hXY u
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero, one_mul]
    rw [eq_add_of_sub_eq e, hu]; abel
  | succ l ih =>
    have e := LinearMap.congr_fun hXY ((X ^ (l + 1)) u)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have hH := eig_pow H X 2 c hHX u hu (l + 1)
    rw [pow_succ_apply' X (l + 1) (Y u), ih, map_add (f := _), map_smul, eq_add_of_sub_eq e, hH,
      ← pow_succ_apply' X (l + 1) u, ← pow_succ_apply' X l u]
    push_cast
    module

theorem pow_succ_apply2 (Y : Module.End ℚ W) (k : ℕ) (v : W) : (Y ^ (k + 1)) v = (Y ^ k) (Y v) := by
  rw [pow_succ, Module.End.mul_apply]

theorem rankTwo : RankTwo := by
  intro W _ _ N K D hG hB o p q ho hp hq hop hoq hpq j T hoo hpp hqq hpqT
  have hpo := Ne.symm hop
  have hqo := Ne.symm hoq
  have hqp := Ne.symm hpq
  have rZXp : D p q * D o p - D o p * D p q = -D o q := by
    simpa [hqo] using hG p q o p hp hq ho hp
  have rZXq : D p q * D o q = D o q * D p q := by
    have := hG p q o q hp hq ho hq; simpa [hqo, hqp, sub_eq_zero] using this
  have rZYp : D p q * D p o = D p o * D p q := by
    have := hG p q p o hp hq hp ho; simpa [hqp, hop, sub_eq_zero] using this
  have rZYq : D p q * D q o - D q o * D p q = D p o := by
    simpa [hop] using hG p q q o hp hq hq ho
  have rXqXp : D o q * D o p = D o p * D o q := by
    have := hG o p o q ho hp ho hq
    exact (by simpa [hpo, hqo, sub_eq_zero] using this : D o p * D o q = D o q * D o p).symm
  have rYpYq : D p o * D q o = D q o * D p o := by
    have := hG p o q o hp ho hq ho; simpa [hoq, hop, sub_eq_zero] using this
  have sXYp : D o p * D p o - D p o * D o p = D o o - D p p := by simpa using hG o p p o ho hp hp ho
  have sXYq : D o q * D q o - D q o * D o q = D o o - D q q := by simpa using hG o q q o ho hq hq ho
  have hHpXp : (D o o - D p p) * D o p - D o p * (D o o - D p p) = (2 : ℚ) • D o p := by
    rw [comm_sub' _ _ _ (D o p) (-D o p) (by simpa [hpo] using hG o o o p ho ho ho hp)
      (by simpa [hpo] using hG p p o p hp hp ho hp), sub_neg_eq_add, two_smul]
  have hHqXq : (D o o - D q q) * D o q - D o q * (D o o - D q q) = (2 : ℚ) • D o q := by
    rw [comm_sub' _ _ _ (D o q) (-D o q) (by simpa [hqo] using hG o o o q ho ho ho hq)
      (by simpa [hqo] using hG q q o q hq hq ho hq), sub_neg_eq_add, two_smul]
  have hHqYq : (D o o - D q q) * D q o - D q o * (D o o - D q q) = (-2 : ℚ) • D q o := by
    rw [comm_sub' _ _ _ (-D q o) (D q o) (by simpa [hoq] using hG o o q o ho ho hq ho)
      (by simpa [hoq] using hG q q q o hq hq hq ho), neg_smul, two_smul]; abel
  have hHpXq : (D o o - D p p) * D o q - D o q * (D o o - D p p) = (1 : ℚ) • D o q := by
    rw [comm_sub' _ _ _ (D o q) 0 (by simpa [hqo] using hG o o o q ho ho ho hq)
      (by simpa [hpo, hqp] using hG p p o q hp hp ho hq), sub_zero, one_smul]
  have hHpYq : (D o o - D p p) * D q o - D q o * (D o o - D p p) = (-1 : ℚ) • D q o := by
    rw [comm_sub' _ _ _ (-D q o) 0 (by simpa [hoq] using hG o o q o ho ho hq ho)
      (by simpa [hpq, hop] using hG p p q o hp hp hq ho), sub_zero, neg_one_smul]
  have hHpT : (D o o - D p p) T = (0 : ℚ) • T := by simp [hoo, hpp]
  have hHqT : (D o o - D q q) T = (0 : ℚ) • T := by simp [hoo, hqq]
  have hZv : ∀ k : ℕ, D p q ((D o q ^ k) T) = 0 := fun k => by
    have c := LinearMap.congr_fun (Commute.pow_right rZXq k).eq T
    simp only [Module.End.mul_apply] at c
    rw [c, hpqT, map_zero]
  have hHqv : ∀ k : ℕ, (D o o - D q q) ((D o q ^ k) T) = ((2 : ℚ) * k) • (D o q ^ k) T := fun k => by
    rw [eig_pow _ _ 2 0 hHqXq T hHqT k]; congr 1; ring
  have hXqK : (D o q ^ (K + 1)) T = 0 := by
    apply hB o ho q hq (2 * K + 2 : ℤ)
    · rw [← LinearMap.sub_apply, hHqv]; congr 1; push_cast; ring
    · push_cast; omega
  have hproj : ∀ (i : ℕ) (X Y : Module.End ℚ W) (x : W),
      (proj K i X Y) x = ∑ k ∈ Finset.range (K + 1), coef i k • (Y ^ k) ((X ^ k) x) := by
    intro i X Y x; unfold proj; rw [LinearMap.sum_apply]; simp only [LinearMap.smul_apply, Module.End.mul_apply]
  obtain ⟨T', hT'⟩ : ∃ x : W, x = (proj K (j + 1) (D o q) (D q o)) T := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ u : W, u = ∑ k ∈ Finset.range K,
      (((k : ℚ) + 1) * coef (j + 1) (k + 1)) • (D q o ^ k) ((D o q ^ (k + 1)) T) := ⟨_, rfl⟩

  have hZT' : D p q T' = D p o U := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT', hproj, map_sum, Finset.sum_range_succ', hU, map_sum]
    simp only [map_smul, pow_zero, Module.End.one_apply, hpqT, smul_zero, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [comm_pow_apply _ _ _ rZYq rYpYq, hZv, map_zero, zero_add, smul_smul, mul_comm]

  have key : ∀ k : ℕ, coef (j + 1) k + coef (j + 1) (k + 1) * (((k : ℚ) + 1) * ((k : ℚ) + 2)) =
      -((j : ℚ) + 1) * (((k : ℚ) + 1) * coef (j + 1) (k + 1)) := by
    intro k; have := coef_succ_mul (j + 1) k; push_cast at this; linear_combination this
  have hXq_step : ∀ k : ℕ, D o q ((D q o ^ (k + 1)) ((D o q ^ (k + 1)) T)) =
      (D q o ^ (k + 1)) ((D o q ^ (k + 1 + 1)) T) +
        (((k : ℚ) + 1) * ((k : ℚ) + 2)) • (D q o ^ k) ((D o q ^ (k + 1)) T) := fun k => by
    rw [sl2_X_Ypow _ _ _ sXYq hHqYq _ _ (hHqv (k + 1)) k, ← pow_succ_apply' (D o q) (k + 1) T]
    congr 2; push_cast; ring
  have hS : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), coef (j + 1) k • D o q ((D q o ^ k) ((D o q ^ k) T)) =
      coef (j + 1) n • (D q o ^ n) ((D o q ^ (n + 1)) T) + ∑ k ∈ Finset.range n,
        (-((j : ℚ) + 1) * (((k : ℚ) + 1) * coef (j + 1) (k + 1))) • (D q o ^ k) ((D o q ^ (k + 1)) T) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hXq_step n, Finset.sum_range_succ, ← key n]
      module
  have hXqT' : D o q T' = (-((j : ℚ) + 1)) • U := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT', hproj, map_sum]
    simp only [map_smul]
    rw [hS K, hXqK, map_zero, smul_zero, zero_add, hU, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul]

  have hHpU : (D o o - D p p) U = (1 : ℚ) • U := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hU, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, eig_pow _ _ (-1) _ hHpYq _ (eig_pow _ _ 1 0 hHpXq T hHpT (k + 1)) k, smul_smul, smul_smul]
    congr 1; push_cast; ring
  have hXpU : (D o p ^ K) U = 0 := by
    apply hB o ho p hp (2 * K + 1 : ℤ)
    · rw [← LinearMap.sub_apply, eig_pow _ _ 2 1 hHpXp U hHpU K]; congr 1; push_cast; ring
    · push_cast; omega
  have hP : (-D o q) * D o p = D o p * (-D o q) := by rw [neg_mul, mul_neg, rXqXp]
  have hf : ∀ l : ℕ, D p q ((D p o ^ (l + 1)) ((D o p ^ (l + 1)) T')) =
      (D p o ^ (l + 1 + 1)) ((D o p ^ (l + 1)) U) +
        (((l : ℚ) + 1) * ((l : ℚ) + j + 2)) • (D p o ^ (l + 1)) ((D o p ^ l) U) := by
    intro l
    have e1 := LinearMap.congr_fun (Commute.pow_right rZYp (l + 1)).eq ((D o p ^ (l + 1)) T')
    simp only [Module.End.mul_apply] at e1
    have c := LinearMap.congr_fun (Commute.pow_right rXqXp l).eq T'
    simp only [Module.End.mul_apply] at c
    rw [e1, comm_pow_apply _ _ _ rZXp hP, hZT', LinearMap.neg_apply, c, hXqT', map_smul, neg_smul, neg_neg,
      sl2_Xpow_Y _ _ _ sXYp hHpXp U 1 hHpU l]
    simp only [map_add (f := _), map_smul]
    rw [← pow_succ_apply2 (D p o) (l + 1)]
    push_cast
    module
  have hT5 : ∀ n : ℕ, D p q (∑ l ∈ Finset.range (n + 1), coef j l • (D p o ^ l) ((D o p ^ l) T')) =
      coef j n • (D p o ^ (n + 1)) ((D o p ^ n) U) := by
    intro n
    induction n with
    | zero => simp [hZT']
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add (f := _), ih, map_smul, hf n, smul_add, smul_smul, coef_succ_mul, neg_smul]
      abel
  rw [← hT', hproj, hT5 K, hXpU, map_zero, smul_zero]

end GlobalTheory.LeviCut.RankTwoProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvarianceStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_consecutive_projector_invariance : GlobalTheory.LeviCut.RankTwo := by
  first | exact @GlobalTheory.LeviCut.RankTwoProof.rankTwo | exact GlobalTheory.LeviCut.RankTwoProof.rankTwo | (intros; apply GlobalTheory.LeviCut.RankTwoProof.rankTwo <;> assumption)
end
end
