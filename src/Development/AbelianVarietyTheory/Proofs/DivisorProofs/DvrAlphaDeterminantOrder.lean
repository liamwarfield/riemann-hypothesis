module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanOfIsLatticeBasis
open scoped NNReal

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

section Core

variable {C : Type} [Field C]

theorem eq_sum_rows {n : ℕ} (U : Fin n → Fin n → C) (h : (Matrix.of U).det ≠ 0)
    (f : Fin n → C) : ∃ γ : Fin n → C, f = ∑ s, γ s • U s := by
  refine ⟨Matrix.vecMul f (Matrix.of U)⁻¹, ?_⟩
  have hu : IsUnit (Matrix.of U).det := isUnit_iff_ne_zero.mpr h
  have key : Matrix.vecMul (Matrix.vecMul f (Matrix.of U)⁻¹) (Matrix.of U) = f := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  funext j
  conv_lhs => rw [← key]
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

theorem exists_eq_sum_of_mem {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u0 : Fin p → Fin (p + q) → C) (m0 : Fin q → Fin (p + q) → C)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i)) (hm0 : ∀ k, m0 k ∈ F)
    (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) (f : Fin (p + q) → C) (hf : f ∈ F) :
    ∃ β : Fin q → C, f = ∑ k, β k • m0 k := by
  obtain ⟨γ, hγ⟩ := eq_sum_rows _ hN f
  rw [Fin.sum_univ_add] at hγ
  simp only [Fin.append_left, Fin.append_right] at hγ
  have hz : ∑ i, γ (Fin.castAdd q i) • F.mkQ (u0 i) = 0 := by
    have h1 := congrArg F.mkQ hγ
    have hf0 : F.mkQ f = 0 := by simpa using hf
    have hm : ∑ k, γ (Fin.natAdd p k) • F.mkQ (m0 k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hm0 k]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf0, map_add (f := _), map_sum, map_sum] at h1
    simp only [map_smul] at h1
    rw [hm, add_zero] at h1
    exact h1.symm
  have h0 := Fintype.linearIndependent_iff.1 hli _ hz
  exact ⟨fun k => γ (Fin.natAdd p k), by rw [hγ]; simp [h0]⟩

theorem det_append_eq {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u u0 : Fin p → Fin (p + q) → C) (m m0 : Fin q → Fin (p + q) → C)
    (A : Matrix (Fin p) (Fin p) C) (B : Matrix (Fin q) (Fin q) C)
    (hu : ∀ i, F.mkQ (u i) = ∑ j, A i j • F.mkQ (u0 j))
    (hm : ∀ i, m i = ∑ j, B i j • m0 j)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i))
    (hm0 : ∀ k, m0 k ∈ F) (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) :
    (Matrix.of (Fin.append u m)).det = A.det * B.det * (Matrix.of (Fin.append u0 m0)).det := by
  have hmem : ∀ i, u i - ∑ j, A i j • u0 j ∈ F := by
    intro i
    have : F.mkQ (u i - ∑ j, A i j • u0 j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, hu i]; simp only [map_smul]; exact sub_self _
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  choose β hβ using fun i => exists_eq_sum_of_mem F u0 m0 hli hm0 hN _ (hmem i)
  have key : (Matrix.of (Fin.append u m)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A (Matrix.of β) 0 B *
        (Matrix.of (Fin.append u0 m0)).submatrix finSumFinEquiv finSumFinEquiv := by
    ext r c
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | k
    · have hi : u i = ∑ j, A i j • u0 j + ∑ k, β i k • m0 k := by rw [← hβ i]; abel
      simp [Matrix.fromBlocks, hi, Finset.sum_apply]
    · simp [Matrix.fromBlocks, hm k, Finset.sum_apply]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_submatrix_equiv_self]

theorem comp_sum {W : Type} [AddCommGroup W] [Module C W] {n k l : ℕ} (a : Fin n → W)
    (b : Fin k → W) (c : Fin l → W) (P : Matrix (Fin k) (Fin n) C)
    (Q : Matrix (Fin l) (Fin k) C) (hb : ∀ i, b i = ∑ j, P i j • a j)
    (hc : ∀ i, c i = ∑ j, Q i j • b j) : ∀ i, c i = ∑ j, (Q * P) i j • a j := by
  intro i
  simp only [hc i, hb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

end Core

section Lattice

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem coeffs {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n k : ℕ} (a : Fin n → W) (b : Fin k → W)
    (h : ∀ i, b i ∈ Submodule.span w.valuationSubring (Set.range a)) :
    ∃ P : Matrix (Fin k) (Fin n) w.valuationSubring,
      ∀ i, b i = ∑ j, algebraMap w.valuationSubring C (P i j) • a j := by
  choose P hP using fun i =>
    (Submodule.mem_span_range_iff_exists_fun w.valuationSubring).1 (h i)
  exact ⟨Matrix.of P, fun i => by
    rw [← hP i]; exact Finset.sum_congr rfl fun j _ => (algebraMap_smul C (P i j) (a j)).symm⟩

theorem mem_span_of_isLatticeBasis {W : Type} [AddCommGroup W] [Module C W]
    [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] {n k : ℕ}
    {a : Fin n → W} {b : Fin k → W} {Y : Submodule w.valuationSubring W}
    (ha : IsLatticeBasis w a Y) (hb : IsLatticeBasis w b Y) (i : Fin k) :
    b i ∈ Submodule.span w.valuationSubring (Set.range a) := by
  rw [ha.2, ← hb.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem transition {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (a b : Fin n → W)
    (Y : Submodule w.valuationSubring W) (ha : IsLatticeBasis w a Y)
    (hb : IsLatticeBasis w b Y) :
    ∃ P : Matrix (Fin n) (Fin n) C, (∀ i, b i = ∑ j, P i j • a j) ∧ w P.det = 1 := by
  obtain ⟨P, hP⟩ := coeffs a b (mem_span_of_isLatticeBasis ha hb)
  obtain ⟨Q, hQ⟩ := coeffs b a (mem_span_of_isLatticeBasis hb ha)
  have hQP := comp_sum a b a (P.map (algebraMap w.valuationSubring C))
    (Q.map (algebraMap w.valuationSubring C)) hP hQ
  have hone : (Q.map (algebraMap w.valuationSubring C)) * (P.map (algebraMap w.valuationSubring C))
      = 1 := by
    ext i j
    have h := Fintype.linearIndependent_iff.1 ha.1
      (fun j => ((Q.map (algebraMap w.valuationSubring C)) *
        (P.map (algebraMap w.valuationSubring C))) i j - (1 : Matrix (Fin n) (Fin n) C) i j)
      (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hQP i]
        simp [Matrix.one_apply])
      j
    exact sub_eq_zero.1 h
  have hdet := congrArg Matrix.det hone
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hle : ∀ R : Matrix (Fin n) (Fin n) w.valuationSubring,
      w (R.map (algebraMap w.valuationSubring C)).det ≤ 1 := by
    intro R
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ValuationSubring.algebraMap_apply]
    exact (w.mem_valuationSubring_iff _).1 R.det.2
  refine ⟨P.map (algebraMap w.valuationSubring C), fun i => hP i, le_antisymm (hle P) ?_⟩
  calc (1 : ℝ≥0) = w (Q.map (algebraMap w.valuationSubring C)).det *
        w (P.map (algebraMap w.valuationSubring C)).det := by rw [← map_mul, hdet, map_one]
    _ ≤ w (P.map (algebraMap w.valuationSubring C)).det :=
        mul_le_of_le_one_left (by positivity) (hle Q)

end Lattice

end GlobalTheory.DetRelCompare

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

end GlobalTheory.DetRelCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShift
open scoped NNReal

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem addVal_inv_pow_mul {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {d c : C} (hd : d ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    addVal w ℓ (d⁻¹ ^ n * c) = addVal w ℓ c - (n : ℝ) * addVal w ℓ d := by
  have hwd : ((w d : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hd)
  have hwc : ((w c : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hc)
  have hl : Real.log ((w ℓ : ℝ≥0) : ℝ) ≠ 0 := by
    refine (Real.log_neg ?_ ?_).ne
    · exact_mod_cast h0
    · exact_mod_cast h1
  unfold addVal
  rw [map_mul, map_pow, map_inv₀]
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero hwd)) hwc, Real.log_pow, Real.log_inv]
  field_simp
  ring

theorem detRel_of_detRel_lsmul (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (p q : ℕ) (F : Submodule C (Fin (p + q) → C))
    (X0 : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring)
    (hd : d ≠ 0)
    (h : DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y) :
    DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * addVal w ℓ (d : C)) := by
  obtain ⟨x, u, m, c, hx, hu, hm, hmF, ⟨hc0, hcy⟩, hdet⟩ := h
  have hdC : (d : C) ≠ 0 := fun e => hd (Subtype.ext e)
  have hsm : ∀ v : Fin (p + q) → C, d • v = (d : C) • v := fun v => rfl
  have hinj : Function.Injective (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d) := by
    intro a b hab
    simp only [LinearMap.lsmul_apply, hsm] at hab
    exact smul_right_injective _ hdC hab
  refine ⟨fun i => (d : C)⁻¹ • x i, u, m, (d : C)⁻¹ ^ (p + q) * c, ⟨?_, ?_⟩, hu, hm, hmF,
    ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hdC)) hc0, ?_⟩, ?_⟩
  · exact hx.1.units_smul (fun _ => Units.mk0 _ (inv_ne_zero hdC))
  · apply Submodule.map_injective_of_injective hinj
    rw [← hx.2, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [hsm, smul_smul, hdC]
  · rw [addVal_inv_pow_mul w ℓ h0 h1 hdC hc0, hcy]
  · have : Matrix.of (fun i => (d : C)⁻¹ • x i) = (d : C)⁻¹ • Matrix.of x := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin, hdet, mul_assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShiftStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDetRelation_of_lsmul_shift : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (p q : ℕ) (F : Submodule C (Fin (p + q) → C)) (X0 : Submodule w.valuationSubring (Fin (p + q) → C)) (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F)) (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring), d ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ (d : C)) := by
  first | exact @GlobalTheory.detRel_of_detRel_lsmul | exact GlobalTheory.detRel_of_detRel_lsmul | (intros; apply GlobalTheory.detRel_of_detRel_lsmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiEigenSublatticeFreeEqDifferentScaled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiEigenSublatticeFreeEqDifferentScaled
open scoped NNReal

namespace GlobalTheory.EigenSubFree

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference Polynomial

theorem prod_X_sub_C_dvd {O ι : Type} [CommRing O] [IsDomain O] (T : Finset ι)
    (c : ι → O) (hc : Set.InjOn c (↑T : Set ι)) (f : Polynomial O)
    (hf : ∀ j ∈ T, f.eval (c j) = 0) :
    (∏ i ∈ T, (X - C (c i))) ∣ f := by
  by_cases h0 : f = 0
  · simp [h0]
  have hnd : (T.val.map c).Nodup :=
    Multiset.Nodup.map_on (fun x hx y hy h => hc hx hy h) T.nodup
  have hle : T.val.map c ≤ f.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro b hb
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hb
    exact (Polynomial.mem_roots h0).2 (hf j hj)
  have := (Multiset.prod_X_sub_C_dvd_iff_le_roots h0 _).2 hle
  rwa [Multiset.map_map] at this

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {S : Type}

theorem mem_eigenQuot_freeLattice (a : S → w.valuationSubring) (r : ℕ) (τ : S) (u : Fin r → C) :
    u ∈ eigenQuot (W := fun _ => Fin r → C) (freeLattice a r) τ ↔
      ∀ i, u i ∈ w.valuationSubring := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨f, hf⟩ := hx i
    simp only [LinearMap.proj_apply]
    rw [hf τ]
    exact Subtype.prop _
  · intro hu
    exact ⟨fun _ => u, fun i => ⟨Polynomial.C ⟨u i, hu i⟩, fun s => by simp⟩, rfl⟩

theorem mem_eigenSub_freeLattice [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (τ : S)
    (v : Fin r → C) :
    v ∈ eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ ↔
      ∀ i, ∃ f : Polynomial w.valuationSubring,
        (∀ s, s ≠ τ → f.eval (a s) = 0) ∧ ((f.eval (a τ) : w.valuationSubring) : C) = v i := by
  show (LinearMap.single w.valuationSubring (fun _ : S => Fin r → C) τ v) ∈ freeLattice a r ↔ _
  constructor
  · intro h i
    obtain ⟨f, hf⟩ := h i
    refine ⟨f, fun s hs => ?_, ?_⟩
    · have := hf s
      simp [hs] at this
      exact_mod_cast this.symm
    · have := hf τ
      simp at this
      exact this.symm
  · intro h i
    obtain ⟨f, h0, h1⟩ := h i
    refine ⟨f, fun s => ?_⟩
    by_cases hs : s = τ
    · subst hs; simp [h1]
    · simp [hs, h0 s hs]

theorem eigenSub_freeLattice [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ)
    (τ : S) (ha : Function.Injective a) :
    eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ =
      flatLattice (r := r) a τ (diffGen a τ) := by
  ext v
  rw [mem_eigenSub_freeLattice]
  unfold flatLattice
  rw [Submodule.mem_map]
  constructor
  · intro h
    have key : ∀ i, ∃ g : w.valuationSubring, (diffGen a τ : C) * g = v i := by
      intro i
      obtain ⟨f, h0, h1⟩ := h i
      obtain ⟨q, hq⟩ := prod_X_sub_C_dvd (Finset.univ.erase τ) a
        (fun x _ y _ e => ha e) f (fun j hj => h0 j (Finset.ne_of_mem_erase hj))
      refine ⟨q.eval (a τ), ?_⟩
      rw [← h1, hq, eval_mul, eval_prod]
      simp [diffGen]
    choose g hg using key
    refine ⟨fun i => (g i : C), (mem_eigenQuot_freeLattice a r τ _).2 fun i => (g i).2, ?_⟩
    funext i
    simp [Algebra.smul_def, hg i]
  · rintro ⟨u, hu, rfl⟩ i
    have hu' := (mem_eigenQuot_freeLattice a r τ u).1 hu
    refine ⟨Polynomial.C (⟨u i, hu' i⟩ : w.valuationSubring) *
      ∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s)), fun s hs => ?_, ?_⟩
    · rw [eval_mul, eval_prod]
      rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩) (by simp)]
      simp
    · rw [eval_mul, eval_prod]
      simp [diffGen, Algebra.smul_def, mul_comm]

theorem main : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (r : ℕ) (τ : S), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ =
      GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.flatLattice (r := r) a τ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ) :=
  fun _ _ _ _ _ _ a r τ ha => eigenSub_freeLattice a r τ ha

end GlobalTheory.EigenSubFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiEigenSublatticeFreeEqDifferentScaledStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piEigenSublattice_free_eq_differentScaled : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ = GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.flatLattice (r := r) a τ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ) := by
  first | exact @GlobalTheory.EigenSubFree.main | exact GlobalTheory.EigenSubFree.main | (intros; apply GlobalTheory.EigenSubFree.main <;> assumption)
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.FrameModel

theorem det_append_eq_mul_det : ∀ (C : Type) [Field C] (w : Valuation C NNReal) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → ∀ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C) (m : Fin q → Fin (p + q) → C), GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w x (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w (fun i => (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ).mkQ (u i)) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w m (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) → ∃ c : C, w c = ∏ s ∈ Finset.univ.erase τ, w ((a τ : C) - (a s : C)) ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) ∧ (Matrix.of (Fin.append u m)).det = c * (Matrix.of x).det := by
  intro C _ w ℓ hℓ0 hℓ1 S _ _ a p q Fil τ ha hFil x u m hx hu hm
  set F := GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ with hF
  have hfin : Module.finrank C F = q := by
    have hsp : F = Submodule.span C (Set.range m) := by
      rw [hF, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace, ← hm.2, Submodule.span_span_of_tower]
    rw [hsp, finrank_span_eq_card hm.1, Fintype.card_fin]
  have hd0 : GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr ?_
    exact ha.ne (Finset.ne_of_mem_erase hs).symm
  have h1 := GlobalTheory.T.latticeDetRelation_herbrand_eigenspace C w ℓ hℓ0 hℓ1 S a p q Fil τ ha hFil hfin
  rw [GlobalTheory.T.piEigenSublattice_free_eq_differentScaled C w S a (p + q) τ ha] at h1
  have h2 := GlobalTheory.T.latticeDetRelation_of_lsmul_shift C w ℓ hℓ0 hℓ1 p q _ _ _ _ _ _ hd0 h1
  obtain ⟨x', u', m', c, hx', hu', hm', hmF, ⟨hc0, hcv⟩, hdet⟩ := h2
  obtain ⟨P, hP, hPdet⟩ := GlobalTheory.DetRelCompare.transition x' x _ hx' hx
  obtain ⟨A, hA, hAdet⟩ := GlobalTheory.DetRelCompare.transition _ _ _ hu' hu
  obtain ⟨B, hB, hBdet⟩ := GlobalTheory.DetRelCompare.transition m' m _ hm' hm
  have hx'0 : (Matrix.of x').det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp hx'.1)).ne_zero
  have happ0 : (Matrix.of (Fin.append u' m')).det ≠ 0 := by
    intro h0
    exact hx'0 (by rw [hdet, h0, mul_zero])
  have hrel := GlobalTheory.DetRelCompare.det_append_eq F u u' m m' A B hA hB hu'.1 hmF happ0
  have hxP : (Matrix.of x).det = P.det * (Matrix.of x').det := by
    have hmat : Matrix.of x = P * Matrix.of x' := by
      ext i k
      simp [Matrix.mul_apply, hP i, Finset.sum_apply]
    rw [hmat, Matrix.det_mul]
  have hP0 : P.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hPdet
    exact zero_ne_one hPdet
  refine ⟨A.det * B.det * (P.det * c)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv₀, map_mul, hAdet, hBdet, hPdet, one_mul, one_mul, one_mul]
    have hlam : Real.log (w ℓ : ℝ) ≠ 0 :=
      (Real.log_neg (NNReal.coe_pos.mpr hℓ0) (NNReal.coe_lt_one.mpr hℓ1)).ne
    have hds : ∀ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ) ≠ 0 := by
      intro s hs
      rw [NNReal.coe_ne_zero, Valuation.ne_zero_iff]
      exact sub_ne_zero.mpr (Subtype.coe_injective.ne (ha.ne (Finset.ne_of_mem_erase hs).symm))
    have hdiff : ((GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ : w.valuationSubring) : C)
        = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen]
    have hle : ∀ s, Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) ≤ p + q := fun s =>
      (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun C)
    have hlogc : Real.log (w c : ℝ) = - ∑ s ∈ Finset.univ.erase τ,
        ((p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℕ) : ℝ)
          * Real.log (w ((a τ : C) - (a s : C)) : ℝ) := by
      have e := hcv
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal] at e
      rw [hdiff, map_prod, NNReal.coe_prod, Real.log_prod hds, div_eq_iff hlam] at e
      rw [e, sub_mul, Finset.sum_mul, mul_assoc, div_mul_cancel₀ _ hlam, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Nat.cast_sub (hle s)]
      field_simp
      ring
    have hwc : 0 < ((w c : NNReal) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff w).mpr hc0))
    apply NNReal.coe_injective
    rw [NNReal.coe_inv, NNReal.coe_prod]
    simp only [NNReal.coe_pow]
    have hpos2 : 0 < ∏ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ)
        ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) :=
      Finset.prod_pos fun s hs => pow_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (hds s hs).symm) _
    rw [← Real.exp_log (inv_pos.mpr hwc), ← Real.exp_log hpos2, Real.log_inv, hlogc, neg_neg,
      Real.log_prod fun s hs => pow_ne_zero _ (hds s hs)]
    simp only [Real.log_pow]
  · rw [hrel, hxP, hdet]
    field_simp

end GlobalTheory.FrameModel

namespace GlobalTheory.FrameModel

section Small

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

end Small

end GlobalTheory.FrameModel
