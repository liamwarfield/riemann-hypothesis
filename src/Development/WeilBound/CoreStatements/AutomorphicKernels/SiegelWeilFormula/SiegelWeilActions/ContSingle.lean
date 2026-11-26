module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FrameDil
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainLe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PiMapConst
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DMEqDiag
noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n)

def dg (x y : R) (u : Fin n ⊕ Fin n) : R := if u = Sum.inl i₀ then x else if u = Sum.inr i₀ then y else 1

theorem dM_eq_diag (x y : R) : dM i₀ x y = Matrix.diagonal (dg i₀ x y) := by
  ext u v
  rw [dM_apply, Matrix.diagonal_apply, dg]

def wM (a b : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  1 - Matrix.single (Sum.inl i₀) (Sum.inl i₀) 1 - Matrix.single (Sum.inr i₀) (Sum.inr i₀) 1 +
    Matrix.single (Sum.inl i₀) (Sum.inr i₀) a + Matrix.single (Sum.inr i₀) (Sum.inl i₀) b

theorem wM_apply (a b : R) (u v : Fin n ⊕ Fin n) :
    wM i₀ a b u v = if u = Sum.inl i₀ then (if v = Sum.inr i₀ then a else 0) else if u = Sum.inr i₀ then
      (if v = Sum.inl i₀ then b else 0) else if u = v then 1 else 0 := by
  simp only [wM, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
  rcases u with u | u <;> rcases v with v | v <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
    false_and, if_false, sub_zero, add_zero, zero_add, and_self] <;> by_cases h : u = v <;> by_cases h' : u = i₀ <;>
    subst_vars <;> simp_all [eq_comm]

theorem wM_dM (a b x y : R) : wM i₀ a b * dM i₀ x y = dM i₀ y x * wM i₀ a b := by
  rw [dM_eq_diag, dM_eq_diag]
  ext u v
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, wM_apply, dg, dg]
  rcases u with u | u <;> rcases v with v | v <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
    by_cases h : u = v <;> by_cases h' : u = i₀ <;> by_cases h'' : v = i₀ <;> subst_vars <;> simp_all [mul_comm]

theorem smz {i j k l : Fin n ⊕ Fin n} (h : j ≠ k) (c d : R) : Matrix.single i j c * Matrix.single k l d = 0 :=
  Matrix.single_mul_single_of_ne c i j k h d

theorem wM_mul (a b a' b' : R) (h1 : a * b' = 1) (h2 : b * a' = 1) : wM i₀ a b * wM i₀ a' b' = 1 := by
  have n1 : (Sum.inl i₀ : Fin n ⊕ Fin n) ≠ Sum.inr i₀ := by simp
  have n2 : (Sum.inr i₀ : Fin n ⊕ Fin n) ≠ Sum.inl i₀ := by simp
  simp only [wM, sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, Matrix.single_mul_single_same,
    smz n1, smz n2, h1, h2]
  abel

theorem comm_dM (J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (hJ : ∀ u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n)), ∀ v,
      J u v = (1 : Matrix _ _ R) u v ∧ J v u = (1 : Matrix _ _ R) v u) (x y : R) :
    J * dM i₀ x y = dM i₀ x y * J := by
  rw [dM_eq_diag]
  ext u v
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases huv : u = v
  · subst huv; ring
  · by_cases hu : u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n))
    · rw [(hJ u hu v).1, Matrix.one_apply_ne huv]; ring
    · by_cases hv : v ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n))
      · rw [(hJ v hv u).2, Matrix.one_apply_ne huv]; ring
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu hv
        rw [dg, dg, if_neg hu.1, if_neg hu.2, if_neg hv.1, if_neg hv.2]; ring

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsSigmaNe
noncomputable section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma_cm (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2 w.embedding, h.2.2.2 w.embedding, star_star]

theorem exists_sigma_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc : w.IsComplex := h.2.1.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.2 hc
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  change star (w.embedding x) = w.embedding x
  rw [← h.2.2.2 w.embedding, hne]

theorem deltaEx' (h : IsCMExt F E σ) (ε : ℤˣ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -(((ε : ℤ) : E) * δ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨x, hx⟩ := exists_sigma_ne h
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sigma_sigma_cm h]
    simp
  · exact ⟨1, one_ne_zero, by simp⟩

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CBDM
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CBUnitary
noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n k : ℕ} (i₀ : Fin n) (em : Fin k → Fin n)

def cB (u v : Fin k → R) (z : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks (1 + ∑ j, Matrix.single i₀ (em j) (u j)) (Matrix.single i₀ i₀ z) 0 (1 - ∑ j, Matrix.single (em j) i₀ (v j))

variable {i₀ em}

theorem cB_mul (hem : ∀ j, em j ≠ i₀) (u v : Fin k → R) (z : R) : cB i₀ em u v z * cB i₀ em (-u) (-v) (-z) = 1 := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, Matrix.fromBlocks_multiply, Pi.neg_apply, ← Matrix.single_neg,
    Finset.sum_neg_distrib]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, one_mul, mul_one, mul_zero, zero_mul,
      hPP, hQQ, hPZ, hZQ, neg_zero, add_zero, zero_add, sub_zero, neg_neg] <;>
    abel

theorem cB_unitary (hem : ∀ j, em j ≠ i₀) (f : R →+* R) (hf : ∀ a, f (f a) = a) (e : R) (he : e * e = 1)
    (u : Fin k → R) (z : R) (hz : f z = -(e * z)) :
    (cB i₀ em u (fun j => f (u j)) z)ᵀ * kunf.jw n e * (cB i₀ em u (fun j => f (u j)) z).map f = kunf.jw n e := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  have hmap : ∀ M : Matrix (Fin n) (Fin n) R, M.map f = f.mapMatrix M := fun M =>
    (RingHom.mapMatrix_apply f M).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, PositivityTheory.SiegelWeilFormula.kunf.jw, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_sum, Matrix.transpose_single, hmap,
    map_add, map_sub, map_one, map_zero, map_sum]
  simp only [RingHom.mapMatrix_apply, Matrix.map_single, hf, hz]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mul_zero, zero_mul, add_zero]
  · simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_sub, add_mul, one_mul, hQQ, sub_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one]
    congr 1
    simp only [mul_add, sub_mul, one_mul, mul_one, hPP, add_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one,
      mul_sub, sub_mul, one_mul, hPZ, hZQ, sub_zero, Matrix.smul_single, smul_eq_mul, smul_zero]
    rw [← Matrix.single_add, show e * -(e * z) + z = 0 by linear_combination (-z) * he, Matrix.single_zero]

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n k : ℕ} {i₀ : Fin n} {em : Fin k → Fin n}

theorem cB_dM (hem : ∀ j, em j ≠ i₀) (u v : Fin k → R) (z x y : R) (hxy : x * y = 1) :
    cB i₀ em u v z * dM i₀ x y = dM i₀ x y * cB i₀ em (fun j => y * u j) (fun j => y * v j) (y * y * z) := by
  have hS : ∀ (w : Fin k → R) a b, (∑ j, Matrix.single i₀ (em j) (w j)) a b =
      if a = i₀ then ∑ j, (if em j = b then w j else 0) else 0 := by
    intro w a b
    rw [Matrix.sum_apply]
    split_ifs with ha
    · subst ha; exact Finset.sum_congr rfl fun j _ => by rw [Matrix.single_apply]; simp
    · exact Finset.sum_eq_zero fun j _ => by
        rw [Matrix.single_apply]; split_ifs with h
        · exact absurd h.1.symm ha
        · rfl
  have hT : ∀ (w : Fin k → R) a b, (∑ j, Matrix.single (em j) i₀ (w j)) a b =
      if b = i₀ then ∑ j, (if em j = a then w j else 0) else 0 := by
    intro w a b
    rw [Matrix.sum_apply]
    split_ifs with hb
    · subst hb; exact Finset.sum_congr rfl fun j _ => by rw [Matrix.single_apply]; simp
    · exact Finset.sum_eq_zero fun j _ => by
        rw [Matrix.single_apply]; split_ifs with h
        · exact absurd h.2.symm hb
        · rfl
  have hs0 : ∀ (w : Fin k → R), ∑ j, (if em j = i₀ then w j else 0) = 0 :=
    fun w => Finset.sum_eq_zero fun j _ => by rw [if_neg (hem j)]
  have hsy : ∀ (w : Fin k → R) b, ∑ j, (if em j = b then y * w j else 0) = y * ∑ j, (if em j = b then w j else 0) := by
    intro w b; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  rw [dM_eq_diag]
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases p with a | a <;> rcases q with b | b
  · simp only [cB, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.one_apply, hS, hsy, dg, Sum.inl.injEq, reduceCtorEq,
      if_false]
    by_cases hab : a = b
    · subst hab; by_cases ha : a = i₀
      · subst ha; simp [hs0]
      · simp [ha]
    · by_cases ha : a = i₀
      · subst ha
        simp only [if_neg hab, if_true, if_neg (Ne.symm hab), zero_add, mul_one]
        rw [← mul_assoc, hxy, one_mul]
      · simp [ha, hab]
  · simp only [cB, Matrix.fromBlocks_apply₁₂, Matrix.single_apply, dg, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]
    by_cases h : i₀ = a ∧ i₀ = b
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true]
      linear_combination (-(y * z)) * hxy
    · simp only [if_neg h, zero_mul, mul_zero]
  · simp [cB]
  · simp only [cB, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.one_apply, hT, hsy, dg, Sum.inr.injEq, reduceCtorEq,
      if_false]
    by_cases hab : a = b
    · subst hab; by_cases ha : a = i₀
      · subst ha; simp [hs0]
      · simp [ha]
    · by_cases hb : b = i₀
      · subst hb
        simp only [if_neg hab, if_true, if_neg hab, zero_sub]
        ring
      · simp [hb, hab]

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.WMUnitary
noncomputable section

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n)

theorem wM_map {S : Type} [CommRing S] (f : R →+* S) (a b : R) : (wM i₀ a b).map f = wM i₀ (f a) (f b) := by
  delta wM
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply, map_add, map_sub]
  split_ifs <;> simp

theorem wM_blocks (a b : R) : wM i₀ a b = Matrix.fromBlocks (1 - Matrix.single i₀ i₀ 1) (a • Matrix.single i₀ i₀ 1)
    (b • Matrix.single i₀ i₀ 1) (1 - Matrix.single i₀ i₀ 1) := by
  delta wM
  ext (i | i) (j | j) <;>
    simp [Matrix.single_apply, Matrix.one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem wM_unitary (f : R →+* R) (a b e : R) (h1 : b * e * f a = 1) (h2 : a * f b = e) :
    (wM i₀ a b)ᵀ * kunf.jw n e * (wM i₀ a b).map f = kunf.jw n e := by
  have hjw : kunf.jw n e = Matrix.fromBlocks 0 1 (e • 1) 0 := rfl
  have hEE : Matrix.single i₀ i₀ (1 : R) * Matrix.single i₀ i₀ 1 = Matrix.single i₀ i₀ 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hET : (Matrix.single i₀ i₀ (1 : R))ᵀ = Matrix.single i₀ i₀ 1 := Matrix.transpose_single _ _ _
  have h1' : e * b * f a = 1 := by rw [mul_comm e b]; exact h1
  rw [wM_map, wM_blocks, wM_blocks, hjw]
  generalize Matrix.single i₀ i₀ (1 : R) = E at hEE hET ⊢
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hET,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, hEE, sub_self, smul_zero,
    sub_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · trivial
  · linear_combination (norm := module) h1' • E
  · linear_combination (norm := module) h2 • E
  · trivial
end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

def CLawEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d),
  ∃ (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G) (κ : Measure ((Fin L.n → AE F E) × AF F)),
    CLaw R L w₁ cM κ ∧ w₁ ∈ rat2 σ d.Y ∧
    (∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)) ∧
    Continuous cM ∧ κ.IsAddHaarMeasure ∧
    ∃ δ : E, δ ≠ 0 ∧ ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (c.1 j))
      (Matrix.single L.i₀ L.i₀ (c.2 • inclR (F := F) (AF F) δ)) 0 A'

theorem cont_single {X α : Type} [TopologicalSpace X] [TopologicalSpace α] [Zero α] {m p : Type} [DecidableEq m]
    [DecidableEq p] (i : m) (j : p) {f : X → α} (hf : Continuous f) : Continuous fun x => Matrix.single i j (f x) :=
  continuous_pi fun a => continuous_pi fun b => by
    simp only [Matrix.single_apply]
    split_ifs
    exacts [hf, continuous_const]

theorem cLawEx : CLawEx := by
  intro F E _ _ _ _ _ σ d R L
  have hε := R.hε
  have hem : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  set e : AE F E := ((R.ε : ℤ) : AE F E) with he_def
  have hee : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  obtain ⟨δ, hδ0, hδ⟩ := CL.deltaEx' d.cm R.ε
  obtain ⟨κ, hκ, hsc⟩ := CL.measEx' (F := F) (E := E) L.n d.bs

  let M₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ (1 : E) ((R.ε : ℤ) : E)
  let M₀' : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ ((R.ε : ℤ) : E) (1 : E)
  have hW : incM F M₀ = CL.wM L.i₀ (1 : AE F E) e := by
    show M₀.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hW' : incM F M₀' = CL.wM L.i₀ e (1 : AE F E) := by
    show M₀'.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hWW : incM F M₀ * incM F M₀' = 1 := by
    rw [hW, hW']; exact CL.wM_mul L.i₀ _ _ _ _ (one_mul 1) hee
  have hWu : (incM F M₀)ᵀ * kunf.jw d.n e * (incM F M₀).map (cA σ) = kunf.jw d.n e := by
    rw [hW]
    refine CL.wM_unitary L.i₀ (cA σ).toRingHom 1 e e ?_ ?_
    · simp only [AlgHom.toRingHom_eq_coe, map_one, mul_one, hee]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, he_def, map_intCast, one_mul]
  obtain ⟨w₁, hw₁⟩ := kunf.exists_of_frame hε (incM F M₀) (incM F M₀') hWW hWu
  have hw₁' : inFrame d.b w₁ = CL.wM L.i₀ (1 : AE F E) e := hw₁.trans hW

  set δ' : AE F E := inclR (F := F) (AF F) δ with hδ'
  let Mc : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em c.1 (fun j => cA σ (c.1 j)) (c.2 • δ')
  let Mc' : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em (-c.1) (-fun j => cA σ (c.1 j)) (-(c.2 • δ'))
  have hcont : ∀ s : AF F → AF F, Continuous s → ∀ t : (Fin L.n → AE F E) → (Fin L.n → AE F E), Continuous t →
      Continuous fun c : (Fin L.n → AE F E) × AF F =>
        CL.cB L.i₀ L.em (t c.1) (fun j => cA σ (t c.1 j)) (s c.2 • δ') := by
    intro s hs t ht
    refine Continuous.matrix_fromBlocks ?_ ?_ continuous_const ?_
    · exact continuous_const.add (continuous_finsetSum _ fun j _ =>
        cont_single _ _ ((continuous_apply j).comp (ht.comp continuous_fst)))
    · exact cont_single _ _ (Continuous.smul (f := fun c : (Fin L.n → AE F E) × AF F => s c.2) (g := fun _ => δ')
        (hs.comp continuous_snd) continuous_const)
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => cont_single _ _
        ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp ((continuous_apply j).comp (ht.comp continuous_fst))))
  have hMc : Continuous Mc := hcont id continuous_id id continuous_id
  have hMc' : Continuous Mc' := by
    have := hcont (fun a => -a) continuous_neg (fun u => -u) continuous_neg
    convert this using 2 with c
    simp only [Mc', neg_smul, Pi.neg_apply, map_neg]
    rfl
  have cA_inclR (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have cA_invol (z : AE F E) : cA σ (cA σ z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
        (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, CL.sigma_sigma_cm d.cm]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcA_z : ∀ a : AF F, cA σ (a • δ') = -(e * (a • δ')) := by
    intro a
    rw [map_smul, hδ', cA_inclR δ, hδ, map_neg, map_mul, map_intCast, smul_neg, mul_smul_comm]
  obtain ⟨cM, hcMc, hcM⟩ := CL.ptEx' d hε Mc Mc' hMc hMc'
    (fun c => CL.cB_mul hem c.1 _ _) (fun c => CL.cB_unitary hem (cA σ).toRingHom
      cA_invol e hee c.1 (c.2 • δ') (hcA_z c.2))
  have hfr := fun x y => GlobalTheory.EisBL.DoubledParabolic.inFrame_mul (σ := σ) (Y := d.Y) d.b x y
  refine ⟨w₁, cM, κ, ⟨?_, ?_, ?_⟩, kunf.rat_of_inFrame hw₁, ⟨1, (R.ε : ℤ), one_ne_zero, ?_, ?_⟩, hcMc, hκ,
    ⟨δ, hδ0, fun c => ⟨_, hcM c⟩⟩⟩
  ·
    intro w τ y g hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := CL.rEx d w
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, CL.frame_dil d R w r hrw hro hrf L.i₀ hy]
    exact CL.comm_dM L.i₀ _ (L.j_out g) _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := CL.rEx d w
    have hy' := CL.isDil_inv hy
    obtain ⟨t, ht, ha, hχ⟩ := CL.par_dil d R w L.i₀ hy'
    refine ⟨R.ι w y⁻¹, t, ht, by rw [ha]; ring_nf, hχ, ?_⟩
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, hw₁', CL.frame_dil d R w r hrw hro hrf L.i₀ hy, CL.frame_dil d R w r hrw hro hrf L.i₀ hy', neg_neg]
    exact CL.wM_dM L.i₀ _ _ _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, hrm, hrw, hro, hrf⟩ := CL.rEx d w
    obtain ⟨sc, hsc1, hsc2⟩ := hsc (r (-τ))
    refine ⟨sc, fun c => ?_, ?_⟩
    · apply kunf.inFrame_injective d.b
      rw [hfr, hfr, hcM, hcM, CL.frame_dil d R w r hrw hro hrf L.i₀ hy]
      have hxy : ((r τ : AF F) • (1 : AE F E)) * ((r (-τ) : AF F) • (1 : AE F E)) = 1 := by
        rw [smul_mul_smul_comm, one_mul, ← Units.val_mul, ← hr0, add_neg_cancel, hr1]; simp
      rw [CL.cB_dM hem _ _ _ _ _ hxy, hsc1]
      congr 1
      simp only [Mc]
      congr 1
      · funext j; exact smul_one_mul _ _
      · funext j; rw [map_smul, smul_one_mul]
      · rw [mul_assoc, smul_one_mul, smul_one_mul, smul_assoc, mul_smul]
    · rw [hsc2, hrm, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul, ← Atop.LD.n_succ L]
      congr 2
      push_cast; ring
  · simp [map_intCast]
  · rw [hw₁']; simp [CL.wM, map_intCast, map_one, he_def]

end PositivityTheory.SiegelWeilFormula.Act

end
