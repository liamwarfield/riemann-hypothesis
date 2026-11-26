module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section Ring

variable {R : Type} [CommRing R]

private def Low (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) : Prop :=
  ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 → M i j = 0

private theorem low_mul {M N : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R} (hM : Low M) (hN : Low N) : Low (M * N) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < 2
  · rw [hM i k hi hk, zero_mul]
  · rw [hN k j (not_lt.1 hk) hj, mul_zero]

private theorem low_blocks (A B D : Matrix (Fin 2) (Fin 2) R) :
    Low (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D)) := by
  intro i j hi hj
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rcases i with i | i
  · exact absurd (show 2 ≤ (i : ℕ) from hi) (not_le.2 i.2)
  rcases j with j | j
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
  · exact absurd (show 2 + (j : ℕ) < 2 from hj) (by omega)

private def xm (X : UPos (2 + 2) 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j => X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), i.2, Nat.le_add_right 2 j⟩

private theorem unip_eq (X : UPos (2 + 2) 2 → R) :
    unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 (xm X) 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply, xm] <;> rfl

private theorem xm_bij : Function.Bijective (xm : (UPos (2 + 2) 2 → R) → _) := by
  constructor
  · intro X Y h
    apply unipGL_injective
    apply Units.ext
    rw [coe_unipGL, coe_unipGL, unip_eq, unip_eq, h]
  · intro B
    refine ⟨fun p => B ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩, ?_⟩
    ext i j
    simp [xm]

private theorem unip_blk (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    ((unipGL X * blk a b : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val (xm X * b.val) 0 b.val) := by
  rw [Units.val_mul, coe_unipGL, unip_eq]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem unip_blk_inj {X X' : UPos (2 + 2) 2 → R} {a b a' b' : GL (Fin 2) R}
    (h : unipGL X * blk a b = unipGL X' * blk a' b') : X = X' ∧ a = a' ∧ b = b' := by
  have h1 := congrArg Units.val h
  rw [unip_blk, unip_blk] at h1
  obtain ⟨ha, hx, -, hb⟩ := Matrix.fromBlocks_inj.1 ((Matrix.reindex _ _).injective h1)
  obtain rfl : b = b' := Units.ext hb
  exact ⟨xm_bij.1 ((Units.mul_left_inj b).1 hx), Units.ext ha, rfl⟩

private theorem low_inv_unip_blk (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    Low (((unipGL X * blk a b)⁻¹ : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) := by
  rw [mul_inv_rev, Units.val_mul, coe_unipGL_inv, unip_eq]
  exact low_mul (low_blocks _ _ _) (low_blocks _ _ _)

end Ring

private theorem low_decomp {K : Type} [Field K] (g : GL (Fin (2 + 2)) K) (hg : Low g.val) :
    ∃ (X : UPos (2 + 2) 2 → K) (a b : GL (Fin 2) K), g = unipGL X * blk a b := by
  set M := (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm g.val with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    exact hg _ _ (Nat.le_add_right 2 i) j.2
  have hb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hd : M.det ≠ 0 := by
    rw [hM, Matrix.reindex_symm, Matrix.det_reindex_self]
    exact g.det_ne_zero
  rw [hb, Matrix.det_fromBlocks_zero₂₁, mul_ne_zero_iff] at hd
  let a := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd.1
  let b := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd.2
  obtain ⟨X, hX⟩ := xm_bij.2 (M.toBlocks₁₂ * (b⁻¹).val)
  refine ⟨X, a, b, Units.ext ?_⟩
  rw [unip_blk, hX, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  change _ = Matrix.reindex _ _ (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂)
  rw [← hb, hM, Equiv.apply_symm_apply]

variable {K : Type} [Field K] [NumberField K]

private theorem diag_blk (a b : GL (Fin 2) K) :
    AdelicGLn.diagonal K (2 + 2) (blk a b) = blk (AdelicGLn.diagonal K 2 a) (AdelicGLn.diagonal K 2 b) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rw [AdelicGLn.diagonal_apply]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp

private theorem zt_zero : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  congr 1
  exact Subtype.ext Real.exp_zero

private theorem low_diag (g : GL (Fin (2 + 2)) K) : Low (AdelicGLn.diagonal K (2 + 2) g).val ↔ Low g.val :=
  forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => forall_congr' fun _ => by
    rw [AdelicGLn.diagonal_apply]
    exact map_eq_zero_iff _ (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K)

private theorem gam_cases {n : ℕ} (γ : Gam K n) : ∃ g : GL (Fin n) K,
    γ = ⟨⟨AdelicGLn.diagonal K n g, rationalGL_le_normOneGL ⟨g, rfl⟩⟩, g, rfl⟩ := by
  obtain ⟨g, hg⟩ := γ.2
  exact ⟨g, Subtype.ext (Subtype.ext hg.symm)⟩

private def lowΓ (K : Type) [Field K] [NumberField K] : Subgroup (Gam K (2 + 2)) where
  carrier := {γ | Low ((γ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)).val}
  one_mem' := by
    intro i j hi hj
    exact Matrix.one_apply_ne (by rintro rfl; omega)
  mul_mem' ha hb := low_mul ha hb
  inv_mem' := by
    intro γ hg
    obtain ⟨g, rfl⟩ := gam_cases γ
    obtain ⟨X, a, b, rfl⟩ := low_decomp g ((low_diag g).1 hg)
    change Low (AdelicGLn.diagonal K (2 + 2) (unipGL X * blk a b))⁻¹.val
    rw [← map_inv, low_diag]
    exact low_inv_unip_blk X a b

private theorem par_eq : ParΓ K 2 2 = lowΓ K := Subgroup.closure_eq (lowΓ K)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pkLaws :
    ∀ {K : Type} [Field K] [NumberField K], (∀ γ : Gam K (2 + 2), γ ∈ ParΓ K 2 2 ↔ ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 →
        (((γ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) i j = 0) ∧
      (∀ γ : G1 K (2 + 2), γ ∈ PK K ↔ ∃ (ξ : unipLattice K (2 + 2) 2) (γ₁ : Gam K 2) (γ₂ : Gam K 2),
        γ = unipOne (K := K) (n := 2 + 2) 2 ξ.1 * lv γ₁ γ₂ 0) ∧
      (∀ (ξ ξ' : UPos (2 + 2) 2 → 𝔸[K]) (a b a' b' : G1 K 2) (t t' : ℝ),
        unipOne (K := K) (n := 2 + 2) 2 ξ * lv a b t =
          unipOne (K := K) (n := 2 + 2) 2 ξ' * lv a' b' t' → ξ = ξ' ∧ a = a' ∧ b = b' ∧ t = t') ∧
      ∀ γ : Gam K (2 + 2), ∃ δ ∈ PK K, (((Quotient.mk _ γ : Cos K).out : Gam K (2 + 2)) : G1 K (2 + 2)) = δ * γ := by
  intro K _ _
  have hlv := (blkLaws (K := K)).1
  have hco : ∀ (ξ : UPos (2 + 2) 2 → 𝔸[K]) (a b : G1 K 2) (t : ℝ),
      ((unipOne (K := K) (n := 2 + 2) 2 ξ * lv a b t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        unipGL ξ * blk ((a : AdelicGLn.AdelicGL K 2) * zt K t) ((b : AdelicGLn.AdelicGL K 2) * zt K (-t)) :=
    fun ξ a b t => by rw [Subgroup.coe_mul, hlv, coe_unipOne]
  have hdg : ∀ (X : UPos (2 + 2) 2 → K) (a b : GL (Fin 2) K) (h₁ h₂),
      ((unipOne (K := K) (n := 2 + 2) 2 (fun p => algebraMap K 𝔸[K] (X p)) *
        lv ⟨AdelicGLn.diagonal K 2 a, h₁⟩ ⟨AdelicGLn.diagonal K 2 b, h₂⟩ 0 :
        G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = AdelicGLn.diagonal K (2 + 2) (unipGL X * blk a b) :=
    fun X a b h₁ h₂ => by rw [hco, neg_zero, zt_zero, mul_one, mul_one, map_mul, diag_blk, diagonal_unipGL]
  refine ⟨fun γ => by rw [par_eq]; rfl, fun γ => ⟨?_, ?_⟩, ?_, fun γ => ?_⟩
  · rintro ⟨γ, hg, rfl⟩
    obtain ⟨g, rfl⟩ := gam_cases γ
    rw [par_eq] at hg
    obtain ⟨X, a, b, rfl⟩ := low_decomp g ((low_diag g).1 hg)
    exact ⟨⟨_, X, rfl⟩, ⟨⟨_, rationalGL_le_normOneGL ⟨a, rfl⟩⟩, a, rfl⟩, ⟨⟨_, rationalGL_le_normOneGL ⟨b, rfl⟩⟩, b, rfl⟩,
      Subtype.ext (hdg X a b _ _).symm⟩
  · rintro ⟨⟨_, X, rfl⟩, γ₁, γ₂, rfl⟩
    obtain ⟨a, rfl⟩ := gam_cases γ₁
    obtain ⟨b, rfl⟩ := gam_cases γ₂
    have h₁ : AdelicGLn.diagonal K 2 a ∈ normOneGL (K := K) (n := 2) := rationalGL_le_normOneGL ⟨a, rfl⟩
    have h₂ : AdelicGLn.diagonal K 2 b ∈ normOneGL (K := K) (n := 2) := rationalGL_le_normOneGL ⟨b, rfl⟩
    refine ⟨⟨_, unipGL X * blk a b, (hdg X a b h₁ h₂).symm⟩, ?_, rfl⟩
    rw [par_eq]
    change Low (Units.val _)
    have h := (low_diag (unipGL X * blk a b)).2 (by rw [unip_blk]; exact low_blocks _ _ _)
    rw [← hdg X a b h₁ h₂] at h
    exact h
  · intro ξ ξ' a b a' b' t t' h
    have h1 := congrArg Subtype.val h
    rw [hco, hco] at h1
    obtain ⟨hx, ha, hb⟩ := unip_blk_inj h1
    have h2 := congrArg (detModule K 2) ha
    rw [map_mul, map_mul, mem_normOneGL_iff_detModule.1 a.2, mem_normOneGL_iff_detModule.1 a'.2, one_mul, one_mul,
      zt, zt, detModule_centralSection two_pos, detModule_centralSection two_pos] at h2
    obtain rfl : t = t' := Real.exp_injective (congrArg Subtype.val h2)
    exact ⟨hx, Subtype.ext (mul_right_cancel ha), Subtype.ext (mul_right_cancel hb), rfl⟩
  · have h : (QuotientGroup.rightRel (ParΓ K 2 2)) γ (Quotient.mk _ γ : Cos K).out :=
      Quotient.exact (Quotient.out_eq _).symm
    rw [QuotientGroup.rightRel_apply] at h
    refine ⟨_, ⟨_, h, rfl⟩, ?_⟩
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem unip_blocks {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 ((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ 0 (1 : Matrix (Fin b) (Fin b) R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_onto {a b : ℕ} {R : Type} [CommRing R] (B : Matrix (Fin a) (Fin b) R) : ∃ X : UPos (a + b) a → R,
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B 0 0) p.1.1 p.1.2, ?_⟩
  rw [unip_blocks]
  congr 1
  ext i j
  have : (Fin.castAdd b i : Fin (a + b)) ≠ Fin.natAdd a j := by
    simp [Fin.ext_iff]; omega
  simp [unipMatrix, blockEntry_apply, Matrix.toBlocks₁₂, this]

private theorem dec {a b : ℕ} {R : Type} [CommRing R] (g : GL (Fin (a + b)) R)
    (h : (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ (c : GL (Fin a) R) (d : GL (Fin b) R), (c.val = (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ ∧
      c⁻¹.val = (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁) ∧
      (d.val = (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ ∧
      d⁻¹.val = (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂) ∧
      ∃ X : UPos (a + b) a → R, g = unipGL X * blk c d := by
  have e1 : g.val.submatrix finSumFinEquiv finSumFinEquiv * g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv =
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) := by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hg : ∀ M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R, g.val.submatrix finSumFinEquiv finSumFinEquiv = M →
      g.val = M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rintro _ rfl
    simp
  generalize g.val.submatrix finSumFinEquiv finSumFinEquiv = M at *
  generalize g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv = N at *
  have hM := (Matrix.fromBlocks_toBlocks M).symm
  rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, h, h', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1
  obtain ⟨e1, -, -, e2⟩ := e1
  obtain ⟨X, hX⟩ := unip_onto (M.toBlocks₁₂ * N.toBlocks₂₂)
  refine ⟨⟨_, _, e1, mul_eq_one_comm.1 e1⟩, ⟨_, _, e2, mul_eq_one_comm.1 e2⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, X, Units.ext ?_⟩
  have hX' : unipMatrix X = (Matrix.fromBlocks 1 (M.toBlocks₁₂ * N.toBlocks₂₂) 0 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hX]; simp
  rw [Units.val_mul, coe_unipGL, hX', hg M rfl]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_assoc, mul_eq_one_comm.1 e2, Matrix.mul_one]
  rw [← h, ← hM]

private theorem of_low {K : Type} [Field K] [NumberField K] (s : G1 K (2 + 2))
    (h : ((s : AdelicGLn.AdelicGL K (2 + 2)).val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : ((s : AdelicGLn.AdelicGL K (2 + 2))⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ X m₁ m₂ t, s = unipOne (K := K) (n := 2 + 2) 2 X * lv m₁ m₂ t := by
  obtain ⟨hlv, -, -, -, hdet, -⟩ := blkLaws (K := K)
  obtain ⟨a, d, -, -, X, hX⟩ := dec (s : AdelicGLn.AdelicGL K (2 + 2)) h h'
  refine ⟨X, retractOne a, retractOne d, Real.log (detModule K 2 a).1, ?_⟩
  have h1 : detModule K 2 a * detModule K 2 d = 1 := by
    have := mem_normOneGL_iff_detModule.1 s.2
    rwa [hX, map_mul, mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL _), one_mul, hdet] at this
  have z1 : zt K (Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 a) := by
    unfold zt
    congr 1
    exact Subtype.ext (Real.exp_log (detModule K 2 a).2)
  have z2 : zt K (-Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 d) := by
    unfold zt
    congr 1
    refine Subtype.ext ?_
    rw [eq_inv_of_mul_eq_one_right h1]
    show Real.exp (-Real.log _) = _
    rw [Real.exp_neg, Real.exp_log (detModule K 2 a).2]
    rfl
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, coe_unipOne, hlv, z1, z2, coe_retractOne, coe_retractOne,
    inv_mul_cancel_right, inv_mul_cancel_right]
  exact hX

private theorem low_borel {K : Type} [Field K] [NumberField K] {b : AdelicGLn.AdelicGL K (2 + 2)} (hb : b ∈ adelicBorel) :
    (b.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
  ext i j
  refine mem_adelicBorel.1 hb ?_
  show finSumFinEquiv (Sum.inl j) < finSumFinEquiv (Sum.inr i)
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.iwa :
    ∀ {K : Type} [Field K] [NumberField K] (g : G1 K (2 + 2)),
      ∃ (X : UPos (2 + 2) 2 → 𝔸[K]) (m₁ m₂ : G1 K 2) (t : ℝ),
        ∃ k ∈ KG K (2 + 2), g = unipOne (K := K) (n := 2 + 2) 2 X * lv m₁ m₂ t * k := by
  intro K _ _ g
  obtain ⟨b, hb, k, hk, e⟩ := exists_adelicBorel_mul_maxCompact (g : AdelicGLn.AdelicGL K (2 + 2))
  let k' : G1 K (2 + 2) := ⟨k, maxCompact_le_normOneGL hk⟩
  have hs : ((g * k'⁻¹ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = b := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, e]
    exact mul_inv_cancel_right b k
  obtain ⟨X, m₁, m₂, t, h⟩ := of_low (g * k'⁻¹) (by rw [hs]; exact low_borel hb) (by rw [hs]; exact low_borel (inv_mem hb))
  exact ⟨X, m₁, m₂, t, k', hk, by rw [← h, inv_mul_cancel_right]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open scoped Matrix Kronecker in
private theorem adMeas_pi {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι 𝔸[K]) (u : (𝔸[K])ˣ) (hu : (u : 𝔸[K]) = M.det) :
    (Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K).map (fun x => x ᵥ* M) =
      ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ))⁻¹ •
        Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K := by
  let σ := Fintype.equivFin ι
  have hd : (Matrix.reindex σ σ M).det = u := by rw [Matrix.det_reindex_self, hu]
  let g : GL (Fin (Fintype.card ι)) 𝔸[K] :=
    Matrix.GeneralLinearGroup.mk'' (Matrix.reindex σ σ M) (hd ▸ u.isUnit)
  have hg : (g : Matrix _ _ 𝔸[K]) = Matrix.reindex σ σ M := rfl
  have hdet : Matrix.GeneralLinearGroup.det g = u := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hd])
  have h := GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  rw [hdet] at h
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => 𝔸[K]) σ
  have hE : MeasurePreserving E (Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K)
      (GJMatrix.adeleMeasurePi K) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) => GroundTheory.Global.adeleMeasure K) σ
  have hfun : (fun x : ι → 𝔸[K] => x ᵥ* M) =
      E.symm ∘ (fun x => x ᵥ* (g : Matrix _ _ 𝔸[K])) ∘ E := by
    funext x
    have hx : E x = x ∘ σ.symm := by
      funext i
      obtain ⟨j, rfl⟩ := σ.surjective i
      simp [E, MeasurableEquiv.piCongrLeft_apply_apply]
    funext i
    change _ = (E x ᵥ* (g : Matrix _ _ 𝔸[K])) (σ i)
    rw [hx, hg, Matrix.reindex_apply, Matrix.submatrix_vecMul_equiv]
    simp [Function.comp_assoc]
  have hm := GJGlobal.Modulus.measurable_vecMul' g
  rw [hfun, ← Measure.map_map E.symm.measurable (hm.comp E.measurable),
    ← Measure.map_map hm E.measurable, hE.map_eq, h, Measure.map_smul, hE.symm.map_eq]
  exact E.symm.measurable.aemeasurable

private def adMeas_tau : Fin 2 × Fin 2 ≃ UPos (2 + 2) 2 where
  toFun p := ⟨(Fin.castAdd 2 p.1, Fin.natAdd 2 p.2), p.1.2, Nat.le_add_right _ _⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩)
  left_inv := by decide
  right_inv := by decide

private theorem adMeas_unip {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) :
    unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks 1 (Matrix.of fun i j => X (adMeas_tau (i, j))) 0 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] <;>
    fin_cases i <;> fin_cases j <;> simp [adMeas_tau, Fin.ext_iff]

open scoped Matrix Kronecker in
private noncomputable def adMeas_M {R : Type} [CommRing R] (a b : GL (Fin 2) R) :
    Matrix (UPos (2 + 2) 2) (UPos (2 + 2) 2) R :=
  Matrix.reindex adMeas_tau adMeas_tau (((a⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)ᵀ ⊗ₖ (b : Matrix (Fin 2) (Fin 2) R))

private theorem adMeas_M_mul {R : Type} [CommRing R] (a b : GL (Fin 2) R) :
    adMeas_M a b * adMeas_M a⁻¹ b⁻¹ = 1 := by
  simp only [adMeas_M, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, ← Units.val_mul, ← Units.val_mul]
  simp

open scoped Matrix in
private theorem adMeas_conj {R : Type} [CommRing R] (a b : GL (Fin 2) R) (X : UPos (2 + 2) 2 → R) :
    unipGL X * blk a b = blk a b * unipGL (X ᵥ* adMeas_M a b) := by
  have h : (Matrix.of fun i j => (X ᵥ* adMeas_M a b) (adMeas_tau (i, j))) =
      ((a⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (Matrix.of fun i j => X (adMeas_tau (i, j))) *
        (b : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    rw [adMeas_M, Matrix.reindex_apply, Matrix.of_apply, Matrix.submatrix_vecMul_equiv]
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm, Matrix.vecMul, dotProduct,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_two]
    ring
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_unipGL, coe_unipGL, adMeas_unip, adMeas_unip, h]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
  simp

open scoped Matrix in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.adMeas :
    ∀ {K : Type} [Field K] [NumberField K] (m₁ m₂ : G1 K 2) (t : ℝ),
    ∃ e : (UPos (2 + 2) 2 → 𝔸[K]) ≃ₜ+ (UPos (2 + 2) 2 → 𝔸[K]),
      (∀ X, unipOne (K := K) (n := 2 + 2) 2 X * lv m₁ m₂ t =
        lv m₁ m₂ t * unipOne (K := K) (n := 2 + 2) 2 (e X)) ∧
      (unipMeasure K (2 + 2) 2).map e = ENNReal.ofReal (Real.exp (4 * t)) • unipMeasure K (2 + 2) 2 := by
  intro K _ _ m₁ m₂ t
  set a : AdelicGLn.AdelicGL K 2 := (m₁ : AdelicGLn.AdelicGL K 2) * zt K t with ha
  set b : AdelicGLn.AdelicGL K 2 := (m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t) with hb
  have h2 : adMeas_M a⁻¹ b⁻¹ * adMeas_M a b = 1 := by
    simpa using adMeas_M_mul a⁻¹ b⁻¹
  refine ⟨{ toFun := fun X => X ᵥ* adMeas_M a b
            invFun := fun X => X ᵥ* adMeas_M a⁻¹ b⁻¹
            left_inv := fun X => by simp only [Matrix.vecMul_vecMul, adMeas_M_mul, Matrix.vecMul_one]
            right_inv := fun X => by simp only [Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
            map_add' := fun X Y => Matrix.add_vecMul _ _ _
            continuous_toFun := continuous_id.matrix_vecMul continuous_const
            continuous_invFun := continuous_id.matrix_vecMul continuous_const }, fun X => ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, (blkLaws (K := K)).1 m₁ m₂ t]
    exact adMeas_conj a b X
  · have hm : ∀ (m : G1 K 2) (s : ℝ),
        (detModule K 2 ((m : AdelicGLn.AdelicGL K 2) * zt K s) : ℝ) = Real.exp s := by
      intro m s
      rw [map_mul, mem_normOneGL_iff_detModule.1 m.2, one_mul, zt, detModule_centralSection two_pos]
    have h := adMeas_pi (adMeas_M a b)
      (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) (by
        rw [adMeas_M, Matrix.det_reindex_self, Matrix.det_kronecker, Matrix.det_transpose]
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply,
          Fintype.card_fin])
    have hv : ((GroundTheory.Global.IdeleGroup.ideleModule K
        (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) : ℝ))⁻¹ =
        Real.exp (4 * t) := by
      have e1 : GroundTheory.Global.IdeleGroup.ideleModule K
          (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) =
          (detModule K 2 a)⁻¹ ^ 2 * detModule K 2 b ^ 2 := by
        rw [map_mul, map_pow, map_pow, ← map_inv (detModule K 2)]
        rfl
      rw [e1, Positive.val_mul, Positive.val_pow, Positive.val_pow, Positive.coe_inv, hm, hm,
        ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    rw [hv] at h
    exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [T2Space G]

private theorem integ {U : Set G} (hU : IsCompact U) {ν : Measure G} [IsProbabilityMeasure ν] (hs : ∀ᵐ k ∂ν, k ∈ U)
    {F : G → ℂ} (hF : Continuous F) : Integrable F ν := by
  have h := hF.continuousOn.integrableOn_compact (μ := ν) hU
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at h

private def fixSub {U : Set G} (hU : IsCompact U) (ν : Measure G) [IsProbabilityMeasure ν] (hs : ∀ᵐ k ∂ν, k ∈ U)
    {e : G → ℂ} (he : Continuous e) : Submodule ℂ (G → ℂ) where
  carrier := {F | Continuous F ∧ ∀ g, ∫ k, e k * F (g * k) ∂ν = F g}
  add_mem' := by
    rintro F F' ⟨hF, h⟩ ⟨hF', h'⟩
    refine ⟨hF.add hF', fun g => ?_⟩
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (integ hU hs (by fun_prop)) (integ hU hs (by fun_prop)), h, h']
  zero_mem' := ⟨continuous_const, by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, h⟩
    refine ⟨hF.const_smul c, fun g => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [integral_const_mul, h]

private theorem detect (U : Subgroup G) (hU : IsCompact (U : Set G)) (ν : Measure G) [IsProbabilityMeasure ν]
    (hs : ∀ᵐ k ∂ν, k ∈ U) (hinv : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) {e : G → ℂ} (he : Continuous e) :
    ∃ t : Finset G, (∀ x ∈ t, x ∈ U) ∧ ∀ F : G → ℂ, Continuous F → (∀ g, ∫ k, e k * F (g * k) ∂ν = F g) →
      (∀ x ∈ t, F x = 0) → ∀ x ∈ U, F x = 0 := by
  have h1 : ∀ u ∈ (U : Set G), {x : G | ∀ k ∈ (U : Set G), ‖e (x⁻¹ * k) - e (u⁻¹ * k)‖ < 1 / 2} ∈ 𝓝 u := by
    intro u _
    refine hU.eventually_forall_of_forall_eventually (x₀ := u)
      (P := fun x k => ‖e (x⁻¹ * k) - e (u⁻¹ * k)‖ < 1 / 2) fun k _ => ?_
    have hc : Continuous fun p : G × G => ‖e (p.1⁻¹ * p.2) - e (u⁻¹ * p.2)‖ := by fun_prop
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨t, ht, hcov⟩ := hU.elim_nhds_subcover _ h1
  refine ⟨t, ht, fun F hF hfix h0 => ?_⟩
  have hrep : ∀ u ∈ U, F u = ∫ k, e (u⁻¹ * k) * F k ∂ν := by
    intro u hu
    rw [← hfix u]
    conv_rhs => rw [← (hinv u hu).map_eq]
    rw [integral_map (hinv u hu).measurable.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp
  obtain ⟨x, hx, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hF.norm.continuousOn
  have hx0 : ‖F x‖ ≤ 1 / 2 * ‖F x‖ := by
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (hcov hx)
    have e1 : F x = ∫ k, (e (x⁻¹ * k) - e (u⁻¹ * k)) * F k ∂ν := by
      simp only [sub_mul]
      rw [integral_sub (integ hU hs (by fun_prop)) (integ hU hs (by fun_prop)), ← hrep x hx, ← hrep u (ht u hu), h0 u hu,
        sub_zero]
    have e2 := norm_integral_le_of_norm_le_const (μ := ν) (f := fun k => (e (x⁻¹ * k) - e (u⁻¹ * k)) * F k)
      (C := 1 / 2 * ‖F x‖) (by
        filter_upwards [hs] with k hk
        rw [norm_mul]
        exact mul_le_mul (hxu k hk).le (hmax hk) (norm_nonneg _) (by norm_num))
    rw [← e1] at e2
    simpa using e2
  intro y hy
  have : ‖F y‖ ≤ ‖F x‖ := hmax hy
  have := norm_nonneg (F x)
  exact norm_le_zero_iff.1 (by linarith)

end General

private theorem leftRight {H : Type} [Group H] (V : Submodule ℂ (H → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ a ∈ V, ∀ g, (fun x => a (g * x)) ∈ V) :
    FiniteDimensional ℂ (Submodule.span ℂ {b : H → ℂ | ∃ a ∈ V, ∃ u, b = fun x => a (x * u)}) := by
  classical
  let B := Module.finBasis ℂ V
  let L : H → V →ₗ[ℂ] V := fun g =>
    { toFun := fun a => ⟨fun x => (a : H → ℂ) (g * x), hV a a.2 g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let c : Fin (Module.finrank ℂ V) × Fin (Module.finrank ℂ V) → H → ℂ := fun p x => B.repr (L x (B p.2)) p.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨a, ha, u, rfl⟩
  have key : (fun x => a (x * u)) = ∑ p : Fin (Module.finrank ℂ V) × Fin (Module.finrank ℂ V),
      (B.repr ⟨a, ha⟩ p.2 * (B p.1 : H → ℂ) u) • c p := by
    funext x
    have h1 : a (x * u) = (L x ⟨a, ha⟩ : H → ℂ) u := rfl
    have h2 : L x ⟨a, ha⟩ = ∑ i, ∑ j, (B.repr ⟨a, ha⟩ j * c (i, j) x) • B i := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← B.sum_repr ⟨a, ha⟩, map_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      conv_lhs => rw [← B.sum_repr (L x (B j))]
      rw [Finset.smul_sum]
      simp only [smul_smul, c]
    rw [h1, h2, Fintype.sum_prod_type]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [SetLike.mem_coe, key]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.typeFin :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n), IsCompact (D.U : Set (G1 K n)) ∧ D.U ≤ KG K n ∧ ∃ 𝒜 : Submodule ℂ (D.U → ℂ), FiniteDimensional ℂ 𝒜 ∧
      (∀ a ∈ 𝒜, Continuous a ∧ ∀ u : D.U, (fun x => a (x * u)) ∈ 𝒜) ∧
      ∀ f : G1 K n → ℂ, Continuous f → D.Fix f → ∀ g, (fun u : D.U => f (g * u)) ∈ 𝒜 := by
  intro K _ _ n D
  obtain ⟨O, hO, hUO⟩ := D.isOpen
  have hle : D.U ≤ KG K n := fun g hg => ((hUO g).1 hg).2
  have hK : IsCompact (KG K n : Set (G1 K n)) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  have hU : IsCompact (D.U : Set (G1 K n)) := by
    haveI : CompactSpace (KG K n) := isCompact_iff_compactSpace.1 hK
    have hop : IsOpen ((D.U.subgroupOf (KG K n) : Subgroup (KG K n)) : Set (KG K n)) := by
      have : ((D.U.subgroupOf (KG K n) : Subgroup (KG K n)) : Set (KG K n)) =
          (fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n)) ⁻¹' O := by
        ext k
        exact ⟨fun h => ((hUO k).1 h).1, fun h => (hUO k).2 ⟨h, k.2⟩⟩
      rw [this]
      exact hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
    have := ((Subgroup.isClosed_of_isOpen _ hop).isCompact).image continuous_subtype_val
    convert this using 1
    ext g
    exact ⟨fun h => ⟨⟨g, hle h⟩, h, rfl⟩, by rintro ⟨k, hk, rfl⟩; exact hk⟩
  refine ⟨hU, hle, ?_⟩
  haveI := D.prob
  let V : Submodule ℂ (D.U → ℂ) := (fixSub hU D.ν D.supp D.cont).map (LinearMap.funLeft ℂ ℂ (Subtype.val : D.U → G1 K n))
  have hmem : ∀ f : G1 K n → ℂ, Continuous f → D.Fix f → ∀ g, (fun u : D.U => f (g * u)) ∈ V := by
    intro f hf hfix g
    refine ⟨fun x => f (g * x), ⟨by fun_prop, fun y => ?_⟩, rfl⟩
    simp only [← mul_assoc]
    exact hfix (g * y)
  haveI : FiniteDimensional ℂ V := by
    obtain ⟨t, ht, h⟩ := detect D.U hU D.ν D.supp D.inv D.cont
    let ev : V →ₗ[ℂ] (t → ℂ) := (LinearMap.funLeft ℂ ℂ (fun x : t => (⟨x, ht x x.2⟩ : D.U))).comp V.subtype
    refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero _).2 ?_)
    rintro ⟨_, F, ⟨hF, hfix⟩, rfl⟩ h0
    apply Subtype.ext
    funext u
    exact h F hF hfix (fun x hx => congrFun h0 ⟨x, hx⟩) u u.2
  refine ⟨_, leftRight V ?_, fun a ha => ?_, fun f hf hfix g => Submodule.subset_span ⟨_, hmem f hf hfix g, 1, by simp⟩⟩
  · rintro _ ⟨F, ⟨hF, hfix⟩, rfl⟩ g
    exact hmem F hF hfix g
  · induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨_, ⟨F, ⟨hF, hfix⟩, rfl⟩, u, rfl⟩ := hb
      refine ⟨?_, fun w => Submodule.subset_span ⟨_, ⟨F, ⟨hF, hfix⟩, rfl⟩, w * u, by simp only [mul_assoc]⟩⟩
      exact hF.comp (continuous_subtype_val.comp (continuous_id.mul continuous_const))
    | zero => exact ⟨continuous_const, fun _ => Submodule.zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨ha.1.add hb.1, fun u => Submodule.add_mem _ (ha.2 u) (hb.2 u)⟩
    | smul c a _ ha => exact ⟨ha.1.const_smul c, fun u => Submodule.smul_mem _ c (ha.2 u)⟩
end
