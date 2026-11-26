module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicPairReducedBasis
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHom
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHom
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbHom

variable {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
  [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A)

theorem res_one' : res b (1 : Matrix κ κ A) = 1 := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases h : i = j
  · subst h
    simp [res, Matrix.one_apply]
  · simp [res, Matrix.one_apply, h]

omit [DecidableEq κ] in
theorem res_mul' (g h : Matrix κ κ A) : res b (g * h) = res b g * res b h := by
  ext ⟨i, x⟩ ⟨j, y⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

omit [Fintype κ] [DecidableEq κ] in
theorem res_inj' (g h : Matrix κ κ A) (e : res b g = res b h) : g = h := by
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext x y
  exact congrFun (congrFun e (i, x)) (j, y)

theorem emb_one' : emb b (1 : GL κ A) = 1 := by
  unfold emb
  rw [inv_one, Units.val_one, res_one', Matrix.det_one, ← Matrix.fromBlocks_one]
  congr 1

theorem emb_mul' (g h : GL κ A) : emb b (g * h) = emb b g * emb b h := by
  unfold emb
  rw [Matrix.fromBlocks_multiply, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, res_mul', res_mul',
    Matrix.det_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  simp [Matrix.mul_apply, mul_comm]

theorem emb_det' (g : GL κ A) : (emb b g).det = 1 := by
  unfold emb
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (n := Unit), Matrix.of_apply, ← Matrix.det_mul, ← res_mul',
    Units.mul_inv, res_one', Matrix.det_one]

theorem emb_adjugate' (g : GL κ A) : (emb b g).adjugate = emb b g⁻¹ := by
  have h1 : emb b g * emb b g⁻¹ = 1 := by rw [← emb_mul', mul_inv_cancel, emb_one']
  calc (emb b g).adjugate = (emb b g).adjugate * (emb b g * emb b g⁻¹) := by rw [h1, Matrix.mul_one]
    _ = emb b g⁻¹ := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, emb_det', one_smul, Matrix.one_mul]

theorem emb_injective' : Function.Injective (fun g : GL κ A => emb b g) := by
  intro g h e
  apply Units.ext
  apply res_inj' b
  exact (Matrix.fromBlocks_inj.mp e).1

theorem emb_hom : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), emb b (1 : GL κ A) = 1 ∧ (∀ g h : GL κ A, emb b (g * h) = emb b g * emb b h) ∧ (∀ g : GL κ A, (emb b g).det = 1 ∧ (emb b g).adjugate = emb b g⁻¹) ∧ Function.Injective (fun g : GL κ A => emb b g) := by
  intro R A β κ _ _ _ _ _ _ _ b
  exact ⟨emb_one' b, emb_mul' b, fun g => ⟨emb_det' b g, emb_adjugate' b g⟩, emb_injective' b⟩

end GlobalTheory.ClassFin.EmbHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHomStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), emb b (1 : GL κ A) = 1 ∧ (∀ g h : GL κ A, emb b (g * h) = emb b g * emb b h) ∧ (∀ g : GL κ A, (emb b g).det = 1 ∧ (emb b g).adjugate = emb b g⁻¹) ∧ Function.Injective (fun g : GL κ A => emb b g) := by
  first | exact @GlobalTheory.ClassFin.EmbHom.emb_hom | exact GlobalTheory.ClassFin.EmbHom.emb_hom | (intros; apply GlobalTheory.ClassFin.EmbHom.emb_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGL
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQGroupWeilRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalEquationsWeilRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalCoordPolynomialBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalCoordPolynomialBaseChange
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem repr_algebraMap_of_basis_eq {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (a : F) (k : β) :
    b.repr (algebraMap F A a) k = algebraMap ℚ R (ω.repr a k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) :=
    fun q => DFunLike.congr_fun (RingHom.ext_rat ((algebraMap F A).comp (algebraMap ℚ F))
      ((algebraMap R A).comp (algebraMap ℚ R))) q
  have hsum : algebraMap F A a = ∑ i, algebraMap ℚ R (ω.repr a i) • b i := by
    conv_lhs => rw [← ω.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def (ω.repr a i) (ω i), map_mul, hq, hb,
      Algebra.smul_def (algebraMap ℚ R (ω.repr a i))]
  rw [hsum, b.repr_sum_self]

private theorem basis_repr_mul_of_basis_eq_algebraMap {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (u v : A)
    (k : β) : b.repr (u * v) k =
      ∑ i, ∑ j, b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
  have e : ∀ i j, b.repr ((b.repr u i • b i) * (b.repr v j • b j)) k
      = b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
    intro i j
    rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, hb i, hb j, ← map_mul,
      repr_algebraMap_of_basis_eq ω b hb]
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, e]
  exact Finset.sum_comm

theorem exists_coord_polynomial : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  intro F β _ _ _ _ ω τ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨fun k => MvPolynomial.C (ω.repr a k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, repr_algebraMap_of_basis_eq ω b hb]
  | add p q hp hq =>
    obtain ⟨Q1, h1⟩ := hp
    obtain ⟨Q2, h2⟩ := hq
    refine ⟨fun k => Q1 k + Q2 k, ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, map_add (f := _), h1 R A b hb x k, h2 R A b hb x k]
  | mul_X p n hp =>
    obtain ⟨Q1, h1⟩ := hp
    refine ⟨fun k => ∑ i, ∑ j, Q1 i * MvPolynomial.X (n, j) *
      MvPolynomial.C (ω.repr (ω i * ω j) k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_mul, MvPolynomial.aeval_X, basis_repr_mul_of_basis_eq_algebraMap ω b hb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, h1 R A b hb x]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalCoordPolynomialBaseChangeStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_coord_polynomial_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  first | exact @GlobalTheory.ClassFin.exists_coord_polynomial | exact GlobalTheory.ClassFin.exists_coord_polynomial | (intros; apply GlobalTheory.ClassFin.exists_coord_polynomial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RestrictScalarsMatrixOfBasisHomInjectiveIsUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RestrictScalarsMatrixOfBasisHomInjectiveIsUnit
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem res_mulVec_repr {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] (b : Module.Basis β R A) (g : Matrix κ κ A) (v : κ → A) :
    res b g *ᵥ (fun p : κ × β => b.repr (v p.1) p.2) = fun p : κ × β => b.repr ((g *ᵥ v) p.1) p.2 := by
  funext p
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, res, Matrix.of_apply, Fintype.sum_prod_type, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b (g p.1 j) (v j)) p.2
  simpa [Matrix.mulVec, dotProduct] using h

theorem res_one_mul_injective_isUnit :
    ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), res b (1 : Matrix κ κ A) = 1 ∧ (∀ g h : Matrix κ κ A, res b (g * h) = res b g * res b h) ∧ Function.Injective (fun g : Matrix κ κ A => res b g) ∧ ∀ g : Matrix κ κ A, IsUnit (res b g).det → IsUnit g := by
  intro R A β κ _ _ _ _ _ _ _ b
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨i, k⟩ ⟨j, l⟩
    by_cases h : i = j
    · subst h
      simp [res, Matrix.one_apply]
    · simp [res, Matrix.one_apply, h]
  · intro g h
    ext ⟨i, k⟩ ⟨j, l⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [res, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, map_sum, map_mul,
      Matrix.sum_apply]
  · intro g h hgh
    ext i j
    apply Algebra.leftMulMatrix_injective b
    ext k l
    exact congrFun (congrFun hgh (i, k)) (j, l)
  · intro g hg
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro w
    have hs : Function.Surjective (res b g).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hg)
    obtain ⟨u, hu⟩ := hs (fun p : κ × β => b.repr (w p.1) p.2)
    refine ⟨fun i => b.equivFun.symm (fun k => u (i, k)), ?_⟩
    have h := res_mulVec_repr b g (fun i => b.equivFun.symm (fun k => u (i, k)))
    have hu' : (fun p : κ × β => b.repr (b.equivFun.symm (fun k => u (p.1, k))) p.2) = u := by
      funext p
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hu', hu] at h
    funext i
    apply b.repr.injective
    ext k
    exact (congrFun h (i, k)).symm

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RestrictScalarsMatrixOfBasisHomInjectiveIsUnitStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictScalarsMatrixOfBasis_hom_injective_isUnit : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), res b (1 : Matrix κ κ A) = 1 ∧ (∀ g h : Matrix κ κ A, res b (g * h) = res b g * res b h) ∧ Function.Injective (fun g : Matrix κ κ A => res b g) ∧ ∀ g : Matrix κ κ A, IsUnit (res b g).det → IsUnit g := by
  first | exact @GlobalTheory.ClassFin.res_one_mul_injective_isUnit | exact GlobalTheory.ClassFin.res_one_mul_injective_isUnit | (intros; apply GlobalTheory.ClassFin.res_one_mul_injective_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordsLeftMulMatrixConstBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordsLeftMulMatrixConstBaseChange
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem repr_algebraMap_of_basis_image (F β : Type) [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) := by
    intro q
    have h : (algebraMap F A).comp (algebraMap ℚ F) = (algebraMap R A).comp (algebraMap ℚ R) :=
      RingHom.ext_rat _ _
    exact RingHom.congr_fun h q
  have hx : algebraMap F A x = ∑ j, algebraMap ℚ R (ω.repr x j) • b j := by
    conv_lhs => rw [← ω.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, hq, hb, Algebra.smul_def]
  rw [hx, b.repr_sum_self]

theorem coords_const_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ x : F, (∀ k, b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k)) ∧ Algebra.leftMulMatrix b (algebraMap F A x) = (Algebra.leftMulMatrix ω x).map (algebraMap ℚ R) := by
  intro F β _ _ _ _ ω R A _ _ _ _ _ b hb x
  refine ⟨repr_algebraMap_of_basis_image F β ω R A b hb x, ?_⟩
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    hb j, ← map_mul, repr_algebraMap_of_basis_image F β ω R A b hb]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordsLeftMulMatrixConstBaseChangeStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_leftMulMatrix_const_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ x : F, (∀ k, b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k)) ∧ Algebra.leftMulMatrix b (algebraMap F A x) = (Algebra.leftMulMatrix ω x).map (algebraMap ℚ R) := by
  first | exact @GlobalTheory.ClassFin.coords_const_baseChange | exact GlobalTheory.ClassFin.coords_const_baseChange | (intros; apply GlobalTheory.ClassFin.coords_const_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalEquationsWeilRestriction
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.WeilEqs

noncomputable def coordOf {κ β R : Type} [Fintype β] [CommRing R] [Algebra ℚ R] (c : β → ℚ)
    (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) : R :=
  ∑ l, y (Sum.inl (i, k)) (Sum.inl (j, l)) * algebraMap ℚ R (c l)

noncomputable def gen (ι : Type) : Matrix ι ι (MvPolynomial (ι × ι) ℚ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

section
variable {κ β R : Type} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] [CommRing R] [Algebra ℚ R]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_coordOf (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (coordOf c (gen ((κ × β) ⊕ Unit)) i j k) = coordOf c y i j k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordOf, gen, map_sum, map_mul, Matrix.of_apply, MvPolynomial.aeval_X, AlgHom.commutes]

theorem aeval_det (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      ((gen ((κ × β) ⊕ Unit)).toBlocks₁₁.det) = y.toBlocks₁₁.det := by
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp [gen, Matrix.toBlocks₁₁]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_comp_coord (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R)
    (Q : MvPolynomial ((κ × κ) × β) ℚ) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c (gen ((κ × β) ⊕ Unit)) p.1.1 p.1.2 p.2) Q) =
      MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c y p.1.1 p.1.2 p.2) Q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp only [aeval_coordOf]

variable {A : Type} [CommRing A] [Algebra R A]

theorem sum_leftMul_one (b : Module.Basis β R A) (x : A) (k : β) :
    ∑ l, Algebra.leftMulMatrix b x k l * b.repr 1 l = b.repr x k := by
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b x 1) k
  simpa [Matrix.mulVec, dotProduct] using h

theorem leftMul_expand (b : Module.Basis β R A) (x : A) (k l : β) :
    Algebra.leftMulMatrix b x k l = ∑ m, b.repr x m * Algebra.leftMulMatrix b (b m) k l := by
  conv_lhs => rw [← b.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end

theorem exists_equations : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), ∃ S' : Set (MvPolynomial (((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit)) ℚ), ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ y : Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) R, (∀ f ∈ S', ev f y = 0) ↔ ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0) ∧ y = emb b g := by
  intro F β _ _ _ _ ω n S
  choose Q hQ using fun P : MvPolynomial (Fin n × Fin n) F => GlobalTheory.T.exists_rational_coord_polynomial_baseChange F β ω (Fin n × Fin n) P
  let c : β → ℚ := fun l => ω.repr 1 l
  let X := gen ((Fin n × β) ⊕ Unit)
  refine ⟨{f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ?_⟩
  intro R A _ _ _ _ _ b hb y
  have hm := GlobalTheory.T.coords_leftMulMatrix_const_baseChange F β ω R A b hb
  obtain ⟨h1, hmul, -, hunit⟩ := GlobalTheory.T.restrictScalarsMatrixOfBasis_hom_injective_isUnit R A β (Fin n) b
  have hc : ∀ l, algebraMap ℚ R (c l) = b.repr 1 l := fun l => by
    have := (hm 1).1 l
    rw [map_one] at this
    exact this.symm
  have hL : ∀ m k l, algebraMap ℚ R (Algebra.leftMulMatrix ω (ω m) k l) =
      Algebra.leftMulMatrix b (b m) k l := fun m k l => by
    rw [hb m, (hm (ω m)).2, Matrix.map_apply]
  have hX : ∀ p q, MvPolynomial.aeval
      (fun ij : ((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit) => y ij.1 ij.2) (X p q) = y p q := fun p q => by
    simp [X, gen]
  have hinv : ∀ g : GL (Fin n) A, (res b (g : Matrix (Fin n) (Fin n) A)).det *
      (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det = 1 := fun g => by
    rw [← Matrix.det_mul, ← hmul, Units.mul_inv, h1, Matrix.det_one]
  have key : (∀ f ∈ {f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ev f y = 0) ↔
      ((∀ p u, y (Sum.inl p) (Sum.inr u) = 0) ∧ (∀ p u, y (Sum.inr u) (Sum.inl p) = 0) ∧
       (∀ i j k l, y (Sum.inl (i, k)) (Sum.inl (j, l)) =
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l) ∧
       y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) = 1 ∧
       ∀ P ∈ S, ∀ k, MvPolynomial.aeval
          (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) = 0) := by
    have e3 : ∀ i j k l, ev (X (Sum.inl (i, k)) (Sum.inl (j, l)) -
        ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) y =
        y (Sum.inl (i, k)) (Sum.inl (j, l)) -
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l := fun i j k l => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ev, map_sub, map_sum, map_mul, hX, AlgHom.commutes, hL]
      simp only [X, aeval_coordOf]
    have e4 : ev (X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1) y =
        y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) - 1 := by
      simp only [ev, map_sub, map_mul, hX, map_one]
      simp only [X, aeval_det]
    have e5 : ∀ P k, ev (MvPolynomial.aeval
        (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)) y =
        MvPolynomial.aeval (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) :=
      fun P k => aeval_comp_coord c y (Q P k)
    have e1 : ∀ p q, ev (X p q) y = y p q := hX
    constructor
    · intro h
      refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
      · rw [← e1]; exact h _ (Or.inl ⟨p, u, rfl⟩)
      · rw [← e1]; exact h _ (Or.inr (Or.inl ⟨p, u, rfl⟩))
      · rw [← sub_eq_zero, ← e3]; exact h _ (Or.inr (Or.inr (Or.inl ⟨i, j, k, l, rfl⟩)))
      · rw [← sub_eq_zero, ← e4]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · rw [← e5]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨P, hP, k, rfl⟩))))
    · rintro ⟨a1, a2, a3, a4, a5⟩ f (⟨p, u, rfl⟩ | ⟨p, u, rfl⟩ | ⟨i, j, k, l, rfl⟩ | rfl | ⟨P, hP, k, rfl⟩)
      · rw [e1, a1]
      · rw [e1, a2]
      · rw [e3, ← a3, sub_self]
      · rw [e4, a4, sub_self]
      · rw [e5, a5 P hP]
  rw [key]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5⟩
    let G : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => b.equivFun.symm (coordOf c y i j)
    have hG : ∀ i j k, b.repr (G i j) k = coordOf c y i j k := fun i j k => by
      have := congrFun (b.equivFun.apply_symm_apply (coordOf c y i j)) k
      rw [Module.Basis.equivFun_apply] at this
      exact this
    have hres : res b G = y.toBlocks₁₁ := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [res, Matrix.of_apply, Matrix.toBlocks₁₁]
      rw [a3, leftMul_expand]
      simp only [hG]
    have hu : IsUnit G := hunit G (by rw [hres]; exact IsUnit.of_mul_eq_one _ a4)
    obtain ⟨g, hg⟩ := hu
    refine ⟨g, fun P hP => ?_, ?_⟩
    · apply b.repr.injective
      ext k
      rw [hQ P R A b hb, hg]
      simp only [hG]
      simpa using a5 P hP k
    · have hi := hinv g
      rw [hg, hres] at hi
      have hcorner : y (Sum.inr ()) (Sum.inr ()) =
          (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by
        calc y (Sum.inr ()) (Sum.inr ()) = (y.toBlocks₁₁.det *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det) * y (Sum.inr ()) (Sum.inr ()) := by
              rw [hi, one_mul]
          _ = (y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ())) *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by ring
          _ = _ := by rw [a4, one_mul]
      ext (p | u) (q | v)
      · simp only [emb, Matrix.fromBlocks_apply₁₁, hg, hres, Matrix.toBlocks₁₁, Matrix.of_apply]
      · simp only [emb, Matrix.fromBlocks_apply₁₂, a1, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₁, a2, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
        exact hcorner
  · rintro ⟨g, hg, rfl⟩
    have hco : ∀ i j k, coordOf c (emb b g) i j k = b.repr ((g : Matrix (Fin n) (Fin n) A) i j) k :=
      fun i j k => by
        simp only [coordOf, emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply, hc]
        exact sum_leftMul_one b _ k
    refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
    · simp [emb]
    · simp [emb]
    · simp only [hco]
      rw [← leftMul_expand]
      simp only [emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply]
    · simp only [emb, Matrix.toBlocks_fromBlocks₁₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      exact hinv g
    · simp only [hco]
      rw [← hQ P R A b hb (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) k, hg P hP]
      simp

end GlobalTheory.ClassFin.WeilEqs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalEquationsWeilRestrictionStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_equations_weil_restriction : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), ∃ S' : Set (MvPolynomial (((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit)) ℚ), ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ y : Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) R, (∀ f ∈ S', ev f y = 0) ↔ ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0) ∧ y = emb b g := by
  first | exact @GlobalTheory.ClassFin.WeilEqs.exists_equations | exact GlobalTheory.ClassFin.WeilEqs.exists_equations | (intros; apply GlobalTheory.ClassFin.WeilEqs.exists_equations <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRatZariskiClosurePointsIffOfIsReduced
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRatZariskiClosurePointsIffOfIsReduced
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mem_pts_zeroSet_of_isReduced :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R]
      [Algebra ℚ R] (y : Matrix ι ι R),
      (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧
      (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  intro ι _ _ S' R _ _ y
  refine ⟨fun hy f hf => hy f (fun g hg => hg f hf), fun hR hy f hf => ?_⟩
  have hrad : f ∈ (Ideal.span S').radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hx' := MvPolynomial.mem_zeroLocus_iff.1 hx
    exact hf (Matrix.of fun i j => x (i, j)) (fun p hp => hx' p (Ideal.subset_span hp))
  obtain ⟨n, hn⟩ := hrad
  have hle : Ideal.span S' ≤
      RingHom.ker (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => y ij.1 ij.2)) :=
    Ideal.span_le.2 fun p hp => hy p hp
  have h0 := hle hn
  rw [RingHom.mem_ker, map_pow] at h0
  exact IsReduced.eq_zero _ ⟨n, h0⟩

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRatZariskiClosurePointsIffOfIsReducedStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R), (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧ (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  first | exact @GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced | exact GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced | (intros; apply GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQGroupWeilRestriction
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem ev_map_complexAut {ι : Type} (f : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι ℂ) (σ : ℂ ≃+* ℂ) : ev f (g.map σ) = σ (ev f g) := by
  unfold ev
  have h := MvPolynomial.comp_aeval (f := fun ij : ι × ι => g ij.1 ij.2) (σ.toRingHom.toRatAlgHom)
  have h2 := DFunLike.congr_fun h f
  simp only [AlgHom.comp_apply, RingHom.toRatAlgHom_apply] at h2
  exact h2.symm

theorem exists_isQGroup_weilRestriction : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ Γ : Set (Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) ℂ), IsQGroup Γ ∧ ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → (∀ y ∈ pts Γ R, ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) ∧ y = emb b g) ∧ (IsReduced R → ∀ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) → emb b g ∈ pts Γ R) := by
  intro F β _ _ _ _ ω n S hS
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_rational_equations_weil_restriction F β ω n S
  letI : Algebra F (ℂ ⊗[ℚ] F) := Algebra.TensorProduct.rightAlgebra
  have hb : ∀ i, Algebra.TensorProduct.basis ℂ ω i = algebraMap F (ℂ ⊗[ℚ] F) (ω i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have hC := hS' ℂ (ℂ ⊗[ℚ] F) (Algebra.TensorProduct.basis ℂ ω) hb
  obtain ⟨h1, hm, hi⟩ := hS (ℂ ⊗[ℚ] F)
  obtain ⟨e1, em, ed, -⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom ℂ (ℂ ⊗[ℚ] F) β (Fin n) (Algebra.TensorProduct.basis ℂ ω)
  refine ⟨{g | ∀ f ∈ S', ev f g = 0}, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact (hC 1).2 ⟨1, h1, e1.symm⟩
  · intro g hg h hh
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    obtain ⟨h', hh', rfl⟩ := (hC h).1 hh
    exact (hC _).2 ⟨g' * h', hm g' h' hg' hh', (em g' h').symm⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (hC _).2 ⟨g'⁻¹, hi g' hg', (ed g').2⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (ed g').1
  · intro σ g hg f hf
    rw [ev_map_complexAut, hg f hf, map_zero]
  · intro y hy
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' ℂ y).1 hy
  · intro R A _ _ _ _ _ b hbb
    refine ⟨fun y hy => (hS' R A b hbb y).1 ((GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R y).1 hy), fun hR g hg => ?_⟩
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R _).2 hR ((hS' R A b hbb _).2 ⟨g, hg, rfl⟩)

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQGroupWeilRestrictionStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isQGroup_weilRestriction_alt : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ Γ : Set (Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) ℂ), IsQGroup Γ ∧ ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → (∀ y ∈ pts Γ R, ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) ∧ y = emb b g) ∧ (IsReduced R → ∀ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) → emb b g ∈ pts Γ R) := by
  first | exact @GlobalTheory.ClassFin.exists_isQGroup_weilRestriction | exact GlobalTheory.ClassFin.exists_isQGroup_weilRestriction | (intros; apply GlobalTheory.ClassFin.exists_isQGroup_weilRestriction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraEmbIntegralAndRational
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraEmbIntegralAndRational
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbInt

theorem res_mul' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (g h : Matrix κ κ A) :
    res b (g * h) = res b g * res b h := by
  ext p q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

theorem res_one' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) :
    res b (1 : Matrix κ κ A) = 1 := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.one_apply]
  by_cases h : p.1 = q.1
  · rw [if_pos h, map_one, Matrix.one_apply]
    by_cases h' : p.2 = q.2
    · rw [if_pos h', if_pos (Prod.ext h h')]
    · rw [if_neg h', if_neg (fun e => h' (congrArg Prod.snd e))]
  · rw [if_neg h, map_zero, Matrix.zero_apply, if_neg (fun e => h (congrArg Prod.fst e))]

theorem repr_mem {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    (b : Module.Basis β R A) (R₀ : Subring R) (h1 : ∀ i, b.repr 1 i ∈ R₀) (x : A)
    (hx : ∀ p q, Algebra.leftMulMatrix b x p q ∈ R₀) (k : β) : b.repr x k ∈ R₀ := by

  have hsum : x = ∑ i, b.repr 1 i • (x * b i) := by
    conv_lhs => rw [← mul_one x, ← b.sum_repr 1]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
  have hk : b.repr x k = ∑ i, b.repr 1 i * Algebra.leftMulMatrix b x k i := by
    conv_lhs => rw [hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hk]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h1 i) (hx k i)

theorem inv_mem {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (R₀ : Subring R)
    (M N : Matrix ι ι R) (hNM : N * M = 1) (hM : ∀ p q, M p q ∈ R₀) (hd : N.det ∈ R₀) (p q : ι) :
    N p q ∈ R₀ := by

  have hadj : N = N.det • M.adjugate := by
    have h1 : N * M * M.adjugate = M.adjugate := by rw [hNM, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h1
    have hd1 : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
    rw [← h1, smul_smul, hd1, one_smul]

  let M' : Matrix ι ι R₀ := Matrix.of fun p q => ⟨M p q, hM p q⟩
  have hM' : R₀.subtype.mapMatrix M' = M := by ext; rfl
  have hA : M.adjugate p q = R₀.subtype (M'.adjugate p q) := by
    rw [← hM', ← RingHom.map_adjugate]; rfl
  rw [hadj, Matrix.smul_apply, smul_eq_mul, hA]
  exact Subring.mul_mem _ hd (M'.adjugate p q).2

theorem repr_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by

  have hq : ∀ c : ℚ, algebraMap R A (algebraMap ℚ R c) = algebraMap F A (algebraMap ℚ F c) := fun c =>
    DFunLike.congr_fun (RingHom.ext_rat ((algebraMap R A).comp (algebraMap ℚ R))
      ((algebraMap F A).comp (algebraMap ℚ F))) c
  have hx : algebraMap F A x = ∑ i, algebraMap ℚ R (ω.repr x i) • b i := by
    conv_lhs => rw [← ω.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hq, hb]
  rw [hx, Module.Basis.repr_sum_self]

theorem res_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {κ R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (g : Matrix κ κ F) :
    res b (g.map (algebraMap F A)) = (res ω g).map (algebraMap ℚ R) := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, hb,
    ← map_mul]
  exact repr_map ω b hb _ _

theorem emb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  refine ⟨fun R A β κ _ _ _ _ _ _ _ b R₀ u h1 he i j k => ?_,
    fun F β _ _ _ _ ω κ _ _ R A _ _ _ _ _ b hb γ => ?_⟩
  ·

    have hres : ∀ p q, res b (u : Matrix κ κ A) p q ∈ R₀ := fun p q => by
      simpa [emb] using he (Sum.inl p) (Sum.inl q)
    have hdet : (res b ((u⁻¹ : GL κ A) : Matrix κ κ A)).det ∈ R₀ := by
      simpa [emb] using he (Sum.inr ()) (Sum.inr ())
    have hinv : res b ((u⁻¹ : GL κ A) : Matrix κ κ A) * res b (u : Matrix κ κ A) = 1 := by
      rw [← res_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, res_one']
    have hres' : ∀ p q, res b ((u⁻¹ : GL κ A) : Matrix κ κ A) p q ∈ R₀ :=
      fun p q => inv_mem R₀ _ _ hinv hres hdet p q
    exact ⟨repr_mem b R₀ h1 _ (fun p q => hres (i, p) (j, q)) k,
      repr_mem b R₀ h1 _ (fun p q => hres' (i, p) (j, q)) k⟩
  · have hc : ((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ : GL κ A) :
        Matrix κ κ A) = (γ : Matrix κ κ F).map (algebraMap F A) := rfl
    have hc' : (((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ)⁻¹ : GL κ A) :
        Matrix κ κ A) = ((γ⁻¹ : GL κ F) : Matrix κ κ F).map (algebraMap F A) := by
      rw [← map_inv]; rfl
    unfold emb
    rw [hc, hc', res_map ω b hb, res_map ω b hb, Matrix.fromBlocks_map]
    ext (x | x) (y | y) <;> simp [RingHom.map_det]

end GlobalTheory.ClassFin.EmbInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraEmbIntegralAndRationalStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  first | exact @GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational | exact GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational | (intros; apply GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGL
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem classFinite_integralLevel : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  intro F _ _ n S hS
  classical

  obtain ⟨R, _, _, R₀, _, b, hAP, hred, hb, hint⟩ :=
    GlobalTheory.T.adelic_pair_reduced_basis F _ (NumberField.RingOfIntegers.basis F)
  obtain ⟨Γ, hΓ, hcorr⟩ := GlobalTheory.T.exists_isQGroup_weilRestriction_alt F _ (NumberField.integralBasis F) n S hS
  have hbF : ∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (NumberField.integralBasis F i) := by
    intro i
    rw [hb i, NumberField.integralBasis_apply]
  have hA := hcorr R (FiniteAdeleRing (𝓞 F) F) b hbF
  have hQ := hcorr ℚ F (NumberField.integralBasis F) (fun i => rfl)
  obtain ⟨T₀, hT₀, hdec⟩ := GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup _ Γ R R₀ hΓ hAP

  let lift : Matrix ((Fin n × _) ⊕ Unit) ((Fin n × _) ⊕ Unit) R → GL (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
    fun s => if h : ∃ g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F),
        (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
          ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
        s = GlobalTheory.ClassFin.emb b g then h.choose else 1
  have hlift : ∀ s ∈ pts Γ R, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
      ((lift s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
      s = GlobalTheory.ClassFin.emb b (lift s) := by
    intro s hs
    have h := hA.1 s hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hemb1, hembmul, -, hembinj⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom R (FiniteAdeleRing (𝓞 F) F) _ (Fin n) b
  refine ⟨T₀.image lift, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact (hlift s (hT₀ s hs)).1
  · intro x hx
    obtain ⟨γ₀, hγ₀, s, hs, u₀, hu₀, hu₀int, hx₀⟩ := hdec _ (hA.2 hred x hx)
    obtain ⟨γ, hγS, rfl⟩ := hQ.1 γ₀ hγ₀
    obtain ⟨u, huS, rfl⟩ := hA.1 u₀ hu₀
    obtain ⟨hsS, hsemb⟩ := hlift s (hT₀ s hs)
    have h1 : ∀ i, b.repr 1 i ∈ R₀ := by
      refine (hint 1).1 ?_
      intro v
      exact (HeightOneSpectrum.adicCompletionIntegers F v).one_mem
    have hunits := GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.1 R _ _ (Fin n) b R₀ u h1 hu₀int
    refine ⟨γ, hγS, lift s, Finset.mem_image_of_mem lift hs, u, huS, ?_, ?_⟩
    · intro i j
      exact ⟨(hint _).2 (fun k => (hunits i j k).1), (hint _).2 (fun k => (hunits i j k).2)⟩
    · apply hembinj
      simp only [hembmul]
      rw [hx₀, ← hsemb, GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.2 F _ (NumberField.integralBasis F) (Fin n) R _ b hbF γ]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGLStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  first | exact @GlobalTheory.ClassFin.classFinite_integralLevel | exact GlobalTheory.ClassFin.classFinite_integralLevel | (intros; apply GlobalTheory.ClassFin.classFinite_integralLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompactIntegralPointsFiniteAdelicAlgebraicGrou
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompactIntegralPointsFiniteAdelicAlgebraicGrou
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralPointsCompact

theorem continuous_aeval_family {F A X σ : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X] (f : X → σ → A)
    (hf : ∀ s, Continuous fun x => f x s) (P : MvPolynomial σ F) :
    Continuous fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hf s)

theorem isClosed_of_equations {F A ι : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Fintype ι] [DecidableEq ι]
    (S : Set (MvPolynomial (ι × ι) F)) (H : Subgroup (GL ι A))
    (hH : ∀ g, g ∈ H ↔ ∀ P ∈ S, MvPolynomial.aeval
      (fun ij : ι × ι => ((g : GL ι A) : Matrix ι ι A) ij.1 ij.2) P = 0) :
    IsClosed (H : Set (GL ι A)) := by
  have e : (H : Set (GL ι A)) = ⋂ P ∈ S, {g : GL ι A | MvPolynomial.aeval
      (fun ij : ι × ι => (g : Matrix ι ι A) ij.1 ij.2) P = 0} := by
    ext g
    simp only [Set.mem_iInter, SetLike.mem_coe]
    exact hH g
  rw [e]
  refine isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const
  exact continuous_aeval_family (fun (g : GL ι A) (ij : ι × ι) => (g : Matrix ι ι A) ij.1 ij.2)
    (fun s => Units.continuous_val.matrix_elem s.1 s.2) P

theorem isCompact_integral_points : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (H : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))), (∀ g, g ∈ H ↔ (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) → IsCompact {u : H | (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v))} := by
  intro F _ _ n S H hH
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  have hK := GlobalTheory.GLIntegral.isCompact_glSub (ι := Fin n) (GlobalTheory.GLIntegral.intSubring F)
    (GlobalTheory.AdeleCocompact.isCompact_integral F)
  have hc := isClosed_of_equations S H hH
  have h := hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  refine (congrArg IsCompact (Set.ext fun u => ?_)).mpr h
  exact ⟨fun hu => ⟨fun i j => (hu i j).1, fun i j => (hu i j).2⟩,
    fun hu i j => ⟨hu.1 i j, hu.2 i j⟩⟩

end GlobalTheory.IntegralPointsCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompactIntegralPointsFiniteAdelicAlgebraicGrouStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (H : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))), (∀ g, g ∈ H ↔ (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) → IsCompact {u : H | (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v))} := by
  first | exact @GlobalTheory.IntegralPointsCompact.isCompact_integral_points | exact GlobalTheory.IntegralPointsCompact.isCompact_integral_points | (intros; apply GlobalTheory.IntegralPointsCompact.isCompact_integral_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompactMeetsFinitelyManyLeftCosetsOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompactMeetsFinitelyManyLeftCosetsOpen
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem compact_subset_finite_leftCosets (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (K : Set G) (hU : IsOpen (U : Set G))
    (hK : IsCompact K) : ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, ∃ u ∈ U, k = t * u := by
  obtain ⟨T, -, hT⟩ := hK.elim_nhds_subcover (fun t : G => (fun k => t⁻¹ * k) ⁻¹' (U : Set G))
    (fun t _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨T, fun k hk => ?_⟩
  have := hT hk
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨t, ht, h⟩ := this
  exact ⟨t, ht, t⁻¹ * k, h, by simp⟩

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompactMeetsFinitelyManyLeftCosetsOpenStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_meets_finitely_many_leftCosets_open : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (K : Set G), IsOpen (U : Set G) → IsCompact K → ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, ∃ u ∈ U, k = t * u := by
  first | exact @GlobalTheory.ClassFin.compact_subset_finite_leftCosets | exact GlobalTheory.ClassFin.compact_subset_finite_leftCosets | (intros; apply GlobalTheory.ClassFin.compact_subset_finite_leftCosets <;> assumption)
end
end

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem classNumberFinite_holds : HeckeCharacterZeroLocus.ClassNumberFinite := by
  classical
  intro F _ _ n S hS U hUo _
  obtain ⟨T₀, hT₀, hx⟩ := GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL F n S (fun B _ _ =>
    ⟨(hS B).1, fun g h hg hh => (hS B).2.1 g hg h hh, fun g hg => (hS B).2.2 g hg⟩)
  have hK := GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup F n S (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))
    (fun g => Iff.rfl)
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.compact_meets_finitely_many_leftCosets_open _ U _ hUo hK
  refine ⟨Finset.image₂ (fun (s : T₀) (t : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) =>
    (⟨s.1, hT₀ s.1 s.2⟩ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) * t) T₀.attach T₁, ?_⟩
  intro x
  obtain ⟨γ, hγ, s, hs, k, hk, hki, hxe⟩ := hx x.1 x.2
  obtain ⟨t, ht, u, hu, hke⟩ := hT₁ ⟨k, hk⟩ hki
  refine ⟨γ, hγ, _, Finset.mem_image₂_of_mem (Finset.mem_attach T₀ ⟨s, hs⟩) ht, u, hu, ?_⟩
  have hke' : k = t.1 * u.1 := congrArg Subtype.val hke
  rw [hxe, hke']
  simp only [Subgroup.coe_mul, mul_assoc]

end GlobalTheory
