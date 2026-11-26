module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponents
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false

namespace GlobalTheory.DiagRowSubst

theorem diag_var (N : ℕ) (R : Type) [CommRing R] (d : Fin N → R) (v : Fin N × Fin N) :
    (∑ b : Fin N, C (Matrix.diagonal d v.1 b) * X (b, v.2) : MvPolynomial (Fin N × Fin N) R) = C (d v.1) * X v := by
  simp only [Matrix.diagonal_apply, apply_ite C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem weight_prod (N : ℕ) (R : Type) [CommRing R] (d : Fin N → R) (m : Fin N × Fin N →₀ ℕ) :
    ∏ a, d a ^ Finsupp.weight (rowW N N) m a = m.prod (fun v e => d v.1 ^ e) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [pow_ite, pow_zero]
  rw [Finset.prod_ite_eq' Finset.univ v.1]
  simp

theorem weight_le (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a ≤ m.sum (fun _ e => e) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_le_sum fun v _ => by split_ifs <;> omega

theorem mono (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R)
    (m : Fin N × Fin N →₀ ℕ) (c : O) :
    rowSubst O N R (Matrix.diagonal d) (monomial m c) =
      monomial m (algebraMap O R c * ∏ a, d a ^ Finsupp.weight (rowW N N) m a) := by
  rw [weight_prod, rowSubst, aeval_monomial]
  simp_rw [diag_var, mul_pow]
  rw [Finsupp.prod_mul, monomial_eq, map_mul, map_finsuppProd]
  simp only [map_pow, MvPolynomial.algebraMap_apply, mul_assoc]

theorem rowSubst_diagonal_eq_sum_components : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.diagonal d) f = ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (D + 1)), (∏ a, d a ^ w a) • MvPolynomial.map (algebraMap O R) (weightedHomogeneousComponent (rowW N N) w f) := by
  intro O _ N R _ _ d D f hf
  classical
  have hL : rowSubst O N R (Matrix.diagonal d) f = ∑ m ∈ f.support,
      monomial m (algebraMap O R (AddMonoidAlgebra.coeff f m) * ∏ a, d a ^ Finsupp.weight (rowW N N) m a) := by
    conv_lhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [mono]
  rw [hL]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [weightedHomogeneousComponent_apply, map_sum, map_monomial, Finset.smul_sum, smul_monomial, smul_eq_mul,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_ite_eq, if_pos, mul_comm]
  rw [Fintype.mem_piFinset]
  intro a
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact (weight_le N m a).trans ((le_totalDegree hm).trans hf)

end GlobalTheory.DiagRowSubst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponentsStatement
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_diagonal_eq_sum_components : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.diagonal d) f = ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (D + 1)), (∏ a, d a ^ w a) • MvPolynomial.map (algebraMap O R) (weightedHomogeneousComponent (rowW N N) w f) := by
  first | exact @GlobalTheory.DiagRowSubst.rowSubst_diagonal_eq_sum_components | exact GlobalTheory.DiagRowSubst.rowSubst_diagonal_eq_sum_components | (intros; apply GlobalTheory.DiagRowSubst.rowSubst_diagonal_eq_sum_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyTransvectionEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyTransvectionEqSum
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.RowSubstTransvection

theorem natDegree_rowGen_le (O : Type) [CommRing O] (N : ℕ) (a b : Fin N)
    (f : MvPolynomial (Fin N × Fin N) O) :
    (rowGen O (n := N) a b f).natDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [rowGen, aeval_monomial]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h0 : (algebraMap O (Polynomial (MvPolynomial (Fin N × Fin N) O)) (f.coeff m)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; exact Polynomial.natDegree_C _
  rw [h0, zero_add]
  have hg : ∀ v : Fin N × Fin N, (Polynomial.C (X v : MvPolynomial (Fin N × Fin N) O) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)).natDegree ≤ 1 := by
    intro v
    split_ifs
    · refine (Polynomial.natDegree_add_le _ _).trans ?_
      rw [Polynomial.natDegree_C]
      refine (Polynomial.natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_C]
      simpa using Polynomial.natDegree_X_le
    · simp
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum]
  apply Finset.sum_le_sum
  intro v _
  refine (Polynomial.natDegree_pow_le).trans ?_
  simpa using Nat.mul_le_mul_left (m v) (hg v)

theorem rowSubst_transvection (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f.totalDegree ≤ D) :
    rowSubst O N R (Matrix.transvection a b r) f = ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := by
  have key : (rowSubst O N R (Matrix.transvection a b r)).toRingHom =
      (Polynomial.evalRingHom (C r : MvPolynomial (Fin N × Fin N) R)).comp
        ((Polynomial.mapRingHom (MvPolynomial.map (σ := Fin N × Fin N) (algebraMap O R))).comp
          (rowGen O (n := N) b a).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowSubst, rowGen, MvPolynomial.algebraMap_eq]
    · intro v
      simp [rowSubst, rowGen, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        Finset.sum_add_distrib, add_mul, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
      by_cases h : v.1 = a
      · have h' : a = v.1 := h.symm
        simp only [h', true_and, if_true]
        simp [apply_ite C, ite_mul, Finset.sum_ite_eq']
        ring
      · have h' : ¬ a = v.1 := fun e => h e.symm
        simp [h, h']
  have h1 := DFunLike.congr_fun key f
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
    Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom] at h1
  rw [h1, Polynomial.eval_eq_sum_range' (n := D + 1)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.coeff_map, smul_eq_C_mul, C_pow, mul_comm]
    rfl
  · exact Nat.lt_succ_of_le ((Polynomial.natDegree_map_le).trans ((natDegree_rowGen_le O N b a f).trans hf))

end GlobalTheory.RowSubstTransvection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyTransvectionEqSumStatement
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_transvection_eq_sum : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.transvection a b r) f = ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := by
  first | exact @GlobalTheory.RowSubstTransvection.rowSubst_transvection | exact GlobalTheory.RowSubstTransvection.rowSubst_transvection | (intros; apply GlobalTheory.RowSubstTransvection.rowSubst_transvection <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIntegralInvariantHeisenbergFirstVars
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIntegralInvariantHeisenbergFirstVars
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagIntTransl

def liftFst {R : Type} [CommRing R] {κ : Type} (a : (κ → R) × (κ → R)) : (κ ⊕ κ → R) × (κ ⊕ κ → R) :=
  (Sum.elim a.1 0, Sum.elim a.2 0)

theorem liftFst_add {R : Type} [CommRing R] {κ : Type} (a b : (κ → R) × (κ → R)) :
    liftFst (a + b) = liftFst a + liftFst b := by
  simp only [liftFst, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

theorem liftFst_dot {R : Type} [CommRing R] {κ : Type} [Fintype κ] (a b : (κ → R) × (κ → R)) :
    (liftFst a).1 ⬝ᵥ (liftFst b).2 = a.1 ⬝ᵥ b.2 := by
  simp [liftFst, dotProduct, Fintype.sum_sum_type]

theorem boxFun_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : (κ → R) × (κ → R)) (φ₁ φ₂ : (κ → R) → ℂ) :
    boxFun (schr ψ a φ₁) φ₂ = schr ψ (liftFst a) (boxFun φ₁ φ₂) := by
  funext z
  simp only [boxFun, schr, liftFst, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    Pi.add_apply, Pi.zero_apply, mul_zero, add_zero, mul_assoc]
  have e1 : (z + Sum.elim a.1 0) ∘ Sum.inl = z ∘ Sum.inl + a.1 := by funext i; simp
  have e2 : (z + Sum.elim a.1 0) ∘ Sum.inr = z ∘ Sum.inr := by funext i; simp
  rw [e1, e2]
  simp

theorem diagW_schr (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ)
    (μ : @Measure (κ → Fv F v) (borel _)) (a w : (κ → Fv F v) × (κ → Fv F v)) (h : w.1 ⬝ᵥ a.2 = a.1 ⬝ᵥ w.2)
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) :
    diagW ψ μ (boxFun (schr ψ a φ₁) φ₂) w = diagW ψ μ (boxFun φ₁ φ₂) (w + a) := by
  unfold diagW
  rw [boxFun_schr]
  congr 1
  funext x
  have h' : (liftFst w).1 ⬝ᵥ (liftFst a).2 = (liftFst a).1 ⬝ᵥ (liftFst w).2 := by
    rw [liftFst_dot, liftFst_dot, h]
  have := GlobalTheory.MixXEvUniq.schr_add ψ (liftFst w) (liftFst a) h' (boxFun φ₁ φ₂)
  rw [← liftFst_add] at this
  rw [show ((Sum.elim (w + a).1 0, Sum.elim (w + a).2 0) : (κ ⊕ κ → Fv F v) × (κ ⊕ κ → Fv F v)) = liftFst (w + a) from rfl,
    this]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  intro F _ _ v κ _ ψ μ _ N ν hν j hj y₀ φ₁ φ₂
  unfold lagInt
  have h1 : ∀ y, diagW ψ μ (boxFun (schr ψ (j y₀) φ₁) φ₂) (j y) = diagW ψ μ (boxFun φ₁ φ₂) (j (y + y₀)) := fun y => by
    rw [diagW_schr F v κ ψ μ _ _ (hj y y₀), map_add (f := _)]
  simp only [h1]
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  exact integral_add_right_eq_self (μ := ν) (fun y => diagW ψ μ (boxFun φ₁ φ₂) (j y)) y₀

end GlobalTheory.LagIntTransl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIntegralInvariantHeisenbergFirstVarsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicIntegral_invariant_heisenberg_first_vars : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  first | exact @GlobalTheory.LagIntTransl.main | exact GlobalTheory.LagIntTransl.main | (intros; apply GlobalTheory.LagIntTransl.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTangentPointUniqueLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

section General

variable {R : Type} [CommRing R] (I : Ideal R)

theorem dualMap_mk_struct (e : ℕ) :
    spMap (algebraMap (R ⧸ I ^ (e + 1)) (DualNumber (R ⧸ I ^ (e + 1)))) ≫ thick R I e =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ (epsR R).hom := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => ?_)
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_factor_dualMap (e : ℕ) :
    ∃ l, l ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) =
      adicLevelι (I.map (algebraMap R (DualNumber R))) (e + 1) := by
  have hs : Function.Surjective (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) := fun x => by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective x.snd
    refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, TrivSqZeroExt.ext ?_ ?_⟩ <;> simp [dualMap, ha, hb]
  have hk : RingHom.ker (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≤
      RingHom.ker (Ideal.Quotient.mk ((I.map (algebraMap R (DualNumber R))) ^ (e + 1))) := fun x hx => by
    rw [RingHom.mem_ker] at hx
    have h1 : x.fst ∈ I ^ (e + 1) := by
      have := congrArg TrivSqZeroExt.fst hx
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [dualMap] using this
    have h2 : x.snd ∈ I ^ (e + 1) := by
      have := congrArg TrivSqZeroExt.snd hx
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [dualMap] using this
    have ex : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [Ideal.mk_ker, ← Ideal.map_pow, ex]
    exact add_mem (Ideal.mem_map_of_mem _ h1) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h2))
  refine ⟨spMap (RingHom.liftOfSurjective _ hs ⟨_, hk⟩), ?_⟩
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.liftOfSurjective_comp]

variable {I} [IsDomain R] {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem tanRel_iff_isPointOf (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) :
    TanRel U y gm ↔ FormalPoint.IsPointOf U gm y := by
  constructor
  · intro h
    refine (FormalPoint.isPointOf_iff_reduction U gm y).2 fun e => ?_
    obtain ⟨ye, h1, h2⟩ := h e
    obtain ⟨l, hl⟩ := exists_factor_dualMap I e
    have h3 : FormalPoint.HasCoords U e gm _ ye := h2
    have h4 := h3.comp l
    have h5 : FormalPoint.reduction I y e = l ≫ ye := by
      rw [← cancel_mono (fstG I e G).left, FormalPoint.reduction_fstG, Category.assoc, h1, ← hl]
      exact Category.assoc _ _ _
    rw [h5, ← hl]
    exact h4
  · intro h e
    obtain ⟨ye, hy⟩ := FormalPoint.exists_hasCoords U e gm _ _ (dualMap_mk_struct I e)
    exact ⟨ye, h.comp_fstG_eq hy, hy⟩

theorem isTangent_of_isPointOf [IsLocalRing R] [IsAdicComplete I R] {y : epsR R ⟶ G} {gm : GtPt D.toPre (epsR R)}
    (hg : GtTan gm) (h : FormalPoint.IsPointOf U gm y) : IsTangent y := by
  obtain ⟨o, ho, hp⟩ := hg
  let k : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) (by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
      RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
    rw [h3]
    exact Spec.map_id _)
  have h1 : k ≫ y = 1 := (FormalPoint.existsUnique_isPointOf_unit U o).unique (h.pull k hp)
    (FormalPoint.isPointOf_one U ho)
  refine (congrArg (·.left) h1).trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

end General

theorem existsUnique_tangent_of_gtTan : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ gm : GtPt D.toPre (epsR V), GtTan gm → ∃! y : epsR V ⟶ G, IsTangent y ∧ TanRel U.toUnifPre y gm := by
  intro V _ _ _ _ hV D A G _ _ _ U gm hg
  have : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  have := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)
  have : Nontrivial (DualNumber V) := (TrivSqZeroExt.inl_injective (R := V) (M := V)).nontrivial
  have : IsLocalRing (DualNumber V) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  obtain ⟨y, hy, hu⟩ := FormalPoint.existsUnique_isPointOf U.toUnifPre gm
  exact ⟨y, ⟨isTangent_of_isPointOf _ hg hy, (tanRel_iff_isPointOf _ _ _).2 hy⟩,
    fun y' h' => hu y' ((tanRel_iff_isPointOf _ _ _).1 h'.2)⟩

end GlobalTheory.MBLow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictUpperMemClosureTransvection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictUpperMemClosureTransvection
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.UpperTransvection

theorem upper_mem_closure (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R)
    (hc : ∀ a b, b ≤ a → c a b = 0) :
    1 + c ∈ Submonoid.closure
      {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  classical
  set S := Submonoid.closure
      {M : Matrix (Fin N) (Fin N) R | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r}
  suffices key : ∀ n : ℕ, ∀ c : Matrix (Fin N) (Fin N) R, (∀ a b, b ≤ a → c a b = 0) →
      (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0).card ≤ n → 1 + c ∈ S from
    key _ c hc le_rfl
  intro n
  induction n with
  | zero =>
    intro c _ hcard
    have hc0 : c = 0 := by
      ext i j
      by_contra h
      have : (i, j) ∈ (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) := by
        simpa using h
      rw [Nat.le_zero, Finset.card_eq_zero] at hcard
      simp [hcard] at this
    subst hc0
    simpa using S.one_mem
  | succ n ih =>
    intro c hc hcard
    set T := (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) with hT
    rcases T.eq_empty_or_nonempty with hE | hne
    · exact ih c hc (by rw [← hT, hE]; simp)
    obtain ⟨p, hpT, hpmin⟩ := Finset.exists_min_image T (fun p => p.1) hne
    obtain ⟨a, b⟩ := p
    have hab : c a b ≠ 0 := by simpa [hT] using hpT
    have hlt : a < b := by
      by_contra h
      exact hab (hc a b (not_lt.mp h))

    have hcol : ∀ i, c i a = 0 := by
      intro i
      by_contra h
      have hi : (i, a) ∈ T := by simpa [hT] using h
      have h1 := hpmin _ hi
      have h2 : a ≤ i := h1
      exact h (hc i a h2)
    set r := c a b
    set c' := c - Matrix.single a b r with hc'
    have hc'_apply : ∀ i j, c' i j = if i = a ∧ j = b then 0 else c i j := by
      intro i j
      simp only [hc', Matrix.sub_apply, Matrix.single_apply]
      by_cases h : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h; simp [r]
      · have h' : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
        simp [h, h']
    have hc'up : ∀ i j, j ≤ i → c' i j = 0 := by
      intro i j hji
      rw [hc'_apply]; split_ifs
      · rfl
      · exact hc i j hji
    have hT' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0) ⊆ T.erase (a, b) := by
      intro q hq
      obtain ⟨i, j⟩ := q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [hc'_apply] at hq
      split_ifs at hq with h
      · exact absurd rfl hq
      · rw [Finset.mem_erase]
        refine ⟨?_, by simpa [hT] using hq⟩
        intro heq
        simp only [Prod.mk.injEq] at heq
        exact h heq
    have hcard' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0).card ≤ n := by
      have := Finset.card_le_card hT'
      rw [Finset.card_erase_of_mem hpT] at this
      omega
    have hmem' : 1 + c' ∈ S := ih c' hc'up hcard'
    have hcolz : c' * Matrix.single a b r = 0 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [hc'_apply]; split_ifs
        · simp
        · rw [hcol]; simp
      · simp
    have heq : 1 + c = (1 + c') * Matrix.transvection a b r := by
      rw [Matrix.transvection, add_mul, one_mul, mul_add, mul_one, hcolz, add_zero, hc']
      abel
    rw [heq]
    refine S.mul_mem hmem' (Submonoid.subset_closure ⟨a, b, r, hlt.ne, rfl⟩)

end GlobalTheory.UpperTransvection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictUpperMemClosureTransvectionStatement
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_strictUpper_mem_closure_transvection : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, b ≤ a → c a b = 0) → 1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  first | exact @GlobalTheory.UpperTransvection.upper_mem_closure | exact GlobalTheory.UpperTransvection.upper_mem_closure | (intros; apply GlobalTheory.UpperTransvection.upper_mem_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfFibre
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratFunc_C_laurent (F : Type) [Field F] : (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C =
    (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  ext1 a
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

theorem sqr_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : sqr G' ≫ φ = φ ≫ sqr G := by
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e := h.2 G' (𝟙 G') (𝟙 G') x₀ x₀ rfl rfl
  have e2 : x₀ * x₀ = x₀ ≫ (𝟙 G * 𝟙 G) := by rw [comp_mul]; simp
  rw [e2] at e
  exact e.symm

theorem ratRigid_of_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (Ω : Type) [Field Ω] [CharZero Ω]
    (b : Sp Ω ⟶ S), RatRigid ((Over.pullback b).obj G) (𝟙 (Sp Ω)) → RatRigid G b := by
  intro S G _ Ω _ _ b hR ξ hξ ⟨β, hβ⟩
  have hp := isGrpPullback_pullback G b
  have hu : unitSec ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = b ≫ unitSec G := GlobalTheory.LieVB.unitSec_comp hp
  have hs : sqr ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = pullback.fst G.hom b ≫ sqr G :=
    sqr_comp_of_isGrpPullback hp
  have hsh : sqr ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = pullback.snd G.hom b :=
    Over.w (𝟙 ((Over.pullback b).obj G) * 𝟙 ((Over.pullback b).obj G))
  have hus : unitSec ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = 𝟙 _ := sec_hom _
  let ξ' : Sp (PowerSeries Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift ξ (spMap PowerSeries.C) hξ.base
  have hξ₁ : ξ' ≫ pullback.fst G.hom b = ξ := pullback.lift_fst _ _ _
  have hξ₂ : ξ' ≫ pullback.snd G.hom b = spMap PowerSeries.C := pullback.lift_snd _ _ _
  have hsp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hpath : IsPath ((Over.pullback b).obj G) 2 (𝟙 (Sp Ω)) ξ' := by
    refine ⟨?_, ?_, ?_⟩
    · exact hξ₂.trans (Category.comp_id _).symm
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, hξ.zero, Category.assoc, hu, Category.id_comp]
      · rw [Category.assoc, hξ₂, Category.assoc, hus, Category.id_comp, hsp]
        have : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω := by
          ext a; simp
        rw [this]
        show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = _
        rw [CommRingCat.ofHom_id, Spec.map_id]
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, Category.assoc, hs, ← Category.assoc, hξ₁, hξ.scale]
      · rw [Category.assoc, hξ₂, Category.assoc, hsh, hξ₂, hsp]
        have : (PowerSeries.rescale (2 : Ω)).comp PowerSeries.C = PowerSeries.C := by
          ext1 a; ext n; rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
          rcases n with _ | n <;> simp
        rw [this]
  have hβb : β ≫ G.hom = spMap RatFunc.C ≫ b := by
    have cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    apply cancel (algebraMap (RatFunc Ω) (LaurentSeries Ω))
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, ← Category.assoc, ← Category.assoc, hsp, hsp,
      ratFunc_C_laurent]
  let β' : Sp (RatFunc Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift β (spMap RatFunc.C) hβb
  have hrat : IsRatPath ξ' := by
    refine ⟨β', ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hξ₁, hβ]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hξ₂, hsp, hsp, ratFunc_C_laurent]
  have e := hR ξ' hpath hrat
  rw [← hξ₁, e]
  simp only [triv, Category.assoc, hu, Category.id_comp]

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfFibreStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (Ω : Type) [Field Ω] [CharZero Ω] (b : Sp Ω ⟶ S), RatRigid ((Over.pullback b).obj G) (𝟙 (Sp Ω)) → RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_fibre | exact GlobalTheory.Nef.ratRigid_of_fibre | (intros; apply GlobalTheory.Nef.ratRigid_of_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndOfBasis
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

open Formalism.IndefR.Bridge

theorem linInd_of_basis {K C X M I : Type} [Field K] [Field C] [AddCommGroup X] [Module K X] [AddCommGroup M] [Module C M]
    (φ : K →+* C) (f : X →ₛₗ[φ] M) (b : Module.Basis I K X) (h : LinearIndependent C fun i => f (b i))
    (n : ℕ) (x : Fin n → X) (hx : LinearIndependent K x) : LinearIndependent C fun a => f (x a) := by
  classical
  have h1 : LinearIndependent K fun a => b.repr (x a) :=
    hx.map' b.repr.toLinearMap (LinearMap.ker_eq_bot.2 b.repr.injective)
  have h2 := GlobalTheory.LatBC.linInd_mapRange φ φ.injective h1
  have h3 := h2.map' (Finsupp.linearCombination C fun i => f (b i)) (LinearMap.ker_eq_bot.2 h)
  refine (funext fun a => ?_ : (fun a => f (x a)) = _) ▸ h3
  simp only [Function.comp_apply]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← b.linearCombination_repr (x a), Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp only [map_smulₛₗ, Finsupp.sum]

theorem exists_avatar {K C X W M I : Type} [Field K] [Field C] [AddCommGroup X] [Module K X] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup M] [Module C M] [Fintype I] (io : C ≃+* ℂ) {σ : K →+* ℂ} {e0 : K →+* C} (h : ∀ x, io (e0 x) = σ x)
    (b : Module.Basis I K X) (c0 : X →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => c0 (b i))
    (hsp : Submodule.span ℂ (Set.range fun i => c0 (b i)) = ⊤) (Φ : X →ₛₗ[e0] M) (hΦ : LinearIndependent C fun i => Φ (b i)) :
    ∃ θ : W →+ M, (∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w) ∧ (∀ x, θ (c0 x) = Φ x) ∧ Function.Injective θ := by
  classical
  let B : Module.Basis I ℂ W := Module.Basis.mk hli hsp.ge
  have hB : ∀ i, B i = c0 (b i) := fun i => Module.Basis.mk_apply _ _ i
  let θ : W →+ M :=
    { toFun := fun w => ∑ i, io.symm (B.repr w i) • Φ (b i)
      map_zero' := by simp
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] }
  have hθ : ∀ w, θ w = ∑ i, io.symm (B.repr w i) • Φ (b i) := fun _ => rfl
  have hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w := fun a w => by
    simp [hθ, Finset.smul_sum, mul_smul]
  have hb : ∀ i, θ (c0 (b i)) = Φ (b i) := fun i => by
    rw [← hB, hθ, B.repr_self, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj.symm]
    · simp
  refine ⟨θ, hs, fun x => ?_, (injective_iff_map_eq_zero θ).2 fun w hw => ?_⟩
  · rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, hs, hb, ← h, RingEquiv.symm_apply_apply]
  · have := Fintype.linearIndependent_iff.1 hΦ _ ((hθ w).symm.trans hw)
    refine B.ext_elem fun i => ?_
    simpa using this i

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
  {χ : J →* ℂˣ}

theorem exists_reading (P : ClassPres ι S σ ρ J χ) {C M : Type} [Field C] [AddCommGroup M] [Module C M] (io : C ≃+* ℂ)
    {e0 : K →+* C} (h : ∀ x, io (e0 x) = σ x) (θ : W →+ M) (hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w)
    (hinj : Function.Injective θ) (Λ : G →* Module.End C M) (hΛ : ∀ γ w, θ (ρ γ w) = Λ (ι γ) (θ w)) :
    ∃ rd : S.Forms →ₛₗ[e0] (G → M),
      (∀ f γ g, rd f (ι γ * g) = rd f g) ∧
      (∀ f (k : J) g, Λ k (rd f (g * k)) = io.symm (χ k : ℂ) • rd f g) ∧
      (∀ (n : ℕ) (f : Fin n → S.Forms), LinearIndependent K f → LinearIndependent C fun a => rd (f a)) ∧
      (∀ (f f' : S.Forms) (A : Finset G), P.ext f' = dcOp A (P.ext f) → (∀ a ∈ A, Λ a = 1) → ∀ g, rd f' g = ∑ s ∈ A, rd f (g * s)) ∧
      ∀ (f : S.Forms) c, rd f (P.y c) = Λ (P.y c)⁻¹ (θ (P.coef ((f : S.Cl → S.V) c))) := by
  let rd : S.Forms →ₛₗ[e0] (G → M) :=
    { toFun := fun f g => Λ g⁻¹ (θ (P.extL f g))
      map_add' := fun f f' => by funext g; simp only [map_add (f := _), Pi.add_apply]
      map_smul' := fun a f => by
        funext g
        simp only [map_smulₛₗ, Pi.smul_apply, hs, ← h, RingEquiv.symm_apply_apply, RingHom.id_apply] }
  have hrd : ∀ f g, rd f g = Λ g⁻¹ (θ (P.ext f g)) := fun _ _ => rfl
  have hm : ∀ a b z, Λ a (Λ b z) = Λ (a * b) z := fun a b z => by rw [map_mul]; rfl
  refine ⟨rd, fun f γ g => ?_, fun f k g => ?_, fun n f hf => ?_, fun f f' A hA h1 g => ?_, fun f c => ?_⟩
  · have := P.extMem_holds f γ g 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this
    rw [hrd, hrd, this, hΛ, hm]
    congr 2
    group
  · have := P.extMem_holds f 1 g k
    simp only [one_mul, map_one, Module.End.one_apply] at this
    rw [hrd, hrd, this, hs, hm, map_smul]
    congr 3
    group
  · have h1 := linInd_of_basis σ P.extL S.basis P.extBij_holds.1 n f hf
    rw [Fintype.linearIndependent_iff] at h1 ⊢
    intro a ha i
    have h2 := h1 (fun i => io (a i)) (funext fun g => hinj ?_) i
    · simpa using h2
    have h3 := congrArg (fun F => Λ g (F g)) ha
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, hrd, map_sum, map_smul, hm, mul_inv_cancel, map_one, Module.End.one_apply,
      Pi.zero_apply, map_zero] at h3
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, hs, RingEquiv.symm_apply_apply, Pi.zero_apply, map_zero]
    exact h3
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hrd, hA, dcOp, map_sum, map_sum]
      refine Finset.sum_congr rfl fun s hs' => ?_
      have e : Λ s⁻¹ = 1 := by
        have := map_mul Λ s⁻¹ s
        rw [h1 s hs', mul_one, inv_mul_cancel, map_one] at this
        exact this.symm
      rw [hrd, mul_inv_rev, map_mul, e, one_mul]
  · rw [hrd, P.ext_rep]

end GlobalTheory.FrameRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentRelationAdditiveScaling
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanAdd

section General

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem corr_mul {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (ρ : (Over.map (thick R I e)).obj T' ⟶ T) (x x' : T' ⟶ thickObj R I e G) (p p' p'' : GtPt D T)
    (h : GtPt.IsAdd p p' p'') (hb : TorusCoord.im g x = ρ ≫ p.b) (hb' : TorusCoord.im g x' = ρ ≫ p'.b) (χ : D.X)
    (hs : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x.left) (LB.pullGen D.P.L _ _ (p.s χ) ρ.left))
    (hs' : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x'.left) (LB.pullGen D.P.L _ _ (p'.s χ) ρ.left)) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) (x * x').left) (LB.pullGen D.P.L _ _ (p''.s χ) ρ.left) := by
  refine corr_of_val D.P.isLB fun z J hJ => ?_
  have k := TorusCoord.val_t_mul_points g GlobalTheory.globalFns_holds χ x x' z J hJ
  have a := val_corr hJ (h.2 χ) ρ.left
  have a₁ := (val_mul hJ _ _ _).symm.trans (a.trans (val_mul hJ _ _ _))
  have c : val (DegPre.cubAtT D T (DegPre.cT D T χ) p.b p'.b) ρ.left z J = TorusCoord.cubeVal g χ z J x x' := by
    refine (val_cub D.cub ρ hJ _ _ _).trans ?_
    unfold TorusCoord.cubeVal
    rw [hb, hb']
    congr 1
    simp
  have s := ((val_pull hJ _ _ _).symm.trans (val_corr hJ hs (𝟙 _))).trans (val_pull hJ _ _ _)
  have s' := ((val_pull hJ _ _ _).symm.trans (val_corr hJ hs' (𝟙 _))).trans (val_pull hJ _ _ _)
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  simp only [Category.id_comp] at s s' ⊢
  refine mul_right_cancel (k.trans ?_)
  exact ((congrArg₂ (· * ·) s s').trans a₁.symm).trans (congrArg (_ * ·) c)

theorem fst_mul {T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' : T' ⟶ thickObj R I e G) :
    (Over.map (thick R I e)).map (x * x') ≫ fstG I e G =
      ((Over.map (thick R I e)).map x ≫ fstG I e G) * ((Over.map (thick R I e)).map x' ≫ fstG I e G) :=
  map_mul (pushHom (isGrpPullback_pullback G (thick R I e)) T') x x'

end General

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_over {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ (epsR A).hom = (epsR B).hom ≫ spMap f := by
  change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_scale {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c : A) :
    spMap (epsScaleR (f c)) ≫ spMap (dualMap f) = spMap (dualMap f) ≫ spMap (epsScaleR c) := by
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap, epsScaleR, mul_comm]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem tanRel_mul (y y' : epsR R ⟶ G) (gm gm' gm'' : GtPt D.toPre (epsR R)) (h : TanRel U y gm) (h' : TanRel U y' gm')
    (ha : GtPt.IsAdd gm gm' gm'') : TanRel U (y * y') gm'' := by
  intro e
  obtain ⟨ye, h₁, h₂, h₃⟩ := h e
  obtain ⟨ye', h₁', h₂', h₃'⟩ := h' e
  have hci : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hw := dual_over (Ideal.Quotient.mk (I ^ (e + 1)))
  let ρ : (Over.map (thick R I e)).obj (epsR (R ⧸ I ^ (e + 1))) ⟶ epsR R :=
    Over.homMk (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1))))) hw
  have key : ∀ (w : epsR R ⟶ G) (we : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left),
      we ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ w.left →
      we ≫ (thickObj R I e G).hom = (epsR (R ⧸ I ^ (e + 1))).hom := by
    intro w we hh
    have h0 := congrArg (· ≫ G.hom) hh
    simp only [Category.assoc, Over.w] at h0
    rw [← cancel_mono (thick R I e), Category.assoc]
    exact h0.trans hw
  let x : epsR (R ⧸ I ^ (e + 1)) ⟶ thickObj R I e G := Over.homMk ye (key y ye h₁)
  let x' : epsR (R ⧸ I ^ (e + 1)) ⟶ thickObj R I e G := Over.homMk ye' (key y' ye' h₁')
  have f : (Over.map (thick R I e)).map x ≫ fstG I e G = ρ ≫ y := Over.OverMorphism.ext h₁
  have f' : (Over.map (thick R I e)).map x' ≫ fstG I e G = ρ ≫ y' := Over.OverMorphism.ext h₁'
  have b : TorusCoord.im (U.gt e) x = ρ ≫ gm.b := Over.OverMorphism.ext h₂
  have b' : TorusCoord.im (U.gt e) x' = ρ ≫ gm'.b := Over.OverMorphism.ext h₂'
  refine ⟨(x * x').left, ?_, ?_, fun χ => corr_mul (U.gt e) ρ x x' gm gm' gm'' ha b b' χ (h₃ χ) (h₃' χ)⟩
  · have := fst_mul x x'
    rw [f, f', ← MonObj.comp_mul] at this
    exact congrArg (·.left) this
  · have := TorusCoord.im_mul (U.gt e) x x'
    rw [b, b', ← MonObj.comp_mul] at this
    rw [ha.1]
    exact congrArg (·.left) this

theorem tanRel_scale (c : R) (y : epsR R ⟶ G) (gm gm' : GtPt D.toPre (epsR R)) (h : TanRel U y gm)
    (hp : GtPt.IsPull (epsScale R c).left gm gm') : TanRel U (epsScale R c ≫ y) gm' := by
  intro e
  obtain ⟨ye, h₁, h₂, h₃⟩ := h e
  have hc : spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c)) ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ (epsScale R c).left := dual_scale _ c
  refine ⟨spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c)) ≫ ye, ?_, ?_, fun χ => ?_⟩
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans ?_)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.left) hc).trans (Category.assoc _ _ _))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ gm.b.left) hc).trans ((Category.assoc _ _ _).trans ?_))
    exact congrArg (_ ≫ ·) hp.1.symm
  · refine corr_of_val D.toPre.P.isLB fun z J hJ => ?_
    have s := ((val_pull hJ _ _ _).symm.trans
      (val_corr hJ (h₃ χ) (spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c))))).trans (val_pull hJ _ _ _)
    have t := (val_corr hJ (hp.2 χ) (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))))).trans (val_pull hJ _ _ _)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    simp only [Category.id_comp]
    exact s.trans ((congrArg (fun q => val (gm.s χ) q z J) hc).trans t.symm)

end GlobalTheory.MBLow.TanAdd

end
end
