module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsUnitCharacterDiffAtChosenInertiaStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularRankThreeCrystallineAfterPush
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularConjOfOrdIdealEqBot
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsGLConjEqDiagonalOfCharpolyEqProd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsGLConjEqDiagonalOfCharpolyEqProd
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem isUnit_det_sub_smul_one_of_forall_not_isUnit {C : Type} [CommRing C] [IsLocalRing C]
    {n : Type} [Fintype n] [DecidableEq n] (Q : Matrix n n C) (hQ : ∀ i j, ¬ IsUnit (Q i j))
    (c : C) (hc : IsUnit c) : IsUnit (Q - c • (1 : Matrix n n C)).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hm : (IsLocalRing.residue C).mapMatrix (Q - c • (1 : Matrix n n C)) =
      (-(IsLocalRing.residue C c)) • (1 : Matrix n n _) := by
    ext i j
    have hq : IsLocalRing.residue C (Q i j) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (hQ i j))
    by_cases h : i = j
    · subst h; simp [hq]
    · simp [hq, h]
  rw [hm, Matrix.det_smul, Matrix.det_one, mul_one]
  refine pow_ne_zero _ (neg_ne_zero.2 ?_)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hc

theorem exists_GL_conj_eq_diagonal_of_charpoly_eq_prod :
    ∀ {C : Type} [CommRing C] [IsLocalRing C] (A : Matrix (Fin 3) (Fin 3) C) (p : Fin 3 → C),
      (∀ a b, a ≠ b → IsUnit (p a - p b)) → A.charpoly = ∏ a, (X - Polynomial.C (p a)) →
      ∃ h : GL (Fin 3) C, (h : Matrix (Fin 3) (Fin 3) C) * A *
        ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = Matrix.diagonal p := by
  intro C _ _ A p hp hchar
  classical
  set P : Fin 3 → C[X] := fun a => ∏ b ∈ Finset.univ.erase a, (X - Polynomial.C (p b)) with hPdef
  have hfull : ∀ a, (X - Polynomial.C (p a)) * P a = ∏ b, (X - Polynomial.C (p b)) := fun a =>
    Finset.mul_prod_erase _ (fun b => X - Polynomial.C (p b)) (Finset.mem_univ a)
  have hz : aeval A (∏ b, (X - Polynomial.C (p b))) = 0 := by
    rw [← hchar]; exact Matrix.aeval_self_charpoly A
  have hsplit : ∀ (f : C[X]) a, f = Polynomial.C (f.eval (p a)) +
      (X - Polynomial.C (p a)) * (f /ₘ (X - Polynomial.C (p a))) := by
    intro f a
    have h := modByMonic_add_div f (X - Polynomial.C (p a))
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact h.symm
  have key : ∀ (f : C[X]) a, aeval A (f * P a) = f.eval (p a) • aeval A (P a) := by
    intro f a
    conv_lhs => rw [hsplit f a]
    rw [add_mul, mul_comm (X - Polynomial.C (p a)), mul_assoc, hfull]
    simp only [map_add (f := _), map_mul, hz, mul_zero, add_zero, aeval_C, Algebra.smul_def]
  have hq : ∀ a, IsUnit ((P a).eval (p a)) := by
    intro a
    simp only [hPdef, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun b hb => hp a b (Finset.ne_of_mem_erase hb).symm)
  have hq0 : ∀ a b, a ≠ b → (P a).eval (p b) = 0 := by
    intro a b hab
    simp only [hPdef, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩) (sub_self _)
  have hBA : ∀ a, aeval A (P a) * A = p a • aeval A (P a) := by
    intro a
    have h := key X a
    rwa [mul_comm, map_mul, aeval_X, eval_X] at h
  have hBB : ∀ a b, aeval A (P a) * aeval A (P b) = (P a).eval (p b) • aeval A (P b) := by
    intro a b
    rw [← map_mul]
    exact key (P a) b
  have hex : ∀ a, ∃ i j, IsUnit (aeval A (P a) i j) := by
    intro a
    by_contra hne
    push_neg at hne
    obtain ⟨u, hu⟩ := hq a
    set E := ((u⁻¹ : Cˣ) : C) • aeval A (P a) with hE
    have hEn : ∀ i j, ¬ IsUnit (E i j) := by
      intro i j h
      apply hne i j
      have h' : aeval A (P a) i j = (u : C) * E i j := by
        rw [hE, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]
      rw [h']
      exact (Units.isUnit u).mul h
    have hEE : E * E = E := by
      rw [hE, Matrix.smul_mul, Matrix.mul_smul, hBB, ← hu, smul_smul, smul_smul,
        mul_assoc, Units.inv_mul, mul_one]
    have hdet := isUnit_det_sub_smul_one_of_forall_not_isUnit E hEn 1 isUnit_one
    rw [one_smul] at hdet
    have hE0 : E = 0 := by
      have h1 : (E - 1) * E = 0 := by rw [sub_mul, hEE, one_mul, sub_self]
      obtain ⟨w, hw⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
      calc E = ((w⁻¹ : (Matrix (Fin 3) (Fin 3) C)ˣ) : Matrix (Fin 3) (Fin 3) C) * ((E - 1) * E) := by
            rw [← mul_assoc, ← hw, Units.inv_mul, one_mul]
        _ = 0 := by rw [h1, mul_zero]
    have hB0 : aeval A (P a) = 0 := by
      have h' : aeval A (P a) = (u : C) • E := by rw [hE, smul_smul, Units.mul_inv, one_smul]
      rw [h', hE0, smul_zero]
    have hs := congrArg (aeval A) (hsplit (P a) a)
    rw [hB0, map_add (f := _), aeval_C, map_mul, ← hu] at hs
    have hinv : aeval A (X - Polynomial.C (p a)) *
        (-(((u⁻¹ : Cˣ) : C) • aeval A (P a /ₘ (X - Polynomial.C (p a))))) = 1 := by
      have h2 : aeval A (X - Polynomial.C (p a)) * aeval A (P a /ₘ (X - Polynomial.C (p a))) =
          -algebraMap C _ (u : C) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hs.symm
      rw [mul_neg, Matrix.mul_smul, h2, smul_neg, neg_neg, Algebra.smul_def, ← map_mul,
        Units.inv_mul, map_one]
    have hdx : IsUnit (aeval A (X - Polynomial.C (p a))).det :=
      IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hinv, Matrix.det_one])
    have hev : A.charpoly.eval (p a) = 0 := by
      rw [hchar, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
    rw [Matrix.eval_charpoly] at hev
    have hneg : Matrix.scalar (Fin 3) (p a) - A = -(aeval A (X - Polynomial.C (p a))) := by
      simp [Algebra.algebraMap_eq_smul_one, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hneg, Matrix.det_neg] at hev
    have hu2 : IsUnit ((-1 : C) ^ Fintype.card (Fin 3) * (aeval A (X - Polynomial.C (p a))).det) :=
      ((isUnit_neg_one).pow _).mul hdx
    rw [hev] at hu2
    exact not_isUnit_zero hu2
  choose i j hij using hex
  let H : Matrix (Fin 3) (Fin 3) C := Matrix.of fun a k => aeval A (P a) (i a) k
  let Q : Matrix (Fin 3) (Fin 3) C := Matrix.of fun k b => aeval A (P b) k (j b)
  have hHQ : H * Q = Matrix.diagonal fun a => (P a).eval (p a) * aeval A (P a) (i a) (j a) := by
    ext a b
    have h' : (H * Q) a b = (aeval A (P a) * aeval A (P b)) (i a) (j b) := by
      simp [H, Q, Matrix.mul_apply]
    rw [h', hBB, Matrix.smul_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp
    · rw [hq0 a b hab, zero_mul, Matrix.diagonal_apply_ne _ hab]
  have hdetH : IsUnit H.det := by
    have h2 : IsUnit (H * Q).det := by
      rw [hHQ, Matrix.det_diagonal]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun a _ => (hq a).mul (hij a))
    rw [Matrix.det_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hHA : H * A = Matrix.diagonal p * H := by
    ext a k
    have h' : (H * A) a k = (aeval A (P a) * A) (i a) k := by simp [H, Matrix.mul_apply]
    rw [h', hBA, Matrix.diagonal_mul]
    simp [H]
  have hU := (Matrix.isUnit_iff_isUnit_det H).2 hdetH
  refine ⟨hU.unit, ?_⟩
  rw [IsUnit.unit_spec, hHA, mul_assoc, hU.mul_val_inv, mul_one]

end GlobalTheory
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsGLConjEqDiagonalOfCharpolyEqProdStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalize_of_distinct_eigenvalues : ∀ {C : Type} [CommRing C] [IsLocalRing C] (A : Matrix (Fin 3) (Fin 3) C) (p : Fin 3 → C), (∀ a b, a ≠ b → IsUnit (p a - p b)) → A.charpoly = ∏ a, (X - Polynomial.C (p a)) → ∃ h : GL (Fin 3) C, (h : Matrix (Fin 3) (Fin 3) C) * A * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = Matrix.diagonal p := by
  first | exact @GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod | exact GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod | (intros; apply GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularConjOfOrdIdealEqBot
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem conjBy_right_eq {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C) (r : G →* GG (m := 3) (R := C)) (g : G) :
    (conjBy h r g).right = (r g).right := by
  simp [conjBy, MulAut.conj_apply]

end GlobalTheory.OrdLoc

private theorem fin_eq_eI_or_wI_or_esI {C : Type} [CommRing C] (p q : Fin 3 → C)
    (hp : ∀ a b, a ≠ b → IsUnit (p a - p b)) (N : Matrix (Fin 3) (Fin 3) C)
    (h0 : (N - Matrix.scalar (Fin 3) (q 0)) * (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 1)) *
      (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 2)) = 0)
    (h1 : (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 0)) * (N - Matrix.scalar (Fin 3) (q 1)) *
      (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 2)) = 0)
    (h2 : (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 0)) * (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 1)) *
      (N - Matrix.scalar (Fin 3) (q 2)) = 0) :
    N 1 0 = 0 ∧ N 2 0 = 0 ∧ N 2 1 = 0 ∧ N 0 0 = q 0 ∧ N 1 1 = q 1 ∧ N 2 2 = q 2 := by
  have e : ∀ c, Matrix.diagonal p - Matrix.scalar (Fin 3) c = Matrix.diagonal (fun i => p i - c) := by
    intro c
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  simp only [e] at h0 h1 h2
  have u01 := hp 0 1 (by decide)
  have u02 := hp 0 2 (by decide)
  have u10 := hp 1 0 (by decide)
  have u12 := hp 1 2 (by decide)
  have u20 := hp 2 0 (by decide)
  have u21 := hp 2 1 (by decide)
  have a10 := congrFun (congrFun h0 1) 0
  have a20 := congrFun (congrFun h0 2) 0
  have a00 := congrFun (congrFun h0 0) 0
  have b21 := congrFun (congrFun h1 2) 1
  have b11 := congrFun (congrFun h1 1) 1
  have c22 := congrFun (congrFun h2 2) 2
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul] at a10 a20 a00 b21 b11 c22
  have k : ∀ {x a b : C}, IsUnit a → IsUnit b → x * a * b = 0 → x = 0 := by
    intro x a b ha hb h
    rw [mul_assoc] at h
    exact (ha.mul hb).mul_left_eq_zero.mp h
  rw [mul_comm (p 2 - p 0)] at b21
  rw [mul_comm (p 1 - p 0)] at b11
  rw [mul_comm] at c22
  refine ⟨k u01 u02 a10, k u01 u02 a20, k u20 u12 b21, sub_eq_zero.mp (k u01 u02 a00),
    sub_eq_zero.mp (k u10 u12 b11), sub_eq_zero.mp ((u20.mul u21).mul_left_eq_zero.mp c22)⟩

private theorem exists_isUnit_det_apply_eq_sum_of_mem_Nof {C : Type} [CommRing C] (p : Fin 3 → C)
    (hp : ∀ a b, a ≠ b → IsUnit (p a - p b)) (M T : Matrix (Fin 3) (Fin 3) C)
    (hT : T 1 0 = 0 ∧ T 2 0 = 0 ∧ T 2 1 = 0 ∧ T 0 0 = p 0 ∧ T 1 1 = p 1 ∧ T 2 2 = p 2)
    (h : T * M = M * Matrix.diagonal p) : M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 := by
  obtain ⟨t10, t20, t21, t00, t11, t22⟩ := hT
  have e20 := congrFun (congrFun h 2) 0
  have e10 := congrFun (congrFun h 1) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_diagonal, t10, t20, t21, t00, t11, t22] at e20 e10 e21
  have m20 : M 2 0 = 0 := by
    have : (p 2 - p 0) * M 2 0 = 0 := by linear_combination e20
    exact (hp 2 0 (by decide)).mul_right_eq_zero.mp this
  have m10 : M 1 0 = 0 := by
    have : (p 1 - p 0) * M 1 0 = 0 := by linear_combination e10 - T 1 2 * m20
    exact (hp 1 0 (by decide)).mul_right_eq_zero.mp this
  have m21 : M 2 1 = 0 := by
    have : (p 2 - p 1) * M 2 1 = 0 := by linear_combination e21
    exact (hp 2 1 (by decide)).mul_right_eq_zero.mp this
  exact ⟨m10, m20, m21⟩

private theorem upperTriangular_fin_three_mul_entries {C : Type} [CommRing C] (A B : Matrix (Fin 3) (Fin 3) C)
    (hA : A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0) (hB : B 1 0 = 0 ∧ B 2 0 = 0 ∧ B 2 1 = 0) :
    (∀ i, (A * B) i i = A i i * B i i) ∧ (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
      (A * B) 1 2 = A 1 1 * B 1 2 + A 1 2 * B 2 2 ∧
      (A * B) 0 2 = A 0 0 * B 0 2 + A 0 1 * B 1 2 + A 0 2 * B 2 2 := by
  obtain ⟨a10, a20, a21⟩ := hA
  obtain ⟨b10, b20, b21⟩ := hB
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]


open GlobalTheory.OrdLoc in
theorem GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (r : GQ l →* GG (m := 3) (R := B)), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ → ∃ (h : GL (Fin 3) B) (ρ : ↥D.HL →* GL (Fin 3) B) (κ : Fin 3 → ↥D.HL →* Bˣ) (x y z : ↥D.HL → B), (∀ g, ρ g = (conjBy h r g).left) ∧ (∀ i, Continuous fun g => (κ i g : B)) ∧ (∀ g : ↥D.HL, (g : GQ l) ∈ Iq l → ∀ i, κ i g = cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i)) ∧ Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ x ∈ Z1 (chRep (κ 0 / κ 1)) ∧ y ∈ Z1 (chRep (κ 1 / κ 2)) ∧ ∀ hσ : GlobalTheory.OrdLoc.fr D ∈ D.HL, (∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 0 = v * (((κ 0 / κ 1) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B))) ∧ ∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 1 = v * (((κ 1 / κ 2) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B)) := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _ _ _ _ _ _ r hmult hcont hbot
  obtain ⟨hHLn, -, -, hPsi, hS0⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  obtain ⟨hsHL, hsIq, -⟩ := hS0
  obtain ⟨hpu, hcc⟩ := GlobalTheory.T.isUnit_characterDiff_at_chosenInertia D B
  set p : Fin 3 → B := fun a => algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0) with hp_def
  have hchar : (r D.s0).mat.charpoly = ∏ a : Fin 3, (X - Polynomial.C (p a)) := by
    rw [← sub_eq_zero]
    ext i
    have hm : ((r D.s0).mat.charpoly - ∏ a : Fin 3, (X - Polynomial.C (p a))).coeff i ∈
        GlobalTheory.OrdLoc.ordIdeal D r :=
      Ideal.subset_span (Set.mem_union_left _ ⟨D.s0, ⟨hsHL, hsIq⟩, i, rfl⟩)
    rw [hbot, Ideal.mem_bot] at hm
    simpa using hm
  obtain ⟨h, hh⟩ := GlobalTheory.T.diagonalize_of_distinct_eigenvalues (r D.s0).mat p hpu hchar
  have hright : ∀ g ∈ D.HL, (r g).right = 1 := by
    intro g hg
    rw [hmult g]
    have := (Subgroup.mem_inf.mp hg).1
    simpa using this
  set r' := conjBy h r with hr'_def
  have hright' : ∀ g ∈ D.HL, (r' g).right = 1 := by
    intro g hg
    rw [hr'_def, GlobalTheory.OrdLoc.conjBy_right_eq]
    exact hright g hg
  let H : Matrix (Fin 3) (Fin 3) B := h
  let K : Matrix (Fin 3) (Fin 3) B := (h⁻¹ : GL (Fin 3) B)
  let conjM (M : Matrix (Fin 3) (Fin 3) B) := H * M * K
  have hHK : H * K = 1 := h.val_inv
  have hKH : K * H = 1 := h.inv_val
  have hconj_mul (M N : Matrix (Fin 3) (Fin 3) B) : conjM M * conjM N = conjM (M * N) := by
    simp only [conjM, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc K H, hKH, Matrix.one_mul]
  have hmat : ∀ g ∈ D.HL, (r' g).mat = conjM (r g).mat := by
    intro g hg
    have hleft : (r' g).left = h * (r g).left * h⁻¹ := by
      show (GG.ofGL h * r g * (GG.ofGL h)⁻¹).left = _
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
      simp only [SemidirectProduct.right_inl, SemidirectProduct.left_inl, SemidirectProduct.mul_right,
        hright g hg, mul_one, inv_one, map_one, MulAut.one_apply]
    unfold GG.mat
    rw [hleft, Units.val_mul, Units.val_mul]
  have hshift : ∀ a s, s ∈ D.HL → D.sh r' a s = conjM (D.sh r a s) := by
    intro a s hs
    rw [Dat3.sh, Dat3.sh, hmat s hs]
    have hscalar (c : B) : conjM (Matrix.scalar (Fin 3) c) = Matrix.scalar (Fin 3) c := by
      unfold conjM
      rw [← (Matrix.scalar_commute c (fun _ => Commute.all _ _) H), Matrix.mul_assoc, hHK,
        Matrix.mul_one]
    simp only [conjM, Matrix.mul_sub, Matrix.sub_mul] at hscalar ⊢
    rw [hscalar]
  have hs0' : (r' D.s0).mat = Matrix.diagonal p := (hmat _ hsHL).trans hh
  have hsh : ∀ s : Fin 3 → GQ l, (∀ a, s a ∈ D.HL ⊓ Iq l) →
      D.sh r' 0 (s 0) * D.sh r' 1 (s 1) * D.sh r' 2 (s 2) = 0 := by
    intro s hs
    have hzero : D.sh r 0 (s 0) * D.sh r 1 (s 1) * D.sh r 2 (s 2) = 0 := by
      ext i j
      have hm : (D.sh r 0 (s 0) * D.sh r 1 (s 1) * D.sh r 2 (s 2)) i j ∈
          GlobalTheory.OrdLoc.ordIdeal D r :=
        Ideal.subset_span (Set.mem_union_right _ ⟨s, hs, i, j, rfl⟩)
      rwa [hbot, Ideal.mem_bot] at hm
    rw [hshift _ _ (hs 0).1, hshift _ _ (hs 1).1, hshift _ _ (hs 2).1,
      hconj_mul, hconj_mul, hzero]
    simp [conjM]
  have hs0I : D.s0 ∈ D.HL ⊓ Iq l := ⟨hsHL, hsIq⟩
  have htriI : ∀ t ∈ D.HL ⊓ Iq l, (r' t).mat 1 0 = 0 ∧ (r' t).mat 2 0 = 0 ∧ (r' t).mat 2 1 = 0 ∧
      (r' t).mat 0 0 = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 0 t) ∧
      (r' t).mat 1 1 = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 1 t) ∧
      (r' t).mat 2 2 = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 2 t) := by
    intro t ht
    apply fin_eq_eI_or_wI_or_esI p (fun a => algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a t)) hpu
    · have := hsh ![t, D.s0, D.s0] (by intro a; fin_cases a <;> simpa)
      simpa [UpperTheory.V.Loc.Dat3.sh, hs0'] using this
    · have := hsh ![D.s0, t, D.s0] (by intro a; fin_cases a <;> simpa)
      simpa [UpperTheory.V.Loc.Dat3.sh, hs0'] using this
    · have := hsh ![D.s0, D.s0, t] (by intro a; fin_cases a <;> simpa)
      simpa [UpperTheory.V.Loc.Dat3.sh, hs0'] using this
  have hmm : ∀ x y : GG (m := 3) (R := B), x.right = 1 → (x * y).mat = x.mat * y.mat := by
    intro x y hx
    simp [UpperTheory.V.U3.GG.mat, SemidirectProduct.mul_left, hx]
  have hpsiconj : ∀ g a, UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (g * D.s0 * g⁻¹) = UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0 := by
    intro g a
    simp [UpperTheory.V.UnitaryThreeInertia.psi, mul_inv_cancel_comm]
  have htri : ∀ g ∈ D.HL, (r' g).mat 1 0 = 0 ∧ (r' g).mat 2 0 = 0 ∧ (r' g).mat 2 1 = 0 := by
    intro g hg
    have ht : g * D.s0 * g⁻¹ ∈ D.HL ⊓ Iq l :=
      ⟨hHLn.conj_mem _ hsHL g, (UpperTheory.V.Loc.iqBasic l).1.conj_mem _ hsIq g⟩
    obtain ⟨a, b, c, d, e, f⟩ := htriI _ ht
    apply exists_isUnit_det_apply_eq_sum_of_mem_Nof p hpu (r' g).mat (r' (g * D.s0 * g⁻¹)).mat
    · refine ⟨a, b, c, ?_, ?_, ?_⟩
      · rw [d, hpsiconj]
      · rw [e, hpsiconj]
      · rw [f, hpsiconj]
    · rw [← hs0', ← hmm _ _ (hright' _ ht.1), ← hmm _ _ (hright' _ hg), ← map_mul, ← map_mul]
      rw [show g * D.s0 * g⁻¹ * g = g * D.s0 by group]
  have hc : ∀ a b, Continuous fun g : GQ l => (r g).mat a b := by
    intro a b
    have := hcont a b
    unfold UpperTheory.V.Loc.QCont at this
    rwa [← eq_moduleTopology ℚ_[l] B] at this
  have hMc : ∀ i j, Continuous fun g : ↥D.HL => (r' (g : GQ l)).mat i j := by
    intro i j
    have e : (fun g : ↥D.HL => (r' (g : GQ l)).mat i j) = fun g : ↥D.HL =>
        ((h : Matrix (Fin 3) (Fin 3) B) * (r (g : GQ l)).mat *
          ((h⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) i j := by
      funext g
      rw [hmat g g.2]
    rw [e]
    have hr : Continuous fun g : GQ l => (r g).mat := continuous_matrix fun a b => hc a b
    exact ((continuous_const.matrix_mul (hr.comp continuous_subtype_val)).matrix_mul
      continuous_const).matrix_elem i j
  have hmulHL : ∀ a b : ↥D.HL, (r' ((a * b : ↥D.HL) : GQ l)).mat = (r' a).mat * (r' b).mat := by
    intro a b
    rw [Subgroup.coe_mul, map_mul, hmm _ _ (hright' _ a.2)]
  have hinv1 : ∀ a : ↥D.HL, (r' a).mat * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat = 1 := by
    intro a
    rw [← hmulHL, mul_inv_cancel]
    simp [UpperTheory.V.U3.GG.mat]
  have hdiag : ∀ (a b : ↥D.HL) i,
      (r' ((a * b : ↥D.HL) : GQ l)).mat i i = (r' a).mat i i * (r' b).mat i i := by
    intro a b i
    rw [hmulHL]
    exact (upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ b.2)).1 i
  have hunit : ∀ (a : ↥D.HL) i, (r' a).mat i i * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat i i = 1 := by
    intro a i
    rw [← (upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ (a⁻¹).2)).1 i, hinv1]
    simp
  have hunit' : ∀ (a : ↥D.HL) i, (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat i i * (r' a).mat i i = 1 := by
    intro a i
    rw [mul_comm]
    exact hunit a i
  let κ : Fin 3 → ↥D.HL →* Bˣ := fun i => MonoidHom.mk'
    (fun g => ⟨(r' g).mat i i, (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat i i, hunit g i, hunit' g i⟩)
    (fun a b => by
      ext
      simp only [Units.val_mul]
      exact hdiag a b i)
  let ρ : ↥D.HL →* GL (Fin 3) B := MonoidHom.mk' (fun g => (r' g).left) (fun a b => by
    rw [Subgroup.coe_mul, map_mul, SemidirectProduct.mul_left, hright' _ a.2, map_one]
    rfl)
  have hκ : ∀ i (g : ↥D.HL), ((κ i g : Bˣ) : B) = (r' g).mat i i := fun i g => rfl
  have hq : ∀ (i j : Fin 3) (a : ↥D.HL), (((κ i / κ j) a : Bˣ) : B) =
      (r' a).mat i i * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat j j := by
    intro i j a
    rw [MonoidHom.div_apply, div_eq_mul_inv, Units.val_mul]
    rfl
  have hcyc : ∀ s, Units.map (algebraMap O B : O →* B) (cycA l l O s) = cycA l l B s := by
    intro s
    ext
    simp [UpperTheory.V.Loc.cycA, ← IsScalarTower.algebraMap_apply]
  refine ⟨h, ρ, κ, fun g => (r' g).mat 0 1 * (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat 1 1,
    fun g => (r' g).mat 1 2 * (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat 2 2,
    fun g => (r' g).mat 0 2 * (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat 2 2,
    fun g => rfl, fun i => hMc i i, ?_, (hMc 0 2).mul ((hMc 2 2).comp continuous_inv), ?_, ?_, ?_, ?_⟩
  · intro g hgI i
    obtain ⟨-, -, -, d0, d1, d2⟩ := htriI _ ⟨g.2, hgI⟩
    have key : ∀ i, algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ i g) =
        ((cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i) : Bˣ) : B) := by
      intro i
      rw [UpperTheory.V.UnitaryThreeInertia.psi, hPsi _ g.2 hgI, ← hcyc, ← map_zpow, Units.coe_map, zpow_mul, zpow_natCast]
      rfl
    ext
    fin_cases i
    · exact d0.trans (key 0)
    · exact d1.trans (key 1)
    · exact d2.trans (key 2)
  · intro g
    obtain ⟨t10, t20, t21⟩ := htri _ g.2
    have u1 := hunit g 1
    have u2 := hunit g 2
    change (r' (g : GQ l)).mat = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Loc.triM, hκ, t10, t20, t21] at u1 u2 ⊢
    all_goals first
      | linear_combination -(r' (g : GQ l)).mat 0 1 * u1
      | linear_combination -(r' (g : GQ l)).mat 0 2 * u2
      | linear_combination -(r' (g : GQ l)).mat 1 2 * u2
  · refine ⟨(hMc 0 1).mul ((hMc 1 1).comp continuous_inv), fun a b => ?_⟩
    dsimp only
    rw [UpperTheory.V.Loc.chRep_apply, hq, mul_inv_rev, hmulHL, hmulHL]
    obtain ⟨-, e01, -, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ b.2)
    obtain ⟨dB, -, -, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ (b⁻¹).2) (htri _ (a⁻¹).2)
    rw [e01, dB 1]
    linear_combination ((r' a).mat 0 1 * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat 1 1) * hunit b 1
  · refine ⟨(hMc 1 2).mul ((hMc 2 2).comp continuous_inv), fun a b => ?_⟩
    dsimp only
    rw [UpperTheory.V.Loc.chRep_apply, hq, mul_inv_rev, hmulHL, hmulHL]
    obtain ⟨-, -, e12, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ b.2)
    obtain ⟨dB, -, -, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ (b⁻¹).2) (htri _ (a⁻¹).2)
    rw [e12, dB 2]
    linear_combination ((r' a).mat 1 2 * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat 2 2) * hunit b 2
  · intro hσ
    have htr : ∀ a, D.tr r' a = D.tr r a := by
      intro a
      rw [Dat3.tr, Dat3.tr, hshift _ _ hsHL, hshift _ _ hsHL, hmat _ hσ,
        hconj_mul, hconj_mul]
      unfold conjM
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hKH, Matrix.one_mul]
    have hdd : ∀ a, D.dd r a = D.dd r' a := by
      intro a
      simp only [Dat3.dd, htr]
    have hshift_diag : ∀ b, D.sh r' b D.s0 = Matrix.diagonal (fun c => p c - p b) := by
      intro b
      rw [Dat3.sh, hs0', Matrix.scalar_apply, Matrix.diagonal_sub]
    have htr_diag : ∀ a, D.tr r' a = algebraMap O B (D.cc a) * (r' D.fr).mat a a := by
      intro a
      rw [Dat3.tr, hshift_diag, hshift_diag, Matrix.diagonal_mul_diagonal, Matrix.trace,
        Fin.sum_univ_three]
      simp only [Matrix.diag, Matrix.diagonal_mul, Dat3.cc, map_mul, map_sub, ← hp_def]
      fin_cases a <;> simp <;> ring
    have hdiag' : ∀ a : Fin 3, D.dd r' a = algebraMap O B (D.cc a * D.cc (a + 1)) *
        ((r' D.fr).mat a a - algebraMap O B ((cycA l l O D.fr : Oˣ) : O) *
          (r' D.fr).mat (a + 1) (a + 1)) := by
      intro a
      simp only [Dat3.dd, htr_diag, map_mul]
      ring
    have hc' : algebraMap O B ((cycA l l O (GlobalTheory.OrdLoc.fr D) : Oˣ) : O) =
        ((cycA l l B (GlobalTheory.OrdLoc.fr D) : Bˣ) : B) := by
      rw [← hcyc]
      rfl
    have u1 := hunit ⟨_, hσ⟩ 1
    have u2 := hunit ⟨_, hσ⟩ 2
    refine ⟨⟨(hcc 0).unit * (hcc 1).unit * κ 1 ⟨_, hσ⟩, ?_⟩, ⟨(hcc 1).unit * (hcc 2).unit * κ 2 ⟨_, hσ⟩, ?_⟩⟩
    · rw [hdd, hdiag' 0, hq, Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hκ, ← hc']
      simp only [map_mul]
      have e01 : (0 : Fin 3) + 1 = 1 := rfl
      rw [e01]
      linear_combination (-(algebraMap O B (D.cc 0) * algebraMap O B (D.cc 1) *
        (r' (GlobalTheory.OrdLoc.fr D)).mat 0 0)) * u1
    · rw [hdd, hdiag' 1, hq, Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hκ, ← hc']
      simp only [map_mul]
      have e12 : (1 : Fin 3) + 1 = 2 := rfl
      rw [e12]
      linear_combination (-(algebraMap O B (D.cc 1) * algebraMap O B (D.cc 2) *
        (r' (GlobalTheory.OrdLoc.fr D)).mat 1 1)) * u2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularConjOfOrdIdealEqBotStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_conj_of_ordIdeal_eq_bot : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (r : GQ l →* GG (m := 3) (R := B)), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ → ∃ (h : GL (Fin 3) B) (ρ : ↥D.HL →* GL (Fin 3) B) (κ : Fin 3 → ↥D.HL →* Bˣ) (x y z : ↥D.HL → B), (∀ g, ρ g = (conjBy h r g).left) ∧ (∀ i, Continuous fun g => (κ i g : B)) ∧ (∀ g : ↥D.HL, (g : GQ l) ∈ Iq l → ∀ i, κ i g = cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i)) ∧ Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ x ∈ Z1 (chRep (κ 0 / κ 1)) ∧ y ∈ Z1 (chRep (κ 1 / κ 2)) ∧ ∀ hσ : GlobalTheory.OrdLoc.fr D ∈ D.HL, (∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 0 = v * (((κ 0 / κ 1) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B))) ∧ ∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 1 = v * (((κ 1 / κ 2) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B)) := by
  first | exact @GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot | exact GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot | (intros; apply GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallineConjByInvariant
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallineConjByInvariant
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.LCrConj

open TensorProduct

private theorem isCr_transfer {l : ℕ} [Fact l.Prime] {G A A' V V' : Type} [Group G] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [CommRing A']
    [Algebra ℚ_[l] A'] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V']
    (φ : G →* GQ l) (ρ : Representation A G V)
    (ρ' : Representation A' G V') (f : V ≃ₗ[ℚ_[l]] V') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    IsCr φ ρ ↔ IsCr φ ρ' := by
  let F : V ⊗[ℚ_[l]] Bcr l ≃ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bcr l := TensorProduct.congr f (LinearEquiv.refl _ _)
  have hF : ∀ g x, F (actC φ (resCoef ℚ_[l] ρ) g x) = actC φ (resCoef ℚ_[l] ρ') g (F x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b => simp [F, actC, resCoef, hf]
  have hD : (Dcr φ (resCoef ℚ_[l] ρ)).map F.toLinearMap = Dcr φ (resCoef ℚ_[l] ρ') := by
    ext x
    obtain ⟨x, rfl⟩ := F.surjective x
    rw [Submodule.mem_map_equiv, F.symm_apply_apply]
    simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      ← hF, F.injective.eq_iff]
  unfold IsCr
  rw [← hD, LinearEquiv.finrank_map_eq, f.finrank_eq]

private theorem isCr_conjGL {l : ℕ} [Fact l.Prime] {G A : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] {n : ℕ}
    (φ : G →* GQ l) (r : G →* GL (Fin n) A) (h : GL (Fin n) A) :
    IsCr φ (colRep r) ↔ IsCr φ (colRep (conjGL h r)) :=
  isCr_transfer φ (colRep r) (colRep (conjGL h r))
    ((Matrix.toLinearEquiv' (h : Matrix (Fin n) (Fin n) A) h.invertible).restrictScalars ℚ_[l]) fun g x => by
      simp [colRep, conjGL, Matrix.toLinearEquiv', Matrix.mul_assoc]

private def glPart {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G)
    (r : G →* GG (m := m) (R := R))
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem isLCr_iff' {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B]
    (r : GQ l →* GG (m := 3) (R := B))
    (h : ∀ g ∈ D.HL, (r g).right = 1) : D.IsLCr r ↔ IsCr D.HL.subtype (colRep (glPart D.HL r h)) := by
  refine ⟨fun ⟨ρ, h1, h2⟩ => ?_, fun h2 => ⟨_, fun _ => rfl, h2⟩⟩
  have : ρ = glPart D.HL r h := MonoidHom.ext h1
  exact this ▸ h2

end GlobalTheory.LCrConj


open GlobalTheory.LCrConj in
theorem GlobalTheory.LCrConj.main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG (m := 3) (R := B)) (h : GL (Fin 3) B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → D.IsLCr (conjBy h r) → D.IsLCr r := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _ _ r h hm _ hc
  have h1 : ∀ g ∈ D.HL, (r g).right = 1 := fun g hg => (hm g).trans hg.1
  have hm' : HasMult D.η (conjBy h r) := fun g => (by simp [conjBy] : (conjBy h r g).right = (r g).right).trans (hm g)
  have h1' : ∀ g ∈ D.HL, (conjBy h r g).right = 1 := fun g hg => (hm' g).trans hg.1
  have he : glPart D.HL (conjBy h r) h1' = conjGL h (glPart D.HL r h1) := by
    ext g : 1
    have h2 : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by rw [map_inv]; rfl
    show (conjBy h r g).left = _
    rw [h2, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, h1 g g.2, mul_one, sgnAct_one,
      sgnAct_one]
    rfl
  rw [isLCr_iff' D r h1, isCr_conjGL _ _ h, ← he, ← isLCr_iff']
  exact hc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallineConjByInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLCrystalline_conjBy_invariant : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG (m := 3) (R := B)) (h : GL (Fin 3) B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → D.IsLCr (conjBy h r) → D.IsLCr r := by
  first | exact @GlobalTheory.LCrConj.main | exact GlobalTheory.LCrConj.main | (intros; apply GlobalTheory.LCrConj.main <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsFiniteLocalLiftOfSaturatedIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_local_lift_of_saturated_ideal : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (J : Ideal R) (d : R), (l : R) ∣ d → (∀ a, d * a ∈ J → a ∈ J) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B), J ≤ RingHom.ker f → ∃ (B' : Type) (_ : CommRing B') (_ : IsLocalRing B') (_ : Algebra ℚ_[l] B') (_ : Module.Finite ℚ_[l] B') (_ : Algebra O B') (_ : Algebra ℤ_[l] B') (_ : IsScalarTower ℤ_[l] O B') (_ : IsScalarTower ℤ_[l] ℚ_[l] B') (f' : R →ₐ[O] B') (q : B' →ₐ[ℚ_[l]] B), J ≤ RingHom.ker f' ∧ (∀ a, q (f' a) = f a) ∧ ∀ b, f' d * b = 0 → q b = 0 := by
  intro l _ O _ _ R _ _ _ J d _ hreg B _ _ _ _ _ _ _ _ f hJf
  classical
  let M0 : Ideal R := (IsLocalRing.maximalIdeal B).comap f
  let RM := Localization.AtPrime M0
  have hgu : ∀ y : M0.primeCompl, IsUnit ((f : R →+* B) (y : R)) := by
    intro y
    have hy := Ideal.mem_primeCompl_iff.1 y.2
    by_contra h
    exact hy (show (y : R) ∈ M0 from (IsLocalRing.mem_maximalIdeal _).2 h)
  let g : RM →+* B := IsLocalization.lift (M := M0.primeCompl) (S := RM) (g := (f : R →+* B)) hgu
  have hg : ∀ r : R, g (algebraMap R RM r) = f r := fun r => IsLocalization.lift_eq hgu r
  let α : O →+* RM := (algebraMap R RM).comp (algebraMap O R)
  let ψ : ℤ_[l] →+* RM := α.comp (algebraMap ℤ_[l] O)
  have hfψ : ∀ y : ℤ_[l], g (ψ y) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] y) := by
    intro y
    show g (algebraMap R RM (algebraMap O R (algebraMap ℤ_[l] O y))) = _
    rw [hg, f.commutes, ← IsScalarTower.algebraMap_apply ℤ_[l] O B y,
      ← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B y]
  have hψu : ∀ y : nonZeroDivisors ℤ_[l], IsUnit (ψ y) := by
    intro y
    have hy0 : algebraMap ℤ_[l] ℚ_[l] y ≠ 0 := by
      intro h
      exact nonZeroDivisors.coe_ne_zero y
        ((IsFractionRing.injective ℤ_[l] ℚ_[l]) (h.trans (map_zero _).symm))
    have hr : IsUnit (f (algebraMap O R (algebraMap ℤ_[l] O y))) := by
      rw [← hg]
      have := (isUnit_iff_ne_zero.2 hy0).map (algebraMap ℚ_[l] B)
      rw [← hfψ y] at this
      exact this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff RM M0 _).2
      (Ideal.mem_primeCompl_iff.2 (fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) hr))
  let φ : ℚ_[l] →+* RM := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) (S := ℚ_[l]) hψu
  have hφ : ∀ y : ℤ_[l], φ (algebraMap ℤ_[l] ℚ_[l] y) = ψ y := fun y => IsLocalization.lift_eq hψu y
  have hgφ : g.comp φ = algebraMap ℚ_[l] B := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l])
    ext y
    simp only [RingHom.comp_apply, hφ, hfψ]
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  obtain ⟨N0, hN0⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).1 this
  have hmaxg : ∀ x ∈ IsLocalRing.maximalIdeal RM ^ N0, g x = 0 := by
    intro x hx
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M0 RM, ← Ideal.map_pow] at hx
    have hle : Ideal.map (algebraMap R RM) (M0 ^ N0) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hg]
      have h1 : f r ∈ (M0 ^ N0).map f := Ideal.mem_map_of_mem f hr
      rw [Ideal.map_pow] at h1
      have h2 : (M0.map f) ^ N0 ≤ IsLocalRing.maximalIdeal B ^ N0 :=
        Ideal.pow_right_mono Ideal.map_comap_le N0
      have h3 := h2 h1
      rw [hN0, Submodule.zero_eq_bot, Ideal.mem_bot] at h3
      exact h3
    exact RingHom.mem_ker.1 (hle hx)
  let J' : Ideal RM := J.map (algebraMap R RM)
  have hJg : ∀ x ∈ J', g x = 0 := by
    intro x hx
    have hle : J' ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hg]
      exact RingHom.mem_ker.1 (hJf hr)
    exact RingHom.mem_ker.1 (hle hx)
  have hreg' : ∀ a : RM, algebraMap R RM d * a ∈ J' → a ∈ J' := by
    intro a ha
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M0.primeCompl a
    simp only at ha ⊢
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_map_algebraMap_iff] at ha
    obtain ⟨t, ht, htJ⟩ := ha
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    refine ⟨t, ht, hreg _ ?_⟩
    rw [mul_left_comm]
    exact htJ
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal RM)
    (Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)})
  have hkey : ∀ c : RM, algebraMap R RM d * c ∈ J' ⊔ IsLocalRing.maximalIdeal RM ^ (N0 + k) →
      g c = 0 := by
    intro c hc
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 hc
    have hx1 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        (IsLocalRing.maximalIdeal RM ^ (N0 + k)) • (⊤ : Submodule RM (RM ⧸ J')) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hjy, map_add (f := _),
        Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
      exact Ideal.mem_map_of_mem _ hy
    have hx2 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)} := by
      have : Ideal.Quotient.mk J' (algebraMap R RM d * c) =
          c • Ideal.Quotient.mk J' (algebraMap R RM d) := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm c]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hx3 := hk (N0 + k) (by omega)
    have h5 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        IsLocalRing.maximalIdeal RM ^ (N0 + k - k) • (IsLocalRing.maximalIdeal RM ^ k • ⊤ ⊓
          Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)}) := by
      rw [← hx3]
      exact Submodule.mem_inf.2 ⟨hx1, hx2⟩
    rw [Nat.add_sub_cancel] at h5
    have hx4 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈ IsLocalRing.maximalIdeal RM ^ N0 •
        Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)} :=
      Submodule.smul_mono le_rfl inf_le_right h5
    obtain ⟨a, ha, hav⟩ := Submodule.mem_smul_span_singleton.1 hx4
    have hdiff : algebraMap R RM d * (c - a) ∈ J' := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mul_sub, map_sub, ← hav, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm a, sub_self]
    have hca : c - a ∈ J' := hreg' _ hdiff
    have hc : c = (c - a) + a := by ring
    rw [hc, map_add (f := _), hJg _ hca, hmaxg _ ha, add_zero]
  let I : Ideal RM := J' ⊔ IsLocalRing.maximalIdeal RM ^ (N0 + k)
  have hIg : ∀ x ∈ I, g x = 0 := by
    intro x hx
    obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), hJg _ hj, hmaxg _ (Ideal.pow_le_pow_right (by omega) hy), add_zero]
  have hIne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : RM) ∈ I := by rw [h]; exact Submodule.mem_top
    have := hIg 1 h1
    simp at this
  haveI : Nontrivial (RM ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIne
  haveI hloc : IsLocalRing (RM ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI aQ : Algebra ℚ_[l] (RM ⧸ I) := ((Ideal.Quotient.mk I).comp φ).toAlgebra
  letI aO : Algebra O (RM ⧸ I) := ((Ideal.Quotient.mk I).comp α).toAlgebra
  letI aZ : Algebra ℤ_[l] (RM ⧸ I) := ((Ideal.Quotient.mk I).comp ψ).toAlgebra
  haveI t1 : @IsScalarTower ℤ_[l] O (RM ⧸ I) _ aO.toSMul aZ.toSMul := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI t2 : IsScalarTower ℤ_[l] ℚ_[l] (RM ⧸ I) := IsScalarTower.of_algebraMap_eq (fun x => by
    show Ideal.Quotient.mk I (ψ x) = Ideal.Quotient.mk I (φ (algebraMap ℤ_[l] ℚ_[l] x))
    rw [hφ])
  let f' : R →ₐ[O] (RM ⧸ I) :=
    { (Ideal.Quotient.mk I).comp (algebraMap R RM) with commutes' := fun o => rfl }
  let q : (RM ⧸ I) →ₐ[ℚ_[l]] B :=
    { Ideal.Quotient.lift I g hIg with
      commutes' := fun c => by
        show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I (φ c)) = algebraMap ℚ_[l] B c
        rw [Ideal.Quotient.lift_mk]
        exact RingHom.congr_fun hgφ c }
  have hmaxQ : IsLocalRing.maximalIdeal (RM ⧸ I) ≤
      (IsLocalRing.maximalIdeal RM).map (Ideal.Quotient.mk I) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    by_contra hy
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hx hy
    exact hx (hy.map _)
  have hnil : IsLocalRing.maximalIdeal (RM ⧸ I) ^ (N0 + k) = ⊥ := by
    rw [eq_bot_iff]
    calc IsLocalRing.maximalIdeal (RM ⧸ I) ^ (N0 + k)
        ≤ ((IsLocalRing.maximalIdeal RM).map (Ideal.Quotient.mk I)) ^ (N0 + k) :=
          Ideal.pow_right_mono hmaxQ _
      _ = (IsLocalRing.maximalIdeal RM ^ (N0 + k)).map (Ideal.Quotient.mk I) :=
          (Ideal.map_pow _ _ _).symm
      _ ≤ I.map (Ideal.Quotient.mk I) := Ideal.map_mono le_sup_right
      _ = ⊥ := Ideal.map_quotient_self I
  haveI hart : IsArtinianRing (RM ⧸ I) := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
    exact ⟨N0 + k, by rw [hnil]; rfl⟩
  have hfin : Module.Finite ℚ_[l] (RM ⧸ I) := by
    haveI : Module.Finite ℚ_[l] ((RM ⧸ I) ⧸ Ring.jacobson (RM ⧸ I)) := by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      have hle : IsLocalRing.maximalIdeal (RM ⧸ I) ≤ (IsLocalRing.maximalIdeal B).comap q := by
        intro x hx
        rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have hx0 : x ^ (N0 + k) = 0 := by
          have := Ideal.pow_mem_pow hx (N0 + k)
          rw [hnil] at this
          exact (Ideal.mem_bot).1 this
        have := hu.pow (N0 + k)
        rw [← map_pow, hx0, map_zero] at this
        exact not_isUnit_zero this
      have hcomap : (IsLocalRing.maximalIdeal B).comap (q : (RM ⧸ I) →+* B) ≤
          IsLocalRing.maximalIdeal (RM ⧸ I) :=
        IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
      have hinj : Function.Injective (Ideal.quotientMap (IsLocalRing.maximalIdeal B)
          (q : (RM ⧸ I) →+* B) hle) := Ideal.quotientMap_injective' hcomap
      haveI : Module.Finite ℚ_[l] (B ⧸ IsLocalRing.maximalIdeal B) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[l] (IsLocalRing.maximalIdeal B)).toLinearMap
          (Ideal.Quotient.mkₐ_surjective ℚ_[l] (IsLocalRing.maximalIdeal B))
      exact Module.Finite.of_injective
        (Ideal.quotientMapₐ (IsLocalRing.maximalIdeal B) q hle).toLinearMap hinj
    exact IsSemiprimaryRing.finite_of_isArtinian ℚ_[l] (RM ⧸ I) (RM ⧸ I)
  refine ⟨RM ⧸ I, inferInstance, hloc, aQ, hfin, aO, aZ, t1, t2, f', q, ?_, ?_, ?_⟩
  · intro x hx
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk I (algebraMap R RM x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)
  · intro a
    show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I (algebraMap R RM a)) = f a
    rw [Ideal.Quotient.lift_mk, hg]
  · intro b hb
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I c) = 0
    rw [Ideal.Quotient.lift_mk]
    apply hkey
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hb
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallinePointOfSaturatedOrdIdeal
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLocPt

theorem main : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] (f : U.R →ₐ[O] B), GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f → D.IsLCr (push f U.r.hom) := by
  intro hP l _ O _ _ _ _ _ _ _ D U B _ _ _ _ _ _ _ _ f hf

  have hord : GlobalTheory.OrdLoc.ordIdeal D U.r.hom ≤ GlobalTheory.OrdLoc.IY D U := fun a ha => ⟨0, by simpa using ha⟩
  have hdiv : (l : U.R) ∣ GlobalTheory.OrdLoc.del D U.r.hom :=
    ⟨GlobalTheory.OrdLoc.dd D U.r.hom 0 * GlobalTheory.OrdLoc.dd D U.r.hom 1, by unfold GlobalTheory.OrdLoc.del; ring⟩
  have hsat : ∀ a, GlobalTheory.OrdLoc.del D U.r.hom * a ∈ GlobalTheory.OrdLoc.IY D U → a ∈ GlobalTheory.OrdLoc.IY D U := by
    rintro a ⟨n, hn⟩
    exact ⟨n + 1, by rw [pow_succ, mul_assoc]; exact hn⟩
  obtain ⟨B', _, _, _, _, _, _, _, _, f', q, hJ, hqf, hkill⟩ :=
    GlobalTheory.T.exists_finite_local_lift_of_saturated_ideal U.R (GlobalTheory.OrdLoc.IY D U) (GlobalTheory.OrdLoc.del D U.r.hom) hdiv hsat B f hf
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  obtain ⟨hnat, -, hdel⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D f' U.r.hom
  have hzero : GlobalTheory.OrdLoc.ordIdeal D (push f' U.r.hom) = ⊥ := by
    rw [← hnat, Ideal.map_eq_bot_iff_le_ker]
    exact hord.trans hJ
  have hmult' : HasMult D.η (push f' U.r.hom) := fun g => U.r.hasMult g
  have hcont' : ∀ a b, QCont l fun g => (push f' U.r.hom g).mat a b := fun a b =>
    (ptCont U.R B' f').1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)
  obtain ⟨h, ρ, κ, x, y, z, hρ, hκc, hκI, hz, hρM, hx, hy, hσd⟩ :=
    GlobalTheory.T.triangular_conj_of_ordIdeal_eq_bot D B' (push f' U.r.hom) hmult' hcont' hzero
  obtain ⟨⟨hσ, hcl⟩, -⟩ := GlobalTheory.T.chosenFrobenius_isFrobenius D
  obtain ⟨-, -, hφ, -, -⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  obtain ⟨⟨v0, hv0⟩, ⟨v1, hv1⟩⟩ := hσd hσ
  have hdel' : f' (GlobalTheory.OrdLoc.del D U.r.hom) = (l : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 0 *
      GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 1 := hdel
  have hcr := GlobalTheory.T.triangular_rank_three_crystalline_after_push hP D.HL.subtype hφ q D.e D.e_pos κ hκc hκI x y z ρ hz hρM hx hy ⟨_, hσ⟩ hcl
    (fun b hb => hkill b (by
      have hb' : ((((κ 0 / κ 1) ⟨_, hσ⟩ : B'ˣ) : B') - (cycA l l B' (GlobalTheory.OrdLoc.fr D) : B')) * b = 0 := hb
      rw [hdel', hv0]
      linear_combination ((l : B') * (v0 : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 1) * hb'))
    (fun b hb => hkill b (by
      have hb' : ((((κ 1 / κ 2) ⟨_, hσ⟩ : B'ˣ) : B') - (cycA l l B' (GlobalTheory.OrdLoc.fr D) : B')) * b = 0 := hb
      rw [hdel', hv1]
      linear_combination ((l : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 0 * (v1 : B')) * hb'))
  have hmult : HasMult D.η (push f U.r.hom) := fun g => U.r.hasMult g
  have hcont : ∀ a b, QCont l fun g => (push f U.r.hom g).mat a b := fun a b =>
    (ptCont U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)
  have hqf' : (q : B' →+* B).comp (f' : U.R →+* B') = (f : U.R →+* B) := RingHom.ext hqf
  refine GlobalTheory.T.isLCrystalline_conjBy_invariant D B (push f U.r.hom) (Matrix.GeneralLinearGroup.map (q : B' →+* B) h) hmult hcont
    ⟨(Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ, fun g => ?_, hcr⟩
  have e1 : GG.map (q : B' →+* B) (conjBy h (push f' U.r.hom) (g : GQ l)) =
      conjBy (Matrix.GeneralLinearGroup.map (q : B' →+* B) h) (push f U.r.hom) (g : GQ l) := by
    simp only [conjBy, push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
      GG.map_map, hqf']
    congr 2 <;> simp [GG.ofGL, GG.map, SemidirectProduct.map_inl]
  rw [MonoidHom.comp_apply, hρ g, ← e1]
  rfl

end GlobalTheory.OrdLocPt
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallinePointOfSaturatedOrdIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLCrystalline_point_of_saturatedOrdIdeal : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] (f : U.R →ₐ[O] B), GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f → D.IsLCr (push f U.r.hom) := by
  first | exact @GlobalTheory.OrdLocPt.main | exact GlobalTheory.OrdLocPt.main | (intros; apply GlobalTheory.OrdLocPt.main <;> assumption)
end
