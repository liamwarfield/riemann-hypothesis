module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.GenericMatrixEvaluationDet

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.SubstitutionPreservesOfGenerators
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.PropertySubmoduleWeightEntryComponent
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.LaurentCoefficientsMemProperty
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialStableContainsComponents
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def genericMatrixRootWeights (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  (genMat R n).map fun x => algebraMap _ (GLCoord R n) x

def genericMatrixInverse (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  ((genMat R n).adjugate).map fun x =>
    IsLocalization.Away.invSelf (genMat R n).det * algebraMap _ (GLCoord R n) x

def coefficientMap (R : Type*) [CommRing R] (n : ℕ) : R →+* GLCoord R n :=
  (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).comp MvPolynomial.C

def genericTranslate {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) (GLCoord R n) :=
  matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n) G


open Classical in
def weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ F.support.filter (fun m => wtS LL S m = nu), monomial m (F.coeff m)

def TorusActsThroughWeight : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (φ : R →+* B) (D : Fin n → Bˣ) (m : ι × Fin n →₀ ℕ) (c : R),
      matrixSubst LL S φ (Matrix.diagonal fun a => ((D a : Bˣ) : B)) (Matrix.diagonal fun a => (((D a)⁻¹ : Bˣ) : B))
        (monomial m c) = monomial m (φ c * ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B))

def BinomialStableContainsComponents : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (W : Submodule R (MvPolynomial (ι × Fin n) R)), (∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) →
    ∀ x ∈ W, ∀ nu, weightComponent LL S nu x ∈ W

def TwistExponentsAreWeightEntries : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R),
      sDegs LL S j G = (genericTranslate LL S G).support.image (fun m => wtS LL S m j)

def GenericMonomialsSpecialise : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1), g0 * g0inv = 1 →
    ∀ G : MvPolynomial (ι × Fin n) R, (matrixSubst LL S φ g0inv g0 G).support ⊆ (genericTranslate LL S G).support

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def laurentUnit (B : Type*) [CommRing B] : (LaurentPolynomial B)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
    by rw [← LaurentPolynomial.T_add]; simp⟩

theorem laurentUnit_zpow (B : Type*) [CommRing B] (w : ℤ) :
    (((laurentUnit B) ^ w : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T w := by
  have hinv : (((laurentUnit B)⁻¹ : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T (-1) := rfl
  have hval : (((laurentUnit B) : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  induction w using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, hval, ← LaurentPolynomial.T_add]
  | pred i ih => rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add]; rfl

theorem binomialOperator_monomial {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : R) :
    binomPol R LL S a k (monomial m c) = monomial m (c * ((Ring.choose (wtS LL S m a) k : ℤ) : R)) := by
  have hm : (monomial m c : MvPolynomial (ι × Fin n) R) = c • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, LinearMap.map_smul]
  simp only [binomPol]
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι) (j : Fin n)
  (Pr : ℤ → Prop)

def weightEntryPropertySubmodule : Submodule R (MvPolynomial (ι × Fin n) R) where
  carrier := {y | ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1),
    g0 * g0inv = 1 → ∀ m ∈ (matrixSubst LL S φ g0inv g0 y).support, Pr (wtS LL S m j)}
  zero_mem' := by
    intro k1 _ φ g0 g0inv _ m hm
    simp at hm
  add_mem' := by
    classical
    intro x y hx hy k1 _ φ g0 g0inv h m hm
    rw [map_add (f := _)] at hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h1 | h1
    · exact hx k1 φ g0 g0inv h m h1
    · exact hy k1 φ g0 g0inv h m h1
  smul_mem' := by
    intro c y hy k1 _ φ g0 g0inv h m hm
    rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, ← MvPolynomial.smul_eq_C_mul] at hm
    exact hy k1 φ g0 g0inv h m (MvPolynomial.support_smul hm)

theorem laurent_coefficients_mem_property (y : MvPolynomial (ι × Fin n) R) (K : Finset ℤ) (yk : ℤ → MvPolynomial (ι × Fin n) R)
    (hh : ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1), ∃ h h' : Matrix (Fin n) (Fin n) (LaurentPolynomial k1),
      h' * h = 1 ∧ matrixSubst LL S (LaurentPolynomial.C.comp φ) h h' y =
        ∑ k ∈ K, C (LaurentPolynomial.T k) * MvPolynomial.map (LaurentPolynomial.C.comp φ) (yk k))
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : ∀ k ∈ K, yk k ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  intro k hk k1 _ φ g0 g0inv hg m hm
  obtain ⟨h, h', hh1, hE⟩ := hh k1 φ
  set ψ : k1 →+* LaurentPolynomial k1 := LaurentPolynomial.C with hψ
  have h2 : g0.map ψ * g0inv.map ψ = 1 := by
    rw [← Matrix.map_mul, hg, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]
  have hinv : (h' * g0.map ψ) * (g0inv.map ψ * h) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g0.map ψ), h2, Matrix.one_mul, hh1]
  apply hy (LaurentPolynomial k1) (ψ.comp φ) (h' * g0.map ψ) (g0inv.map ψ * h) hinv m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← matrixSubst_comp, hE, map_sum]
  have hA : ∀ k', matrixSubst LL S (RingHom.id _) (g0inv.map ψ) (g0.map ψ)
      (C (LaurentPolynomial.T k') * MvPolynomial.map (ψ.comp φ) (yk k')) =
      C (LaurentPolynomial.T k') * MvPolynomial.map ψ (matrixSubst LL S φ g0inv g0 (yk k')) := by
    intro k'
    rw [map_mul, matrixSubst_C, RingHom.id_apply, matrixSubst_map, map_matrixSubst]
  simp_rw [hA]
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro hz
  apply hm
  rw [MvPolynomial.coeff_sum] at hz
  simp_rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hz
  have hz2 := congrArg (fun p : LaurentPolynomial k1 => p.coeff k) hz
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hz2
  have hT : ∀ k' (c : k1), (LaurentPolynomial.T k' * ψ c).coeff k = if k' = k then c else 0 := by
    intro k' c
    rw [hψ, mul_comm, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp_rw [hT, Finset.sum_ite_eq' K k] at hz2
  simpa [hk] using hz2

end fwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι) (j : Fin n)
  (Pr : ℤ → Prop)

theorem propertySubmodule_dividedPower_stable (hT : TransvectionExpansion) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : divPow R LL S a b k y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  have key := laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y
    ((Finset.range (y.totalDegree + k + 1)).image (fun i : ℕ => (i : ℤ)))
    (fun z => divPow R LL S a b z.toNat y) ?_ hy
  · have hk := key (k : ℤ) (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩)
    simpa using hk
  intro k1 _ φ
  refine ⟨Matrix.transvection a b (LaurentPolynomial.T 1), Matrix.transvection a b (-LaurentPolynomial.T 1),
    ?_, ?_⟩
  · rw [Matrix.transvection_mul_transvection_same (h := hab), neg_add_cancel, Matrix.transvection_zero]
  · rw [hT R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) a b hab (LaurentPolynomial.T 1) y
      (y.totalDegree + k + 1) (by omega)]
    rw [Finset.sum_image (fun x _ z _ h => by exact_mod_cast h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [LaurentPolynomial.T_pow]


open Classical in
def weightEntryComponent (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ y.support.filter (fun m => wtS LL S m a = w), monomial m (y.coeff m)

private theorem laurent_T_unit_zpow_eq_T {k1 : Type} [CommRing k1] (z : ℤ) :
    (((⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
      by rw [← LaurentPolynomial.T_add]; simp⟩ : (LaurentPolynomial k1)ˣ) ^ z :
        (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1) = LaurentPolynomial.T z := by
  induction z using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, ← LaurentPolynomial.T_add]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih, Units.inv_mk, ← LaurentPolynomial.T_add]
    rfl

theorem propertySubmodule_weightEntryComponent (hTo : TorusActsThroughWeight) (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : weightEntryComponent LL S a w y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  set K : Finset ℤ := y.support.image (fun m => wtS LL S m a) with hK
  by_cases hw : w ∈ K
  swap
  · have h0 : weightEntryComponent LL S a w y = 0 := by
      unfold weightEntryComponent
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_filter] at hm
      exact absurd (Finset.mem_image.2 ⟨m, hm.1, hm.2⟩) hw
    rw [h0]
    exact Submodule.zero_mem _
  refine laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y K (fun w => weightEntryComponent LL S a w y) ?_ hy w hw
  intro k1 _ φ
  let u : (LaurentPolynomial k1)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let D : Fin n → (LaurentPolynomial k1)ˣ := fun b => if b = a then u else 1
  refine ⟨Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1),
    Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1), ?_, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal]
    simp
  ·
    have hmono : ∀ m : ι × Fin n →₀ ℕ, ∀ c : R,
        matrixSubst LL S (LaurentPolynomial.C.comp φ)
          (Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1))
          (Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1))
          (monomial m c) = C (LaurentPolynomial.T (wtS LL S m a)) *
            monomial m (LaurentPolynomial.C (φ c)) := by
      intro m c
      rw [hTo R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) D m c, C_mul_monomial]
      congr 1
      have hp : (∏ b, D b ^ (wtS LL S m b) : (LaurentPolynomial k1)ˣ) = u ^ (wtS LL S m a) := by
        rw [Finset.prod_eq_single a (fun b _ hb => by simp [D, hb]) (fun h => absurd (Finset.mem_univ a) h)]
        simp [D]
      rw [hp, laurent_T_unit_zpow_eq_T, mul_comm]
      rfl
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [hmono]
    unfold weightEntryComponent
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [map_sum, MvPolynomial.map_monomial, Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := K) (g := fun m => wtS LL S m a)
      (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    rw [hm.2]
    rfl

theorem propertySubmodule_binomial_stable (hTo : TorusActsThroughWeight) (a : Fin n) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : binomPol R LL S a k y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical

  have hdec : binomPol R LL S a k y = ∑ w ∈ y.support.image (fun m => wtS LL S m a),
      (((Ring.choose w k : ℤ) : R)) • weightEntryComponent LL S a w y := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    unfold weightEntryComponent
    simp_rw [Finset.smul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := y.support.image (fun m => wtS LL S m a))
      (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    have h1 : monomial m (y.coeff m) = (y.coeff m) • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, binomPol, Module.Basis.constr_basis, MvPolynomial.coe_basisMonomials,
      MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, hm.2]
    congr 1
    simp only [smul_eq_mul]
    ring
  rw [hdec]
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (propertySubmodule_weightEntryComponent LL S j Pr hTo a w y hy)

theorem weights_property_of_generic_translate (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hSp : GenericMonomialsSpecialise) (G : MvPolynomial (ι × Fin n) R)
    (hG : ∀ m ∈ (genericTranslate LL S G).support, Pr (wtS LL S m j)) :
    ∀ mu ∈ polWts LL S (polGenSub R LL S G), Pr (mu j) := by
  classical

  have hG0 : G ∈ weightEntryPropertySubmodule LL S j Pr := by
    intro k1 _ φ g0 g0inv h m hm
    exact hG m (hSp R ι LL n S k1 φ g0 g0inv h G hm)

  have hclos : ∀ u ∈ Submonoid.closure (polUZgens R LL S),
      ∀ x ∈ weightEntryPropertySubmodule LL S j Pr, u x ∈ weightEntryPropertySubmodule LL S j Pr := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu =>
      rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
      · exact fun x hx => propertySubmodule_dividedPower_stable LL S j Pr hT a b hab k x hx
      · exact fun x hx => propertySubmodule_binomial_stable LL S j Pr hTo a k x hx
    | one => exact fun x hx => hx
    | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)
  have hsub : polGenSub R LL S G ≤ weightEntryPropertySubmodule LL S j Pr := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨u, hu, rfl⟩
    exact hclos u hu G hG0
  rintro mu ⟨x, hx, hx0, hxw⟩
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hx0
  rw [← MvPolynomial.mem_support_iff] at hm
  have h1 := hsub hx R (RingHom.id R) 1 1 (mul_one 1) m
  rw [matrixSubst_one, MvPolynomial.map_id] at h1
  rw [← hxw m hm]
  exact h1 hm

end fwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem coeff_weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (weightComponent LL S nu F) m = if wtS LL S m = nu then AddMonoidAlgebra.coeff F m else 0 := by
  classical
  unfold weightComponent
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases h1 : wtS LL S m = nu <;> by_cases h2 : AddMonoidAlgebra.coeff F m = 0 <;> simp [h1, h2]

section bwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)
  {L : Type} [Field L] (φ : R →+* L) (W : Submodule R (MvPolynomial (ι × Fin n) R))

def scalarExtension : Submodule L (MvPolynomial (ι × Fin n) L) :=
  Submodule.span L ((MvPolynomial.map φ) '' (W : Set (MvPolynomial (ι × Fin n) R)))

def SubstitutionPreservesExtension (h h' : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ x ∈ scalarExtension φ W, matrixSubst LL S (RingHom.id L) h h' x ∈ scalarExtension φ W

theorem scalarExtension_monomial_weights (hGr : BinomialStableContainsComponents) (hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) :
    ∀ z ∈ scalarExtension φ W, ∀ m ∈ z.support, wtS LL S m ∈ polWts LL S W := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    intro m hm
    have hm' : m ∈ w.support := MvPolynomial.support_map_subset φ w hm
    simp only [polWts, Set.mem_setOf_eq]
    refine ⟨weightComponent LL S (wtS LL S m) w, hGr R ι LL n S W hW2 w hw _, ?_, ?_⟩
    · intro h0
      have e := congrArg (AddMonoidAlgebra.coeff · m) h0
      rw [coeff_weightComponent, if_pos rfl, MvPolynomial.coeff_zero] at e
      exact (MvPolynomial.mem_support_iff.1 hm') e
    · intro m' hm''
      rw [MvPolynomial.mem_support_iff, coeff_weightComponent] at hm''
      by_contra hne
      exact hm'' (if_neg hne)
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    classical
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

end bwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem genericMatrixInverse_eq_adjugate (R : Type*) [CommRing R] (n : ℕ) :
    genericMatrixInverse R n = (IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det) •
      ((genMat R n).adjugate.map (algebraMap _ (GLCoord R n))) := by
  ext i j
  simp [genericMatrixInverse, Matrix.smul_apply]

theorem genericMatrixInverse_mul (R : Type*) [CommRing R] (n : ℕ) : genericMatrixInverse R n * genericMatrixRootWeights R n = 1 := by
  rw [genericMatrixInverse_eq_adjugate, genericMatrixRootWeights, Matrix.smul_mul, ← Matrix.map_mul, Matrix.adjugate_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp

theorem genericMatrix_mul_inverse (R : Type*) [CommRing R] (n : ℕ) : genericMatrixRootWeights R n * genericMatrixInverse R n = 1 := by
  rw [genericMatrixInverse_eq_adjugate, genericMatrixRootWeights, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp

section asm

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)

theorem generated_submodule_stable (G : MvPolynomial (ι × Fin n) R) (g : MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R)
    (hg : g ∈ polUZgens R LL S) : ∀ x ∈ polGenSub R LL S G, g x ∈ polGenSub R LL S G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact Submodule.subset_span ⟨g * u, Submonoid.mul_mem _ (Submonoid.subset_closure hg) hu, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

theorem self_mem_generated_submodule (G : MvPolynomial (ι × Fin n) R) : G ∈ polGenSub R LL S G := Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩

theorem generic_translate_weights_mem (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents) (G : MvPolynomial (ι × Fin n) R) :
    ∀ m ∈ (genericTranslate LL S G).support, wtS LL S m ∈ polWts LL S (polGenSub R LL S G) := by
  classical
  set W := polGenSub R LL S G with hWdef
  have hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W := fun a k x hx =>
    generated_submodule_stable LL S G (binomPol R LL S a k) (Or.inr ⟨a, k, rfl⟩) x hx
  have hWd : ∀ a b k, a ≠ b → ∀ x ∈ W, divPow R LL S a b k x ∈ W := fun a b k hab x hx =>
    generated_submodule_stable LL S G (divPow R LL S a b k) (Or.inl ⟨a, b, k, hab, rfl⟩) x hx
  haveI hdom : IsDomain (GLCoord R n) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Matrix.det_mvPolynomialX_ne_zero (Fin n) R : (genMat R n).det ≠ 0))
  let K := FractionRing (GLCoord R n)
  let ψ : GLCoord R n →+* K := algebraMap (GLCoord R n) K
  have hψ : Function.Injective ψ := IsFractionRing.injective (GLCoord R n) K
  let φ : R →+* K := ψ.comp (coefficientMap R n)
  have good_of : ∀ h h' : Matrix (Fin n) (Fin n) K,
      (∀ w ∈ W, matrixSubst LL S φ h h' w ∈ scalarExtension φ W) → SubstitutionPreservesExtension LL S φ W h h' := by
    intro h h' hw
    unfold SubstitutionPreservesExtension
    intro x hx
    rw [scalarExtension] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hwW, rfl⟩ := hy
      rw [matrixSubst_map]
      exact hw w hwW
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, RingHom.id_apply, ← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ c hy
  have good_mul : ∀ h1 h1' h2 h2' : Matrix (Fin n) (Fin n) K, SubstitutionPreservesExtension LL S φ W h1 h1' →
      SubstitutionPreservesExtension LL S φ W h2 h2' → SubstitutionPreservesExtension LL S φ W (h1 * h2) (h2' * h1') := by
    intro h1 h1' h2 h2' g1 g2
    unfold SubstitutionPreservesExtension at g1 g2 ⊢
    intro x hx
    rw [← matrixSubst_comp]
    exact g1 _ (g2 x hx)
  have good_tr : ∀ (a b : Fin n), a ≠ b → ∀ t : K,
      SubstitutionPreservesExtension LL S φ W (Matrix.transvection a b t) (Matrix.transvection a b (-t)) := by
    intro a b hab t
    apply good_of
    intro w hw
    rw [hT R K ι LL n S φ a b hab t w (w.totalDegree + 1) (Nat.lt_succ_self _)]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hWd a b k hab w hw, rfl⟩)
  have good_diag : ∀ u : Fin n → Kˣ, SubstitutionPreservesExtension LL S φ W (Matrix.diagonal fun a => ((u a : Kˣ) : K))
      (Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K)) := by
    intro u
    apply good_of
    intro w hw
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.as_sum w, map_sum]
    have hmono : ∀ m ∈ w.support, matrixSubst LL S φ (Matrix.diagonal fun a => ((u a : Kˣ) : K))
        (Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K)) (MvPolynomial.monomial m (w.coeff m)) =
        (((∏ a, u a ^ (wtS LL S m a) : Kˣ) : K)) • MvPolynomial.map φ (MvPolynomial.monomial m (w.coeff m)) := by
      intro m _
      rw [hTo R K ι LL n S φ u m (w.coeff m), MvPolynomial.map_monomial, MvPolynomial.smul_monomial,
        smul_eq_mul]
      congr 1
      exact mul_comm _ _
    rw [Finset.sum_congr rfl hmono,
      ← Finset.sum_fiberwise_of_maps_to (g := fun m => wtS LL S m) (t := w.support.image (fun m => wtS LL S m))
        (fun m hm => Finset.mem_image_of_mem _ hm)]
    refine Submodule.sum_mem _ fun ν _ => ?_
    convert Submodule.smul_mem _ (((∏ a, u a ^ (ν a) : Kˣ) : K))
      (show MvPolynomial.map φ (weightComponent LL S ν w) ∈ scalarExtension φ W by
        rw [scalarExtension]
        exact Submodule.subset_span ⟨_, hGr R ι LL n S W hW2 w hw ν, rfl⟩) using 1
    unfold weightComponent
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr ?_ fun m hm => ?_
    · ext m
      simp
    · rw [(Finset.mem_filter.mp hm).2]
  have good_list : ∀ l : List (Matrix.TransvectionStruct (Fin n) K),
      SubstitutionPreservesExtension LL S φ W (l.map Matrix.TransvectionStruct.toMatrix).prod
        (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod ∧
      (l.map Matrix.TransvectionStruct.toMatrix).prod *
        (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = 1 ∧
      (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod *
        (l.map Matrix.TransvectionStruct.toMatrix).prod = 1 := by
    intro l
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, List.reverse_nil]
      refine ⟨?_, mul_one 1, mul_one 1⟩
      unfold SubstitutionPreservesExtension
      intro x hx
      rw [matrixSubst_one, MvPolynomial.map_id]
      exact hx
    | cons t l ih =>
      obtain ⟨hg, h1, h2⟩ := ih
      have ht1 : t.toMatrix * Matrix.transvection t.i t.j (-t.c) = 1 := by
        exact t.mul_inv
      have ht2 : Matrix.transvection t.i t.j (-t.c) * t.toMatrix = 1 := by
        exact t.inv_mul
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
        List.map_nil, List.prod_nil, mul_one]
      generalize (l.map Matrix.TransvectionStruct.toMatrix).prod = P at hg h1 h2 ⊢
      generalize (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = P' at hg h1 h2 ⊢
      refine ⟨good_mul _ _ _ _ (good_tr t.i t.j t.hij t.c) hg, ?_, ?_⟩
      · rw [mul_assoc, ← mul_assoc P, h1, one_mul, ht1]
      · rw [mul_assoc, ← mul_assoc (Matrix.transvection t.i t.j (-t.c)), ht2, one_mul, h2]
  set A : Matrix (Fin n) (Fin n) K := (genericMatrixInverse R n).map ψ with hAdef
  set A' : Matrix (Fin n) (Fin n) K := (genericMatrixRootWeights R n).map ψ with hA'def
  have hAA' : A * A' = 1 := by
    rw [hAdef, hA'def, ← Matrix.map_mul, genericMatrixInverse_mul, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have hA'A : A' * A = 1 := by
    rw [hAdef, hA'def, ← Matrix.map_mul, genericMatrix_mul_inverse, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  obtain ⟨l1, l2, D, hAdec⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  obtain ⟨g1, e1, f1⟩ := good_list l1
  obtain ⟨g2, e2, f2⟩ := good_list l2
  generalize (l1.map Matrix.TransvectionStruct.toMatrix).prod = P1 at hAdec g1 e1 f1
  generalize (l1.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = P1' at g1 e1 f1
  generalize (l2.map Matrix.TransvectionStruct.toMatrix).prod = P2 at hAdec g2 e2 f2
  generalize (l2.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = P2' at g2 e2 f2
  have hdiag : Matrix.diagonal D = P1' * A * P2' := by
    rw [hAdec, ← mul_assoc, ← mul_assoc, f1, one_mul, mul_assoc, e2, mul_one]
  have hDinv : Matrix.diagonal D * (P2 * A' * P1) = 1 := by
    rw [hdiag]
    simp only [mul_assoc]
    rw [← mul_assoc P2' P2, f2, one_mul, ← mul_assoc A A', hAA', one_mul, f1]
  have hD0 : ∀ a, D a ≠ 0 := by
    intro a h0
    have h3 := congrFun (congrFun hDinv a) a
    rw [Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h3
    exact zero_ne_one h3
  let u : Fin n → Kˣ := fun a => Units.mk0 (D a) (hD0 a)
  have gd := good_diag u
  have hu1 : (Matrix.diagonal fun a => ((u a : Kˣ) : K)) = Matrix.diagonal D := by
    ext i j
    simp [u, Matrix.diagonal_apply]
  have hu2 : (Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K)) = Matrix.diagonal fun a => (D a)⁻¹ := by
    ext i j
    simp [u, Matrix.diagonal_apply]
  rw [hu1, hu2] at gd
  have gA := good_mul _ _ _ _ (good_mul _ _ _ _ g1 gd) g2
  have hX : P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1') = A' := by
    have hdd : Matrix.diagonal D * Matrix.diagonal (fun a => (D a)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      exact mul_inv_cancel₀ (hD0 a)
    have hAX : A * (P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1')) = 1 := by
      rw [hAdec]
      simp only [mul_assoc]
      rw [← mul_assoc P2 P2', e2, one_mul, ← mul_assoc (Matrix.diagonal D), hdd, one_mul, e1]
    calc P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1')
        = (A' * A) * (P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1')) := by rw [hA'A, one_mul]
      _ = A' := by rw [mul_assoc, hAX, mul_one]
  rw [← hAdec, hX] at gA
  have hGW : MvPolynomial.map φ G ∈ scalarExtension φ W := Submodule.subset_span ⟨G, self_mem_generated_submodule LL S G, rfl⟩
  have hHK : MvPolynomial.map ψ (genericTranslate LL S G) ∈ scalarExtension φ W := by
    rw [genericTranslate, map_matrixSubst, ← hAdef, ← hA'def, ← matrixSubst_map]
    exact gA _ hGW
  intro m hm
  have hsupp : m ∈ (MvPolynomial.map ψ (genericTranslate LL S G)).support := by
    rwa [MvPolynomial.support_map_of_injective _ hψ]
  exact scalarExtension_monomial_weights (LL := LL) (S := S) (φ := φ) (W := W) hGr hW2 _ hHK m hsupp

end asm

theorem generated_module_weight_lemma_of_interfaces (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents) (hSt : TwistExponentsAreWeightEntries) (hSp : GenericMonomialsSpecialise) :
    GeneratedModuleWeightDescription := by
  intro R _ ι _ LL n _ S
  refine ⟨fun G θ => ?_, fun G M => ?_⟩
  · rw [valS, hSt R ι LL n S (lastIdx n) G, Finset.le_inf_iff]
    constructor
    · intro h
      exact weights_property_of_generic_translate (LL := LL) (S := S) (j := lastIdx n) (Pr := fun z => θ ≤ z) hT hTo hSp G
        (fun m hm => by
          have := h _ (Finset.mem_image_of_mem _ hm)
          simpa using this)
    · intro h k hk
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      have := h _ (generic_translate_weights_mem LL S hT hTo hGr G m hm)
      simpa using this
  · rw [lam1S, hSt R ι LL n S 0 G, Finset.sup_le_iff]
    constructor
    · intro h
      exact weights_property_of_generic_translate (LL := LL) (S := S) (j := 0) (Pr := fun z => z ≤ M) hT hTo hSp G
        (fun m hm => by
          have := h _ (Finset.mem_image_of_mem _ hm)
          simpa using this)
    · intro h k hk
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      have := h _ (generic_translate_weights_mem LL S hT hTo hGr G m hm)
      simpa using this

end Formalism.MainNotions.G.GLWeightTheory
