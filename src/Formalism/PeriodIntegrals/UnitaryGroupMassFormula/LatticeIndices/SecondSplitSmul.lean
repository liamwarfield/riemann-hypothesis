module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedCore

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PsiKerIff
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondSplitTensorVector
noncomputable section

namespace MassDataIdxCore

open Matrix

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]

def IntV (v : n → K) : Prop := ∀ i, v i ∈ O

def IntM (M : Matrix n n K) : Prop := ∀ i j, M i j ∈ O

theorem intV_mulVec {M : Matrix n n K} {v : n → K} (hM : IntM O M) (hv : IntV O v) : IntV O (M *ᵥ v) := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

theorem intM_one : IntM O (1 : Matrix n n K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K)

def Lat : Set (n → T) :=
  {x | IntV O (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun j => t1 θ (x j)) ∧
    IntV O (((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ fun j => t2 θ (x j))}

theorem firstSplit_mulVec (M : Matrix n n T) (x : n → T) :
    (fun i => t1 θ ((M *ᵥ x) i)) = M.map (t1 θ) *ᵥ fun j => t1 θ (x j) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem secondSplit_mulVec (M : Matrix n n T) (x : n → T) :
    (fun i => t2 θ ((M *ᵥ x) i)) = M.map (t2 θ) *ᵥ fun j => t2 θ (x j) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

def tv (j : n) : n → T := fun i => θ.symm ((P : Matrix n n K) i j, 0)

theorem firstSplit_tensor_vector (j : n) : (fun i => t1 θ (tv θ P j i)) = fun i => (P : Matrix n n K) i j := by
  funext i
  simp [tv, t1]

theorem secondSplit_tensor_vector (j : n) : (fun i => t2 θ (tv θ P j i)) = 0 := by
  funext i
  simp [tv, t2]

theorem mulVec_col (M N : Matrix n n K) (j : n) : (M *ᵥ fun i => N i j) = fun i => (M * N) i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem tv_mem (j : n) : tv θ P j ∈ Lat O θ J P := by
  simp only [Lat, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [firstSplit_tensor_vector, mulVec_col]
    have hP : ((P⁻¹ : GL n K) : Matrix n n K) * (P : Matrix n n K) = 1 := by simp
    rw [hP]
    exact fun i => intM_one O i j
  · rw [secondSplit_tensor_vector, Matrix.mulVec_zero]
    exact fun _ => O.zero_mem

def conjPrime₂ (g : GL n T) : Matrix n n K :=
  ((P⁻¹ : GL n K) : Matrix n n K) * (g : Matrix n n T).map (t1 θ) * (P : Matrix n n K)

theorem conjP_int (g : GL n T) (hg : ∀ x, x ∈ Lat O θ J P → (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) :
    IntM O (conjPrime₂ θ P g) := by
  intro i j
  have h := hg _ (tv_mem O θ J P j)
  simp only [Lat, Set.mem_setOf_eq] at h
  have h1 := h.1
  rw [firstSplit_mulVec, firstSplit_tensor_vector, mulVec_col, mulVec_col] at h1
  have e : conjPrime₂ θ P g i j =
      (((P⁻¹ : GL n K) : Matrix n n K) * ((g : Matrix n n T).map (t1 θ) * (P : Matrix n n K))) i j := by
    rw [conjPrime₂, Matrix.mul_assoc]
  rw [e]
  exact h1 i

theorem conjP_mul (g h : GL n T) : conjPrime₂ θ P (g * h) = conjPrime₂ θ P g * conjPrime₂ θ P h := by
  have hP : (P : Matrix n n K) * ((P⁻¹ : GL n K) : Matrix n n K) = 1 := by simp
  simp only [conjPrime₂, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P : Matrix n n K) ((P⁻¹ : GL n K) : Matrix n n K), hP, Matrix.one_mul]

theorem conjP_one : conjPrime₂ θ P 1 = 1 := by
  simp [conjPrime₂]

end MassDataIdxCore
end
end

noncomputable section

namespace MassDataIdxCore

open Matrix

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]

def toO (M : Matrix n n K) (hM : IntM O M) : Matrix n n O := fun i j => ⟨M i j, hM i j⟩

theorem toO_map (M : Matrix n n K) (hM : IntM O M) : (toO O M hM).map (algebraMap O K) = M := by
  ext i j
  rfl

theorem map_inj : Function.Injective fun M : Matrix n n O => M.map (algebraMap O K) := by
  intro M N h
  ext i j
  have h1 := congrFun (congrFun h i) j
  exact h1

variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K) {H : Type} [Group H] (m : H →* GL n T)
  (hK : ∀ h x, x ∈ Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P)

include hK in
theorem int_of (h : H) : IntM O (conjPrime₂ θ P (m h)) :=
  conjP_int O θ J P (m h) fun x hx => (hK h x).mp hx

def psiU (h : H) : GL n O :=
  ⟨toO O _ (int_of O θ J P m hK h), toO O _ (int_of O θ J P m hK h⁻¹), by
    apply map_inj O
    simp only [Matrix.map_mul, toO_map, ← conjP_mul, ← map_mul, mul_inv_cancel, map_one, conjP_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm, by
    apply map_inj O
    simp only [Matrix.map_mul, toO_map, ← conjP_mul, ← map_mul, inv_mul_cancel, map_one, conjP_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm⟩

theorem psiU_map (h : H) : ((psiU O θ J P m hK h : GL n O) : Matrix n n O).map (algebraMap O K) =
    conjPrime₂ θ P (m h) :=
  toO_map O _ (int_of O θ J P m hK h)

def psi : H →* GL n O where
  toFun := psiU O θ J P m hK
  map_one' := by
    apply Units.ext
    apply map_inj O
    simp only [psiU_map, map_one, conjP_one, Units.val_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  map_mul' _ _ := by
    apply Units.ext
    apply map_inj O
    simp only [Units.val_mul, Matrix.map_mul, psiU_map, map_mul, conjP_mul]

theorem psi_map (h : H) : ((psi O θ J P m hK h : GL n O) : Matrix n n O).map (algebraMap O K) =
    conjPrime₂ θ P (m h) :=
  psiU_map O θ J P m hK h

theorem psi_ker_iff (c : O) (h : H) :
    (∀ i j, (((psi O θ J P m hK h : GL n O) : Matrix n n O) - 1) i j ∈ Ideal.span {c}) ↔
      ∀ i j, ∃ w ∈ O, (conjPrime₂ θ P (m h) - 1) i j = (c : K) * w := by
  have key : ∀ i j, ((((psi O θ J P m hK h : GL n O) : Matrix n n O) - 1) i j : K) =
      (conjPrime₂ θ P (m h) - 1) i j := by
    intro i j
    rw [← psi_map O θ J P m hK h]
    simp [Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro H1 i j
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (H1 i j)
    refine ⟨b, b.2, ?_⟩
    rw [← key, ← hb]
    push_cast
    ring
  · intro H1 i j
    obtain ⟨w, hw, hwe⟩ := H1 i j
    refine Ideal.mem_span_singleton'.mpr ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    rw [key]
    rw [hwe]
    push_cast
    ring

end MassDataIdxCore
end
end

noncomputable section

namespace MassDataIdxCore

open Matrix

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K)

theorem firstSplit_smul (c : K) (t : T) : t1 θ (c • t) = c * t1 θ t := by
  simp [t1, map_smul]

theorem map_sub_one (M : Matrix n n T) (f : T →+* K) : (M - 1).map f = M.map f - 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem ker_fwd (c : K) (g : GL n T)
    (hg : ∀ y ∈ Lat O θ J P, ∃ z ∈ Lat O θ J P, ((g : Matrix n n T) - 1) *ᵥ y = c • z) :
    ∀ i j, ∃ w ∈ O, (conjPrime₂ θ P g - 1) i j = c * w := by
  intro i j

  let y : n → T := fun k => θ.symm ((P : Matrix n n K) k j, 0)
  have ht1 : (fun k => t1 θ (y k)) = fun k => (P : Matrix n n K) k j := by
    funext k
    simp [y, t1]
  have ht2 : (fun k => t2 θ (y k)) = 0 := by
    funext k
    simp [y, t2]
  have hcol : (fun k => (P : Matrix n n K) k j) = (P : Matrix n n K) *ᵥ Pi.single j 1 := by
    funext k
    simp [Matrix.mulVec_single_one]
  have hPinv : ((P⁻¹ : GL n K) : Matrix n n K) * (P : Matrix n n K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hyL : y ∈ Lat O θ J P := by
    unfold Lat
    simp only [Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [ht1, hcol, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
      unfold IntV
      intro k
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    · rw [ht2, Matrix.mulVec_zero]
      unfold IntV
      intro k
      simp
  obtain ⟨z, hz, e⟩ := hg y hyL
  unfold Lat at hz
  simp only [Set.mem_setOf_eq] at hz
  have e1 : ((g : Matrix n n T).map (t1 θ) - 1) *ᵥ (fun k => (P : Matrix n n K) k j) =
      c • (fun k => t1 θ (z k)) := by
    funext k
    have h1 : t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) k) = t1 θ ((c • z) k) := by rw [e]
    rw [RingHom.map_mulVec, map_sub_one, Pi.smul_apply, firstSplit_smul] at h1
    rw [Pi.smul_apply, smul_eq_mul, ← h1, ← ht1]
    rfl
  refine ⟨(((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun k => t1 θ (z k)) i, hz.1 i, ?_⟩
  have key : (conjPrime₂ θ P g - 1) *ᵥ Pi.single j 1 =
      c • (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun k => t1 θ (z k)) := by
    have hc : (conjPrime₂ θ P g - 1 : Matrix n n K) =
        ((P⁻¹ : GL n K) : Matrix n n K) * ((g : Matrix n n T).map (t1 θ) - 1) * (P : Matrix n n K) := by
      unfold conjPrime₂
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPinv]
    rw [hc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hcol, e1, Matrix.mulVec_smul]
  have h2 := congrFun key i
  rw [Matrix.mulVec_single_one] at h2
  simpa using h2

def KerBack : Prop :=
  ∀ c : K, ∀ g : GL n T, g ∈ Formalism.UG.UJ s J → (∀ x, x ∈ Lat O θ J P ↔ (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) →
    (∀ i j, ∃ w ∈ O, (conjPrime₂ θ P g - 1) i j = c * w) →
    ∀ y ∈ Lat O θ J P, ∃ z ∈ Lat O θ J P, ((g : Matrix n n T) - 1) *ᵥ y = c • z

def SurjCore : Prop :=
  ∀ A : GL n O, ∃ g : GL n T, g ∈ Formalism.UG.UJ s J ∧ (∀ x, x ∈ Lat O θ J P ↔ (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) ∧
    conjPrime₂ θ P g = (A : Matrix n n O).map (algebraMap O K)

theorem latGL_gen (hKB : KerBack O θ s J P) (hSU : SurjCore O θ s J P) (c : O) {H : Type} [Group H]
    (m : H →* GL n T) (hmU : ∀ h, m h ∈ Formalism.UG.UJ s J)
    (hK : ∀ h x, x ∈ Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P)
    (hon : ∀ g : GL n T, g ∈ Formalism.UG.UJ s J → (∀ x, x ∈ Lat O θ J P ↔ (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) →
      ∃ h, m h = g) :
    ∃ ψ : H →* GL n O, Function.Surjective ψ ∧ ∀ h, (∀ i j, (((ψ h : GL n O) : Matrix n n O) - 1) i j ∈
      Ideal.span {c}) ↔
      ∀ y ∈ Lat O θ J P, ∃ z ∈ Lat O θ J P, (((m h : GL n T) : Matrix n n T) - 1) *ᵥ y = (c : K) • z := by
  refine ⟨psi O θ J P m hK, ?_, ?_⟩
  · intro A
    obtain ⟨g, hgU, hgL, hgA⟩ := hSU A
    obtain ⟨h, rfl⟩ := hon g hgU hgL
    refine ⟨h, Units.ext (map_inj O ?_)⟩
    simp only
    rw [psi_map, hgA]
  · intro h
    rw [psi_ker_iff]
    constructor
    · intro hw
      exact hKB (c : K) (m h) (hmU h) (hK h) hw
    · intro hl
      exact ker_fwd O θ J P (c : K) (m h) hl

end MassDataIdxCore
