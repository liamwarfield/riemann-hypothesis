module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisIntKQ
open Matrix GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.IntBasisKQ
open ReciprocityTheory.DiscreteGroups.LocalClassField

variable (p : ℕ) [Fact p.Prime]

theorem exists_basis_OK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    ∃ (ι : Type) (_ : Fintype ι) (β : Module.Basis ι ℚ_[p] K),
      ∀ x : K, x ∈ OK p K ↔ ∀ i, ‖β.repr x i‖ ≤ 1 := by
  letI := zpAlgOK p K
  haveI := isScalarTower_zp_OK p K
  haveI := isIntegralClosure_OK p K
  haveI := isTorsionFree_zp_K p K
  haveI : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  haveI : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (OK p K) (nonZeroDivisors ℤ_[p])) K :=
    IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K (OK p K)
  let β₀ := Module.finBasis ℤ_[p] (OK p K)
  let β := β₀.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) K
  refine ⟨_, inferInstance, β, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · have e : x = algebraMap (OK p K) K ⟨x, hx⟩ := rfl
    rw [e, Module.Basis.localizationLocalization_repr_algebraMap]
    exact (β₀.repr ⟨x, hx⟩ i).2
  · let z : _ → ℤ_[p] := fun i => ⟨β.repr x i, hx i⟩
    have hx' : x = algebraMap (OK p K) K (∑ i, z i • β₀ i) := by
      conv_lhs => rw [← β.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply ℤ_[p] (OK p K) K,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, ← Module.Basis.localizationLocalization_apply ℚ_[p]
        (nonZeroDivisors ℤ_[p]) K]
      rfl
    rw [hx']
    exact (∑ i, z i • β₀ i).2

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

variable (p : ℕ) [Fact p.Prime]

section Tensor

variable {A B : Type} [CommRing A] [Algebra ℚ_[p] A] [CommRing B] [Algebra ℚ_[p] B]
  {ι κ : Type} [Fintype ι] [Fintype κ] (β : Module.Basis ι ℚ_[p] A) (γ : Module.Basis κ ℚ_[p] B)
  (OA : Subring A) (OB : Subring B)

def IntCoord (z : A ⊗[ℚ_[p]] B) : Prop := ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1

variable {p β γ}

theorem intCoord_add {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) :
    IntCoord p β γ (z + w) := fun k => by
  rw [map_add (f := _), Finsupp.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz k) (hw k))

theorem intCoord_smul {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    IntCoord p β γ (c • z) := fun k => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hz k)

theorem intCoord_neg {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) : IntCoord p β γ (-z) := fun k => by
  rw [map_neg, Finsupp.neg_apply, norm_neg]
  exact hz k

theorem intCoord_zero : IntCoord p β γ (0 : A ⊗[ℚ_[p]] B) := fun k => by simp

theorem intCoord_sum {σ : Type} (s : Finset σ) (f : σ → A ⊗[ℚ_[p]] B) (h : ∀ t ∈ s, IntCoord p β γ (f t)) :
    IntCoord p β γ (∑ t ∈ s, f t) := by
  induction s using Finset.induction_on with
  | empty => simpa using intCoord_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intCoord_add (h a (Finset.mem_insert_self _ _)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

variable {OA OB}

theorem intCoord_tmul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {a : A} {b : B} (ha : a ∈ OA) (hb : b ∈ OB) : IntCoord p β γ (a ⊗ₜ[ℚ_[p]] b) := fun ⟨i, j⟩ => by
  rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ((hB b).1 hb j) (norm_nonneg _) ((hA a).1 ha i)

theorem basis_mem (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (i : ι) : β i ∈ OA :=
  (hA _).2 fun i' => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem intCoord_mul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) : IntCoord p β γ (z * w) := by
  set b := β.tensorProduct γ
  have e : z * w = ∑ k, ∑ l, (b.repr z k * b.repr w l) • (b k * b l) := by
    conv_lhs => rw [← b.sum_repr z, ← b.sum_repr w]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm]
  rw [e]
  refine intCoord_sum _ _ fun k _ => intCoord_sum _ _ fun l _ => intCoord_smul ?_ ?_
  · obtain ⟨i, j⟩ := k
    obtain ⟨i', j'⟩ := l
    simp only [b, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.tmul_mul_tmul]
    exact intCoord_tmul hA hB (OA.mul_mem (basis_mem hA i) (basis_mem hA i'))
      (OB.mul_mem (basis_mem hB j) (basis_mem hB j'))
  · rw [norm_mul]
    exact mul_le_one₀ (hz k) (norm_nonneg _) (hw l)

theorem mem_closure_iff (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    (z : A ⊗[ℚ_[p]] B) :
    z ∈ Subring.closure (Set.range (fun a : OA => (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) a) ∪
      Set.range (fun b : OB => (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) b)) ↔
      ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1 := by
  let S : Subring (A ⊗[ℚ_[p]] B) :=
    { carrier := {z | IntCoord p β γ z}
      mul_mem' := intCoord_mul hA hB
      one_mem' := intCoord_tmul hA hB OA.one_mem OB.one_mem
      add_mem' := intCoord_add
      zero_mem' := intCoord_zero
      neg_mem' := intCoord_neg }
  constructor
  · intro hz
    refine (Subring.closure_le (t := S)).2 (Set.union_subset ?_ ?_) hz
    · rintro _ ⟨a, rfl⟩
      exact intCoord_tmul hA hB a.2 OB.one_mem
    · rintro _ ⟨b, rfl⟩
      exact intCoord_tmul hA hB OA.one_mem b.2
  · intro hz
    rw [← (β.tensorProduct γ).sum_repr z]
    refine Subring.sum_mem _ fun ⟨i, j⟩ _ => ?_
    rw [Module.Basis.tensorProduct_apply, TensorProduct.smul_tmul',
      show ((β.tensorProduct γ).repr z (i, j) • β i) ⊗ₜ[ℚ_[p]] γ j =
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) ((β.tensorProduct γ).repr z (i, j) • β i) *
        (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) (γ j) by
          rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨_, ?_⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, basis_mem hB j⟩, rfl⟩))
    refine (hA _).2 fun i' => ?_
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, norm_mul]
    refine mul_le_one₀ (hz (i, j)) (norm_nonneg _) ?_
    split_ifs <;> simp

end Tensor

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

theorem exists_basis_intKQ : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℚ_[p] (KQ p K r)),
      ∀ x, x ∈ intKQ p K r ↔ ∀ i, ‖b.repr x i‖ ≤ 1 := by
  intro p _ K hK r hr
  obtain ⟨ι₁, _, β, hβ⟩ := exists_basis_OK p K hK
  obtain ⟨ι₂, _, γ, hγ⟩ := exists_basis_OK p (Qr p r)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr)
  refine ⟨ι₁ × ι₂, inferInstance, β.tensorProduct γ, fun x => ?_⟩
  exact mem_closure_iff (OA := GlobalTheory.LKLoc.intK p K) (OB := GlobalTheory.LKLoc.intR p (Q0 p) r) hβ hγ x

end GlobalTheory.IntBasisKQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceKq
open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKMid

theorem t2Space_kq {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    T2Space (KQ p K r) := by
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  let b := Module.Free.chooseBasis ℚ_[p] (KQ p K r)
  let φ : KQ p K r →ₗ[ℚ_[p]] (Module.Free.ChooseBasisIndex ℚ_[p] (KQ p K r) → ℚ_[p]) :=
    Finsupp.lcoeFun ∘ₗ b.repr.toLinearMap
  have hinj : Function.Injective φ := by
    intro x y h
    apply b.repr.injective
    exact DFunLike.coe_injective h
  exact T2Space.of_injective_continuous hinj (IsModuleTopology.continuous_of_linearMap φ)

end GlobalTheory.LKMid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulNormLeOne
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem isOpen_of_padicLattice {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] [TopologicalSpace V] [IsModuleTopology ℚ_[p] V]
    (A : AddSubgroup V) (hA : ∀ c : ℚ_[p], ‖c‖ ≤ 1 → ∀ v ∈ A, c • v ∈ A)
    (hN : ∀ v : V, ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ A) : IsOpen (A : Set V) := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[p] V
  let b := Module.finBasis ℚ_[p] V
  choose N hN' using fun i => hN (b i)
  set M := ∑ i, N i with hMdef
  have hp1 : ‖(p : ℚ_[p])‖ ≤ 1 := Padic.norm_p_lt_one.le
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hb : ∀ i, (p : ℚ_[p]) ^ M • b i ∈ A := by
    intro i
    have hle : N i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact hA _ (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1) _ (hN' i)
  have hpos : 0 < ‖(p : ℚ_[p]) ^ M‖ := norm_pos_iff.2 (pow_ne_zero _ hp0)
  let U : Set V := ⋂ i, (fun v => b.coord i v) ⁻¹' Metric.closedBall 0 ‖(p : ℚ_[p]) ^ M‖
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hpos.ne').preimage
      (IsModuleTopology.continuous_of_linearMap (b.coord i))
  have hUA : U ⊆ A := by
    intro v hv
    simp only [U, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hv
    rw [← b.sum_repr v]
    refine A.sum_mem fun i _ => ?_
    have : b.repr v i • b i = (b.repr v i / (p : ℚ_[p]) ^ M) • ((p : ℚ_[p]) ^ M • b i) := by
      rw [smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hp0)]
    rw [this]
    refine hA _ ?_ _ (hb i)
    rw [norm_div, div_le_one hpos]
    exact hv i
  have h0 : (0 : V) ∈ U := by
    simp [U, hpos.le]
  exact AddSubgroup.isOpen_of_mem_nhds A (Filter.mem_of_superset (hU.mem_nhds h0) hUA)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem exists_pow_smul_norm_le_one (z : PadicAlgCl p) : ∃ N : ℕ, ‖(p : ℚ_[p]) ^ N • z‖ ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hz') (Padic.norm_p_lt_one (p := p))
  refine ⟨N, ?_⟩
  rw [Algebra.smul_def, norm_mul, map_pow, norm_pow, PadicAlgCl.norm_extends]
  calc ‖(p : ℚ_[p])‖ ^ N * ‖z‖ ≤ ‖z‖⁻¹ * ‖z‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ hz'.ne'

theorem algebraMap_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) :
    algebraMap ℚ_[p] (KQ p K r) c ∈ intKQ p K r := by
  have hK : algebraMap ℚ_[p] K c ∈ GlobalTheory.LKLoc.intK p K := by
    show algebraMap K (PadicAlgCl p) (algebraMap ℚ_[p] K c) ∈ Obar p
    rw [← IsScalarTower.algebraMap_apply, mem_Obar_iff]
    exact (PadicAlgCl.norm_extends (p := p) c).le.trans hc
  exact Subring.subset_closure (Or.inl ⟨⟨_, hK⟩, rfl⟩)

theorem smul_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) (v : KQ p K r) (hv : v ∈ intKQ p K r) :
    c • v ∈ intKQ p K r := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_intKQ p K r c hc) hv

theorem exists_pow_smul_mem_intKQ (r : ℕ) (v : KQ p K r) :
    ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ intKQ p K r := by
  have hp1 : ∀ k : ℕ, ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le
  induction (v : K ⊗[ℚ_[p]] Qr p r) using TensorProduct.induction_on with
  | zero => exact ⟨0, by show (p : ℚ_[p]) ^ 0 • (0 : KQ p K r) ∈ intKQ p K r; rw [smul_zero]; exact zero_mem _⟩
  | tmul x y =>
    obtain ⟨N₁, h₁⟩ := exists_pow_smul_norm_le_one p (x : PadicAlgCl p)
    obtain ⟨N₂, h₂⟩ := exists_pow_smul_norm_le_one p (y : PadicAlgCl p)
    have hx : (p : ℚ_[p]) ^ N₁ • x ∈ GlobalTheory.LKLoc.intK p K := by
      show (((p : ℚ_[p]) ^ N₁ • x : K) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₁
    have hy : (p : ℚ_[p]) ^ N₂ • y ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
      show (((p : ℚ_[p]) ^ N₂ • y : Qr p r) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₂
    refine ⟨N₁ + N₂, ?_⟩
    have key : ((p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y) : K ⊗[ℚ_[p]] Qr p r) =
        (((p : ℚ_[p]) ^ N₁ • x) ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] ((p : ℚ_[p]) ^ N₂ • y)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul_smul, pow_add]
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) =
        inclK p K r ((p : ℚ_[p]) ^ N₁ • x) * inclQ p K r ((p : ℚ_[p]) ^ N₂ • y) := key
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, hx⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, hy⟩, rfl⟩))
  | add a b ha hb =>
    obtain ⟨N₁, h₁⟩ := ha
    obtain ⟨N₂, h₂⟩ := hb
    refine ⟨N₁ + N₂, ?_⟩
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b) =
        (p : ℚ_[p]) ^ N₂ • ((p : ℚ_[p]) ^ N₁ • a) + (p : ℚ_[p]) ^ N₁ • ((p : ℚ_[p]) ^ N₂ • b) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm N₂ N₁]
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact add_mem (smul_mem_intKQ p K r _ (hp1 _) _ h₁) (smul_mem_intKQ p K r _ (hp1 _) _ h₂)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isOpen_intKQ (hK : FiniteDimensional ℚ_[p] K) (r : ℕ) (hr : 0 < r) :
    IsOpen (intKQ p K r : Set (KQ p K r)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI : FiniteDimensional ℚ_[p] (KQ p K r) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  exact isOpen_of_padicLattice (intKQ p K r).toAddSubgroup
    (fun c hc v hv => smul_mem_intKQ p K r c hc v hv) (exists_pow_smul_mem_intKQ p K r)

theorem mem_Kres_iff (n r : ℕ) (g : GL (Fin n) (KQ p K r)) :
    g ∈ Kres p K n r ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r ∧
      ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r := by
  constructor
  · rintro ⟨h, rfl⟩ i j
    exact ⟨((h : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2,
      (((h⁻¹ : GL (Fin n) (intKQ p K r)) : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2⟩
  · intro H
    let A : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).1⟩
    let B : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).2⟩
    have hA : A.map (intKQ p K r).subtype = (g : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hB : B.map (intKQ p K r).subtype =
        ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (intKQ p K r) => M.map (intKQ p K r).subtype :=
      Matrix.map_injective Subtype.val_injective
    have h1 : A * B = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.mul_inv g)
    have h2 : B * A = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.inv_mul g)
    exact ⟨⟨A, B, h1, h2⟩, Units.ext hA⟩

theorem isOpen_Kres : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → IsOpen (Kres p K n r : Set (GL (Fin n) (KQ p K r))) := by
  intro p _ K hK n r hr
  have hS := isOpen_intKQ p K hK r hr
  have e : (Kres p K n r : Set (GL (Fin n) (KQ p K r))) = ⋂ i, ⋂ j,
      ((fun g : GL (Fin n) (KQ p K r) => (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _) ∩
       (fun g : GL (Fin n) (KQ p K r) =>
          ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _)) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    exact mem_Kres_iff p K n r g
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (hS.preimage (Units.continuous_val.matrix_elem i j)).inter
    (hS.preimage (Units.continuous_coe_inv.matrix_elem i j))

end GlobalTheory.LKRes
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical


#check GlobalTheory.IntBasisKQ.exists_basis_intKQ

noncomputable section

open scoped Pointwise

namespace GlobalTheory.FinAtP

variable {p : ℕ} [Fact p.Prime]

theorem kq_lc (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    LocallyCompactSpace (KQ p K 1) ∧ SecondCountableTopology (KQ p K 1) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : ContinuousSMul ℚ_[p] (KQ p K 1) := IsModuleTopology.toContinuousSMul ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  let b := Module.finBasis ℚ_[p] (KQ p K 1)
  let e : KQ p K 1 ≃L[ℚ_[p]] (Fin (Module.finrank ℚ_[p] (KQ p K 1)) → ℚ_[p]) :=
    b.equivFun.toContinuousLinearEquiv
  exact ⟨e.toHomeomorph.isClosedEmbedding.locallyCompactSpace,
    e.toHomeomorph.isEmbedding.secondCountableTopology⟩

theorem isCompact_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    IsCompact (intKQ p K 1 : Set (KQ p K 1)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : ContinuousSMul ℚ_[p] (KQ p K 1) := IsModuleTopology.toContinuousSMul ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  obtain ⟨ι, _, b, hb⟩ := GlobalTheory.IntBasisKQ.exists_basis_intKQ p K inferInstance 1 one_pos
  let e : KQ p K 1 ≃L[ℚ_[p]] (ι → ℚ_[p]) := b.equivFun.toContinuousLinearEquiv
  have hset : (intKQ p K 1 : Set (KQ p K 1)) = e ⁻¹' Set.univ.pi fun _ => Metric.closedBall (0 : ℚ_[p]) 1 := by
    ext x
    simp only [SetLike.mem_coe, hb, Set.mem_preimage, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
    rfl
  rw [hset]
  exact e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ => isCompact_closedBall _ _)

theorem isCompact_Kres (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (n : ℕ) :
    IsCompact (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  set B : Set (Matrix (Fin n) (Fin n) (KQ p K 1)) := {M | ∀ i j, M i j ∈ intKQ p K 1} with hB
  have hBc : IsCompact B := by
    have : B = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (intKQ p K 1 : Set (KQ p K 1)) := by
      ext M
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_intKQ K
  have hB' : IsCompact (MulOpposite.unop ⁻¹' B : Set (Matrix (Fin n) (Fin n) (KQ p K 1))ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hBc
  have e : (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))) = Units.embedProduct _ ⁻¹' (B ×ˢ (MulOpposite.unop ⁻¹' B)) := by
    ext g
    simp only [SetLike.mem_coe, mem_Kres_iff, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
      MulOpposite.unop_op, hB, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hBc.prod hB')


open Polynomial in
theorem rho_charpoly_sep (G : HTGroup p) (w : Fin G.m) (y : G.C) (hdeg : (minpoly G.F y).natDegree = G.n)
    (hsep : (minpoly G.F y).Separable) : (G.rho w y).charpoly.Separable := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  let ρF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    { G.rho w with
      commutes' := fun x => by
        change G.rho w (algebraMap G.F G.C x) = _
        rw [G.rho_F]
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
          RingHom.algebraMap_toAlgebra, HTGroup.embW] }
  have hρF : ∀ c, ρF c = G.rho w c := fun _ => rfl
  let Φ : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) ρF (fun _ _ => Algebra.commute_algebraMap_left _ _)
  have hΦinj : Function.Injective Φ :=
    (Φ : G.Fw w ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) (G.Fw w)).injective
  set z : G.Fw w ⊗[G.F] G.C := (1 : G.Fw w) ⊗ₜ y with hz
  have hΦz : Φ z = G.rho w y := by
    change Φ ((1 : G.Fw w) ⊗ₜ y) = _
    refine (Algebra.TensorProduct.lift_tmul (Algebra.ofId (G.Fw w) (Matrix (Fin G.n) (Fin G.n) (G.Fw w))) ρF _
      (1 : G.Fw w) y).trans ?_
    rw [map_one, one_mul]
    exact hρF y
  set M := G.rho w y with hM
  have hliF : LinearIndependent G.F (fun i : Fin G.n => y ^ (i : ℕ)) := by
    have h := linearIndependent_pow (K := G.F) y
    rw [hdeg] at h
    exact h
  letI : Module.Free G.F (G.Fw w) := Module.Free.of_divisionRing _ _
  letI : Module.Flat G.F (G.Fw w) := Module.Flat.of_free
  have hliC : LinearIndependent (G.Fw w) (fun i : Fin G.n => z ^ (i : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := G.Fw w) hliF
    convert h using 1
    funext i
    simp [z, Algebra.TensorProduct.tmul_pow]
  have hMint : IsIntegral (G.Fw w) M := Algebra.IsIntegral.isIntegral M
  have hQ0 : minpoly (G.Fw w) M ≠ 0 := minpoly.ne_zero hMint
  have hzQ : aeval z (minpoly (G.Fw w) M) = 0 := by
    apply hΦinj
    rw [map_zero, ← Polynomial.aeval_algHom_apply, hΦz, minpoly.aeval]
  have hdegQ : G.n ≤ (minpoly (G.Fw w) M).natDegree := by
    by_contra hlt
    push_neg at hlt
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at hzQ
    have hc := Fintype.linearIndependent_iff.1 hliC (fun i => (minpoly (G.Fw w) M).coeff i) hzQ
    apply hQ0
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_zero]
    by_cases hk : k < G.n
    · exact hc ⟨k, hk⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  set Pv := (minpoly G.F y).map (algebraMap G.F (G.Fw w)) with hPv
  have hPvM : aeval M Pv = 0 := by
    rw [hPv, Polynomial.aeval_map_algebraMap, hM, ← hρF, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hyint : IsIntegral G.F y := Algebra.IsIntegral.isIntegral y
  have hPvmon : Pv.Monic := (minpoly.monic hyint).map _
  have hPvdeg : Pv.natDegree = G.n := by
    rw [hPv, Polynomial.natDegree_map, hdeg]
  have hdvd : minpoly (G.Fw w) M ∣ Pv := minpoly.dvd (G.Fw w) M hPvM
  have hmin : minpoly (G.Fw w) M = Pv :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hMint) hPvmon hdvd (by omega)).symm
  have hchar : M.charpoly = Pv := by
    have h1 : minpoly (G.Fw w) M ∣ M.charpoly := Matrix.minpoly_dvd_charpoly M
    have h2 : M.charpoly.natDegree = G.n := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rw [hmin] at h1
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPvmon (Matrix.charpoly_monic M) h1
      (by omega)
  rw [hchar, hPv]
  exact hsep.map

theorem loc (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {n : ℕ}
    (γ : GL (Fin n) (KQ p K 1)) (hγ : (γ : Matrix (Fin n) (Fin n) (KQ p K 1)).charpoly.Separable)
    (S₂ : Finset (GL (Fin n) (KQ p K 1))) :
    ∃ S : Finset (GL (Fin n) (KQ p K 1)), ∀ h : GL (Fin n) (KQ p K 1),
      (∃ s ∈ S₂, ∃ k₁ ∈ Kres p K n 1, ∃ k₂ ∈ Kres p K n 1, h⁻¹ * γ * h = k₁ * s * k₂) →
      ∃ a : GL (Fin n) (KQ p K 1), a * γ = γ * a ∧ ∃ s ∈ S, ∃ k ∈ Kres p K n 1, h = a * s * k := by
  obtain ⟨hlc, hsc⟩ := kq_lc K
  haveI : FiniteDimensional ℚ_[p] (Qr p 1) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance one_pos
  haveI : FiniteDimensional ℚ_[p] (KQ p K 1) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p 1))
  haveI : IsModuleTopology ℚ_[p] (KQ p K 1) := ⟨rfl⟩
  haveI : IsTopologicalRing (KQ p K 1) := IsModuleTopology.isTopologicalRing ℚ_[p] _
  haveI : T2Space (KQ p K 1) := GlobalTheory.LKMid.t2Space_kq K 1
  haveI : IsArtinianRing (KQ p K 1) := IsArtinianRing.of_finite ℚ_[p] (KQ p K 1)
  have hK := isCompact_Kres K n
  have hO := isOpen_Kres p K inferInstance n 1 one_pos
  set Ω : Set (GL (Fin n) (KQ p K 1)) := ⋃ s ∈ S₂,
    (fun x : GL (Fin n) (KQ p K 1) × GL (Fin n) (KQ p K 1) => x.1 * s * x.2) ''
      ((Kres p K n 1 : Set _) ×ˢ (Kres p K n 1 : Set _)) with hΩdef
  have hΩ : IsCompact Ω := S₂.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop)
  obtain ⟨C, hC, hCx⟩ := GlobalTheory.Orb.isProperOrbit_GL (A := KQ p K 1) (g := γ) hγ Ω hΩ
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun c : C => (c : GL (Fin n) (KQ p K 1)) • (Kres p K n 1 : Set (GL (Fin n) (KQ p K 1))))
    (fun c => hO.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, Set.mem_smul_set.2 ⟨1, one_mem _, by simp⟩⟩)
  refine ⟨t.image fun c : C => (c : GL (Fin n) (KQ p K 1)), fun h ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ => ?_⟩
  have hmem : h⁻¹ * γ * h ∈ Ω := Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, he.symm⟩
  obtain ⟨u, hu, huC⟩ := hCx h hmem
  have := ht huC
  simp only [Set.mem_iUnion] at this
  obtain ⟨c, hc, hx⟩ := this
  obtain ⟨k, hk, hck⟩ := Set.mem_smul_set.1 hx
  refine ⟨u⁻¹, ?_, c, Finset.mem_image_of_mem _ hc, k, hk, ?_⟩
  · have hu' : u * γ = γ * u := GlobalTheory.Orb.mem_cent.1 hu
    calc u⁻¹ * γ = u⁻¹ * (γ * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * γ) * u⁻¹ := by rw [hu']
      _ = γ * u⁻¹ := by group
  · have e : u * h = (c : GL (Fin n) (KQ p K 1)) * k := hck.symm
    calc h = u⁻¹ * (u * h) := by group
      _ = u⁻¹ * c * k := by rw [e]; group

end GlobalTheory.FinAtP

namespace GlobalTheory.FinAtP

variable {p : ℕ} [Fact p.Prime]

theorem gl_one_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem prod_fin (G : HTGroup p) (γ : Gr G 1)
    (hγ : ∀ w, ((γ.2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).charpoly.Separable)
    (S₂ : Finset (Gr G 1)) :
    ∃ S : Finset (Gr G 1), ∀ h : Gr G 1,
      (∃ s ∈ S₂, ∃ k₁ ∈ KHT p G.m G.n 1 G.Fw, ∃ k₂ ∈ KHT p G.m G.n 1 G.Fw, h⁻¹ * γ * h = k₁ * s * k₂) →
      ∃ a : Gr G 1, a * γ = γ * a ∧ ∃ s ∈ S, ∃ k ∈ KHT p G.m G.n 1 G.Fw, h = a * s * k := by
  choose Sw hSw using fun w => loc (G.Fw w) (γ.2 w) (hγ w) (S₂.image fun s => s.2 w)
  refine ⟨(Fintype.piFinset Sw).image fun t => ((1 : GL (Fin 1) (Qr p 1)), t), ?_⟩
  rintro h ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩
  have hw : ∀ w, ∃ a : GL (Fin G.n) (KQ p (G.Fw w) 1), a * γ.2 w = γ.2 w * a ∧
      ∃ s ∈ Sw w, ∃ k ∈ Kres p (G.Fw w) G.n 1, h.2 w = a * s * k := fun w =>
    hSw w (h.2 w) ⟨s.2 w, Finset.mem_image_of_mem _ hs, k₁.2 w, (Subgroup.mem_prod.1 hk₁).2 w (Set.mem_univ _),
      k₂.2 w, (Subgroup.mem_prod.1 hk₂).2 w (Set.mem_univ _), congrArg (fun x : Gr G 1 => x.2 w) he⟩
  choose a ha s' hs' k hk hk' using hw
  refine ⟨(h.1, a), Prod.ext (gl_one_comm _ _) (funext ha), (1, s'),
    Finset.mem_image.2 ⟨s', Fintype.mem_piFinset.2 hs', rfl⟩, (1, k),
    Subgroup.mem_prod.2 ⟨one_mem _, fun w _ => hk w⟩, Prod.ext (by simp) (funext fun w => ?_)⟩
  simp [hk' w]

theorem exists_finset_cosets {H : Type} [Group H] (K₀ K : Subgroup H) (hK : K.relIndex K₀ ≠ 0) :
    ∃ T : Finset H, ∀ k ∈ K₀, ∃ t ∈ T, ∃ k' ∈ K, k = t * k' := by
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hK⟩
  haveI : Finite (K₀ ⧸ K.subgroupOf K₀) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : H), fun k hk => ?_⟩
  set q : K₀ ⧸ K.subgroupOf K₀ := QuotientGroup.mk ⟨k, hk⟩
  have hq : (Quotient.out q)⁻¹ * (⟨k, hk⟩ : K₀) ∈ K.subgroupOf K₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  rw [Subgroup.mem_subgroupOf] at hq
  refine ⟨((Quotient.out q : K₀) : H), Finset.mem_image_of_mem _ (Finset.mem_univ _), _, hq, ?_⟩
  simp

theorem charpoly_formGroupToPadicPoints_component (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (w : Fin G.m) :
    (((toP1 G β y).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).charpoly =
      (G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).charpoly.map (inclK p (G.Fw w) 1).toRingHom := by
  rw [← Matrix.charpoly_map]
  rfl

end GlobalTheory.FinAtP
