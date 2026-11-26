module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicFreeAlmostAll
public import GroundTheory.Brauer.BaseChangeCSA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocalStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAll
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveIffIsUnitDet
noncomputable section
open scoped TensorProduct
open Module

namespace GlobalTheory.LocAzumaya

variable {A Λ : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] {ι : Type*} [Fintype ι] [DecidableEq ι]

def structMat (b : Basis ι A Λ) : Matrix (ι × ι) (ι × ι) A :=
  LinearMap.toMatrix (b.tensorProduct b.mulOpposite) b.end (AlgHom.mulLeftRight A Λ).toLinearMap

theorem stdBasis_repr_apply' (M : Matrix ι ι A) (k l : ι) :
    (Matrix.stdBasis A ι ι).repr M (k, l) = M k l := rfl

theorem repr_equiv_apply {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {κ : Type*} (b₁ : Basis κ A M) (b₂ : Basis κ A N) (x : M) :
    b₂.repr (b₁.equiv b₂ (Equiv.refl κ) x) = b₁.repr x := by
  simp [Basis.equiv]

theorem structMat_apply (b : Basis ι A Λ) (k l i j : ι) :
    structMat b (k, l) (i, j) = b.repr (b i * b l * b j) k := by
  rw [structMat, LinearMap.toMatrix_apply]
  simp [Basis.end_repr_apply, Basis.tensorProduct_apply, LinearMap.toMatrix_apply, stdBasis_repr_apply']

theorem bijective_iff_isUnit_det (b : Basis ι A Λ) :
    Function.Bijective (AlgHom.mulLeftRight A Λ) ↔ IsUnit (structMat b).det := by
  set c := b.tensorProduct b.mulOpposite
  set f := (AlgHom.mulLeftRight A Λ).toLinearMap
  haveI := Module.Free.of_basis c
  haveI := Module.Finite.of_basis c
  let e : Module.End A Λ ≃ₗ[A] Λ ⊗[A] Λᵐᵒᵖ := b.end.equiv c (Equiv.refl _)
  have hM : structMat b = LinearMap.toMatrix c c (e.toLinearMap ∘ₗ f) := by
    ext p q
    rw [structMat, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, repr_equiv_apply]
  rw [hM, LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  constructor
  · intro h; exact e.bijective.comp h
  · intro h
    have := e.symm.bijective.comp h
    simpa [Function.comp_def, f] using this

end GlobalTheory.LocAzumaya
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAll
noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood Module

namespace GlobalTheory.LocAzumaya

theorem exists_den_coords : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] (Λ : Subring B),
    Module.Finite ℤ Λ → ∀ (ι : Type) [Fintype ι] (e : Module.Basis ι F B),
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((D : F) * e.repr x k) := by
  intro F B _ _ _ _ Λ hfin ι _ e
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  obtain ⟨D, hD, hDi⟩ := GlobalTheory.SepModel.exists_nat_integral
    (Finset.univ.image fun p : Fin n × ι => e.repr (s p.1 : B) p.2)
  refine ⟨D, hD, fun x hx => ?_⟩
  have key : ∀ y : Λ, y ∈ Submodule.span ℤ (Set.range s) →
      ∀ k, IsIntegral ℤ ((D : F) * e.repr (y : B) k) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro k
      exact hDi _ (Finset.mem_image.2 ⟨(j, k), Finset.mem_univ _, rfl⟩)
    | zero => intro k; simpa using isIntegral_zero
    | add y z _ _ hy hz =>
      intro k
      simpa [mul_add] using (hy k).add (hz k)
    | smul a y _ hy =>
      intro k
      have : (D : F) * e.repr ((a • y : Λ) : B) k = (a : F) * ((D : F) * e.repr (y : B) k) := by
        have hc : ((a • y : Λ) : B) = (a : F) • (y : B) := by
          have h0 : ((a • y : Λ) : B) = a • (y : B) := rfl
          rw [h0, zsmul_eq_mul, Algebra.smul_def, map_intCast]
        rw [hc]
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
        ring
      rw [this]
      have ha : IsIntegral ℤ (a : F) := by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ F a))
      exact ha.mul (hy k)
  intro k
  exact key ⟨x, hx⟩ (by rw [hs]; trivial) k
theorem exists_coords_of_mem_locOrder : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (Λ : Subring B) (ι : Type) [Fintype ι] (e : Module.Basis ι F B),
    (∀ i, e i ∈ Λ) → (∀ x ∈ Λ, ∀ k, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x k ∈ cenOrder ℓ F) →
    ∀ y ∈ locOrder ℓ Λ, ∃ c : ι → ℚ_[ℓ] ⊗[ℚ] F, (∀ i, c i ∈ cenOrder ℓ F) ∧
      y = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
  intro ℓ _ F B _ _ _ _ _ _ Λ ι _ e he hco
  classical
  have hexp : ∀ x : B, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] x =
      ∑ i, cenMap ℓ F B ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
    intro x
    conv_lhs => rw [← e.sum_repr x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.LocMatrix.cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨fun i => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x i, fun i => hco x hx i, hexp x⟩
  | algebraMap r =>
    refine ⟨fun i => algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) r * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr 1 i),
      fun i => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) (hco 1 Λ.one_mem i), ?_⟩
    have h1 : ∀ a : ℚ_[ℓ] ⊗[ℚ] F, cenMap ℓ F B (algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) r * a) =
        algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) r * cenMap ℓ F B a := by
      intro a
      rw [map_mul, IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F),
        IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B), AlgHom.commutes]
    simp only [h1, mul_assoc]
    rw [← Finset.mul_sum, ← hexp 1, Algebra.TensorProduct.one_def.symm, mul_one]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨c', hc', rfl⟩ := hz
    refine ⟨fun i => c i + c' i, fun i => Subalgebra.add_mem _ (hc i) (hc' i), ?_⟩
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
  | mul y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨c', hc', rfl⟩ := hz
    refine ⟨fun k => ∑ i, ∑ j, c i * c' j * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr (e i * e j) k), fun k => ?_, ?_⟩
    · exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
        Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hc i) (hc' j)) (hco _ (Λ.mul_mem (he i) (he j)) k)
    · have hprod : ∀ i j, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) *
            (cenMap ℓ F B (c' j) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e j)) =
          ∑ k, cenMap ℓ F B (c i * c' j * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr (e i * e j) k)) *
            ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e k) := by
        intro i j
        have hcomm := (GlobalTheory.LocMatrix.cenMap_commute ℓ F B (c' j) ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i)).eq
        have h1 : cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) *
            (cenMap ℓ F B (c' j) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e j)) =
            cenMap ℓ F B (c i * c' j) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (e i * e j)) := by
          rw [map_mul, ← one_mul (1 : ℚ_[ℓ]), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            mul_assoc, ← mul_assoc ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i), ← hcomm]
          simp only [mul_assoc]
        rw [h1, hexp (e i * e j), Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← map_mul]
      rw [Finset.sum_mul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hprod, map_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]

theorem exists_coordProj (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] {ι : Type} [DecidableEq ι] (e : Basis ι F B)
    (k : ι) : ∃ π : ℚ_[ℓ] ⊗[ℚ] B →ₗ[ℚ] ℚ_[ℓ] ⊗[ℚ] F,
      (∀ b : B, π ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k) ∧
      ∀ (a : ℚ_[ℓ] ⊗[ℚ] F) (i : ι),
        π (cenMap ℓ F B a * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i)) = if i = k then a else 0 := by
  refine ⟨LinearMap.lTensor ℚ_[ℓ] ((e.coord k).restrictScalars ℚ), fun b => by simp, fun a i => ?_⟩
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul q x =>
    rw [GlobalTheory.LocMatrix.cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Algebra.smul_def]
    simp only [LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars, map_smul, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  | add a a' ha ha' =>
    rw [map_add (f := _), add_mul, map_add (f := _), ha, ha']
    split_ifs <;> simp

theorem basisLoc : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ), Module.Finite ℤ Λ →
    ∀ (ι : Type) [Fintype ι] (e : Module.Basis ι F B), (∀ i, e i ∈ Λ) →
    ∃ D : ℕ, 0 < D ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ D →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      ∃ f : Module.Basis ι (cenOrder ℓ F) (locOrder ℓ Λ),
        (∀ i, (f i : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) ∧
        ∀ (y : locOrder ℓ Λ) (b : B), (y : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
          ∀ k, ((f.repr y k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
  intro F B _ _ _ _ _ _ Λ hΛ hfin ι _ e he
  classical
  obtain ⟨D, hD, hDint⟩ := exists_den_coords F B Λ hfin ι e
  refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
  letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  have hco : ∀ x ∈ Λ, ∀ k, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x k ∈ cenOrder ℓ F :=
    fun x hx k => GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hDint x hx k)
  have hv : ∀ i, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i ∈ locOrder ℓ Λ := fun i => Algebra.subset_adjoin ⟨_, he i, rfl⟩
  let v : ι → locOrder ℓ Λ := fun i => ⟨_, hv i⟩
  have hsmul : ∀ (c : cenOrder ℓ F) (y : locOrder ℓ Λ),
      ((c • y : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * y := fun c y => rfl
  have hsum : ∀ c : ι → cenOrder ℓ F, ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
      ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [hsmul, v]
  have hcoef : ∀ (c : ι → cenOrder ℓ F) (b : B),
      ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
      ∀ k, ((c k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
    intro c b h k
    obtain ⟨π, hπ1, hπ2⟩ := exists_coordProj ℓ F B e k
    have h' := congrArg π h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, hπ1] at h'
    simp only [hπ2, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h'
    exact h'
  have hli : LinearIndependent (cenOrder ℓ F) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h0 : ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (0 : B) := by
      rw [hc, TensorProduct.tmul_zero]; rfl
    have := hcoef c 0 h0 k
    apply Subtype.ext
    simpa using this
  have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range v) := by
    rintro y -
    obtain ⟨c, hc, hy⟩ := exists_coords_of_mem_locOrder ℓ F B Λ ι e he hco y y.2
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => ⟨c i, hc i⟩, Subtype.ext ?_⟩
    rw [hsum, hy]
  let f := Basis.mk hli hsp
  have hfv : ∀ i, f i = v i := fun i => Basis.mk_apply hli hsp i
  refine ⟨f, fun i => by rw [hfv], fun y b hy k => ?_⟩
  apply hcoef (fun i => f.repr y i) b _ k
  have hs := f.sum_repr y
  simp only [hfv] at hs
  rw [hs, hy]

end GlobalTheory.LocAzumaya

namespace GlobalTheory.LocAzumaya

theorem exists_basis_mem {F B : Type} [Field F] [CharZero F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (Λ : Subring B) (hspan : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) :
    ∃ e : Basis (Fin (Module.finrank F B)) F B, ∀ i, e i ∈ Λ := by
  let b := Module.finBasis F B
  choose m hm hmb using fun i => hspan (b i)
  let u : Fin (Module.finrank F B) → Fˣ := fun i => Units.mk0 (m i : F) (by exact_mod_cast (hm i).ne')
  refine ⟨b.unitsSMul u, fun i => ?_⟩
  rw [Basis.unitsSMul_apply]
  convert hmb i using 1
  simp [u, Algebra.smul_def]

theorem cenMap_injective (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] [Nontrivial B] : Function.Injective (cenMap ℓ F B) := by
  let g : F →ₗ[ℚ] B := ((Algebra.ofId F B).restrictScalars ℚ).toLinearMap
  have hg : Function.Injective g := (algebraMap F B).injective
  have heq : ⇑(cenMap ℓ F B) = ⇑(LinearMap.lTensor ℚ_[ℓ] g) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul q f => simp [cenMap, g]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [heq]
  exact Module.Flat.lTensor_preserves_injective_linearMap g hg

end GlobalTheory.LocAzumaya

namespace GlobalTheory.LocAzumaya

theorem locOrder_isAzumaya : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]
    (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      IsAzumaya (cenOrder ℓ F) (locOrder ℓ Λ) := by
  intro F B _ _ _ _ _ _ _ _ _ Λ hΛ hfin hspan
  classical
  obtain ⟨e, he⟩ := exists_basis_mem (F := F) Λ hspan
  have hδ : IsUnit (structMat e).det :=
    (bijective_iff_isUnit_det e).1 (GroundTheory.Brauer.mulLeftRight_bijective F B)
  obtain ⟨m, hm, hmint⟩ := GlobalTheory.SepModel.exists_nat_integral ({((structMat e).det)⁻¹} : Finset F)
  obtain ⟨D, hD, hbasis⟩ := basisLoc F B Λ hΛ hfin _ e he
  refine ⟨D * m, by positivity, fun ℓ _ hℓ => ?_⟩
  letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  obtain ⟨f, hf1, hf2⟩ := hbasis ℓ (fun h => hℓ (Dvd.dvd.mul_right h _))
  have hinv : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((structMat e).det)⁻¹ ∈ cenOrder ℓ F :=
    GlobalTheory.SepModel.tmul_mem_cenOrder ℓ (fun h => hℓ (Dvd.dvd.mul_left h _))
      (hmint _ (Finset.mem_singleton_self _))
  have hent : (cenOrder ℓ F).val.toRingHom.mapMatrix (structMat f) =
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom.mapMatrix
        (structMat e) := by
    ext ⟨k, l⟩ ⟨i, j⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Subalgebra.coe_val, Algebra.TensorProduct.includeRight_apply, structMat_apply]
    apply hf2
    simp only [Subalgebra.coe_mul, hf1, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hdet : (((structMat f).det : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (structMat e).det := by
    have h1 := RingHom.map_det (cenOrder ℓ F).val.toRingHom (structMat f)
    have h2 := RingHom.map_det
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom (structMat e)
    rw [hent, ← h2] at h1
    simpa using h1
  have hunit : IsUnit (structMat f).det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hdet, Subalgebra.coe_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mul_inv_cancel₀ hδ.ne_zero, Algebra.TensorProduct.one_def]
  haveI : Nontrivial B := inferInstance
  haveI : FaithfulSMul (cenOrder ℓ F) (locOrder ℓ Λ) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h : cenMap ℓ F B a = cenMap ℓ F B b :=
      congrArg (fun x : locOrder ℓ Λ => (x : ℚ_[ℓ] ⊗[ℚ] B)) hab
    exact Subtype.ext (cenMap_injective ℓ F B h)
  haveI := Module.Projective.of_basis f
  haveI := Module.Finite.of_basis f
  exact ⟨(bijective_iff_isUnit_det f).2 hunit⟩

end GlobalTheory.LocAzumaya
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAllStatement
open scoped TensorProduct
open GlobalTheory.LKInvGood
open GlobalTheory.LocAzumaya Module in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]
    (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      IsAzumaya (cenOrder ℓ F) (locOrder ℓ Λ) := by
  intro F B _ _ _ _ _ _ _ _ _ Λ hΛ hfin hspan
  classical
  have hlocalBasis : ∀ (ι : Type) [Fintype ι] (e : Module.Basis ι F B), (∀ i, e i ∈ Λ) →
      ∃ D : ℕ, 0 < D ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ D →
        letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
        ∃ f : Module.Basis ι (cenOrder ℓ F) (locOrder ℓ Λ),
          (∀ i, (f i : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) ∧
          ∀ (y : locOrder ℓ Λ) (b : B), (y : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
            ∀ k, ((f.repr y k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
    intro ι _ e he
    obtain ⟨D, hD, hDint⟩ := exists_den_coords F B Λ hfin ι e
    refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
    let _ := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
    have hco : ∀ x ∈ Λ, ∀ k, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x k ∈ cenOrder ℓ F :=
      fun x hx k => GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hDint x hx k)
    have hv : ∀ i, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i ∈ locOrder ℓ Λ := fun i => Algebra.subset_adjoin ⟨_, he i, rfl⟩
    let v : ι → locOrder ℓ Λ := fun i => ⟨_, hv i⟩
    have hsmul : ∀ (c : cenOrder ℓ F) (y : locOrder ℓ Λ),
        ((c • y : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * y := fun c y => rfl
    have hsum : ∀ c : ι → cenOrder ℓ F, ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
        ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
      intro c
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [hsmul, v]
    have hcoef : ∀ (c : ι → cenOrder ℓ F) (b : B),
        ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
        ∀ k, ((c k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
      intro c b h k
      obtain ⟨π, hπ1, hπ2⟩ := exists_coordProj ℓ F B e k
      have h' := congrArg π h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, map_sum, hπ1] at h'
      simp only [hπ2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h'
      exact h'
    have hli : LinearIndependent (cenOrder ℓ F) v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have h0 : ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (0 : B) := by
        rw [hc, TensorProduct.tmul_zero]; rfl
      have := hcoef c 0 h0 k
      apply Subtype.ext
      simpa using this
    have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range v) := by
      rintro y -
      obtain ⟨c, hc, hy⟩ := exists_coords_of_mem_locOrder ℓ F B Λ ι e he hco y y.2
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨c i, hc i⟩, Subtype.ext ?_⟩
      rw [hsum, hy]
    let f := Basis.mk hli hsp
    have hfv : ∀ i, f i = v i := fun i => Basis.mk_apply hli hsp i
    refine ⟨f, fun i => by rw [hfv], fun y b hy k => ?_⟩
    apply hcoef (fun i => f.repr y i) b _ k
    have hs := f.sum_repr y
    simp only [hfv] at hs
    rw [hs, hy]
  obtain ⟨e, he⟩ := exists_basis_mem (F := F) Λ hspan
  have hδ : IsUnit (structMat e).det :=
    (bijective_iff_isUnit_det e).1 (GroundTheory.Brauer.mulLeftRight_bijective F B)
  obtain ⟨m, hm, hmint⟩ := GlobalTheory.SepModel.exists_nat_integral ({((structMat e).det)⁻¹} : Finset F)
  obtain ⟨D, hD, hbasis⟩ := hlocalBasis _ e he
  refine ⟨D * m, by positivity, fun ℓ _ hℓ => ?_⟩
  let _ := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  obtain ⟨f, hf1, hf2⟩ := hbasis ℓ (fun h => hℓ (Dvd.dvd.mul_right h _))
  have hinv : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((structMat e).det)⁻¹ ∈ cenOrder ℓ F :=
    GlobalTheory.SepModel.tmul_mem_cenOrder ℓ (fun h => hℓ (Dvd.dvd.mul_left h _))
      (hmint _ (Finset.mem_singleton_self _))
  have hent : (cenOrder ℓ F).val.toRingHom.mapMatrix (structMat f) =
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom.mapMatrix
        (structMat e) := by
    ext ⟨k, l⟩ ⟨i, j⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Subalgebra.coe_val, Algebra.TensorProduct.includeRight_apply, structMat_apply]
    apply hf2
    simp only [Subalgebra.coe_mul, hf1, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hdet : (((structMat f).det : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (structMat e).det := by
    have h1 := RingHom.map_det (cenOrder ℓ F).val.toRingHom (structMat f)
    have h2 := RingHom.map_det
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom (structMat e)
    rw [hent, ← h2] at h1
    simpa using h1
  have hunit : IsUnit (structMat f).det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hdet, Subalgebra.coe_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mul_inv_cancel₀ hδ.ne_zero, Algebra.TensorProduct.one_def]
  have : Nontrivial B := inferInstance
  have : FaithfulSMul (cenOrder ℓ F) (locOrder ℓ Λ) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h : cenMap ℓ F B a = cenMap ℓ F B b :=
      congrArg (fun x : locOrder ℓ Λ => (x : ℚ_[ℓ] ⊗[ℚ] B)) hab
    exact Subtype.ext (cenMap_injective ℓ F B h)
  have := Module.Projective.of_basis f
  have := Module.Finite.of_basis f
  exact ⟨(bijective_iff_isUnit_det f).2 hunit⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaMatrixOfFinitePadicAlgebraOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalRingQuotientPairwiseIsCoprimeIInfEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalRingQuotientPairwiseIsCoprimeIInfEq
open scoped TensorProduct
open Function

namespace GlobalTheory

theorem exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A],
      ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A),
        (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  intro ℓ _ A _ _ _
  classical
  have : HenselianLocalRing ℤ_[ℓ] := henselianLocalRing_of_henselianRing ℤ_[ℓ]
  have := finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[ℓ] A
  letI := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨e, he, H⟩ := exists_completeOrthogonalIdempotents_of_henselian ℤ_[ℓ] A
  refine ⟨MaximalSpectrum A, inferInstance, fun q ↦ Ideal.span {1 - e q}, fun q ↦ ?_, ?_, ?_⟩
  · have := q.isMaximal
    exact isLocalRing_quotient_one_sub (he.idem q) q.asIdeal (H q)
  · intro i j hij
    change IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j})
    rw [Ideal.isCoprime_span_singleton_iff]
    have h0 : e i * e j = 0 := he.ortho hij
    exact ⟨1, e i, by linear_combination (-1 : A) * h0⟩
  · refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [Submodule.mem_iInf] at hx
    rw [Ideal.mem_bot, ← one_mul x, ← he.complete, Finset.sum_mul]
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hx q)
    rw [← hw]
    linear_combination (-w) * (he.idem q).eq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalRingQuotientPairwiseIsCoprimeIInfEqStatement
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localRing_quotients_coprime_iInf_eq_bot : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A], ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A), (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  first | (exact @GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (exact GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (intros; apply GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgEquivMatrixGlueCrt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgEquivMatrixGlueCrt
open scoped TensorProduct
open Function

namespace GlobalTheory

noncomputable def crtAlgEquiv (A : Type) [CommRing A] (ι : Type) [Fintype ι] (I : ι → Ideal A)
    (hI : Pairwise (IsCoprime on I)) (hbot : ⨅ i, I i = ⊥) : A ≃ₐ[A] (Π i, A ⧸ I i) :=
  AlgEquiv.ofRingEquiv (f := (RingEquiv.quotientBot A).symm.trans
    ((Ideal.quotEquivOfEq hbot.symm).trans (Ideal.quotientInfRingEquivPiQuotient I hI)))
    (fun x => by ext i; rfl)

theorem matrix_glue_crt : ∀ (A Λ : Type) [CommRing A] [Ring Λ] [Algebra A Λ] (ι : Type) [Fintype ι] (I : ι → Ideal A), Pairwise (IsCoprime on I) → ⨅ i, I i = ⊥ → ∀ (n : ℕ), (∀ i, Nonempty ((A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i))) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro A Λ _ _ _ ι _ I hI hbot n he
  classical
  let c := crtAlgEquiv A ι I hI hbot
  let e : ∀ i, (A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i) := fun i => (he i).some
  exact ⟨(Algebra.TensorProduct.rid A A Λ).symm
    |>.trans (Algebra.TensorProduct.congr AlgEquiv.refl c)
    |>.trans (Algebra.TensorProduct.piRight A A Λ (fun i => A ⧸ I i))
    |>.trans (AlgEquiv.piCongrRight (fun i => (Algebra.TensorProduct.comm A Λ (A ⧸ I i)).trans ((e i).restrictScalars A)))
    |>.trans (Matrix.piAlgEquiv A).symm
    |>.trans (AlgEquiv.mapMatrix c.symm)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgEquivMatrixGlueCrtStatement
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algEquiv_matrix_glue_crt : ∀ (A Λ : Type) [CommRing A] [Ring Λ] [Algebra A Λ] (ι : Type) [Fintype ι] (I : ι → Ideal A), Pairwise (IsCoprime on I) → ⨅ i, I i = ⊥ → ∀ (n : ℕ), (∀ i, Nonempty ((A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i))) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.matrix_glue_crt) | (exact GlobalTheory.matrix_glue_crt) | (intros; apply GlobalTheory.matrix_glue_crt  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaMatrixOfFinitePadicAlgebraOfLocal
open scoped TensorProduct
open Function

namespace GlobalTheory.AzumayaMatrixReduction

theorem of_local : (∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A)) →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro hloc ℓ _ A _ _ _ Λ _ _ _ _ n hn
  obtain ⟨ι, _, I, hlocI, hcop, hbot⟩ := GlobalTheory.T.exists_localRing_quotients_coprime_iInf_eq_bot ℓ A
  refine GlobalTheory.T.algEquiv_matrix_glue_crt A Λ ι I hcop hbot n fun i => ?_
  haveI := hlocI i
  haveI : IsAzumaya (A ⧸ I i) ((A ⧸ I i) ⊗[A] Λ) := GlobalTheory.T.azumaya_base_change A (A ⧸ I i) Λ
  haveI : Module.Finite ℤ_[ℓ] (A ⧸ I i) :=
    Module.Finite.of_surjective ((IsScalarTower.toAlgHom ℤ_[ℓ] A (A ⧸ I i)).toLinearMap)
      Ideal.Quotient.mk_surjective
  refine hloc ℓ (A ⧸ I i) ((A ⧸ I i) ⊗[A] Λ) n ?_
  haveI : Nontrivial A := (Ideal.Quotient.mk (I i)).domain_nontrivial
  rw [Module.finrank_baseChange, hn]

end GlobalTheory.AzumayaMatrixReduction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaMatrixOfFinitePadicAlgebraOfLocalStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local : (∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A)) →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.AzumayaMatrixReduction.of_local) | (exact GlobalTheory.AzumayaMatrixReduction.of_local) | (intros; apply GlobalTheory.AzumayaMatrixReduction.of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderContainingIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTChartExistsHolds
open scoped TensorProduct

namespace GlobalTheory

theorem exists_order_integers_mul_finite_index (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (OB : Subring B) (hfin : Module.Finite ℤ OB)
    (hsat : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) :
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  classical
  let f : NumberField.RingOfIntegers F →ₐ[ℤ] B :=
    ((algebraMap F B).comp (algebraMap (NumberField.RingOfIntegers F) F)).toIntAlgHom
  let g : OB →ₐ[ℤ] B := OB.subtype.toIntAlgHom
  have hc : ∀ a b, Commute (f a) (g b) := fun a b => Algebra.commutes _ _
  let L := Algebra.TensorProduct.lift f g hc
  have hL : ∀ a b, L (a ⊗ₜ b) = f a * g b := fun a b => Algebra.TensorProduct.lift_tmul f g hc a b

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (NumberField.RingOfIntegers F)).FG)
  choose m hm0 hm using fun a : NumberField.RingOfIntegers F => hsat (f a)
  let N : ℕ := ∏ a ∈ s, m a
  have hN0 : 0 < N := Finset.prod_pos fun a _ => hm0 a
  have hnat : ∀ (k : ℕ) (y : B), y ∈ OB → (k : B) * y ∈ OB := fun k y hy =>
    OB.mul_mem (natCast_mem OB k) hy
  let P : Submodule ℤ (NumberField.RingOfIntegers F) :=
    { carrier := {a | (N : B) * f a ∈ OB}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _), mul_add] at *
        exact OB.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro n a ha
        simp only [Set.mem_setOf_eq, map_zsmul, mul_smul_comm] at *
        exact OB.zsmul_mem ha n }
  have hsP : (s : Set (NumberField.RingOfIntegers F)) ⊆ SetLike.coe P := by
    intro a ha
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
    show (N : B) * f a ∈ OB
    have : (N : B) = (k : B) * (m a : B) := by
      rw [show N = m a * k from hk, Nat.cast_mul, (Nat.cast_commute _ _).eq]
    rw [this, mul_assoc]
    exact hnat k _ (hm a)
  have hP : ∀ a, (N : B) * f a ∈ OB := by
    intro a
    have : a ∈ Submodule.span ℤ (s : Set _) := by rw [hs]; trivial
    exact (Submodule.span_le.mpr hsP) this
  refine ⟨L.toRingHom.range, ?_, ?_, ?_, N, hN0, ?_⟩
  · intro b hb
    refine ⟨1 ⊗ₜ ⟨b, hb⟩, ?_⟩
    show L _ = b
    rw [hL]; simp [f, g]
  · intro a
    refine ⟨a ⊗ₜ 1, ?_⟩
    show L _ = _
    rw [hL]; simp [f, g]
  · haveI : Module.Finite ℤ OB := hfin
    haveI : Module.Finite ℤ (NumberField.RingOfIntegers F ⊗[ℤ] OB) := Module.Finite.tensorProduct _ _ _
    exact Module.Finite.of_surjective (L.toRingHom.rangeRestrict.toIntAlgHom.toLinearMap)
      (RingHom.rangeRestrict_surjective _)
  · rintro x ⟨t, rfl⟩
    show (N : B) * L t ∈ OB
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hL, ← mul_assoc]
      exact OB.mul_mem (hP a) b.2
    | add t u ht hu =>
      rw [map_add (f := _), mul_add]
      exact OB.add_mem ht hu

end GlobalTheory
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_order_containing_integers : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  first | (exact @GlobalTheory.exists_order_integers_mul_finite_index) | (exact GlobalTheory.exists_order_integers_mul_finite_index) | (intros; apply GlobalTheory.exists_order_integers_mul_finite_index  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionAvoidPrime
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem one_tmul_mem_locOrder_of_nsmul_mem : ∀ {B : Type} [Ring B] [Algebra ℚ B] (OB : Subring B) (b : B) (m : ℕ),
    0 < m → (m : B) * b ∈ OB → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ m →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b ∈ locOrder ℓ OB := by
  intro B _ _ OB b m hm hmb ℓ _ hℓ
  have hunit : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).mpr hℓ)
  obtain ⟨u, hu⟩ := hunit
  have hgen : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b) ∈ locOrder ℓ OB :=
    Algebra.subset_adjoin ⟨_, hmb, rfl⟩
  have key : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b)) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    have : ((m : B) * b) = (m : ℚ) • b := by rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    have h1 : ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = (m : ℚ_[ℓ]) := by rw [hu]; simp
    have h2 : (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = 1 := by
      rw [← PadicInt.coe_mul]; simp
    rw [h1] at h2
    rw [Algebra.smul_def]
    simp only [map_natCast]
    rw [PadicInt.algebraMap_apply]
    linear_combination h2.symm
  rw [key]
  exact Subalgebra.smul_mem _ hgen _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenOrderFinite
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem cenOrder_finite : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := by
  intro F _ _ ℓ _
  classical
  let f : NumberField.RingOfIntegers F → ℚ_[ℓ] ⊗[ℚ] F := fun a => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F)
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite ℤ (NumberField.RingOfIntegers F)).fg_top
  have hint : ∀ x ∈ (f '' (s : Set (NumberField.RingOfIntegers F))), IsIntegral ℤ_[ℓ] x := by
    rintro _ ⟨a, -, rfl⟩
    have h1 : IsIntegral ℤ ((a : F)) := NumberField.RingOfIntegers.isIntegral_coe a
    have h2 : IsIntegral ℤ (f a) := by
      have := h1.map ((Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).restrictScalars ℤ)
      simpa [f] using this
    exact h2.tower_top
  have hfin : Module.Finite ℤ_[ℓ] (Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral ((s.finite_toSet).image f) hint
  have heq : cenOrder ℓ F = Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F))) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      let A := Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))
      let N : Submodule ℤ (NumberField.RingOfIntegers F) :=
        { carrier := {x | f x ∈ A}
          add_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq, f, map_add (f := _), TensorProduct.tmul_add] at hx hy ⊢
            exact A.add_mem hx hy
          zero_mem' := by
            simp only [Set.mem_setOf_eq, f, map_zero, TensorProduct.tmul_zero]
            exact A.zero_mem
          smul_mem' := by
            intro c x hx
            simp only [Set.mem_setOf_eq, f, zsmul_eq_mul, map_mul, map_intCast] at hx ⊢
            have : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((c : F) * (x : F)) = c • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (x : F)) := by
              rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
            rw [this]
            exact A.toSubring.zsmul_mem hx c }
      have hsN : (s : Set _) ⊆ N := fun x hx => show f x ∈ A from Algebra.subset_adjoin ⟨x, hx, rfl⟩
      have : a ∈ N := by
        have := Submodule.span_le.mpr hsN
        rw [hs] at this
        exact this Submodule.mem_top
      exact this
    · apply Algebra.adjoin_mono
      rintro _ ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
  rw [heq]
  exact hfin

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAll
noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

theorem locOrder_eq_of_le {B : Type} [Ring B] [Algebra ℚ B] (OB Λ : Subring B) (hle : OB ≤ Λ)
    (N : ℕ) (hN : 0 < N) (hNΛ : ∀ x ∈ Λ, (N : B) * x ∈ OB) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    locOrder ℓ OB = locOrder ℓ Λ := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.image_mono hle)
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.one_tmul_mem_locOrder_of_nsmul_mem OB x N hN (hNΛ x hx) ℓ hℓ

theorem locOrder_matrix : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  intro F B _ _ _ _ _ _ _ _ _ n hn OB hfin hspan
  obtain ⟨Λ, hle, hΛ, hΛfin, N₁, hN₁, hN₁Λ⟩ := GlobalTheory.T.exists_order_containing_integers F B OB hfin hspan
  have hspanΛ : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ := fun b => by
    obtain ⟨m, hm, hmb⟩ := hspan b; exact ⟨m, hm, hle hmb⟩
  obtain ⟨N₂, hN₂, hfree⟩ := GlobalTheory.T.localOrderTensorPadic_free_almost_all F B Λ hΛ hΛfin hspanΛ
  obtain ⟨N₃, hN₃, hazu⟩ := GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all F B Λ hΛ hΛfin hspanΛ
  refine ⟨N₁ * N₂ * N₃, by positivity, fun ℓ _ hℓ => ?_⟩
  have h₁ : ¬ ℓ ∣ N₁ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
  have h₂ : ¬ ℓ ∣ N₂ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have h₃ : ¬ ℓ ∣ N₃ := fun h => hℓ (Dvd.dvd.mul_left h _)
  have heq := locOrder_eq_of_le OB Λ hle N₁ hN₁ hN₁Λ ℓ h₁
  letI := cenAlgebra ℓ F B Λ hΛ
  haveI := isScalarTower_cenAlgebra ℓ F B Λ hΛ
  haveI : Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := GlobalTheory.cenOrder_finite F ℓ
  obtain ⟨hF, hrank⟩ := hfree ℓ h₂
  haveI := hF
  haveI := hazu ℓ h₃
  obtain ⟨φ⟩ := GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local ℓ (cenOrder ℓ F) (locOrder ℓ Λ) n (hrank.trans hn)
  refine ⟨(Subalgebra.equivOfEq _ _ heq).trans (φ.restrictScalars ℤ_[ℓ]), fun a => ?_⟩
  refine ⟨heq ▸ cenMap_mem ℓ F B Λ hΛ a.2, ?_⟩
  have h2 : (Subalgebra.equivOfEq _ _ heq) ⟨cenMap ℓ F B a, heq ▸ cenMap_mem ℓ F B Λ hΛ a.2⟩ =
      algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a := Subtype.ext rfl
  rw [AlgEquiv.trans_apply, h2, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

end GlobalTheory.LocMatrix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAllStatement
open scoped TensorProduct
open GlobalTheory.LKInvGood
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  first | (exact @GlobalTheory.LocMatrix.locOrder_matrix) | (exact GlobalTheory.LocMatrix.locOrder_matrix) | (intros; apply GlobalTheory.LocMatrix.locOrder_matrix  <;> assumption)
end
