module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtCompl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtPoints

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalizeThreeByThree
theorem UpperTheory.Reformulated.B.DiagonalizeThreeByThree.diagonalize_three_by_three_split :
    ∀ {K : Type} [inst : Field K] (d : Fin (3 : ℕ) → K),
    Function.Injective d →
      ∀ (M : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K),
        M.charpoly = ∏ a : Fin (3 : ℕ), (Polynomial.X - (Polynomial.C : K → Polynomial K) (d a)) →
          ∃ (h : GL (Fin (3 : ℕ)) K),
            (↑h⁻¹ : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K) * M * (↑h : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K) =
              Matrix.diagonal d := by
  intro K _ d hd M hM
  have hev : ∀ a, Module.End.HasEigenvalue (Matrix.toLin' M) (d a) := by
    intro a
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  choose v hv using fun a => (hev a).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) d hd v hv
  let P : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => v j i
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hMP : M * P = P * Matrix.diagonal d := by
    ext i j
    have h := congrFun (hv j).apply_eq_smul i
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    exact h
  obtain ⟨u, hu⟩ := hP
  refine ⟨u, ?_⟩
  rw [Matrix.mul_assoc, hu, hMP, ← hu, ← Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ScalarMap
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

section

variable {O G : Type} [CommRing O] [Group G]

private def Cond (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (r : G →* GG (m := 3) (R := C)) : Prop :=
  (∀ s ∈ I, (r s).mat.charpoly = ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)))) ∧
    ∀ s : Fin 3 → G, (∀ a, s a ∈ I) →
      ((r (s 0)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) *
        ((r (s 1)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) *
        ((r (s 2)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 2 (s 2)))) = 0

private theorem scalar_map {R C : Type} [CommRing R] [CommRing C] (f : R →+* C) (c : R) :
    f.mapMatrix (Matrix.scalar (Fin 3) c) = Matrix.scalar (Fin 3) (f c) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem cond_eqs (Ψ : G →* Oˣ) (I : Subgroup G) {R : Type} [CommRing R] [Algebra O R] (r : G →* GG (m := 3) (R := R)) :
    ∃ S : Set R, ∀ (C : Type) [CommRing C] [Algebra O C] (f : R →ₐ[O] C),
      Cond Ψ I (push f r) ↔ ∀ a ∈ S, f a = 0 := by
  let P : G → R[X] := fun s =>
    (r s).mat.charpoly - ∏ a, (X - Polynomial.C (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)))
  let M : (Fin 3 → G) → Matrix (Fin 3) (Fin 3) R := fun s =>
    ((r (s 0)).mat - Matrix.scalar _ (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) *
        ((r (s 1)).mat - Matrix.scalar _ (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) *
        ((r (s 2)).mat - Matrix.scalar _ (algebraMap O R (UpperTheory.V.UnitaryThreeInertia.psi Ψ 2 (s 2))))
  refine ⟨{a | (∃ s ∈ I, ∃ k, a = (P s).coeff k) ∨ ∃ s : Fin 3 → G, (∀ a, s a ∈ I) ∧ ∃ i j, a = M s i j},
    fun C _ _ f => ?_⟩
  have hm : ∀ s, (push f r s).mat = (f : R →+* C).mapMatrix (r s).mat := fun _ => rfl
  have hc : ∀ o, (f : R →+* C) (algebraMap O R o) = algebraMap O C o := f.commutes
  have hP : ∀ s, (P s).map (f : R →+* C) = (push f r s).mat.charpoly -
      ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s))) := fun s => by
    simp only [P, hm, RingHom.mapMatrix_apply, Matrix.charpoly_map, Polynomial.map_sub, Polynomial.map_prod,
      Polynomial.map_X, Polynomial.map_C, hc]
  have hM : ∀ s, (f : R →+* C).mapMatrix (M s) =
      ((push f r (s 0)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) *
        ((push f r (s 1)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) *
        ((push f r (s 2)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 2 (s 2)))) := fun s => by
    simp only [M, hm, map_mul, map_sub, scalar_map, hc]
  constructor
  · rintro ⟨h1, h2⟩ a (⟨s, hs, k, rfl⟩ | ⟨s, hs, i, j, rfl⟩)
    · have := hP s
      rw [h1 s hs, sub_self] at this
      simpa using congrArg (fun p => p.coeff k) this
    · have := hM s
      rw [h2 s hs] at this
      simpa using congrFun (congrFun this i) j
  · intro h
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [← sub_eq_zero, ← hP]
      ext k
      simpa using h _ (Or.inl ⟨s, hs, k, rfl⟩)
    · rw [← hM]
      ext i j
      simpa using h _ (Or.inr ⟨s, hs, i, j, rfl⟩)

private theorem cond_tri (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (u : G →* GG (m := 3) (R := C))
    (ht : ∀ g a b, wt a b < 0 → (u g).mat a b = 0)
    (hd : ∀ s ∈ I, ∀ a, (u s).mat a a = algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)) : Cond Ψ I u := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [Matrix.charpoly_of_upperTriangular]
    · simp only [hd s hs]
    · intro a b hab
      apply ht
      have : (b : ℕ) < a := hab
      simp only [wt, wt1]
      omega
  · have h10 := fun g => ht g 1 0 (by decide)
    have h20 := fun g => ht g 2 0 (by decide)
    have h21 := fun g => ht g 2 1 (by decide)
    have e0 := hd _ (hs 0) 0
    have e1 := hd _ (hs 1) 1
    have e2 := hd _ (hs 2) 2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, e0, e1, e2]

private theorem cond_conj (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (u : G →* GG (m := 3) (R := C))
    (hu : ∀ s ∈ I, (u s).right = 1) (n : GL (Fin 3) C) (h : Cond Ψ I u) : Cond Ψ I (conjBy n u) := by
  have hm : ∀ s ∈ I, (conjBy n u s).mat =
      (n : Matrix (Fin 3) (Fin 3) C) * (u s).mat * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro s hs
    have : (conjBy n u s).left = n * (u s).left * n⁻¹ := by
      simp [conjBy, hu s hs]
    simp only [GG.mat, this, Units.val_mul]
  have hc : ∀ (A : Matrix (Fin 3) (Fin 3) C) (c : C),
      (n : Matrix (Fin 3) (Fin 3) C) * A * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c =
      (n : Matrix (Fin 3) (Fin 3) C) * (A - Matrix.scalar _ c) *
        ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro A c
    rw [mul_sub, sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).eq, mul_assoc (Matrix.scalar _ c),
      Units.mul_inv, mul_one]
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [hm s hs, ← h.1 s hs, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  · rw [hm _ (hs 0), hm _ (hs 1), hm _ (hs 2), hc, hc, hc]
    have := h.2 s hs
    generalize (u (s 0)).mat - _ = A at *
    generalize (u (s 1)).mat - _ = B at *
    generalize (u (s 2)).mat - _ = D at *
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc B, ← mul_assoc A, ← mul_assoc A, this, zero_mul, mul_zero]

end

private theorem frac_alg (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    ∃ _ : Algebra ℚ_[l] (FractionRing O), IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) ∧
      Module.Finite ℚ_[l] (FractionRing O) := by
  have hi : Function.Injective (algebraMap ℤ_[l] O) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
    have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
    have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) ⊥ hm
    exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance
  exact ⟨inferInstance, inferInstance,
    Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])⟩

private theorem trunc_data (E : Type) [Field E] (n : ℕ) :
    ∃ π : (MvPowerSeries (Fin 12) E ⧸ maximalIdeal (MvPowerSeries (Fin 12) E) ^ (n + 1)) →ₐ[E] E,
      (∀ a, π (Ideal.Quotient.mk _ a) = MvPowerSeries.constantCoeff a) ∧ (∀ a, π a = 0 → IsNilpotent a) ∧
      Module.Finite E (MvPowerSeries (Fin 12) E ⧸ maximalIdeal (MvPowerSeries (Fin 12) E) ^ (n + 1)) := by
  have hm : ∀ a : MvPowerSeries (Fin 12) E, a ∈ maximalIdeal _ ↔ MvPowerSeries.constantCoeff a = 0 := fun a => by
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
  let c : MvPowerSeries (Fin 12) E →ₐ[E] E :=
    { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 12) E →+* E) with
      commutes' := fun x => by simp [MvPowerSeries.algebraMap_apply] }
  let π := Ideal.Quotient.liftₐ (maximalIdeal (MvPowerSeries (Fin 12) E) ^ (n + 1)) c
    fun a ha => (hm a).1 (Ideal.pow_le_self n.succ_ne_zero ha)
  have hπ : ∀ a, π (Ideal.Quotient.mk _ a) = MvPowerSeries.constantCoeff a := fun _ => rfl
  have hn : ∀ a, π a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow ((hm a).2 ha) _
  refine ⟨π, hπ, hn, Module.finite_of_surjective_of_ker_le_nilradical π (fun x => ⟨algebraMap _ _ x, π.commutes x⟩)
    (fun a ha => hn a ha) (IsNoetherian.noetherian _)⟩

theorem UpperTheory.V.Loc.lemma2a :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (C : Type) [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)), D.On U r → (∀ s ∈ Iq l, (r s).mat.charpoly = ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))) ∧ ∀ s : Fin 3 → GQ l, (∀ a, s a ∈ Iq l) → ((r (s 0)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 0 (s 0)))) * ((r (s 1)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 1 (s 1)))) * ((r (s 2)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 2 (s 2)))) = 0 := by
  intro hL l _ O _ _ _ _ _ _ _ D U C _ _ r hr
  obtain ⟨f, rfl, hf⟩ := hr
  show Cond D.Ψ (Iq l) (push f U.r.hom)
  obtain ⟨S, hS⟩ := cond_eqs D.Ψ (Iq l) U.r.hom
  obtain ⟨_, _, _⟩ := frac_alg l O
  obtain ⟨x, hx, -⟩ := univEx D U
  obtain ⟨-, φ, hφ⟩ := rtCompl hL D U (FractionRing O) x hx
  refine (hS C f).2 fun a ha => hf ?_
  rw [← hφ.ker, RingHom.mem_ker, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (MvPowerSeries (Fin 12) (FractionRing O)))
      (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]
  intro n
  refine Ideal.pow_le_pow_right n.le_succ ?_
  obtain ⟨π, hπ, hn, hfin⟩ := trunc_data (FractionRing O) n
  let B := MvPowerSeries (Fin 12) (FractionRing O) ⧸ maximalIdeal (MvPowerSeries (Fin 12) (FractionRing O)) ^ (n + 1)
  haveI : Module.Finite ℚ_[l] B := Module.Finite.trans (FractionRing O) B
  let g : U.R →ₐ[O] B := (Ideal.Quotient.mkₐ O _).comp φ
  have hon : D.On U (push g U.r.hom) := ⟨g, rfl, fun y hy => by
    rw [← hφ.ker, RingHom.mem_ker] at hy
    show Ideal.Quotient.mkₐ O _ (φ y) = 0
    rw [hy, map_zero]⟩
  obtain ⟨hc, -, hcr⟩ := rtPoints hL D U B _ hon
  have hred : (GG.map (π : B →+* FractionRing O)).comp (push g U.r.hom) = D.rz (FractionRing O) := by
    have e : (π : B →+* FractionRing O).comp (g : U.R →+* B) =
        (algebraMap O (FractionRing O)).comp (x : U.R →+* O) := RingHom.ext fun y => (hπ (φ y)).trans (hφ.const y)
    unfold Dat3.rz
    rw [← show push x U.r.hom = r0 D.η D.Ψ from hx]
    refine MonoidHom.ext fun s => ?_
    simp only [push, MonoidHom.comp_apply, GG.map_map, e]
  obtain ⟨u, m, hu, -, -, hum⟩ := (ordEq hL D (FractionRing O) B π hn _).1 ⟨U.r.hasMult, hred, hc, hcr⟩
  have hcond : Cond D.Ψ (Iq l) (push g U.r.hom) := by
    rw [hum]
    exact cond_conj _ _ u (fun s hs => (hu.mult s).trans (D.η_unr s hs)) m
      (cond_tri _ _ u hu.tri (triDiag D (FractionRing O) B π hn u hu))
  exact Ideal.Quotient.eq_zero_iff_mem.1 ((hS B g).1 hcond a ha)
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

namespace UpperTheory.V.Loc

private theorem commuting_upper_triangular_distinct {K : Type} [Field K] (d : Fin 3 → K) (hd : Function.Injective d)
    (A k B : Matrix (Fin 3) (Fin 3) K) (h : A * k = k * B)
    (hA : ∀ a b, wt a b < 0 → A a b = 0) (hB : ∀ a b, wt a b < 0 → B a b = 0)
    (hA' : ∀ a, A a a = d a) (hB' : ∀ a, B a a = d a) : ∀ a b, wt a b < 0 → k a b = 0 := by
  have a10 := hA 1 0 (by decide)
  have a20 := hA 2 0 (by decide)
  have a21 := hA 2 1 (by decide)
  have b10 := hB 1 0 (by decide)
  have b20 := hB 2 0 (by decide)
  have b21 := hB 2 1 (by decide)
  have d01 : d 0 - d 1 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d02 : d 0 - d 2 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d12 : d 1 - d 2 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21, hA', hB'] at e20 e21 e10
  have k20 : k 2 0 = 0 := (mul_eq_zero.1 (show (d 0 - d 2) * k 2 0 = 0 by linear_combination -e20)).resolve_left d02
  rw [k20] at e21 e10
  have k21 : k 2 1 = 0 := (mul_eq_zero.1 (show (d 1 - d 2) * k 2 1 = 0 by linear_combination -e21)).resolve_left d12
  have k10 : k 1 0 = 0 := (mul_eq_zero.1 (show (d 0 - d 1) * k 1 0 = 0 by linear_combination -e10)).resolve_left d01
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | assumption

private theorem diagonalize_three_by_three_split {K : Type} [Field K] (d : Fin 3 → K) (hd : Function.Injective d)
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.charpoly = ∏ a, (X - C (d a))) :
    ∃ h : GL (Fin 3) K, ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M * h = Matrix.diagonal d :=
  _root_.UpperTheory.Reformulated.B.DiagonalizeThreeByThree.diagonalize_three_by_three_split d hd M hM

private theorem three_eigenvalue_product_zero {K : Type} [Field K] (d p : Fin 3 → K) (hd : Function.Injective d)
    (N : Matrix (Fin 3) (Fin 3) K)
    (h0 : (N - Matrix.scalar _ (p 0)) * (Matrix.diagonal d - Matrix.scalar _ (d 1)) *
      (Matrix.diagonal d - Matrix.scalar _ (d 2)) = 0)
    (h1 : (Matrix.diagonal d - Matrix.scalar _ (d 0)) * (N - Matrix.scalar _ (p 1)) *
      (Matrix.diagonal d - Matrix.scalar _ (d 2)) = 0)
    (h2 : (Matrix.diagonal d - Matrix.scalar _ (d 0)) * (Matrix.diagonal d - Matrix.scalar _ (d 1)) *
      (N - Matrix.scalar _ (p 2)) = 0) :
    (∀ a b, wt a b < 0 → N a b = 0) ∧ ∀ a, N a a = p a := by
  have d01 : d 0 - d 1 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d02 : d 0 - d 2 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d12 : d 1 - d 2 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d10 : d 1 - d 0 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d20 : d 2 - d 0 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d21 : d 2 - d 1 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have hs : ∀ c : K, Matrix.diagonal d - Matrix.scalar (Fin 3) c = Matrix.diagonal fun i => d i - c := fun c => by
    rw [Matrix.scalar_apply, Matrix.diagonal_sub]
  simp only [hs, Matrix.diagonal_mul_diagonal] at h0 h1 h2
  have e00 := congrFun (congrFun h0 0) 0
  have e10 := congrFun (congrFun h0 1) 0
  have e20 := congrFun (congrFun h0 2) 0
  have e11 := congrFun (congrFun h1 1) 1
  have e21 := congrFun (congrFun h2 2) 1
  have e22 := congrFun (congrFun h2 2) 2
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, d01, d02, d12, d10, d20, d21, sub_eq_zero] at e00 e10 e20 e11 e21 e22
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | assumption
  · intro a
    fin_cases a <;> assumption

private theorem conjugate_representation_mat {R D : Type} [CommRing R] [Group D] (r : D →* GG (m := 3) (R := R)) (h : GL (Fin 3) R) (g : D)
    (hg : (r g).right = 1) : (conjBy h⁻¹ r g).mat =
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

private theorem padic_int_ringHom_injective {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [CharZero K] (φ : ℤ_[l] →+* K) :
    Function.Injective φ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero
    (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) hx

private theorem exists_inertia_distinct_characters {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) (K : Type) [Field K] [CharZero K] [Algebra O K] :
    ∃ s ∈ Iq l, Function.Injective fun a => algebraMap O K (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s) := by
  obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := ((cycInertia l).2 D.τ.ker D.τ_open).2
  refine ⟨s, hs2, ?_⟩
  let φ : ℤ_[l] →+* K := (algebraMap O K).comp (algebraMap ℤ_[l] O)
  let t : Kˣ := Units.map (algebraMap O K : O →* K) (D.Ψ s)
  have ht : t = Units.map (φ : ℤ_[l] →* K) (cyc l l s) ^ D.e := by
    have h1 : D.τ s = 1 := hs1
    simp only [t]
    rw [D.Ψ_I s hs2, h1, mul_one, map_pow]
    rfl
  have hinf : ¬ IsOfFinOrder t := by
    rw [ht]
    intro h
    have h2 := h.of_pow (by have := D.e_pos; omega)
    exact hs ((Function.Injective.isOfFinOrder_iff (f := Units.map (φ : ℤ_[l] →* K))
      (Units.map_injective (padic_int_ringHom_injective φ))).1 h2)
  have e : ∀ a, algebraMap O K (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s) = ((t ^ wt1 a : Kˣ) : K) := fun a =>
    congrArg Units.val (map_zpow (Units.map (algebraMap O K : O →* K)) (D.Ψ s) (wt1 a))
  intro a b hab
  simp only [e] at hab
  have h3 := injective_zpow_iff_not_isOfFinOrder.2 hinf (Units.ext hab)
  simp only [wt1] at h3
  exact Fin.ext (by omega)

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.lemma2b :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (K : Type) [Field K] [CharZero K] [Algebra O K] (r : GQ l →* GG (m := 3) (R := K)), D.On U r → (∃ h, UpperTheory.V.UnitaryThreeInertia.TriIn D.η D.Ψ (Iq l) r h) ∧ ∀ h h', UpperTheory.V.UnitaryThreeInertia.TriIn D.η D.Ψ (Iq l) r h → UpperTheory.V.UnitaryThreeInertia.TriIn D.η D.Ψ (Iq l) r h' → ∀ a b, wt a b < 0 → ((h⁻¹ * h' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
  intro hP l _ O _ _ _ _ _ _ _ D U K _ _ _ r hr
  obtain ⟨hch, hpr⟩ := UpperTheory.V.Loc.lemma2a hP D U K r hr
  have hm : ∀ g, D.η g = 1 → (r g).right = 1 := by
    obtain ⟨f, rfl, -⟩ := hr
    exact fun g hg => (U.r.hasMult g).trans hg
  obtain ⟨s, hs, hd⟩ := exists_inertia_distinct_characters D K
  have hηs := D.η_unr s hs
  constructor
  · obtain ⟨h, hh⟩ := diagonalize_three_by_three_split _ hd _ (hch s hs)
    have hc : ∀ (A : Matrix (Fin 3) (Fin 3) K) (c : K),
        ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A * (h : Matrix (Fin 3) (Fin 3) K) - Matrix.scalar _ c =
          ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A - Matrix.scalar _ c) * (h : Matrix (Fin 3) (Fin 3) K) := by
      intro A c
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc _ (Matrix.scalar _ c),
        Matrix.scalar_commute c (fun _ => Commute.all _ _), ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hc3 : ∀ A B C : Matrix (Fin 3) (Fin 3) K, A * B * C = 0 →
        (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A * (h : Matrix (Fin 3) (Fin 3) K)) *
          (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B * (h : Matrix (Fin 3) (Fin 3) K)) *
          (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * C * (h : Matrix (Fin 3) (Fin 3) K)) = 0 := by
      intro A B C h0
      have : ∀ Y : Matrix (Fin 3) (Fin 3) K,
          (h : Matrix (Fin 3) (Fin 3) K) * (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Y) = Y :=
        fun Y => by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      simp only [Matrix.mul_assoc, this]
      rw [← Matrix.mul_assoc B, ← Matrix.mul_assoc A, ← Matrix.mul_assoc A, h0, Matrix.zero_mul, Matrix.mul_zero]
    have hI : ∀ x ∈ Iq l, (∀ a b, wt a b < 0 → (conjBy h⁻¹ r x).mat a b = 0) ∧
        ∀ a, (conjBy h⁻¹ r x).mat a a = algebraMap O K (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a x) := by
      intro x hx
      rw [conjugate_representation_mat r h x (hm x (D.η_unr x hx))]
      refine three_eigenvalue_product_zero _ (fun a => algebraMap O K (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a x)) hd _ ?_ ?_ ?_
      · rw [← hh, hc, hc, hc]
        exact hc3 _ _ _ (hpr ![x, s, s] fun a => by fin_cases a <;> assumption)
      · rw [← hh, hc, hc, hc]
        exact hc3 _ _ _ (hpr ![s, x, s] fun a => by fin_cases a <;> assumption)
      · rw [← hh, hc, hc, hc]
        exact hc3 _ _ _ (hpr ![s, s, x] fun a => by fin_cases a <;> assumption)
    refine ⟨h, fun g hg => ?_, fun x hx _ => (hI x hx).2⟩
    have hx : g * s * g⁻¹ ∈ Iq l := (iqBasic l).1.conj_mem s hs g
    have hr1 : ∀ x, D.η x = 1 → (conjBy h⁻¹ r x).right = 1 := fun x hx => by simp [conjBy, hm x hx]
    have hmul : ∀ x y, D.η x = 1 →
        (conjBy h⁻¹ r (x * y)).mat = (conjBy h⁻¹ r x).mat * (conjBy h⁻¹ r y).mat := fun x y hx => by
      rw [map_mul]
      simp only [GG.mat, SemidirectProduct.mul_left, hr1 x hx, sgnAct_one, Units.val_mul]
    refine commuting_upper_triangular_distinct _ hd (conjBy h⁻¹ r (g * s * g⁻¹)).mat _ (conjBy h⁻¹ r s).mat ?_ (hI _ hx).1 (hI s hs).1
      (fun a => ?_) (hI s hs).2
    · rw [← hmul _ _ (D.η_unr _ hx), ← hmul _ _ hg, inv_mul_cancel_right]
    · rw [(hI _ hx).2]
      simp only [UpperTheory.V.UnitaryThreeInertia.psi, map_mul, map_inv, mul_inv_cancel_comm]
  · intro h h' H H'
    refine commuting_upper_triangular_distinct _ hd (conjBy h⁻¹ r s).mat _ (conjBy h'⁻¹ r s).mat ?_ (H.tri s hηs) (H'.tri s hηs)
      (H.ine s hs hηs) (H'.ine s hs hηs)
    rw [conjugate_representation_mat r h s (hm s hηs), conjugate_representation_mat r h' s (hm s hηs), Units.val_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
