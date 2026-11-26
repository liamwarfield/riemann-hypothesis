module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyAndPrimeDvdDegOfDvdNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqMinpolyPow
open CategoryTheory Polynomial
open GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.CharpolyMinpolyPower

theorem eq_pow_of_roots (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (P m : ℚ[X]) (hP : P.Monic)
    (hm : m.Monic) (hirr : Irreducible m) (h : ∀ a : Ω, aeval a P = 0 → minpoly ℚ a = m) :
    ∃ k : ℕ, P = m ^ k := by
  suffices H : ∀ n : ℕ, ∀ Q : ℚ[X], Q.natDegree = n → Q.Monic →
      (∀ a : Ω, aeval a Q = 0 → minpoly ℚ a = m) → ∃ k : ℕ, Q = m ^ k from H _ P rfl hP h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hQn hQ hroots
    by_cases hn : Q.natDegree = 0
    · exact ⟨0, by rw [pow_zero]; exact Polynomial.eq_one_of_monic_natDegree_zero hQ hn⟩
    · have hdeg : Q.degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hQ.ne_zero]
        exact_mod_cast hn
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_aeval_eq_zero Ω Q hdeg
      have hdvd : m ∣ Q := hroots a ha ▸ minpoly.dvd ℚ a ha
      obtain ⟨Q', rfl⟩ := hdvd
      have hQ' : Q'.Monic := hm.of_mul_monic_left hQ
      have hsum : (m * Q').natDegree = m.natDegree + Q'.natDegree := hm.natDegree_mul hQ'
      have hm0 : 0 < m.natDegree := hirr.natDegree_pos
      obtain ⟨k, hk⟩ := ih Q'.natDegree (by omega) Q' rfl hQ'
        (fun b hb => hroots b (by rw [map_mul, hb, mul_zero]))
      exact ⟨k + 1, by rw [hk, pow_succ, mul_comm]⟩

theorem deg_ne_zero {K : Type} [Field K] (A : AbVar K) {F : Type} [Field F] [NumberField F]
    (ι : NumberField.RingOfIntegers F →+* End A) (r : NumberField.RingOfIntegers F) (hr : r ≠ 0) :
    deg (ι r).asHom ≠ 0 := by
  have hI : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hN0 : Ideal.absNorm (Ideal.span {r}) ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
  have hc : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hN0
  have hι : (ι r).asHom ≫ (ι s).asHom = ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • 𝟙 A := by
    rw [← End.mul_asHom, ← map_mul, hs, map_natCast, natCast_zsmul, ← nsmul_one]
    exact map_nsmul End.addEquiv _ (1 : End A)
  obtain ⟨-, hdN⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A _ hc
  have hcomp := (isIsogeny_comp_iff_and_deg_comp K A A A (ι r).asHom (ι s).asHom rfl rfl).2
  rw [hι, hdN] at hcomp
  intro h0
  rw [h0, zero_mul] at hcomp
  exact pow_ne_zero _ (Int.natAbs_ne_zero.2 hc) hcomp

theorem charpoly_eq_minpoly_pow {K : Type} [Field K] (A : AbVar K) (hA : A.dim ≠ 0) {F : Type} [Field F]
    [NumberField F] (ι : NumberField.RingOfIntegers F →+* End A) (x : NumberField.RingOfIntegers F) :
    ∃ k : ℕ, 0 < k ∧ (charpoly (ι x)).map (Int.castRingHom ℚ) = minpoly ℚ (x : F) ^ k := by
  obtain ⟨hcp, -⟩ := charpoly_spec K A (ι x)
  obtain ⟨hmon, hdeg, -⟩ := hcp
  have hPm : ((charpoly (ι x)).map (Int.castRingHom ℚ)).Monic := hmon.map _
  have hPdeg : ((charpoly (ι x)).map (Int.castRingHom ℚ)).natDegree = 2 * A.dim := by
    rw [hmon.natDegree_map, hdeg]
  let ιa : NumberField.RingOfIntegers F →ₐ[ℤ] End A :=
    AlgHom.mk ι (fun n => by
      show ι (algebraMap ℤ _ n) = algebraMap ℤ (End A) n
      rw [eq_intCast (algebraMap ℤ (NumberField.RingOfIntegers F)), eq_intCast (algebraMap ℤ (End A))]
      exact map_intCast ι n)
  have hxint : IsIntegral ℚ (x : F) := Algebra.IsIntegral.isIntegral _
  have key : ∀ a : AlgebraicClosure ℚ, aeval a ((charpoly (ι x)).map (Int.castRingHom ℚ)) = 0 →
      minpoly ℚ a = minpoly ℚ (x : F) := by
    intro a ha
    have haint : IsIntegral ℚ a := IsAlgebraic.isIntegral ⟨_, hPm.ne_zero, ha⟩
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ a)
    have hRa : aeval a (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 :=
      IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) _ (minpoly.aeval ℚ a)
    have hprod := deg_aeval_eq_prod_aroots K A (ι x) (AlgebraicClosure ℚ)
      (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))
    have hmem : a ∈ ((charpoly (ι x)).map (Int.castRingHom ℚ)).aroots (AlgebraicClosure ℚ) :=
      (Polynomial.mem_aroots).2 ⟨hPm.ne_zero, ha⟩
    rw [Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, hmem, hRa⟩)] at hprod
    have hdeg0 : deg (aeval (ι x)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))).asHom = 0 := by
      have h := (map_eq_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective).1 hprod
      exact_mod_cast h
    rw [show aeval (ι x) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) =
        ι (aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a))) from
      Polynomial.aeval_algHom_apply ιa x _] at hdeg0
    have hRx : aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 := by
      by_contra hne
      exact deg_ne_zero A ι _ hne hdeg0
    have hRxF : aeval (x : F) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ a)) = 0 := by
      have h := congrArg (algebraMap (NumberField.RingOfIntegers F) F) hRx
      rwa [map_zero, ← Polynomial.aeval_algebraMap_apply] at h
    have hqx : aeval (x : F) (minpoly ℚ a) = 0 := by
      have h1 : aeval (x : F) ((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
          (minpoly ℚ a)).map (algebraMap ℤ ℚ)) = 0 := by
        rwa [Polynomial.aeval_map_algebraMap]
      rw [hb, map_zsmul] at h1
      exact (smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero hbM)
    exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible haint) hqx (minpoly.monic haint)
  obtain ⟨k, hk⟩ := eq_pow_of_roots (AlgebraicClosure ℚ) _ _ hPm (minpoly.monic hxint)
    (minpoly.irreducible hxint) key
  refine ⟨k, Nat.pos_of_ne_zero ?_, hk⟩
  rintro rfl
  rw [hk, pow_zero, Polynomial.natDegree_one] at hPdeg
  omega

end GlobalTheory.CharpolyMinpolyPower
end

open CategoryTheory GlobalTheory.AV GlobalTheory.AV.AbVar NumberField Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.DegNorm

theorem dvd_algebraMap_norm {S : Type} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S] (x : S) :
    x ∣ algebraMap ℤ S (Algebra.norm ℤ x) := by
  classical
  let b := Module.Free.chooseBasis ℤ S
  let M := Algebra.leftMulMatrix b x
  have h0 : aeval x M.charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact Matrix.aeval_self_charpoly M
  have hsplit : aeval x M.charpoly = x * aeval x M.charpoly.divX + algebraMap ℤ S (M.charpoly.coeff 0) := by
    conv_lhs => rw [← X_mul_divX_add M.charpoly]
    rw [map_add (f := _), map_mul, aeval_X, aeval_C]
  rw [h0] at hsplit
  refine ⟨-(algebraMap ℤ S ((-1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ S)) * aeval x M.charpoly.divX), ?_⟩
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_eq_sign_charpoly_coeff, map_mul]
  linear_combination (-(algebraMap ℤ S ((-1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ S)))) * hsplit

theorem isIsogeny_and_deg_ne_zero {K : Type} [Field K] (A : AbVar K) {F : Type} [Field F] [NumberField F]
    (ι : 𝓞 F →+* End A) (z : 𝓞 F) (hz : z ≠ 0) :
    IsIsogeny (ι z).asHom ∧ deg (ι z).asHom ≠ 0 := by
  obtain ⟨y, hy⟩ := dvd_algebraMap_norm z
  have hN : Algebra.norm ℤ z ≠ 0 := by
    intro h
    have h1 := Algebra.coe_norm_int z
    rw [h, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff] at h1
    exact hz (by exact_mod_cast h1)
  have hc : (ι y).asHom ≫ (ι z).asHom = Algebra.norm ℤ z • 𝟙 A := by
    rw [← End.mul_asHom]
    rw [← map_mul, ← hy, algebraMap_int_eq, Int.coe_castRingHom, map_intCast, ← zsmul_one]
    rfl
  have h := isIsogeny_comp_iff_and_deg_comp K A A A (ι y).asHom (ι z).asHom rfl rfl
  obtain ⟨hi, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A _ hN
  rw [hc] at h
  refine ⟨(h.1.1 hi).2, fun h0 => ?_⟩
  rw [h0, mul_zero] at h
  rw [h.2] at hd
  exact pow_ne_zero _ (Int.natAbs_ne_zero.2 hN) hd.symm

end GlobalTheory.AV.AbVar.DegNorm

namespace GlobalTheory.AV.AbVar.DegNorm

theorem charpoly_eq_minpoly_pow {K : Type} [Field K] (A : AbVar K) (hA : A.dim ≠ 0) {F : Type} [Field F]
    [NumberField F] (ι : 𝓞 F →+* End A) (x : 𝓞 F) :
    ∃ k : ℕ, 0 < k ∧ (charpoly (ι x)).map (Int.castRingHom ℚ) = minpoly ℚ (x : F) ^ k := by
  first
  | exact @_root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow
  | exact _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow
  | (apply _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow ..)

end GlobalTheory.AV.AbVar.DegNorm

namespace GlobalTheory.AV.AbVar.DegNorm

open IntermediateField

end GlobalTheory.AV.AbVar.DegNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedKernelIsogenyTangentInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedOfDualNumbers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDegreeOneBiholomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedOfDualConstField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.TangentCrit

theorem formallyUnramified_of_dual_const_field {K A B : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Algebra.FiniteType K B] [Algebra.FiniteType A B]
    (H : ∀ φ : B →+* DualNumber K, (∀ c, φ (algebraMap K B c) = algebraMap K (DualNumber K) c) →
      (∀ a, (φ (algebraMap A B a)).snd = 0) → ∀ b, (φ b).snd = 0) :
    Algebra.FormallyUnramified A B := by
  refine ⟨?_⟩
  by_contra hne
  rw [← Module.support_eq_empty_iff (R := B), ← ne_eq, ← Set.nonempty_iff_ne_empty] at hne
  obtain ⟨p, hp⟩ := hne
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let P : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  have hP : P ∈ Module.support B Ω[B⁄A] := by
    rw [Module.support_eq_zeroLocus] at hp ⊢
    exact fun x hx => hpm (hp hx)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hP
  have hsurj : Function.Surjective (algebraMap B m.ResidueField) := by
    intro y
    obtain ⟨x, rfl⟩ := m.bijective_algebraMap_quotient_residueField.surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨b, rfl⟩
  haveI : Algebra.FiniteType K m.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom K B m.ResidueField) hsurj
  haveI : Module.Finite K m.ResidueField := finite_of_finite_type_of_isJacobsonRing K _
  let ev : m.ResidueField →ₐ[K] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra m.ResidueField K := ev.toRingHom.toAlgebra
  letI : Algebra B K := (ev.toRingHom.comp (algebraMap B m.ResidueField)).toAlgebra
  haveI : IsScalarTower B m.ResidueField K := .of_algebraMap_eq fun _ => rfl
  letI : Algebra A K := ((algebraMap B K).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B K := .of_algebraMap_eq fun _ => rfl
  have key : Function.Injective ((0 : Ω[B⁄A] →ₗ[B] PUnit.{1}).lTensor m.ResidueField) :=
    lTensor_injective_of_extend (k := K) _ fun χ => by
      refine ⟨0, ?_⟩
      let D : Derivation A B K := χ.compDer (KaehlerDifferential.D A B)
      have hlin : ∀ c, derToDual D (algebraMap K B c) = algebraMap K (DualNumber K) c := by
        intro c
        ext
        · rw [fst_derToDual]
          change ev (algebraMap B m.ResidueField (algebraMap K B c)) = _
          rw [← IsScalarTower.algebraMap_apply, ev.commutes]
          rfl
        · rw [snd_derToDual, IsScalarTower.algebraMap_apply K A B, D.map_algebraMap]
          rfl
      have := H (derToDual D) hlin (fun a => (snd_derToDual D _).trans (D.map_algebraMap a))
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
      have := this b
      rw [snd_derToDual] at this
      simpa [D] using this.symm
  obtain ⟨z, hz⟩ := exists_ne (0 : m.ResidueField ⊗[B] Ω[B⁄A])
  exact hz (key (by simp))

end GlobalTheory.TangentCrit

namespace GlobalTheory.TangentCrit

end GlobalTheory.TangentCrit
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.FinUnram

theorem formallyUnramified_of_dual_const : ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R] [Module.Finite K R], (∀ (φ : R →ₐ[K] DualNumber K) (r : R), (φ r).snd = 0) → Algebra.FormallyUnramified K R := by
  intro K _ _ R _ _ _ H
  haveI : Algebra.FiniteType K R := inferInstance
  refine GlobalTheory.TangentCrit.formallyUnramified_of_dual_const_field (K := K) (A := K) (B := R)
    (fun φ hK _ b => ?_)
  exact H { φ with commutes' := hK } b

end GlobalTheory.FinUnram
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formally_unramified_of_dual_numbers : ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R] [Module.Finite K R], (∀ (φ : R →ₐ[K] DualNumber K) (r : R), (φ r).snd = 0) → Algebra.FormallyUnramified K R := by
  first | (exact @GlobalTheory.FinUnram.formallyUnramified_of_dual_const) | (exact GlobalTheory.FinUnram.formallyUnramified_of_dual_const) | (intros; apply GlobalTheory.FinUnram.formallyUnramified_of_dual_const  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedKernelIsogenyTangentInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerUnram

theorem formallyUnramified_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) := by
  intro K _ _ B f hf H
  have hfin : IsFinite (Hom.hom f).left := hf.1
  set Z := pullback (Hom.hom f).left η[B.X].left with hZ
  set p : Z ⟶ Sp K := pullback.snd (Hom.hom f).left η[B.X].left with hp
  have : IsFinite p := inferInstance
  have : IsAffine Z := isAffine_of_isAffineHom p
  have hnat := Scheme.isoSpec_hom_naturality p
  have hS : Spec.map p.appTop = Z.isoSpec.inv ≫ p ≫ (Sp K).isoSpec.hom := by
    rw [← hnat]; simp
  have hfinS : IsFinite (Spec.map p.appTop) := by rw [hS]; infer_instance
  have hfinR : p.appTop.hom.Finite := (IsFinite.SpecMap_iff _).1 hfinS
  let ψ : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop
  let _ : Algebra K Γ(Z, ⊤) := ψ.hom.toAlgebra
  have : Module.Finite K Γ(Z, ⊤) := by
    have h : ψ.hom.Finite := by
      show (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite
      exact hfinR.comp (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
    exact h
  have hp' : p.appTop = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ ψ := by simp [ψ]
  have : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified), hp',
    CommRingCat.hom_comp, RingHom.RespectsIso.cancel_left_isIso RingHom.FormallyUnramified.respectsIso]
  show Algebra.FormallyUnramified K Γ(Z, ⊤)
  refine GlobalTheory.T.formally_unramified_of_dual_numbers K Γ(Z, ⊤) fun φ r => ?_

  let q : Sp (DualNumber K) ⟶ Z := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Z.isoSpec.inv
  have hq : q ≫ p = spMap (algebraMap K (DualNumber K)) := by
    have e := Scheme.isoSpec_inv_naturality p
    simp only [q, Category.assoc]
    rw [← e, Scheme.isoSpec_Spec]
    simp only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    exact φ.commutes a
  have hfst : ∀ {T : Scheme} (g : T ⟶ Z), (g ≫ pullback.fst (Hom.hom f).left η[B.X].left) ≫ B.X.hom = g ≫ p := by
    intro T g
    rw [Category.assoc, ← Over.w (Hom.hom f), ← Category.assoc (pullback.fst _ _), pullback.condition,
      Category.assoc, Over.w η[B.X]]
    rfl
  let v : epsPtR (𝟙 (Sp K)) ⟶ B.X := Over.homMk (q ≫ pullback.fst _ _) (by
    rw [hfst, hq]; exact (Category.comp_id _).symm)
  have hv : v ≫ Hom.hom f = 1 := by
    ext1
    rw [Over.comp_left, Hom.one_def, Over.comp_left]
    simp only [v, Over.homMk_left, Category.assoc]
    rw [pullback.condition, ← Category.assoc q, hq]
    rfl

  let T₀ : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let red : T₀ ⟶ epsPtR (𝟙 (Sp K)) := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, ← Spec.map_id]
    congr 1)
  let bas : epsPtR (𝟙 (Sp K)) ⟶ T₀ := Over.homMk (spMap (algebraMap K (DualNumber K))) rfl
  have hrb : red ≫ bas = 𝟙 T₀ := by
    ext1
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  let w : epsPtR (𝟙 (Sp K)) ⟶ B.X := v * (bas ≫ red ≫ v)⁻¹
  have hw₀ : red ≫ w = 1 := by
    simp only [w]
    rw [comp_mul, GrpObj.comp_inv, ← Category.assoc red bas, hrb, Category.id_comp, mul_inv_cancel]
  have hwf : w ≫ Hom.hom f = 1 := by
    simp only [w]
    rw [mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hv, comp_one, comp_one, inv_one,
      _root_.mul_one]
  have hw : w = 1 := H w (by
    have := congrArg Over.Hom.left hw₀
    rw [Over.comp_left] at this
    exact this) hwf
  have hvc : v = bas ≫ red ≫ v := mul_inv_eq_one.mp hw
  have hq2 : q = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ q := by
    refine pullback.hom_ext ?_ ?_
    · have := congrArg Over.Hom.left hvc
      simpa [v, red, bas] using this
    · change q ≫ p = _ ≫ _ ≫ q ≫ p
      rw [hq, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
  simp only [q, ← Category.assoc] at hq2
  rw [cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at hq2
  have := congrArg TrivSqZeroExt.snd congr($(Spec.map_injective hq2).hom r)
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.KerUnram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedKernelIsogenyTangentInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyUnramified_kernel_isogeny_tangent_injective : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) := by
  first | (exact @GlobalTheory.KerUnram.formallyUnramified_ker) | (exact GlobalTheory.KerUnram.formallyUnramified_ker) | (intros; apply GlobalTheory.KerUnram.formallyUnramified_ker  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointAbelianVarietyAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConjugatePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreAV

section

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) (A : Over S) [GrpObj A]

theorem pull_map_left_fst {B : Over S} (f : A ⟶ B) :
    ((Over.pullback x).map f).left ≫ pullback.fst B.hom x = pullback.fst A.hom x ≫ f.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

theorem push_comp_map {T : Over (Sp k)} {g : T.left ⟶ S} (f : A ⟶ A)
    (e : (T ⟶ (Over.pullback x).obj A) → (Over.mk g ⟶ A)) (he : ∀ z, (e z).left = z.left ≫ pullback.fst A.hom x)
    (z : T ⟶ (Over.pullback x).obj A) : e (z ≫ (Over.pullback x).map f) = e z ≫ f := by
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, pull_map_left_fst, Category.assoc]

end

open GlobalTheory.AV.AbVar in
theorem fibre_av : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c).asHom) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c).asHom = 1 → w = 1 := by
  intro S A _ _ hA F _ _ act k _ _ x
  letI : GrpObj ((Over.pullback x).obj A) := Functor.grpObjObj
  have h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x) := isGrpPullback_pullback A x
  have hab : IsAbelianScheme ((Over.pullback x).obj A) := GlobalTheory.isAbelianScheme_pullback_obj x A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab
  let B : AbVar k := { X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)
  have i : ptOver k (AlgebraicClosure k) ≅ 𝟙_ (Over (Sp k)) := by
    let σ : k ≃+* AlgebraicClosure k :=
      RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : IsIso (spMap (algebraMap k (AlgebraicClosure k))) := by
      change IsIso (Spec.map σ.toCommRingCatIso.hom)
      infer_instance
    exact Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (by
      change spMap _ ≫ 𝟙 _ = spMap _
      exact Category.comp_id _)
  let ptEquiv : (𝟙_ (Over (Sp k)) ⟶ B.X) ≃* B.Pt :=
    { toFun := fun t => i.hom ≫ t
      invFun := fun t => i.inv ≫ t
      left_inv := fun t => by simp
      right_inv := fun t => by simp
      map_mul' := fun t u => MonObj.comp_mul _ t u }
  let e : (Over.mk x ⟶ A) ≃* B.Pt := e₀.symm.trans ptEquiv
  have hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c)) := fun c => by
    have := act.hom c; infer_instance
  let ψf : 𝓞 F → (B ⟶ B) := fun c => Hom.mk (A := B) (B := B)
    ((Over.pullback x).map (act.act c)) (h := hm c)
  have hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c) := fun c => rfl
  have hom_ext {f g : B ⟶ B} (hfg : Hom.hom f = Hom.hom g) : f = g := Subtype.ext hfg
  have act0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  let ψ : 𝓞 F →+* End B :=
    { toFun := fun c => End.of (ψf c)
      map_one' := by
        apply End.ext
        change ψf 1 = 𝟙 B
        apply hom_ext
        rw [hψ, act.one, CategoryTheory.Functor.map_id, id_hom]
      map_mul' := fun a b => by
        apply End.ext
        change ψf (a * b) = ψf b ≫ ψf a
        apply hom_ext
        rw [comp_hom, hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]
      map_zero' := by
        apply End.ext
        change ψf 0 = 0
        apply hom_ext
        rw [hψ, act0, zero_hom]
        exact CategoryTheory.Functor.map_one _
      map_add' := fun a b => by
        apply End.ext
        change ψf (a + b) = ψf a + ψf b
        apply hom_ext
        rw [add_hom, hψ, hψ, hψ, act.add]
        exact CategoryTheory.Functor.map_mul _ _ _ }
  refine ⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩
  · show ptEquiv (e₀.symm (z ≫ act.act c)) =
      ptEquiv (e₀.symm z) ≫ (Over.pullback x).map (act.act c)
    have : e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply, push_comp_map x A (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  · obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k)))
      (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)
    obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)
    have one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫
        pullback.fst A.hom x := by
      rw [← he₂, map_one]
    have r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left := by
      rw [he₁, one, ← Category.assoc, hw1]
    have r2 : e₁ w ≫ act.act c = 1 := by
      rw [← push_comp_map x A (act.act c) e₁ he₁]
      have hw2' : w ≫ Hom.hom (ψf c) = 1 := hw2
      change e₁ (w ≫ Hom.hom (ψf c)) = 1
      rw [hw2', map_one]
    exact e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)

end GlobalTheory.FibreAV
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_point_abelian_variety_action : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c).asHom) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c).asHom = 1 → w = 1 := by
  intro S A _ _ hA F _ _ act k _ _ x
  have push_comp_map {T : Over (Sp k)} {g : T.left ⟶ S} (f : A ⟶ A)
      (e : (T ⟶ (Over.pullback x).obj A) → (Over.mk g ⟶ A))
      (he : ∀ z, (e z).left = z.left ≫ pullback.fst A.hom x)
      (z : T ⟶ (Over.pullback x).obj A) :
      e (z ≫ (Over.pullback x).map f) = e z ≫ f := by
    have map_fst : ((Over.pullback x).map f).left ≫ pullback.fst A.hom x =
        pullback.fst A.hom x ≫ f.left := by
      simp only [Over.pullback_map_left, pullback.lift_fst]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, map_fst, Category.assoc]
  have h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x) := isGrpPullback_pullback A x
  have hab : IsAbelianScheme ((Over.pullback x).obj A) := GlobalTheory.isAbelianScheme_pullback_obj x A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab
  let B : AbVar k := { X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)
  have i : ptOver k (AlgebraicClosure k) ≅ 𝟙_ (Over (Sp k)) := by
    let σ : k ≃+* AlgebraicClosure k :=
      RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : IsIso (spMap (algebraMap k (AlgebraicClosure k))) := by
      change IsIso (Spec.map σ.toCommRingCatIso.hom)
      infer_instance
    exact Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (by
      change spMap _ ≫ 𝟙 _ = spMap _
      exact Category.comp_id _)
  let ptEquiv : (𝟙_ (Over (Sp k)) ⟶ B.X) ≃* B.Pt :=
    { toFun := fun t => i.hom ≫ t
      invFun := fun t => i.inv ≫ t
      left_inv := fun t => by simp
      right_inv := fun t => by simp
      map_mul' := fun t u => MonObj.comp_mul _ t u }
  let e : (Over.mk x ⟶ A) ≃* B.Pt := e₀.symm.trans ptEquiv
  have hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c)) := fun c => by
    have := act.hom c; infer_instance
  let ψf : 𝓞 F → (B ⟶ B) := fun c => Hom.mk (A := B) (B := B)
    ((Over.pullback x).map (act.act c)) (h := hm c)
  have hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c) := fun c => rfl
  have hom_ext {f g : B ⟶ B} (hfg : Hom.hom f = Hom.hom g) : f = g := Subtype.ext hfg
  have act0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  let ψ : 𝓞 F →+* End B :=
    { toFun := fun c => End.of (ψf c)
      map_one' := by
        apply End.ext
        change ψf 1 = 𝟙 B
        apply hom_ext
        rw [hψ, act.one, CategoryTheory.Functor.map_id, id_hom]
      map_mul' := fun a b => by
        apply End.ext
        change ψf (a * b) = ψf b ≫ ψf a
        apply hom_ext
        rw [comp_hom, hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]
      map_zero' := by
        apply End.ext
        change ψf 0 = 0
        apply hom_ext
        rw [hψ, act0, zero_hom]
        exact CategoryTheory.Functor.map_one _
      map_add' := fun a b => by
        apply End.ext
        change ψf (a + b) = ψf a + ψf b
        apply hom_ext
        rw [add_hom, hψ, hψ, hψ, act.add]
        exact CategoryTheory.Functor.map_mul _ _ _ }
  refine ⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩
  · show ptEquiv (e₀.symm (z ≫ act.act c)) =
      ptEquiv (e₀.symm z) ≫ (Over.pullback x).map (act.act c)
    have : e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply, push_comp_map (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  · obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k)))
      (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)
    obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)
    have one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫
        pullback.fst A.hom x := by
      rw [← he₂, map_one]
    have r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left := by
      rw [he₁, one, ← Category.assoc, hw1]
    have r2 : e₁ w ≫ act.act c = 1 := by
      rw [← push_comp_map (act.act c) e₁ he₁]
      have hw2' : w ≫ Hom.hom (ψf c) = 1 := hw2
      change e₁ (w ≫ Hom.hom (ψf c)) = 1
      rw [hw2', map_one]
    exact e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePowFinrankEqNatAbsNormPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePowFinrankEqNatAbsNormPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.DegNorm

open Polynomial IntermediateField

theorem deg_pow_finrank_eq_natAbs_norm_pow : ∀ (K : Type) [Field K] (B : AbVar K) (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* End B) (c : 𝓞 F), c ≠ 0 → deg (ψ c).asHom ^ Module.finrank ℚ F = (Algebra.norm ℤ c).natAbs ^ (2 * B.dim) := by
  intro K _ B F _ _ ψ c hc
  have hN : Algebra.norm ℤ c ≠ 0 := by
    intro h
    have h1 := Algebra.coe_norm_int c
    rw [h, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff] at h1
    exact hc (by exact_mod_cast h1)
  by_cases hB : B.dim = 0
  · obtain ⟨y, hy⟩ := dvd_algebraMap_norm c
    have hcomp : (ψ y).asHom ≫ (ψ c).asHom = Algebra.norm ℤ c • 𝟙 B := by
      rw [← End.mul_asHom]
      rw [← map_mul, ← hy, algebraMap_int_eq, Int.coe_castRingHom, map_intCast, ← zsmul_one]
      rfl
    have h := isIsogeny_comp_iff_and_deg_comp K B B B (ψ y).asHom (ψ c).asHom rfl rfl
    obtain ⟨-, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny K B _ hN
    rw [hcomp] at h
    rw [h.2, hB, mul_zero, pow_zero] at hd
    have h1 : deg (ψ c).asHom = 1 := Nat.eq_one_of_mul_eq_one_left hd
    rw [h1, hB, mul_zero, pow_zero, one_pow]
  · classical
    obtain ⟨k, hk, hPQ⟩ := charpoly_eq_minpoly_pow B hB ψ c
    obtain ⟨⟨-, hd, -⟩, -⟩ := isCharpoly_charpoly_unique K B (ψ c)
    have hxint : IsIntegral ℚ (c : F) := Algebra.IsIntegral.isIntegral _
    have hdeg : k * Module.finrank ℚ ℚ⟮(c : F)⟯ = 2 * B.dim := by
      have e := congrArg Polynomial.natDegree hPQ
      rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _), hd,
        Polynomial.natDegree_pow, ← IntermediateField.adjoin.finrank hxint] at e
      omega
    have hD := deg_aeval_eq_prod_aroots K B (ψ c) (AlgebraicClosure ℚ) Polynomial.X
    simp only [aeval_X, Multiset.map_id'] at hD
    rw [hPQ, Polynomial.aroots_pow, Multiset.prod_nsmul] at hD
    have hNr := Algebra.norm_eq_prod_roots (K := ℚ) (L := F) (AlgebraicClosure ℚ) (x := (c : F))
      (IsAlgClosed.splits _)
    have e : algebraMap ℚ (AlgebraicClosure ℚ) ((deg (ψ c).asHom : ℚ) ^ Module.finrank ℚ⟮(c : F)⟯ F) =
        algebraMap ℚ (AlgebraicClosure ℚ) (Algebra.norm ℚ (c : F) ^ k) := by
      rw [map_pow, map_pow, hD, hNr, ← pow_mul, ← pow_mul, mul_comm]
    have e2 := (algebraMap ℚ (AlgebraicClosure ℚ)).injective e
    rw [← Algebra.coe_norm_int] at e2
    have e3 : (deg (ψ c).asHom : ℤ) ^ Module.finrank ℚ⟮(c : F)⟯ F = Algebra.norm ℤ c ^ k := by
      exact_mod_cast e2
    have e4 := congrArg (fun t : ℤ => t ^ Module.finrank ℚ ℚ⟮(c : F)⟯) e3
    simp only [← pow_mul] at e4
    rw [hdeg, mul_comm, Module.finrank_mul_finrank] at e4
    have e5 := congrArg Int.natAbs e4
    simpa [Int.natAbs_pow] using e5

end GlobalTheory.AV.AbVar.DegNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePowFinrankEqNatAbsNormPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_pow_finrank_eq_natAbs_norm_pow : ∀ (K : Type) [Field K] (B : AbVar K) (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* End B) (c : 𝓞 F), c ≠ 0 → deg (A := B) (B := B) (ψ c).asHom ^ Module.finrank ℚ F = (Algebra.norm ℤ c).natAbs ^ (2 * B.dim) := by
  exact GlobalTheory.AV.AbVar.DegNorm.deg_pow_finrank_eq_natAbs_norm_pow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCardKernelEqNormPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.AVCount

section
attribute [local instance] Over.cartesianMonoidalCategory

theorem deg_eq_card_ker_of_unram : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) → deg f = Nat.card (ptMap f).ker := by
  intro K _ A B f hiso hpfu
  have hfl : Flat f.hom.left := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hiso).2.1
  have hfin : IsFinite f.hom.left := hiso.1
  let e : Sp K ⟶ B.X.left := η[B.X].left
  let p := pullback.snd f.hom.left e
  let i := pullback.fst f.hom.left e
  have he1 : e ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
  have hpi : i ≫ A.X.hom = p := by
    calc i ≫ A.X.hom = i ≫ f.hom.left ≫ B.X.hom := by rw [Over.w f.hom]
      _ = p ≫ e ≫ B.X.hom := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = p := by rw [he1, Category.comp_id]
  have hpet : Etale p := Etale.of_formallyUnramified_of_flat p
  let t : Sp (AlgebraicClosure K) ⟶ Sp K := (ptOver K (AlgebraicClosure K)).hom
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t (IsLocalRing.closedPoint _)
  rw [Scheme.Hom.finrank_pullback_snd] at hcard
  have horig : e (t (IsLocalRing.closedPoint _)) = B.origin := by
    rw [origin, GlobalTheory.AV.DegSep.one_left']
    change e _ = (𝟙 (Sp K) ≫ e) _
    rw [Category.id_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [horig] at hcard
  rw [deg, if_pos hiso, ← hcard]
  symm
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨pullback.lift y.1.left t (by
          have h := y.2
          rw [MonoidHom.mem_ker, ptMap_apply] at h
          have h2 : (y.1 ≫ f.hom).left = (1 : ptOver K (AlgebraicClosure K) ⟶ B.X).left := by rw [h]
          rw [Over.comp_left, GlobalTheory.AV.DegSep.one_left'] at h2
          exact h2), pullback.lift_snd _ _ _⟩
      invFun := fun y => ⟨Over.homMk (y.1 ≫ i) (by
          change (y.1 ≫ i) ≫ A.X.hom = t
          rw [Category.assoc, hpi, y.2]), by
          rw [MonoidHom.mem_ker, ptMap_apply]
          ext1
          rw [Over.comp_left, GlobalTheory.AV.DegSep.one_left']
          change (y.1 ≫ i) ≫ f.hom.left = t ≫ e
          rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩
      left_inv := fun y => by
        apply Subtype.ext
        ext1
        exact pullback.lift_fst _ _ _
      right_inv := fun y => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · rw [pullback.lift_snd]; exact y.2.symm }

end

theorem map_zero_eq_one_of_additive_to_group {M G : Type} [AddCommGroup M] [Group G] (f : M → G) (hadd : ∀ a a', f (a + a') = f a * f a') : f 0 = 1 := by
  have := hadd 0 0
  rw [add_zero] at this
  exact mul_left_cancel (this.symm.trans (mul_one (f 0)).symm)

theorem map_nsmul_eq_pow_of_additive_to_mulGroup {M G : Type} [AddCommGroup M] [Group G] (f : M → G) (hadd : ∀ a a', f (a + a') = f a * f a') (n : ℕ) (a : M) : f (n • a) = f a ^ n := by
  induction n with
  | zero => rw [zero_smul, map_zero_eq_one_of_additive_to_group f hadd, pow_zero]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem deg_eq_card_ker_of_tangent : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → deg f = Nat.card (ptMap f).ker :=
  fun K _ _ B f hf hv => deg_eq_card_ker_of_unram K B B f hf (GlobalTheory.T.formallyUnramified_kernel_isogeny_tangent_injective K B f hf hv)

theorem card_ker_eq_norm_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (h ℓ : ℕ), ℓ.Prime → (ℓ : k) ≠ 0 → (∀ j : ℕ, ∃ f : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) → (Over.mk x ⟶ A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) c • a) = f a ≫ act.act c) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g) → ∀ c : 𝓞 F, c ≠ 0 → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = (Algebra.norm ℤ c).natAbs ^ h := by
  intro S A _ _ hA F _ _ act k _ _ x h ℓ hℓ hℓk hyp c hc hv
  obtain ⟨B, e, ψ, he, htan⟩ := GlobalTheory.T.geometric_point_abelian_variety_action S A hA F act k x
  have hiso := (GlobalTheory.AV.AbVar.DegNorm.isIsogeny_and_deg_ne_zero B ψ c hc).1
  have hE := deg_eq_card_ker_of_tangent k B (ψ c).asHom hiso (htan c hv)
  have hD := GlobalTheory.T.degree_pow_finrank_eq_natAbs_norm_pow k B F ψ c hc
  have hker : Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = Nat.card (ptMap (ψ c).asHom).ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv (fun g => ?_)
    change _ ↔ e g ≫ Hom.hom (ψ c).asHom = 1
    rw [← he, MulEquiv.map_eq_one_iff]

  have htors : Nat.card {g : Over.mk x ⟶ A // g ^ ℓ = 1} = ℓ ^ (2 * B.dim) := by
    rw [← card_torsion_pt k B ℓ hℓk]
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv (fun g => ?_)
    change _ ↔ e g ^ ℓ = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have hL2 : Nat.card {g : Over.mk x ⟶ A // g ^ ℓ = 1} = ℓ ^ (h * Module.finrank ℚ F) := by
    obtain ⟨f, hadd, -, hinj, hsurj⟩ := hyp 1
    have h0 := map_zero_eq_one_of_additive_to_group f hadd
    have hns := map_nsmul_eq_pow_of_additive_to_mulGroup f hadd
    have hq : ((ℓ : ℕ) : 𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    have hkill : ∀ a : Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}, ℓ • a = 0 := by
      intro a
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, hq, zero_mul]
    have hcardQ : Nat.card (𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}) = ℓ ^ Module.finrank ℚ F := by
      have h1 := Ideal.absNorm_span_singleton ((ℓ ^ 1 : ℕ) : 𝓞 F)
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
      rw [h1]
      have : ((ℓ ^ 1 : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (ℓ : ℤ) := by simp
      rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
      simp
    let eq : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ 1 : ℕ) : 𝓞 F)}) ≃ {g : Over.mk x ⟶ A // g ^ ℓ = 1} :=
      Equiv.ofBijective (fun a => ⟨f a, by rw [← hns, hkill, h0]⟩)
        ⟨fun a b hab => hinj (congrArg Subtype.val hab),
         fun g => by obtain ⟨a, ha⟩ := hsurj g.1 (by rw [pow_one]; exact g.2); exact ⟨a, Subtype.ext ha⟩⟩
    rw [← Nat.card_congr eq, Nat.card_fun, hcardQ, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm]
  have hℓ1 : 1 < ℓ := hℓ.one_lt
  have hdim : 2 * B.dim = h * Module.finrank ℚ F := by
    have := htors.symm.trans hL2
    exact Nat.pow_right_injective hℓ.two_le this
  have hd0 : Module.finrank ℚ F ≠ 0 := Module.finrank_pos.ne'
  rw [hker, ← hE]
  apply Nat.pow_left_injective hd0
  change deg (A := B) (B := B) (ψ c).asHom ^ Module.finrank ℚ F = ((Algebra.norm ℤ c).natAbs ^ h) ^ Module.finrank ℚ F
  rw [hD, hdim, pow_mul]

end GlobalTheory.AVCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCardKernelEqNormPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (h ℓ : ℕ), ℓ.Prime → (ℓ : k) ≠ 0 → (∀ j : ℕ, ∃ f : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) → (Over.mk x ⟶ A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) c • a) = f a ≫ act.act c) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g) → ∀ c : 𝓞 F, c ≠ 0 → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = (Algebra.norm ℤ c).natAbs ^ h := by
  first | (exact @GlobalTheory.AVCount.card_ker_eq_norm_pow) | (exact GlobalTheory.AVCount.card_ker_eq_norm_pow) | (intros; apply GlobalTheory.AVCount.card_ker_eq_norm_pow  <;> assumption)
end
