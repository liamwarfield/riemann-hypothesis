module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralSuperposition
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekind
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGeneratorsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOfFormallyUnramified
open IsLocalRing Polynomial
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.AbhFin

theorem finite_integralClosure_of_formallyUnramified (R K C : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing C] [Algebra K C] [Algebra R C] [IsScalarTower R K C] [FiniteDimensional K C]
    [Algebra.FormallyUnramified K C] : Module.Finite R (integralClosure R C) := by
  classical
  haveI : IsArtinianRing C := IsArtinianRing.of_finite K C
  haveI : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field K C
  haveI := Fintype.ofFinite (MaximalSpectrum C)
  haveI : ∀ m : MaximalSpectrum C, Module.Finite R (integralClosure R (C ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : Algebra.FormallyUnramified K (C ⧸ m.asIdeal) :=
      Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal) Ideal.Quotient.mk_surjective
    haveI : Algebra.IsSeparable K (C ⧸ m.asIdeal) := Algebra.FormallyUnramified.isSeparable K _
    exact IsIntegralClosure.finite R K (C ⧸ m.asIdeal) _
  let red : ∀ m : MaximalSpectrum C, integralClosure R C →ₗ[R] integralClosure R (C ⧸ m.asIdeal) := fun m =>
    (((Ideal.Quotient.mkₐ R m.asIdeal).comp (integralClosure R C).val).codRestrict
      (integralClosure R (C ⧸ m.asIdeal))
      (fun a => (show IsIntegral R (a : C) from a.2).map (Ideal.Quotient.mkₐ R m.asIdeal))).toLinearMap
  refine Module.Finite.of_injective (LinearMap.pi red) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  apply Subtype.ext
  apply (IsArtinianRing.equivPi C).injective
  show _ = IsArtinianRing.equivPi C 0
  rw [map_zero]
  funext m
  exact congrArg Subtype.val (congrFun ha m)

end GlobalTheory.AbhFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFinite
open IsLocalRing
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.NormFin

theorem main : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  classical
  let K' := FractionRing D
  haveI : IsScalarTower S D K' := inferInstance
  have hSK' : Function.Injective (algebraMap S K') :=
    by
      rw [IsScalarTower.algebraMap_eq S D K']
      exact (IsFractionRing.injective D K').comp (FaithfulSMul.algebraMap_injective S D)
  letI : Algebra K K' := (IsFractionRing.lift hSK' : K →+* K').toAlgebra
  haveI : IsScalarTower S K K' :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap hSK' x).symm)
  haveI : SMulCommClass K D K' := ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  haveI : Algebra.FormallyUnramified K' (K' ⊗[K] L) := inferInstance
  haveI : FiniteDimensional K' (K' ⊗[K] L) := inferInstance
  haveI : IsScalarTower D K' (K' ⊗[K] L) := inferInstance
  have hfinC : Module.Finite D (integralClosure D (K' ⊗[K] L)) :=
    GlobalTheory.AbhFin.finite_integralClosure_of_formallyUnramified D K' (K' ⊗[K] L)
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  let f : D →ₐ[S] K' := IsScalarTower.toAlgHom S D K'
  let Φ : D ⊗[S] L →ₐ[S] K' ⊗[S] L := Algebra.TensorProduct.map f (AlgHom.id S L)
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (f.toLinearMap.rTensor L) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective D K')
    have h2 : (Φ : D ⊗[S] L → K' ⊗[S] L) = f.toLinearMap.rTensor L := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h2]; exact h1
  let ι : K' ⊗[S] L ≃ₐ[K] K' ⊗[K] L := (IsLocalization.algebraTensorEquiv (nonZeroDivisors S) K K' L).symm
  have hι : ∀ (a : K') (b : L), ι (a ⊗ₜ[S] b) = a ⊗ₜ[K] b := by
    intro a b
    rw [AlgEquiv.symm_apply_eq]
    rfl
  let Ψ : D ⊗[S] L →ₐ[D] K' ⊗[K] L :=
    { (ι.toRingEquiv.toRingHom.comp Φ.toRingHom) with
      commutes' := fun d => by
        show ι (Φ (d ⊗ₜ[S] 1)) = (algebraMap D K' d) ⊗ₜ[K] 1
        rw [Algebra.TensorProduct.map_tmul]
        exact hι _ _ }
  have hΨ : Function.Injective Ψ := ι.injective.comp hΦ
  let M := integralClosure D (D ⊗[S] L)
  let lin : M →ₗ[D] integralClosure D (K' ⊗[K] L) :=
    { toFun := fun x => ⟨Ψ (x : D ⊗[S] L), (show IsIntegral D (x : D ⊗[S] L) from x.2).map Ψ⟩
      map_add' := fun x y => Subtype.ext (map_add Ψ (x : D ⊗[S] L) y)
      map_smul' := fun r x => Subtype.ext (map_smul Ψ r (x : D ⊗[S] L)) }
  exact Module.Finite.of_injective lin (fun x y h => Subtype.ext (hΨ (congrArg Subtype.val h)))

end GlobalTheory.NormFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFiniteStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisation_dvr_tensor_separable_finite : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  first | exact @GlobalTheory.NormFin.main | exact GlobalTheory.NormFin.main | (intros; apply GlobalTheory.NormFin.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity Classical

noncomputable section
namespace GlobalTheory.HerbrandBridge

variable {C : Type} [Field C]

def toAddVal (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) :
    AddValuation C (WithTop ℝ) :=
  AddValuation.of
    (fun x => if x = 0 then ⊤ else ((Real.log (w x : ℝ) / Real.log (w ℓ : ℝ) : ℝ) : WithTop ℝ))
    (by simp) (by simp)
    (by
      have hL : Real.log (w ℓ : ℝ) < 0 :=
        Real.log_neg (by exact_mod_cast h0) (by exact_mod_cast h1)
      have key : ∀ x z : C, z ≠ 0 → w z ≤ w x →
          Real.log (w x : ℝ) / Real.log (w ℓ : ℝ) ≤ Real.log (w z : ℝ) / Real.log (w ℓ : ℝ) := by
        intro x z hz hle
        apply div_le_div_of_nonpos_of_le hL.le
        apply Real.log_le_log
        · have := (Valuation.ne_zero_iff w).2 hz
          exact_mod_cast pos_iff_ne_zero.2 this
        · exact_mod_cast hle
      intro x y
      by_cases hxy : x + y = 0
      · simp [hxy]
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      simp only [hx, hy, hxy, if_false]
      rcases le_max_iff.1 (w.map_add x y) with h | h
      · exact min_le_of_left_le (WithTop.coe_le_coe.2 (key x _ hxy h))
      · exact min_le_of_right_le (WithTop.coe_le_coe.2 (key y _ hxy h)))
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      have hx' : (0 : ℝ) < w x := by
        have := (Valuation.ne_zero_iff w).2 hx; exact_mod_cast pos_iff_ne_zero.2 this
      have hy' : (0 : ℝ) < w y := by
        have := (Valuation.ne_zero_iff w).2 hy; exact_mod_cast pos_iff_ne_zero.2 this
      simp only [mul_eq_zero, hx, hy, or_self, if_false, map_mul, NNReal.coe_mul]
      rw [Real.log_mul hx'.ne' hy'.ne', add_div]
      rfl)

theorem toAddVal_apply (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (x : C) :
    toAddVal w ℓ h0 h1 x =
      if x = 0 then ⊤ else ((Real.log (w x : ℝ) / Real.log (w ℓ : ℝ) : ℝ) : WithTop ℝ) := rfl

theorem mem_addValuationIntegerRing_normalized_iff (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (x : C) :
    x ∈ Int0 (toAddVal w ℓ h0 h1) ↔ x ∈ w.valuationSubring := by
  rw [mem_addValuationIntegerRing_iff, toAddVal_apply, Valuation.mem_valuationSubring_iff]
  by_cases hx : x = 0
  · simp [hx]
  have hL : Real.log (w ℓ : ℝ) < 0 :=
    Real.log_neg (by exact_mod_cast h0) (by exact_mod_cast h1)
  have hx' : (0 : ℝ) < w x := by
    have := (Valuation.ne_zero_iff w).2 hx; exact_mod_cast pos_iff_ne_zero.2 this
  simp only [hx, if_false]
  rw [← WithTop.coe_zero, WithTop.coe_le_coe, div_nonneg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_le.2 hL)
    · have := (Real.log_nonpos_iff hx'.le).1 h
      exact_mod_cast this
  · intro h
    right
    exact ⟨Real.log_nonpos hx'.le (by exact_mod_cast h), hL.le⟩

theorem toAddVal_of_ne (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {x : C}
    (hx : x ≠ 0) : toAddVal w ℓ h0 h1 x = ((GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ x : ℝ) : WithTop ℝ) := by
  rw [toAddVal_apply, if_neg hx]; rfl

variable {S : Type} [Fintype S] [DecidableEq S]

def liftA {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (a : S → w.valuationSubring) : S → Int0 v :=
  fun s => ⟨a s, (hv _).2 (a s).2⟩

def evalVec {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ) (x : Fin N → RS a) :
    S → Fin N → C :=
  fun s i => ((ev a s (x i) : Int0 v) : C)

def filPre {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) {N : ℕ}
    (F : Submodule w.valuationSubring (S → Fin N → C)) : Submodule (RS a) (Fin N → RS a) :=
  Submodule.span (RS a) {x | evalVec a N x ∈ F}

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

variable {C : Type} [Field C] {S : Type} [Fintype S] [DecidableEq S]

theorem evalVec_smul {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ) (c : Int0 v)
    (x : Fin N → RS a) : evalVec a N (c • x) = fun s i => (c : C) * evalVec a N x s i := by
  funext s i
  simp only [evalVec, Pi.smul_apply, map_smul, smul_eq_mul, Subring.coe_mul]

theorem evalVec_add {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ)
    (x y : Fin N → RS a) : evalVec a N (x + y) = evalVec a N x + evalVec a N y := by
  funext s i
  simp only [evalVec, Pi.add_apply, map_add (f := _), Subring.coe_add]

theorem evalVec_sub {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ)
    (x y : Fin N → RS a) : evalVec a N (x - y) = evalVec a N x - evalVec a N y := by
  funext s i
  simp only [evalVec, Pi.sub_apply, map_sub]; rfl

theorem comp_coe {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ) (s : S)
    (x : Fin N → RS a) : (fun i => ((comp a N s x i : Int0 v) : C)) = evalVec a N x s := rfl

end GlobalTheory.HerbrandBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinitzPiIdealsLinearEquivOfClassGroupProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinitzPiIdealsLinearEquivOfClassGroupProd
open scoped nonZeroDivisors

namespace GlobalTheory.SteinitzProd

variable {R : Type} [CommRing R] [IsDedekindDomain R]

def coprimeEquiv (I J : Ideal R) (u v : R) (hu : u ∈ I) (hv : v ∈ J) (h : u + v = 1) :
    (I × J) ≃ₗ[R] ((⊤ : Ideal R) × (I * J : Ideal R)) where
  toFun p := (⟨p.1 + p.2, Submodule.mem_top⟩,
    ⟨v * p.1 - u * p.2, Ideal.sub_mem _ (mul_comm (p.1 : R) v ▸ Ideal.mul_mem_mul p.1.2 hv)
      (Ideal.mul_mem_mul hu p.2.2)⟩)
  invFun q := (⟨u * q.1 + q.2, add_mem (Ideal.mul_mem_right _ I hu)
      ((Ideal.mul_le_left (I := I) (J := J)) q.2.2)⟩,
    ⟨v * q.1 - q.2, Ideal.sub_mem _ (Ideal.mul_mem_right _ J hv)
      ((Ideal.mul_le_right (I := I) (J := J)) q.2.2)⟩)
  map_add' p q := by
    ext <;> simp <;> ring
  map_smul' c p := by
    ext <;> simp <;> ring
  left_inv p := by
    ext
    · simp only; linear_combination (p.1 : R) * h
    · simp only; linear_combination (p.2 : R) * h
  right_inv q := by
    ext
    · simp only; linear_combination (q.1 : R) * h
    · simp only; linear_combination (q.2 : R) * h

theorem classGroup_exists_integral_ideal_coprime {m : Ideal R} (hm : m ≠ ⊥) (c : ClassGroup R) :
    ∃ I : (Ideal R)⁰, (I : Ideal R) ⊔ m = ⊤ ∧ ClassGroup.mk0 I = c := by
  by_cases ht : m = ⊤
  · obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
    exact ⟨I, by rw [ht, sup_top_eq], hI⟩
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := (J : Ideal R) * m) (J := J)
    Ideal.mul_le_left (mul_ne_zero hJ0 hm)
  obtain ⟨M, hM⟩ : (J : Ideal R) ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 (ha ▸ le_sup_right)
  have h1 : m ⊔ M = ⊤ := by
    apply mul_left_cancel₀ hJ0
    rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact ht (by simpa using h1)
  refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩, by rw [sup_comm]; exact h1, ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hJ0 hM0 (by simpa using hM.symm)
  rw [← inv_inv c, ← hJ, ClassGroup.mk0_eq_mk0_inv_iff]
  exact ⟨a, ha0, by rw [hM, mul_comm]⟩

theorem exists_prod_equiv (I J : (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 I * ClassGroup.mk0 J ∧
      Nonempty ((↥(I : Ideal R) × ↥(J : Ideal R)) ≃ₗ[R] (R × ↥(L : Ideal R))) := by
  have hJ0 : (J : Ideal R) ≠ ⊥ := by simpa using nonZeroDivisors.coe_ne_zero J
  obtain ⟨I', hcop, hcl⟩ := classGroup_exists_integral_ideal_coprime hJ0 (ClassGroup.mk0 I)
  have h1 : (1 : R) ∈ (I' : Ideal R) ⊔ J := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  refine ⟨I' * J, by rw [map_mul, hcl], ⟨?_⟩⟩
  have e1 := (GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq hcl.symm).some
  exact (e1.prodCongr (LinearEquiv.refl R _)) ≪≫ₗ coprimeEquiv _ _ u v hu hv huv ≪≫ₗ
    (Submodule.topEquiv.prodCongr (LinearEquiv.ofEq _ _ (Submonoid.coe_mul _ _ _).symm))

theorem exists_prod_pi_equiv (n : ℕ) : ∀ (I : Fin n → (Ideal R)⁰) (K : (Ideal R)⁰),
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 K * ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty ((↥(K : Ideal R) × ((i : Fin n) → ↥(I i : Ideal R))) ≃ₗ[R]
        (↥(L : Ideal R) × (Fin n → R))) := by
  induction n with
  | zero =>
    intro I K
    exact ⟨K, by simp, ⟨(LinearEquiv.refl R _).prodCongr (LinearEquiv.ofSubsingleton _ _)⟩⟩
  | succ n ih =>
    intro I K
    obtain ⟨L₁, hL₁, ⟨e₁⟩⟩ := exists_prod_equiv K (I 0)
    obtain ⟨L, hL, ⟨e₂⟩⟩ := ih (fun i => I i.succ) L₁
    refine ⟨L, by rw [hL, hL₁, Fin.prod_univ_succ, mul_assoc], ⟨?_⟩⟩
    exact (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun i => ↥(I i : Ideal R))).symm ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ e₁.prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ (LinearEquiv.refl R R).prodCongr e₂ ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ
      (LinearEquiv.prodComm R _ _).prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ
      (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun _ => R))

theorem exists_pi_equiv {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n + 1))
    (I : ι → (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty (((i : ι) → ↥(I i : Ideal R)) ≃ₗ[R] (↥(L : Ideal R) × (Fin n → R))) := by
  let I' : Fin (n + 1) → (Ideal R)⁰ := fun j => I (e.symm j)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_prod_pi_equiv n (fun j => I' j.succ) (I' 0)
  refine ⟨L, ?_, ⟨?_⟩⟩
  · rw [hL, ← Fin.prod_univ_succ (f := fun j => ClassGroup.mk0 (I' j))]
    exact Equiv.prod_comp e.symm (fun i => ClassGroup.mk0 (I i))
  · exact LinearEquiv.piCongrLeft' R (fun i => ↥(I i : Ideal R)) e ≪≫ₗ
      (Fin.consLinearEquiv R (fun j => ↥(I' j : Ideal R))).symm ≪≫ₗ f

theorem steinitz : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι]
    (I J : ι → (Ideal R)⁰), ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) →
    Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) := by
  intro R _ _ ι _ I J h
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  let e : ι ≃ Fin (n + 1) := (Fintype.equivFin ι).trans (finCongr hn)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_pi_equiv e I
  obtain ⟨L', hL', ⟨f'⟩⟩ := exists_pi_equiv e J
  obtain ⟨g⟩ := GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq (R := R) (I := L) (J := L')
    (by rw [hL, hL', h])
  exact ⟨f ≪≫ₗ g.prodCongr (LinearEquiv.refl R _) ≪≫ₗ f'.symm⟩

end GlobalTheory.SteinitzProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinitzPiIdealsLinearEquivOfClassGroupProdStatement
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.steinitz_pi_ideals_linearEquiv_of_classGroup_prod : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰), ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) → Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) := by
  first | exact @GlobalTheory.SteinitzProd.steinitz | exact GlobalTheory.SteinitzProd.steinitz | (intros; apply GlobalTheory.SteinitzProd.steinitz <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroOfRowsSeparating
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroOfRowsSeparating
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_det_ne_zero_of_rows_separating :
    ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K),
      (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) →
      ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  intro K _ σ h M hM
  have hsp : Submodule.span K (Set.range M) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have ha : (fun j => f (fun k => if j = k then 1 else 0)) = 0 := by
      apply hM
      intro s
      have h1 : f (M s) = 0 := hf (Submodule.subset_span ⟨s, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      refine (Finset.sum_congr rfl fun j _ => ?_).trans h1
      rw [smul_eq_mul, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [Pi.zero_apply] at this
    rw [this, smul_zero]
  obtain ⟨b, hbS, hbsp, hli⟩ := exists_linearIndependent K (Set.range M)
  have hsp' : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin h → K)) := by
    rw [Subtype.range_coe, hbsp, hsp]
  let B := Module.Basis.mk hli hsp'
  let e : Fin h ≃ b := (Pi.basisFun K (Fin h)).indexEquiv B
  have hmem : ∀ i, ∃ s, M s = (e i : Fin h → K) := fun i => hbS (e i).2
  choose s hs using hmem
  refine ⟨s, ?_⟩
  have hrows : LinearIndependent K (Matrix.of fun i j => M (s i) j).row := by
    have : (Matrix.of fun i j => M (s i) j).row = (fun x : b => (x : Fin h → K)) ∘ e := by
      funext i j
      simp [Matrix.row, hs]
    rw [this]
    exact hli.comp e e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroOfRowsSeparatingStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_det_ne_zero_of_separating_functionals : ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K), (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) → ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  first | exact @GlobalTheory.exists_det_ne_zero_of_rows_separating | exact GlobalTheory.exists_det_ne_zero_of_rows_separating | (intros; apply GlobalTheory.exists_det_ne_zero_of_rows_separating <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrime
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_generic_jacobian_data_of_prime (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ]
    (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime] (hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) :
    ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ),
      g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
      (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by
  classical
  obtain ⟨h, f, g, hgQ, hfQ, hgen, -, hmin⟩ := GlobalTheory.T.exists_minimal_local_generators' (MvPolynomial σ Λ) Q

  set φ : MvPolynomial σ Λ →+* FractionRing (MvPolynomial σ Λ ⧸ Q) :=
    (algebraMap (MvPolynomial σ Λ ⧸ Q) (FractionRing (MvPolynomial σ Λ ⧸ Q))).comp
      (Ideal.Quotient.mk Q) with hφ
  have hφker : ∀ x, φ x = 0 ↔ x ∈ Q := by
    intro x
    rw [hφ, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective _ _)

  have hind : ∀ a : Fin h → FractionRing (MvPolynomial σ Λ ⧸ Q),
      (∀ t, ∑ j, a j * φ (MvPolynomial.pderiv t (f j)) = 0) → a = 0 := by
    intro a ha
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (MvPolynomial σ Λ ⧸ Q)) a
    choose c hc using fun j => RingHom.mem_rangeS.mp (hb j)
    choose a' ha' using fun j => Ideal.Quotient.mk_surjective (c j)
    have hφa : ∀ j, φ (a' j) =
        algebraMap _ (FractionRing (MvPolynomial σ Λ ⧸ Q)) (b : MvPolynomial σ Λ ⧸ Q) * a j := by
      intro j
      rw [hφ, RingHom.comp_apply, ha', hc, Algebra.smul_def]
    have hx : ∑ j, a' j * f j ∈ Q := Q.sum_mem fun j _ => Q.mul_mem_left _ (hfQ j)
    have hpd : ∀ t, MvPolynomial.pderiv t (∑ j, a' j * f j) ∈ Q := by
      intro t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
      refine Q.add_mem ?_ (Q.sum_mem fun j _ => Q.mul_mem_right _ (hfQ j))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hφker, map_sum]
      simp only [map_mul, hφa, mul_assoc, ← Finset.mul_sum, ha t, mul_zero]
    obtain ⟨u, hu, hux⟩ := GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem Λ σ Q hQ _ hx hpd
    have haQ := hmin a' u hu hux
    funext j
    have h1 : φ (a' j) = 0 := (hφker _).mpr (haQ j)
    rw [hφa j] at h1
    exact (mul_eq_zero.mp h1).resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_det_ne_zero_of_separating_functionals (FractionRing (MvPolynomial σ Λ ⧸ Q)) σ h
    (fun t j => φ (MvPolynomial.pderiv t (f j))) hind
  refine ⟨h, f, s, g, hgQ, hfQ, hgen, fun hdet => hs ?_⟩
  have hmat : (Matrix.of fun i j => φ (MvPolynomial.pderiv (s i) (f j))) =
      φ.mapMatrix (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)) := by
    ext i j
    simp
  rw [hmat, ← RingHom.map_det, hφker]
  exact hdet

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrimeStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generators_jacobian_det_not_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by
  first | exact @GlobalTheory.exists_generic_jacobian_data_of_prime | exact GlobalTheory.exists_generic_jacobian_data_of_prime | (intros; apply GlobalTheory.exists_generic_jacobian_data_of_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralComplexGaussianPosDefHermitianPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralComplexGaussianPosDefHermitianPart
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.MatrixGaussian

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_congr_diagonal (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    ∃ (M : Matrix ι ι ℂ) (d : ι → ℂ), M.det ≠ 0 ∧ (∀ i, 0 < (d i).re) ∧ Mᴴ * A * M = diagonal d := by
  obtain ⟨B, hB, hBA⟩ : ∃ B : Matrix ι ι ℂ, IsUnit B ∧ A + Aᴴ = star B * B := by
    open scoped MatrixOrder in
    exact CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  set C := B⁻¹ with hC
  have h1 : B * C = 1 := Matrix.mul_nonsing_inv B hBd
  set A' := Cᴴ * A * C with hA'
  have h2 : A' + A'ᴴ = 1 := by
    have : A' + A'ᴴ = Cᴴ * (A + Aᴴ) * C := by
      simp only [hA', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_assoc]
    rw [this, hBA, star_eq_conjTranspose]
    calc Cᴴ * (Bᴴ * B) * C = (B * C)ᴴ * (B * C) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp
  have hK : (I • (A' - A'ᴴ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    simp only [RCLike.star_def, conj_I, neg_smul, ← smul_neg, neg_sub]
  set U : Matrix ι ι ℂ := (hK.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : Uᴴ * U = 1 := hK.eigenvectorUnitary.2.1
  have hD : Uᴴ * (I • (A' - A'ᴴ)) * U = diagonal (RCLike.ofReal ∘ hK.eigenvalues) := by
    have := hK.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using this
  have h3 : A' = (1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ))) := by
    rw [← h2, smul_smul, I_mul_I]
    module
  refine ⟨C * U, fun i => (1 / 2 : ℂ) * (1 - I * (hK.eigenvalues i : ℂ)), ?_, fun i => by simp, ?_⟩
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · intro h
      have := congrArg det h1
      simp [h] at this
    · intro h
      have := congrArg det hUU
      simp [h] at this
  · calc (C * U)ᴴ * A * (C * U) = Uᴴ * A' * U := by
          simp only [hA', conjTranspose_mul, Matrix.mul_assoc]
      _ = Uᴴ * ((1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ)))) * U := by rw [← h3]
      _ = (1 / 2 : ℂ) • (Uᴴ * U - I • (Uᴴ * (I • (A' - A'ᴴ)) * U)) := by
          generalize I • (A' - A'ᴴ) = K
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = _ := by
          rw [hD, hUU]
          ext i j
          by_cases h : i = j
          · subst h; simp
          · simp [h]

theorem exp_diagonal (d z : ι → ℂ) :
    cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = ∏ i, cexp (-(π * d i) * (‖z i‖ : ℂ) ^ 2) := by
  rw [← Complex.exp_sum, dotProduct, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, ← Complex.conj_mul', Pi.star_apply, RCLike.star_def]
  ring

theorem gaussian_diagonal (d : ι → ℂ) (hd : ∀ i, 0 < (d i).re) :
    Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = (diagonal d).det⁻¹ := by
  have hb : ∀ i, 0 < ((π : ℂ) * d i).re := fun i => by
    simpa using mul_pos Real.pi_pos (hd i)
  simp only [exp_diagonal]
  constructor
  · refine Integrable.fintype_prod (f := fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)) fun i => ?_
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (hb i) 0 0
  · rw [integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)),
      det_diagonal, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (hb i), Complex.finrank_real_complex]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
    rw [this, cpow_one, div_mul_cancel_left₀ hπ]

theorem map_mulVec_volume (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    Measure.map (fun z : ι → ℂ => M *ᵥ z) volume = ENNReal.ofReal (normSq M.det)⁻¹ • volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = normSq M.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; simpa using hM)
  rw [hdet, abs_of_nonneg (inv_nonneg.2 (normSq_nonneg _))] at this
  exact this

theorem integral_gaussian (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  obtain ⟨M, d, hM, hd, hMA⟩ := exists_congr_diagonal A hA
  obtain ⟨hi, he⟩ := gaussian_diagonal d hd
  have hn : 0 < normSq M.det := normSq_pos.2 hM
  have hdet : (diagonal d).det = (normSq M.det : ℂ) * A.det := by
    rw [← hMA, det_mul, det_mul, det_conjTranspose, normSq_eq_conj_mul_self, RCLike.star_def]
    ring
  have hd0 : (diagonal d).det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ h => ?_
    have := hd i
    simp [h] at this
  have hA0 : A.det ≠ 0 := fun h => hd0 (by rw [hdet, h, mul_zero])
  have hcomp : ∀ z : ι → ℂ, star (M *ᵥ z) ⬝ᵥ A *ᵥ (M *ᵥ z) = star z ⬝ᵥ (diagonal d) *ᵥ z := fun z => by
    rw [← hMA, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hc : Continuous fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) := by fun_prop
  have hcM : Continuous fun z : ι → ℂ => M *ᵥ z := by fun_prop
  have hmap := map_mulVec_volume M hM
  refine ⟨hA0, ?_, ?_⟩
  · have h := (integrable_map_measure (μ := volume) hc.aestronglyMeasurable hcM.measurable.aemeasurable).2
      (by simpa only [Function.comp_def, hcomp] using hi)
    rw [hmap] at h
    exact (integrable_smul_measure (by simpa using hn) ENNReal.ofReal_ne_top).1 h
  · have h := integral_map (μ := volume) hcM.measurable.aemeasurable hc.aestronglyMeasurable
    simp only [hcomp] at h
    rw [hmap, integral_smul_measure, he, hdet, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le), real_smul,
      mul_inv, ofReal_inv] at h
    exact mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast hn.ne')) h

end GlobalTheory.MatrixGaussian
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralComplexGaussianPosDefHermitianPartStatement
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ), (A + Aᴴ).PosDef → A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧ ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  first | exact @GlobalTheory.MatrixGaussian.integral_gaussian | exact GlobalTheory.MatrixGaussian.integral_gaussian | (intros; apply GlobalTheory.MatrixGaussian.integral_gaussian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGauTwistedConv
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}

theorem integral_gau_twisted_conv (hJ : ∀ x, J (J x) = -x) (a y : V) :
    ∫ u, gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ))) = gau a * gau y := by
  set m : V := (1 / 2 : ℝ) • (y - a) with hm
  have hym : y - a = m + m := by
    rw [hm, ← add_smul]; norm_num
  have hself : ∀ x : V, ⟪x, J x⟫ = 0 := by
    intro x
    have := omJ_skew hJ x x
    unfold omJ at this
    linarith
  have hsk : ∀ x z : V, ⟪z, J x⟫ = -⟪x, J z⟫ := fun x z => by
    have := omJ_skew hJ x z
    unfold omJ at this
    exact this
  have hpt : ∀ v : V, gau (v + m) * (gau (y - (v + m + a)) *
      cexp (π * I * ((omJ J (v + m) a + omJ J (v + m + a) y : ℝ) : ℂ))) =
      cexp (-(π : ℂ) * ‖v‖ ^ 2 + (π * I) * ⟪J (a + y), v⟫) * cexp (-(π : ℂ) * ‖m‖ ^ 2) := by
    intro v
    have e1 : y - (v + m + a) = m - v := by
      have hy : y = m + m + a := by rw [← hym]; abel
      rw [hy]; abel
    have h1 : ‖v + m‖ ^ 2 + ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
      rw [e1, norm_add_sq_real, norm_sub_sq_real, real_inner_comm m v]; ring
    have h2 : omJ J (v + m) a + omJ J (v + m + a) y = ⟪J (a + y), v⟫ := by
      unfold omJ
      rw [real_inner_comm v (J (a + y)), hm]
      simp only [map_add (f := _), inner_add_left, inner_add_right, real_inner_smul_left, inner_sub_left]
      have h3 := hsk a y
      have h4 := hself a
      have h5 := hself y
      linarith
    have h1c : ((‖y - (v + m + a)‖ : ℝ) : ℂ) ^ 2 =
        2 * (‖v‖ : ℂ) ^ 2 + 2 * (‖m‖ : ℂ) ^ 2 - (‖v + m‖ : ℂ) ^ 2 := by
      have h6 : ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 - ‖v + m‖ ^ 2 := by linarith
      exact_mod_cast h6
    simp only [gau, ← Complex.exp_add]
    congr 1
    rw [h1c, h2]
    ring
  have hshift := integral_add_right_eq_self (μ := (volume : Measure V))
    (fun u => gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ)))) m
  rw [← hshift]
  simp only [hpt]
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb, div_self hπ, Complex.one_cpow, one_mul,
    LinearIsometryEquiv.norm_map, gau, gau, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h3 : ‖m‖ ^ 2 = ‖a‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2 - ‖a + y‖ ^ 2 / 4 := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_pow,
      norm_sub_sq_real, norm_add_sq_real, real_inner_comm y a]
    ring
  have h3c : (‖m‖ : ℂ) ^ 2 = (‖a‖ : ℂ) ^ 2 / 2 + (‖y‖ : ℂ) ^ 2 / 2 - (‖a + y‖ : ℂ) ^ 2 / 4 := by
    exact_mod_cast h3
  rw [h3c, mul_pow, I_sq]
  field_simp
  ring

theorem proj_heis_proj {ρ : V → B →L[ℂ] B} (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a : V) (f : B) :
    proj h (ρ a (proj h f)) = gau a • proj h f := by
  have hself : ∀ x : V, omJ J x x = 0 := fun x => by
    have := omJ_skew hJ x x
    linarith
  set F : V → V → B := fun u z =>
    (gau u * (gau (z - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) z : ℝ) : ℂ)))) • ρ z f with hF
  have hin : ∀ u, gau u • ρ u (ρ a (proj h f)) = ∫ z, F u z := by
    intro u
    rw [h.2.1 u a, proj_apply h f, ← (ρ (u + a)).integral_comp_comm (h.integrable f), ← integral_smul,
      ← integral_smul, ← integral_add_right_eq_self (F u) (u + a)]
    congr 1
    ext w
    have hw : omJ J (u + a) (w + (u + a)) = omJ J (u + a) w := by
      have h0 := hself (u + a)
      unfold omJ at h0 ⊢
      rw [map_add (f := _), inner_add_right, h0, add_zero]
    show _ = (gau u * (gau (w + (u + a) - (u + a)) *
      cexp (π * I * ((omJ J u a + omJ J (u + a) (w + (u + a)) : ℝ) : ℂ)))) • ρ (w + (u + a)) f
    rw [add_sub_cancel_right, hw, add_comm w (u + a), map_smul, h.2.1 (u + a) w, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have he : ∀ r : ℝ, ‖cexp (π * I * (r : ℂ))‖ = 1 := fun r => by
    rw [Complex.norm_exp]
    simp
  have hnorm : ∀ u z, ‖F u z‖ = ‖gau u‖ * (‖gau (z - (u + a))‖ * ‖f‖) := by
    intro u z
    simp only [hF, norm_smul, norm_mul, h.2.2.1]
    rw [he, mul_one, mul_assoc]
  have hom : Continuous fun p : V × V => omJ J p.1 p.2 := by
    unfold omJ
    exact continuous_fst.inner (J.continuous.comp continuous_snd)
  have hcont : Continuous (Function.uncurry F) := by
    show Continuous fun p : V × V => (gau p.1 * (gau (p.2 - (p.1 + a)) *
      cexp (π * I * ((omJ J p.1 a + omJ J (p.1 + a) p.2 : ℝ) : ℂ)))) • ρ p.2 f
    refine Continuous.smul ?_ ((h.2.2.2 f).comp continuous_snd)
    refine (continuous_gau.comp continuous_fst).mul
      ((continuous_gau.comp (continuous_snd.sub (continuous_fst.add continuous_const))).mul ?_)
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact (hom.comp (continuous_fst.prodMk continuous_const)).add
      (hom.comp ((continuous_fst.add continuous_const).prodMk continuous_snd))
  have hint : Integrable (Function.uncurry F) ((volume : Measure V).prod volume) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall fun u => ?_
      have hm : AEStronglyMeasurable (fun z => Function.uncurry F (u, z)) volume :=
        (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      rw [← integrable_norm_iff hm]
      simp only [Function.uncurry_apply_pair, hnorm]
      exact (((integrable_gau (V := V)).norm.comp_sub_right (u + a)).mul_const ‖f‖).const_mul ‖gau u‖
    · simp only [Function.uncurry_apply_pair, hnorm]
      simp only [integral_const_mul, integral_mul_const, integral_sub_right_eq_self (‖gau ·‖)]
      exact (integrable_gau (V := V)).norm.mul_const _
  rw [proj_apply h (ρ a (proj h f))]
  simp_rw [hin]
  rw [integral_integral_swap hint]
  have hinner : ∀ z, ∫ u, F u z = (gau a * gau z) • ρ z f := by
    intro z
    simp only [hF]
    rw [integral_smul_const, integral_gau_twisted_conv hJ a z]
  simp_rw [hinner]
  rw [proj_apply h f, ← integral_smul]
  congr 1
  ext z
  rw [smul_smul]

end GlobalTheory.RealWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffPartialDerivMuEqSuccMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OptionEquivLeftPderivNoneCoeff
open MvPolynomial

namespace GlobalTheory

theorem optionEquivLeft_pderiv_none_gen {τ : Type} [DecidableEq τ]
    (p : MvPolynomial (Option τ) ℂ) :
    optionEquivLeft ℂ τ (pderiv none p) = Polynomial.derivative (optionEquivLeft ℂ τ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [optionEquivLeft_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rcases i with _ | j
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_none, mul_comm]
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_some, pderiv_X, mul_comm]

theorem optionEquivLeft_pderiv_none_coeff :
    ∀ {τ : Type} [DecidableEq τ] (k : ℕ) (s : MvPolynomial (Option τ) ℂ),
      (MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.pderiv none s)).coeff k =
        ((k : ℂ) + 1) • (MvPolynomial.optionEquivLeft ℂ τ (s)).coeff (k + 1) := by
  intro τ _ k s
  rw [optionEquivLeft_pderiv_none_gen, Polynomial.coeff_derivative, MvPolynomial.smul_eq_C_mul,
    mul_comm]
  congr 1
  simp

end GlobalTheory
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_coefM_pderiv : T_coefM_pderiv := by
  intro n L k s
  simp only [coefM, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    Polynomial.lcoeff_apply, AlgEquiv.toLinearMap_apply]
  exact GlobalTheory.optionEquivLeft_pderiv_none_coeff k s

end GlobalTheory.PsCo.Cw2a
end
