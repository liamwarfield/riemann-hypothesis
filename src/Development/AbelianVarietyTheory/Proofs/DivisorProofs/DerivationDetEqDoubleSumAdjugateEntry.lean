module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntry
open Matrix Finset

namespace GlobalTheory.DetDeriv

theorem derivation_prod {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    {ι : Type} [DecidableEq ι] (δ : Derivation K R R) (s : Finset ι) (f : ι → R) :
    δ (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * δ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha, Derivation.leibniz, ih,
      add_comm, Finset.smul_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      smul_eq_mul]
    ring

theorem derivation_det_rows {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    δ M.det = ∑ t, (M.updateRow t fun u => δ (M t u)).det := by
  have key : ∀ N : Matrix ι ι R,
      N.det = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, N i (σ i) := by
    intro N
    rw [← det_transpose, det_apply']
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [key, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.leibniz, δ.map_intCast, smul_zero, add_zero, smul_eq_mul, ← Finset.mul_sum,
    derivation_prod]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), updateRow_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [updateRow_ne (Finset.ne_of_mem_erase hi)]

theorem det_updateRow_eq_sum_adjugate {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (t : ι) (v : ι → R) :
    (M.updateRow t v).det = ∑ j, M.adjugate j t * v j := by
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose, mulVec]
  simp [dotProduct, transpose_apply]

theorem derivation_det {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) := by
  rw [derivation_det_rows]
  exact Finset.sum_congr rfl fun i _ => det_updateRow_eq_sum_adjugate M i _

theorem main : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R)
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R),
    δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) :=
  fun δ _ _ _ M => derivation_det δ M

end GlobalTheory.DetDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntryStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R), δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) := by
  first | exact @GlobalTheory.DetDeriv.main | exact GlobalTheory.DetDeriv.main | (intros; apply GlobalTheory.DetDeriv.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSchemeGrpObjOfMonoFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSchemeGrpObjOfMonoFactor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem grpObj_of_mono_factor {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A K : C} [GrpObj A] (i : K ⟶ A) [Mono i] (m : K ⊗ K ⟶ K) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[A])
    (e : 𝟙_ C ⟶ K) (he : e ≫ i = η[A]) (v : K ⟶ K) (hv : v ≫ i = i ≫ ι[A]) :
    ∃ _ : GrpObj K, IsMonHom i := by
  letI M : MonObj K :=
    { one := e, mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : e ▷ K ≫ (i ⊗ₘ i) = 𝟙_ C ◁ i ≫ η[A] ▷ A := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, he, tensorHom_def']
        rw [reassoc_of% h1, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : K ◁ e ≫ (i ⊗ₘ i) = i ▷ 𝟙_ C ≫ A ◁ η[A] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, he, MonoidalCategory.tensorHom_def]
        rw [reassoc_of% h1, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono i]
        have h1 : m ▷ K ≫ m ≫ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[A] ▷ A ≫ μ[A] := by
          simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        have h2 : K ◁ m ≫ m ≫ i = (i ⊗ₘ (i ⊗ₘ i)) ≫ A ◁ μ[A] ≫ μ[A] := by
          simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        simp only [Category.assoc]
        rw [h1, h2, MonObj.mul_assoc (X := A), associator_naturality_assoc] }
  letI G : GrpObj K :=
    { inv := v
      left_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift v (𝟙 K) ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift (i ≫ ι[A]) i = i ≫ lift ι[A] (𝟙 A) := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.left_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)]
      right_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift (𝟙 K) v ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift i (i ≫ ι[A]) = i ≫ lift (𝟙 A) ι[A] := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.right_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)] }
  exact ⟨G, { one_hom := he, mul_hom := hm }⟩

theorem overScheme_grpObj_of_mono_factor : ∀ (T : Scheme.{0}) (A K : Over T) [GrpObj A] (i : K ⟶ A),
    Mono i → (∃ m : K ⊗ K ⟶ K, m ≫ i = (i ⊗ₘ i) ≫ μ[A]) → (∃ e : 𝟙_ (Over T) ⟶ K, e ≫ i = η[A]) →
    (∃ v : K ⟶ K, v ≫ i = i ≫ ι[A]) → ∃ _ : GrpObj K, IsMonHom i := by
  intro T A K _ i hi ⟨m, hm⟩ ⟨e, he⟩ ⟨v, hv⟩
  exact grpObj_of_mono_factor i m hm e he v hv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSchemeGrpObjOfMonoFactorStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpObj_isMonHom_of_mono_factor : ∀ (T : Scheme.{0}) (A K : Over T) [GrpObj A] (i : K ⟶ A), Mono i → (∃ m : K ⊗ K ⟶ K, m ≫ i = (i ⊗ₘ i) ≫ μ[A]) → (∃ e : 𝟙_ (Over T) ⟶ K, e ≫ i = η[A]) → (∃ v : K ⟶ K, v ≫ i = i ≫ ι[A]) → ∃ _ : GrpObj K, IsMonHom i := by
  first | exact @GlobalTheory.overScheme_grpObj_of_mono_factor | exact GlobalTheory.overScheme_grpObj_of_mono_factor | (intros; apply GlobalTheory.overScheme_grpObj_of_mono_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComapIncludeRightField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComapIncludeRightField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem range_comap_includeRight_field :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k],
    Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by
  intro A B _ _ _ k _ _
  ext r
  constructor
  · rintro ⟨q, rfl⟩
    show Ideal.comap (algebraMap A B) (Ideal.comap _ q.asIdeal) = _
    rw [Ideal.comap_comap, ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ q.asIdeal),
      ← RingHom.ker_eq_comap_bot]
  · intro hr
    change Ideal.comap (algebraMap A B) r.asIdeal = RingHom.ker (algebraMap A k) at hr
    set f := algebraMap A k with hf
    let I := RingHom.ker f
    let K := r.asIdeal.ResidueField
    let g : A →+* K := (algebraMap B K).comp (algebraMap A B)
    have hg : RingHom.ker g = I := by
      change RingHom.ker ((algebraMap B K).comp (algebraMap A B)) = RingHom.ker f
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, hr]
    have hIg : ∀ a ∈ I, g a = 0 := fun a ha => by rw [← RingHom.mem_ker, hg]; exact ha
    let ι₁ : A ⧸ I →+* k := RingHom.kerLift f
    let ι₂ : A ⧸ I →+* K := Ideal.Quotient.lift I g hIg
    have inj₁ : Function.Injective ι₁ := RingHom.kerLift_injective f
    have inj₂ : Function.Injective ι₂ := RingHom.lift_injective_of_ker_le_ideal I hIg hg.le
    letI : Algebra (A ⧸ I) k := ι₁.toAlgebra
    letI : Algebra (A ⧸ I) K := ι₂.toAlgebra
    haveI : Nontrivial (k ⊗[A ⧸ I] K) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (A ⧸ I) k K inj₁ inj₂
    haveI : SMulCommClass (A ⧸ I) A k := ⟨fun x a y => by
      simp only [Algebra.smul_def]; ring⟩
    let α : k →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.includeLeft
    let β : B →ₐ[A] k ⊗[A ⧸ I] K :=
      { ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) with
        commutes' := fun a => by
          change (1 : k) ⊗ₜ[A ⧸ I] (algebraMap (A ⧸ I) K (Ideal.Quotient.mk I a)) = _
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := K),
            ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
          rfl }
    let φ : k ⊗[A] B →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _)
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[A ⧸ I] K)
    refine ⟨PrimeSpectrum.comap φ.toRingHom ⟨m, hm.isPrime⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.comap φ.toRingHom m) = r.asIdeal
    have hcomp : φ.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom =
        ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) := by
      ext b
      simp [φ, α, β, Algebra.TensorProduct.lift_tmul]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ m),
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComapIncludeRightFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k], Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by
  first | exact @GlobalTheory.range_comap_includeRight_field | exact GlobalTheory.range_comap_includeRight_field | (intros; apply GlobalTheory.range_comap_includeRight_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntForm
namespace GlobalTheory

open Matrix

theorem gram_posSemidef_of_int_form {X : Type} [AddCommGroup X] {r : ℕ}
    (b : LinearMap.BilinForm ℤ X) (hsymm : ∀ y z, b y z = b z y) (hpos : ∀ y, 0 ≤ b y y)
    (v : Fin r → X) : (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by
  set G : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => (b (v i) (v j) : ℝ) with hG
  have hint : ∀ m : Fin r → ℤ, 0 ≤ ∑ i, ∑ j, (m i : ℝ) * (m j : ℝ) * G i j := by
    intro m
    have key : (∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ)
        = b (∑ i, m i • v i) (∑ j, m j • v j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm (v i) (v j)]; ring
    have h0 : (0:ℝ) ≤ ((∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ) : ℝ) := by
      rw [key]; exact_mod_cast hpos _
    simpa [hG] using h0
  have hrat : ∀ c : Fin r → ℚ, 0 ≤ ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
    intro c
    set N : ℕ := ∏ i, (c i).den with hN
    have hNpos : (0:ℝ) < N := by
      have : 0 < N := Finset.prod_pos (fun i _ => (c i).den_pos)
      exact_mod_cast this
    have hm : ∀ i, ∃ k : ℤ, (k : ℝ) = N * (c i : ℝ) := by
      intro i
      obtain ⟨t, ht⟩ : (c i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(c i).num * t, ?_⟩
      have h1 : ((c i).num : ℚ) = c i * (c i).den := (Rat.mul_den_eq_num (c i)).symm
      have h2 : ((c i).num : ℝ) = (c i : ℝ) * (c i).den := by exact_mod_cast h1
      rw [ht]; push_cast
      rw [h2]; ring
    choose m hm using hm
    have h3 := hint m
    simp_rw [hm] at h3
    have e : ∑ i, ∑ j, ((N:ℝ) * c i) * (N * c j) * G i j
        = (N:ℝ) ^ 2 * ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e] at h3
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h3
  have hreal : ∀ x : Fin r → ℝ, 0 ≤ ∑ i, ∑ j, x i * x j * G i j := by
    intro x
    have hd : DenseRange (Pi.map fun (_ : Fin r) (q : ℚ) => (q : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on (p := fun x : Fin r → ℝ => 0 ≤ ∑ i, ∑ j, x i * x j * G i j) x ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · intro c
      simpa [Pi.map] using hrat c
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [hG, Matrix.conjTranspose_apply, hsymm]
  · intro x
    have e : star x ⬝ᵥ (G *ᵥ x) = ∑ i, ∑ j, x i * x j * G i j := by
      simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]; exact hreal x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntFormStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm : ∀ {X : Type} [AddCommGroup X] {r : ℕ} (b : LinearMap.BilinForm ℤ X), (∀ y z, b y z = b z y) → (∀ y, 0 ≤ b y y) → ∀ v : Fin r → X, (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by
  first | exact @GlobalTheory.gram_posSemidef_of_int_form | exact GlobalTheory.gram_posSemidef_of_int_form | (intros; apply GlobalTheory.gram_posSemidef_of_int_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

universe u

theorem ringHom_formallyEtale_of_ringEquiv {S T : Type u} [CommRing S] [CommRing T]
    (e : S ≃+* T) : (e : S →+* T).FormallyEtale := by
  algebraize [(e : S →+* T)]
  exact Algebra.FormallyEtale.of_equiv (R := S) (A := S) (B := T)
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

theorem ringHom_formallyEtale_respectsIso : RingHom.RespectsIso.{u} @RingHom.FormallyEtale := by
  have hiso := @ringHom_formallyEtale_of_ringEquiv.{u}
  constructor
  · intro R S T _ _ _ f e hf
    exact RingHom.FormallyEtale.comp hf (hiso e)
  · intro R S T _ _ _ f e hf
    exact RingHom.FormallyEtale.comp (hiso e) hf

theorem formallyEtale_localRingHom_of_etale {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) (J : Ideal S) [J.IsPrime] :
    (Localization.localRingHom (J.comap f) J f rfl).FormallyEtale := by
  algebraize [f]
  let Rₓ := Localization.AtPrime (J.comap f)
  let Sₓ := Localization.AtPrime J
  let : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyEtale R Sₓ := inferInstance
  have : Algebra.FormallyEtale Rₓ Sₓ :=
    Algebra.FormallyEtale.localization_base (J.comap f).primeCompl
  exact (RingHom.formallyEtale_algebraMap (R := Rₓ) (S := Sₓ)).2 this

theorem formallyEtale_stalkMap_of_etale {X Y : Scheme.{0}} (g : X ⟶ Y) [Etale g] (x : X) :
    (g.stalkMap x).hom.FormallyEtale :=
  HasRingHomProperty.stalkMap_of_respectsIso (P := @Etale) (Q := RingHom.Etale)
    ringHom_formallyEtale_respectsIso
    (fun f hf J _ => formallyEtale_localRingHom_of_etale f hf J) ‹_› x

theorem stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict :
    ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U,
      (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧
        (f.stalkMap y).hom.EssFiniteType := by
  intro M W f U hg y hy
  have key : ∀ (x : M) (z : U), U.ι z = x →
      (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyEtale ∧
        (f.stalkMap x).hom.EssFiniteType := by
    intro x z hz
    subst hz
    have h1 := Flat.stalkMap (U.ι ≫ f) z
    have h2 := formallyEtale_stalkMap_of_etale (U.ι ≫ f) z
    have h3 := LocallyOfFiniteType.stalkMap (U.ι ≫ f) z
    have e := Scheme.Hom.stalkMap_comp U.ι f z
    rw [e] at h1 h2 h3
    have : IsIso (U.ι.stalkMap z) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
    refine ⟨?_, ?_, ?_⟩
    · exact (RingHom.Flat.respectsIso.cancel_right_isIso _ _).1 h1
    · exact (ringHom_formallyEtale_respectsIso.cancel_right_isIso _ _).1 h2
    · exact (RingHom.EssFiniteType.respectsIso.cancel_right_isIso _ _).1 h3
  exact key y ⟨y, hy⟩ (by simp)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleResStatement
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧ (f.stalkMap y).hom.EssFiniteType := by
  first | exact @GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | exact GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | (intros; apply GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfResidueFieldFibres
namespace GlobalTheory

open TensorProduct


open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.subsingleton_of_residueField_fibres (O Q : Type) [CommRing O]
    [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    (h : ∀ q : PrimeSpectrum O, Subsingleton (q.asIdeal.ResidueField ⊗[O] Q)) :
    Subsingleton Q := by
  rw [← Module.support_eq_empty_iff (R := O), Set.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hq
  exact not_nontrivial_iff_subsingleton.mpr (h q) hq

open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.surjective_of_fibre_rank (O M N : Type) [CommRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N)
    (h : ∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField
      (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) =
      Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  refine _root_.GlobalTheory.subsingleton_of_residueField_fibres O _ fun q => ?_
  have htop : LinearMap.range (f.baseChange q.asIdeal.ResidueField) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (h q)
  have hex := lTensor_exact q.asIdeal.ResidueField (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective _)
  refine ⟨fun y y' => ?_⟩
  suffices ∀ y : q.asIdeal.ResidueField ⊗[O] (N ⧸ LinearMap.range f), y = 0 by
    rw [this y, this y']
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective q.asIdeal.ResidueField
    (Submodule.mkQ_surjective (LinearMap.range f)) y
  have hx : x ∈ LinearMap.range (f.baseChange q.asIdeal.ResidueField) := htop ▸ Submodule.mem_top
  obtain ⟨z, rfl⟩ := hx
  rw [LinearMap.baseChange_eq_ltensor]
  exact hex.apply_apply_eq_zero z

theorem injective_of_fibre_rank (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N)
    [Module.Finite O M] [Module.Projective O N] (hf : Function.Surjective f)
    (h : ∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField
      (TensorProduct O q.asIdeal.ResidueField M) =
      Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) :
    Function.Injective f := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf

  have hsurj : Function.Surjective s := by
    apply surjective_of_fibre_rank O N M s
    intro q
    have hinj : Function.Injective (s.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := f.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hs]
      simp
    rw [LinearMap.finrank_range_of_inj hinj, h q]
  intro a b hab
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  have hx : f (s x) = x := LinearMap.congr_fun hs x
  have hy : f (s y) = y := LinearMap.congr_fun hs y
  rw [hx, hy] at hab
  rw [hab]

theorem surjective_injective_of_fibre_rank :
    ∀ (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N), ((∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Surjective f) ∧ (Module.Finite O M → Module.Projective O N → Function.Surjective f → (∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField M) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Injective f) := by
  intro O M N _ _ _ _ _ _ f
  exact ⟨surjective_of_fibre_rank O M N f,
    fun _ _ hf h => injective_of_fibre_rank O M N f hf h⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
noncomputable section

namespace GlobalTheory.OrbitUnfold

def ConjSelf (Γ : Type) : Type := Γ

namespace ConjSelf

variable {Γ : Type} [Group Γ]

def of (γ : Γ) : ConjSelf Γ := γ

def val (γ : ConjSelf Γ) : Γ := γ

instance : MulAction Γ (ConjSelf Γ) where
  smul η γ := of (η * val γ * η⁻¹)
  one_smul γ := by
    change (1 : Γ) * val γ * 1⁻¹ = val γ
    simp
  mul_smul a b γ := by
    change a * b * val γ * (a * b)⁻¹ = a * (b * val γ * b⁻¹) * a⁻¹
    group

theorem val_smul (η : Γ) (γ : ConjSelf Γ) : val (η • γ) = η * val γ * η⁻¹ := rfl

theorem stabilizer_eq_centralizer (γ : ConjSelf Γ) :
    MulAction.stabilizer Γ γ = Subgroup.centralizer {val γ} := by
  ext η
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg val h
    rw [val_smul] at h'
    calc η * val γ = η * val γ * η⁻¹ * η := by group
      _ = val γ * η := by rw [h']
  · intro h
    change η * val γ * η⁻¹ = val γ
    rw [h.eq]
    group

end ConjSelf

open ConjSelf

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem stabilizer_pair (p : Y × ConjSelf Γ) :
    MulAction.stabilizer Γ p = MulAction.stabilizer Γ p.1 ⊓ Subgroup.centralizer {val p.2} := by
  rw [← stabilizer_eq_centralizer]
  ext η
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Prod.smul_def, Prod.ext_iff]

def pairTerm (F : Y → Γ → ℂ) (p : Y × ConjSelf Γ) : ℂ :=
  ((Nat.card (MulAction.stabilizer Γ p) : ℕ) : ℂ)⁻¹ * F p.1 (val p.2)

theorem pairTerm_smul (F : Y → Γ → ℂ) (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (η : Γ) (p : Y × ConjSelf Γ) : pairTerm F (η • p) = pairTerm F p := by
  unfold pairTerm
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj η).injective]
  congr 1
  exact hF η p.1 (val p.2)

theorem pairTerm_out (F : Y → Γ → ℂ) (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (p : Y × ConjSelf Γ) :
    pairTerm F (Quotient.out (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p)) = pairTerm F p := by
  obtain ⟨η, hη⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p))
  rw [← hη]
  exact pairTerm_smul F hF η p

def pairSum (F : Y → Γ → ℂ) : ℂ :=
  ∑ᶠ o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ), pairTerm F (Quotient.out o)

end GlobalTheory.OrbitUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyAnnihilatesCommutingLinearCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyAnnihilatesCommutingLinearCombination
noncomputable section

open Polynomial

namespace GlobalTheory.CommutingPoly

theorem exists_poly_annihilates_linear_combination : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [Fintype ι] (A : ι → Module.End ℂ M),
    (∀ i j, Commute (A i) (A j)) → ∀ (c : ι → ℂ) (P : ι → Polynomial ℂ), (∀ i, P i ≠ 0) →
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) →
        Polynomial.aeval (∑ i, c i • A i) p v = 0 := by
  intro M _ _ ι _ A hc c P hP
  classical
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range A)) :=
    Algebra.isMulCommutative_adjoin ℂ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hc i j)
  open scoped IsMulCommutative in
  let S := Algebra.adjoin ℂ (Set.range A)
  let I : Ideal S :=
    { carrier := {a | ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0}
      add_mem' := by
        intro a b ha hb v hv
        simp only [Set.mem_setOf_eq] at ha hb
        simp [ha v hv, hb v hv]
      zero_mem' := by intro v _; simp
      smul_mem' := by
        intro a b hb v hv
        show ((a * b : S) : Module.End ℂ M) v = 0
        rw [Subalgebra.coe_mul, Module.End.mul_apply, hb v hv, map_zero] }
  have hI : ∀ a : S, a ∈ I ↔ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0 :=
    fun a => Iff.rfl
  let t : ι → S := fun i => ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let q : S →ₐ[ℂ] S ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hint : ∀ i, IsIntegral ℂ (q (t i)) := by
    intro i
    refine IsAlgebraic.isIntegral ⟨P i, hP i, ?_⟩
    rw [aeval_algHom_apply]
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    rw [hI]
    intro v hv
    rw [aeval_subalgebra_coe]
    exact hv i
  have hs : IsIntegral ℂ (q (∑ i, c i • t i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact IsIntegral.sum _ (fun i _ => by rw [map_smul]; exact (hint i).smul _)
  obtain ⟨p, hpm, hp⟩ := hs
  refine ⟨p, hpm.ne_zero, fun v hv => ?_⟩
  have hq : q (aeval (∑ i, c i • t i) p) = 0 := by
    rw [← aeval_algHom_apply, aeval_def]
    exact hp
  have hmem : aeval (∑ i, c i • t i) p ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp hq
  have h := (hI _).mp hmem v hv
  rw [aeval_subalgebra_coe] at h
  have hsum : ((∑ i, c i • t i : S) : Module.End ℂ M) = ∑ i, c i • A i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, c i • t i : S) : Module.End ℂ M) = S.val (∑ i, c i • t i) from rfl, map_sum]
    simp [t]
  rw [hsum] at h
  exact h

end GlobalTheory.CommutingPoly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyAnnihilatesCommutingLinearCombinationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_annihilates_commuting_linear_combination : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [Fintype ι] (A : ι → Module.End ℂ M),
    (∀ i j, Commute (A i) (A j)) → ∀ (c : ι → ℂ) (P : ι → Polynomial ℂ), (∀ i, P i ≠ 0) →
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) →
        Polynomial.aeval (∑ i, c i • A i) p v = 0 := by
  first | exact @GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination | exact GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination | (intros; apply GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdArgRealUnitEqOne
open NumberField

namespace GlobalTheory

theorem prod_arg_real_unit_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ)
    (hq : q.Prime) (hq2 : 2 < q)
    (u : (𝓞 E)ˣ) (hu : (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)})
    (hreal : ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E)) :
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) /
      ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  set x : E := ((u : 𝓞 E) : E) with hx
  have hnorm : ∏ w : InfinitePlace E, ‖w.embedding x‖ = 1 := by
    have h1 := InfinitePlace.prod_eq_abs_norm x
    have hN : |Algebra.norm ℚ x| = 1 := Units.norm E u
    rw [hN] at h1
    have h2 : ∏ w : InfinitePlace E, w x ^ w.mult =
        (∏ w : InfinitePlace E, ‖w.embedding x‖) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [IsTotallyComplex.mult_eq, InfinitePlace.norm_embedding_eq]
    rw [h2] at h1
    have h0 : 0 ≤ ∏ w : InfinitePlace E, ‖w.embedding x‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    exact (pow_eq_one_iff_of_nonneg h0 two_ne_zero).mp (by exact_mod_cast h1)
  rw [Finset.prod_div_distrib, ← Complex.ofReal_prod, hnorm, Complex.ofReal_one, div_one]
  set P : ℂ := ∏ w : InfinitePlace E, w.embedding x with hP
  have hPreal : starRingEnd ℂ P = P := by
    rw [hP, map_prod]
    exact Finset.prod_congr rfl fun w _ => hreal w.embedding
  have hPnorm : ‖P‖ = 1 := by rw [hP, norm_prod, hnorm]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hu
  have hxy : x = 1 + ((y : 𝓞 E) : E) * (q : E) := by
    have : (u : 𝓞 E) = 1 + y * (q : 𝓞 E) := by rw [hy]; ring
    rw [hx, this]; push_cast; ring
  have hcong : ∃ s ∈ integralClosure ℤ ℂ, P = 1 + s * (q : ℂ) := by
    rw [hP]
    refine Finset.prod_induction _ (fun z => ∃ s ∈ integralClosure ℤ ℂ, z = 1 + s * (q : ℂ))
      ?_ ⟨0, zero_mem _, by ring⟩ ?_
    · rintro a b ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
      refine ⟨s + t + s * t * q, ?_, by ring⟩
      exact add_mem (add_mem hs ht) (mul_mem (mul_mem hs ht) (Subalgebra.natCast_mem _ q))
    · intro w _
      refine ⟨w.embedding ((y : 𝓞 E) : E), ?_, ?_⟩
      · rw [mem_integralClosure_iff]
        exact (RingOfIntegers.isIntegral_coe y).map w.embedding.toIntAlgHom
      · rw [hxy]; simp
  obtain ⟨s, hs, hPs⟩ := hcong
  have hre : P = (P.re : ℂ) := ((Complex.conj_eq_iff_re).mp hPreal).symm
  have habs : |P.re| = 1 := by
    rw [← hPnorm, hre, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  rcases (abs_eq zero_le_one).mp habs with h | h
  · rw [hre, h, Complex.ofReal_one]
  · exfalso
    have hPm : P = -1 := by rw [hre, h]; simp
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hs' : s = algebraMap ℚ ℂ (-2 / q) := by
      rw [hPm] at hPs
      rw [map_div₀, map_neg, map_ofNat, map_natCast]
      field_simp
      linear_combination -hPs
    rw [mem_integralClosure_iff, hs'] at hs
    have hint : IsIntegral ℤ ((-2 / q : ℚ)) :=
      (isIntegral_algebraMap_iff ).mp hs
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h2 : (n : ℚ) * q = -2 := by
      rw [show (algebraMap ℤ ℚ n) = (n : ℚ) from rfl] at hn
      rw [hn]; field_simp
    have h3 : n * (q : ℤ) = -2 := by exact_mod_cast h2
    have h4 : (q : ℤ) ∣ 2 := ⟨-n, by linarith⟩
    have h5 : q ∣ 2 := by exact_mod_cast h4
    have := Nat.le_of_dvd two_pos h5
    omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRealOfCongrOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRealOfCongrOne
open NumberField

namespace GlobalTheory.UnitReal

theorem unit_real_of_congr_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime →
    ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E) := by
  intro E _ _ _ q hq hqt u hu φ
  set I : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with hI
  set c : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hc
  set v : (𝓞 E)ˣ := IsCMField.unitsComplexConj E u with hv
  have hvc : (v : 𝓞 E) = c u := rfl
  have hv1 : (v : 𝓞 E) - 1 ∈ I := by
    rw [hI, Ideal.mem_span_singleton] at hu ⊢
    obtain ⟨y, hy⟩ := hu
    refine ⟨c y, ?_⟩
    rw [hvc, ← map_one c, ← map_sub, hy, map_mul, map_natCast]
  set ζ : (𝓞 E)ˣ := (IsCMField.unitsMulComplexConjInv E u : (𝓞 E)ˣ) with hζ
  have hζv : ζ * v = u := by rw [hζ, IsCMField.unitsMulComplexConjInv_apply, inv_mul_cancel_right]
  have hζ1 : Ideal.Quotient.mk I (ζ : 𝓞 E) = 1 := by
    have a1 : Ideal.Quotient.mk I (u : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hu
    have a2 : Ideal.Quotient.mk I (v : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hv1
    have := congrArg (fun x : (𝓞 E)ˣ => Ideal.Quotient.mk I (x : 𝓞 E)) hζv
    simp only [Units.val_mul, map_mul, a1, a2, mul_one] at this
    exact this
  have ht : ζ ^ Nat.card (Units.torsion E) = 1 := by
    have h4 : (IsCMField.unitsMulComplexConjInv E u) ^ Nat.card (Units.torsion E) = 1 := pow_card_eq_one'
    have := congrArg Subtype.val h4
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    exact this
  have hζeq : ζ = 1 := by
    by_contra hne
    have hne' : (ζ : 𝓞 E) - 1 ≠ 0 := by
      rw [sub_ne_zero]; intro h; exact hne (Units.ext h)
    have hsum : ∑ j ∈ Finset.range (Nat.card (Units.torsion E)), (ζ : 𝓞 E) ^ j = 0 := by
      have := mul_geom_sum ((ζ : 𝓞 E)) (Nat.card (Units.torsion E))
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_left hne'
    have hmod := congrArg (Ideal.Quotient.mk I) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_pow, hζ1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, map_zero] at hmod
    have hmem : ((Nat.card (Units.torsion E) : ℕ) : 𝓞 E) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hmod
    rw [hI, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hn := congrArg (Algebra.norm ℤ) hy
    rw [map_mul] at hn
    have e1 : ∀ n : ℕ, Algebra.norm ℤ ((n : 𝓞 E)) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      intro n
      rw [← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]
    rw [e1, e1] at hn
    have hd : 0 < Module.finrank ℤ (𝓞 E) := by
      rw [RingOfIntegers.rank]; exact Module.finrank_pos
    have hdvd : (q : ℤ) ∣ (Nat.card (Units.torsion E) : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [hn]; exact Dvd.dvd.mul_right (dvd_pow_self _ hd.ne') _
    have hdvd' : q ∣ Nat.card (Units.torsion E) ^ Module.finrank ℤ (𝓞 E) := by exact_mod_cast hdvd
    exact hqt (hq.dvd_of_dvd_pow hdvd')
  have huv : (v : 𝓞 E) = u := by rw [← hζv, hζeq, one_mul]
  have hE : IsCMField.complexConj E ((u : 𝓞 E) : E) = ((u : 𝓞 E) : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) huv
    exact this
  rw [← IsCMField.complexEmbedding_complexConj, hE]

end GlobalTheory.UnitReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRealOfCongrOneStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_real_of_sub_one_mem_span_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime →
    ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E) := by
  first | exact @GlobalTheory.UnitReal.unit_real_of_congr_one | exact GlobalTheory.UnitReal.unit_real_of_congr_one | (intros; apply GlobalTheory.UnitReal.unit_real_of_congr_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCompEqFinsumCardFiberMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCompEqFinsumCardFiberMul
open scoped Pointwise

namespace GlobalTheory

theorem finsum_comp_eq_finsum_natCard_fiber_mul {X Y : Type} (π : X → Y) (h : Y → ℂ)
    (hf : (∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) :
    ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
  classical
  by_cases hfin : (Function.support (h ∘ π)).Finite
  · set S := hfin.toFinset with hS
    have hmemS : ∀ x, x ∈ S ↔ h (π x) ≠ 0 := by
      intro x
      simp [hS]
    have hL : ∑ᶠ x, h (π x) = ∑ x ∈ S, h (π x) := by
      apply finsum_eq_sum_of_support_subset
      intro x hx
      exact (hmemS x).2 hx
    have hR : ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y
        = ∑ y ∈ S.image π, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
      apply finsum_eq_sum_of_support_subset
      intro y hy
      rw [Function.mem_support] at hy
      have h1 : h y ≠ 0 := right_ne_zero_of_mul hy
      have h2 : Nat.card (π ⁻¹' {y}) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hy
      obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp h2).1
      have hxy : π x = y := hx
      rw [Finset.coe_image]
      refine ⟨x, ?_, hxy⟩
      rw [Finset.mem_coe, hmemS, hxy]
      exact h1
    rw [hL, hR, ← Finset.sum_fiberwise_of_maps_to (g := π) (t := S.image π)
      (fun x hx => Finset.mem_image_of_mem π hx)]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
    have hne : h (π x₀) ≠ 0 := (hmemS x₀).1 hx₀
    have hfib : π ⁻¹' {π x₀} = ↑(S.filter (fun x => π x = π x₀)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Set.mem_ofPred_eq]
      constructor
      · intro hx
        refine ⟨?_, hx⟩
        rw [hmemS, hx]
        exact hne
      · exact fun hx => hx.2
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul, hfib, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  · rw [finsum_of_infinite_support (f := fun x => h (π x)) hfin]
    symm
    rcases hf with hf | hf
    · apply finsum_of_infinite_support
      intro hR
      apply hfin
      refine (hR.preimage' (f := π) ?_).subset ?_
      · intro y hy
        exact hf y (right_ne_zero_of_mul hy)
      · intro x hx
        simp only [Function.mem_support, Function.comp_apply] at hx
        simp only [Set.mem_preimage, Function.mem_support]
        have hfinx : Finite (π ⁻¹' {π x}) := (hf (π x) hx).to_subtype
        have hnx : Nonempty (π ⁻¹' {π x}) := ⟨⟨x, rfl⟩⟩
        have hc : Nat.card (π ⁻¹' {π x}) ≠ 0 := Nat.card_ne_zero.mpr ⟨hnx, hfinx⟩
        exact mul_ne_zero (by exact_mod_cast hc) hx
    · have hz : (fun y => (Nat.card (π ⁻¹' {y}) : ℂ) * h y) = fun _ => 0 := by
        funext y
        by_cases hy : h y = 0
        · simp [hy]
        · simp [hf y hy]
      rw [hz, finsum_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCompEqFinsumCardFiberMulStatement
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_comp_eq_finsum_card_fiber_mul : ∀ {X Y : Type} (π : X → Y) (h : Y → ℂ), ((∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) → ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
  first | exact @GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | exact GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | (intros; apply GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul <;> assumption)
end
end
