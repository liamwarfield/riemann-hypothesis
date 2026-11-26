module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UT.ExactTerm

theorem exists_ringHom_lift (F : Type) [Field F] [IsAlgClosed F] {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsIntegrallyClosed O] [Algebra O F] [IsFractionRing O F] {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] (φ : A →+* ResidueField O)
    (hφ : φ.comp (algebraMap O A) = residue O) :
    ∃ ψ : A →+* O, ψ.comp (algebraMap O A) = RingHom.id O ∧ (residue O).comp ψ = φ := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker φ).LiesOver (maximalIdeal O) := ⟨by
    show maximalIdeal O = Ideal.comap (algebraMap O A) (RingHom.ker φ)
    rw [RingHom.comap_ker, hφ, ker_residue]⟩
  obtain ⟨P, hPQ, hP, hPlo⟩ := (RingHom.ker φ).exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal O)) (q := maximalIdeal O) bot_le
  have hjinj : Function.Injective (algebraMap O P.ResidueField) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : algebraMap O A y ∈ P := by
      rw [← Ideal.algebraMap_residueField_eq_zero, ← IsScalarTower.algebraMap_apply]
      exact hy
    have h2 : y ∈ P.under O := h1
    rw [← hPlo.over] at h2
    simpa using h2
  let : Algebra F P.ResidueField := (IsFractionRing.lift (K := F) hjinj).toAlgebra
  have : IsScalarTower O F P.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun y => (IsFractionRing.lift_algebraMap hjinj y).symm
  have hrange : ∀ a : A, ∃ y : O, algebraMap O P.ResidueField y = algebraMap A P.ResidueField a := by
    intro a
    have hO : IsIntegral O (algebraMap A P.ResidueField a) :=
      (Algebra.IsIntegral.isIntegral a).algebraMap
    have hF : IsIntegral F (algebraMap A P.ResidueField a) := hO.tower_top
    obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F)
      (K := integralClosure F P.ResidueField)).2 ⟨_, hF⟩
    have hr' : algebraMap F P.ResidueField r = algebraMap A P.ResidueField a := congrArg Subtype.val hr
    have hrO : IsIntegral O r := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom O F P.ResidueField)
        (algebraMap F P.ResidueField).injective]
      simpa [hr'] using hO
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrO
    exact ⟨y, by rw [IsScalarTower.algebraMap_apply O F P.ResidueField, hy, hr']⟩
  let e : O ≃+* (algebraMap O P.ResidueField).range :=
    RingEquiv.ofBijective (algebraMap O P.ResidueField).rangeRestrict
      ⟨fun a b h => hjinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let π' : A →+* (algebraMap O P.ResidueField).range :=
    (algebraMap A P.ResidueField).codRestrict _ fun a => by
      obtain ⟨y, hy⟩ := hrange a
      exact ⟨y, hy⟩
  have key : ∀ a, algebraMap O P.ResidueField (e.symm (π' a)) = algebraMap A P.ResidueField a :=
    fun a => congrArg Subtype.val (e.apply_symm_apply (π' a))
  refine ⟨e.symm.toRingHom.comp π', ?_, ?_⟩
  · ext y
    apply hjinj
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.id_apply]
    rw [key]
    exact (IsScalarTower.algebraMap_apply O A P.ResidueField y).symm
  · ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have hmem : algebraMap O A (e.symm (π' a)) - a ∈ RingHom.ker φ := by
      apply hPQ
      rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, ← IsScalarTower.algebraMap_apply, key,
        sub_self]
    have h1 : φ (algebraMap O A (e.symm (π' a))) = φ a := by
      rw [← sub_eq_zero, ← map_sub]
      exact (RingHom.mem_ker).mp hmem
    rw [← h1, ← RingHom.comp_apply φ (algebraMap O A), hφ]

theorem exists_section_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of O)) [IsFinite f] [Flat f] (p : Spec (CommRingCat.of (ResidueField O)) ⟶ H)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (residue O))) :
    ∃ q : Spec (CommRingCat.of O) ⟶ H, q ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ q = p := by
  have : IsAffine H := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = H.isoSpec.inv ≫ f := ⟨_, Spec.map_preimage _⟩
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hflat : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    exact MorphismProperty.comp_mem @Flat _ _ (inferInstance : Flat H.isoSpec.inv) ‹Flat f›
  obtain ⟨χ, hχ⟩ : ∃ χ, Spec.map χ = p ≫ H.isoSpec.hom := ⟨_, Spec.map_preimage _⟩
  let _ := φ.hom.toAlgebra
  have : Module.Finite O Γ(H, ⊤) := hfin
  have : Module.Flat O Γ(H, ⊤) := hflat
  have hcomp : χ.hom.comp (algebraMap O Γ(H, ⊤)) = residue O := by
    have h1 : Spec.map (φ ≫ χ) = Spec.map (CommRingCat.ofHom (residue O)) := by
      rw [Spec.map_comp, hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_ringHom_lift F χ.hom hcomp
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ H.isoSpec.inv, ?_, ?_⟩
  · have h2 : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
      exact CommRingCat.hom_ext hψ1
    rw [Category.assoc, ← hφ, ← Spec.map_comp, h2, Spec.map_id]
  · have h3 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (residue O) = χ := by
      exact CommRingCat.hom_ext hψ2
    rw [← Category.assoc, ← Spec.map_comp, h3, hχ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

theorem exists_torsion_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (n : ℕ) [IsFinite ((𝟙 G) ^ n : G ⟶ G).left] [Flat ((𝟙 G) ^ n : G ⟶ G).left]
    (t : Spec (CommRingCat.of O) ⟶ S)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G) (hx : x ^ n = 1) :
    ∃ y : Over.mk t ⟶ G, y ^ n = 1 ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ y.left = x.left := by
  have hpow : ∀ {Y : Over S} (z : Y ⟶ G), z ^ n = z ≫ (𝟙 G) ^ n := fun z => by
    rw [MonObj.comp_pow, Category.comp_id]
  have hxm : x.left ≫ ((𝟙 G) ^ n : G ⟶ G).left =
      Spec.map (CommRingCat.ofHom (residue O)) ≫ t ≫ η[G].left := by
    have h1 : (x ≫ (𝟙 G) ^ n).left = (1 : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G).left := by
      rw [← hpow, hx]
    rw [Over.comp_left, CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left] at h1
    rw [h1]
    exact Category.assoc _ _ _
  obtain ⟨q, hq1, hq2⟩ := exists_section_lift O
    (pullback.snd ((𝟙 G) ^ n : G ⟶ G).left (t ≫ η[G].left))
    (pullback.lift x.left (Spec.map (CommRingCat.ofHom (residue O))) hxm) (pullback.lift_snd _ _ _)
  have hw : ((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom = G.hom := Over.w _
  have he : η[G].left ≫ G.hom = 𝟙 S := Over.w η[G]
  refine ⟨Over.homMk (q ≫ pullback.fst _ _) ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hw, pullback.condition_assoc, Category.assoc, he, Category.comp_id,
      ← Category.assoc, hq1]
    exact Category.id_comp t
  · rw [hpow, CategoryTheory.Hom.one_def]
    ext
    change (q ≫ pullback.fst _ _) ≫ ((𝟙 G) ^ n : G ⟶ G).left = t ≫ η[G].left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq1]
    exact Category.id_comp _
  · change Spec.map (CommRingCat.ofHom (residue O)) ≫ (q ≫ pullback.fst _ _) = x.left
    rw [← Category.assoc, hq2, pullback.lift_fst]

end GlobalTheory.UT.ExactTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfIsPullbackSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.Unif

theorem locallyQuasiFinite_of_isPullback_surjective :
    ∀ (X Z X' Z' : Scheme.{0}) (φ : X ⟶ Z) (φ' : X' ⟶ Z') (a : X' ⟶ X) (p : Z' ⟶ Z),
      IsPullback a φ' φ p → Surjective p → LocallyOfFiniteType φ → QuasiCompact φ →
      LocallyQuasiFinite φ' → LocallyQuasiFinite φ := by
  intro X Z X' Z' φ φ' a p h hp _ hqc _
  have : QuasiCompact φ' := MorphismProperty.of_isPullback h hqc
  refine LocallyQuasiFinite.of_finite_preimage_singleton φ fun z => ?_
  obtain ⟨z', rfl⟩ := p.surjective z
  refine ((φ'.finite_preimage_singleton z').image a).subset fun x hx => ?_
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := p) x z' hx
  refine ⟨h.isoPullback.inv w, ?_, ?_⟩
  · change φ' (h.isoPullback.inv w) = z'
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hw2]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw1]

end GlobalTheory.Unif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ShortestVectorStrictOfMul
namespace GlobalTheory

theorem shortest_vector_strict_of_mul :
    ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (n r : ℕ), 1 ≤ n → 2 ≤ r → ∀ z : X, (∀ m, Q z ≤ Q (z + n • m)) → ∀ m : X, (n * r) • m ≠ 0 → Q z < Q (z + (n * r) • m) := by
  intro X _ Q B hadd hdiag hpos n r _ hr z hmin m hm
  have hnr : (n * r) • m = r • (n • m) := by rw [mul_comm, mul_smul]
  rw [hnr] at hm ⊢
  have h1 := hmin m
  generalize n • m = a at hm h1
  have ha : a ≠ 0 := by
    rintro rfl
    exact hm (smul_zero _)
  have hQa := hpos a ha
  have h2 : 2 * Q (r • a) = (r : ℤ) * ((r : ℤ) * (2 * Q a)) := by
    rw [hdiag, hdiag]
    simp only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
  have h3 : B z (r • a) = (r : ℤ) * B z a := by
    simp only [map_nsmul, nsmul_eq_mul]
  rw [hadd] at h1 ⊢
  rw [h3]
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have h4 : 0 ≤ (r : ℤ) * (Q a + B z a) := mul_nonneg (by omega) (by omega)
  have h5 : 0 < ((r : ℤ) * (r - 1)) * Q a :=
    mul_pos (mul_pos (by omega) (by omega)) (by omega)
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSmulEqBilinOfAnisotropic
namespace GlobalTheory

theorem exists_smul_eq_bilin_of_anisotropic {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : X →+ X →+ ℤ) (hB : ∀ a, B a a = 0 → a = 0) (l : X →+ ℚ) :
    ∃ (M : ℤ) (x : X), 0 < M ∧ ∀ m, (B x m : ℚ) = M * l m := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => l (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose c hc using hint
  let φ : Module.Dual ℤ X := b.constr ℤ c
  have hφ : ∀ m, (φ m : ℚ) = d * l m := by
    have : (Algebra.linearMap ℤ ℚ).comp φ = d • l.toIntLinearMap := by
      refine b.ext fun i => ?_
      have := hc i
      simpa [φ] using this
    intro m
    have := LinearMap.congr_fun this m
    simpa using this
  let Bh : X →+ Module.Dual ℤ X :=
    { toFun := fun x => (B x).toIntLinearMap
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let BL : X →ₗ[ℤ] Module.Dual ℤ X := Bh.toIntLinearMap
  have hBL : ∀ x m, BL x m = B x m := fun _ _ => rfl
  have hinj : Function.Injective BL := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    apply hB
    rw [← hBL, ha]; rfl
  have hrk : Module.finrank ℤ (LinearMap.range BL) = Module.finrank ℤ (Module.Dual ℤ X) := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact b.toDualEquiv.finrank_eq
  have hfin : Finite (Module.Dual ℤ X ⧸ LinearMap.range BL) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ hrk
  obtain ⟨n, hn, hnφ⟩ := (isOfFinAddOrder_of_finite
    (Submodule.Quotient.mk (p := LinearMap.range BL) φ)).exists_nsmul_eq_zero
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hnφ
  obtain ⟨x, hx⟩ := hnφ
  refine ⟨n * (d * d), d • x, mul_pos (by exact_mod_cast hn) (mul_self_pos.2 hd0), fun m => ?_⟩
  have h1 : B x m = n * φ m := by
    rw [← hBL, hx]; simp
  rw [map_zsmul, AddMonoidHom.zsmul_apply, h1]
  simp only [smul_eq_mul]
  push_cast
  rw [hφ]; ring

theorem exists_rep_mod_shifted_form_small :
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (l : X →+ ℚ) (k : ℕ), 1 ≤ k → ∀ y : X, ∃ z : X, ∀ m : X, |(B (y + k • z) m : ℚ) - l m| ≤ k * Q m := by
  intro X _ _ _ Q B hadd h2 hpos l k hk y
  have hQ0 : ∀ a, 0 ≤ Q a := by
    intro a
    by_cases ha : a = 0
    · have := h2 a
      rw [ha] at this ⊢
      simp at this
      omega
    · have := hpos a ha
      omega
  have hsm : ∀ (n : ℤ) a, Q (n • a) = n * n * Q a := by
    intro n a
    have e1 := h2 (n • a)
    have e2 := h2 a
    rw [map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, ← e2] at e1
    simp only [smul_eq_mul] at e1
    linarith
  obtain ⟨M, x, hM, hx⟩ := exists_smul_eq_bilin_of_anisotropic B (fun a ha => by
    by_contra h
    have := hpos a h
    have := h2 a
    omega) l
  let F : X → ℕ := fun z => (Q (M • (y + k • z) - x)).toNat
  obtain ⟨z, hz⟩ : ∃ z, ∀ z', F z ≤ F z' :=
    ⟨Function.argmin F, fun z' => Function.argmin_le F z'⟩
  refine ⟨z, fun m => ?_⟩
  have hz' : ∀ z', Q (M • (y + k • z) - x) ≤ Q (M • (y + k • z') - x) := by
    intro z'
    have := hz z'
    have a := hQ0 (M • (y + k • z) - x)
    have b := hQ0 (M • (y + k • z') - x)
    simp only [F] at this
    omega
  have key : ∀ s : ℤ, 0 ≤ (M * k * s) * (M * k * s) * Q m
      + (M * k * s) * (M * B (y + k • z) m - B x m) := by
    intro s
    have h := hz' (z + s • m)
    have e : M • (y + k • (z + s • m)) - x = (M • (y + k • z) - x) + (M * k * s) • m := by
      module
    rw [e, hadd, hsm, map_zsmul, map_sub, map_zsmul, AddMonoidHom.sub_apply,
      AddMonoidHom.zsmul_apply] at h
    simp only [smul_eq_mul] at h
    linarith
  have k1 : (0 : ℚ) ≤ ((M * k * 1) * (M * k * 1) * Q m
      + (M * k * 1) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key 1
  have k2 : (0 : ℚ) ≤ ((M * k * (-1)) * (M * k * (-1)) * Q m
      + (M * k * (-1)) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key (-1)
  push_cast at k1 k2
  rw [hx] at k1 k2
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hp : (0 : ℚ) < M * M * k := by positivity
  set β : ℚ := ((B (y + k • z) m : ℤ) : ℚ)
  rw [abs_le]
  constructor
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m + (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m - (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGradedRingKernelLift
open Polynomial

namespace GlobalTheory

def reesShiftIdeal {R : Type} [CommRing R] (I : Ideal R) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1)}
  zero_mem' := fun n => by simp
  add_mem' := fun {p q} hp hq n => by
    rw [Subalgebra.coe_add, coeff_add]
    exact Ideal.add_mem _ (hp n) (hq n)
  smul_mem' := fun p q hq n => by
    rw [smul_eq_mul, Subalgebra.coe_mul, coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ e
    have e' : j + k = n := by simpa using e
    rw [← e', add_assoc, pow_add]
    exact Ideal.mul_mem_mul (p.2 j) (hq k)

theorem mem_reesShiftIdeal {R : Type} [CommRing R] {I : Ideal R} (p : reesAlgebra I) :
    p ∈ reesShiftIdeal I ↔ ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1) := Iff.rfl

theorem coeff_sum_algebraMap_mul_rees {R : Type} [CommRing R] {I : Ideal R} {a : ℕ}
    (r : Fin a → R) (p : Fin a → reesAlgebra I) (n : ℕ) :
    ((∑ k, algebraMap R (reesAlgebra I) (r k) * p k : reesAlgebra I) : R[X]).coeff n
      = ∑ k, r k * (p k : R[X]).coeff n := by
  simp [Polynomial.algebraMap_eq]

theorem exists_graded_ring_kernel_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∃ (S : Type) (_ : CommRing S) (g : R →+* S), IsNoetherianRing S ∧ (∀ x ∈ I, g x = 0) ∧ ∀ (e : ℕ) (g' : R ⧸ I ^ (e + 1 + 1) →+* S), g'.comp (Ideal.Quotient.mk _) = g → ∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) (R ⧸ I ^ (e + 1 + 1))) (D₁ : Matrix (Fin c) (Fin b) (R ⧸ I ^ (e + 1 + 1))), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g').mulVec w = 0 → ∃ v, (D₀.map g').mulVec v = w) → ∀ v' : Fin a → R ⧸ I ^ (e + 1), (D₀.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1))).mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1)) (v k) = v' k := by
  intro R _ _ I
  refine ⟨reesAlgebra I ⧸ reesShiftIdeal I, inferInstance,
    (Ideal.Quotient.mk _).comp (algebraMap R (reesAlgebra I)), inferInstance, ?_, ?_⟩
  ·
    intro x hx
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_reesShiftIdeal]
    intro n
    rw [Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.coeff_C]
    split_ifs with hn
    · subst hn
      simpa using hx
    · exact Ideal.zero_mem _
  · intro e g' hg' a b c D₀ D₁ hD hex v' hv'
    have hg'x : ∀ x : R, g' (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk (reesShiftIdeal I) (algebraMap R (reesAlgebra I) x) := fun x => by
      have := RingHom.congr_fun hg' x
      simpa only [RingHom.comp_apply] using this

    obtain ⟨d₀, rfl⟩ : ∃ d : Matrix (Fin b) (Fin a) R, D₀ = d.map (Ideal.Quotient.mk _) :=
      ⟨Matrix.of fun j k => (Ideal.Quotient.mk_surjective (D₀ j k)).choose, by
        ext j k
        simp [(Ideal.Quotient.mk_surjective (D₀ j k)).choose_spec]⟩
    obtain ⟨d₁, rfl⟩ : ∃ d : Matrix (Fin c) (Fin b) R, D₁ = d.map (Ideal.Quotient.mk _) :=
      ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (D₁ i j)).choose, by
        ext i j
        simp [(Ideal.Quotient.mk_surjective (D₁ i j)).choose_spec]⟩
    obtain ⟨r, rfl⟩ : ∃ r : Fin a → R, v' = fun k => Ideal.Quotient.mk _ (r k) :=
      ⟨fun k => (Ideal.Quotient.mk_surjective (v' k)).choose,
        funext fun k => (Ideal.Quotient.mk_surjective (v' k)).choose_spec.symm⟩

    have hs : ∀ j, ∑ k, d₀ j k * r k ∈ I ^ (e + 1) := fun j => by
      have h := congrFun hv' j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Ideal.Quotient.factor_mk,
        Pi.zero_apply] at h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_mul] using h

    have hs2 : ∀ i, ∑ j, d₁ i j * ∑ k, d₀ j k * r k ∈ I ^ (e + 1 + 1) := fun i => by
      have hrow : ∀ k, ∑ j, d₁ i j * d₀ j k ∈ I ^ (e + 1 + 1) := fun k => by
        have h := congrFun (congrFun hD i) k
        simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at h
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        simpa only [map_mul] using h
      have heq : ∑ j, d₁ i j * ∑ k, d₀ j k * r k = ∑ k, (∑ j, d₁ i j * d₀ j k) * r k := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
      rw [heq]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hrow k)

    obtain ⟨m, hm⟩ : ∃ m : Fin b → reesAlgebra I,
        ∀ j, (m j : R[X]) = Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k) :=
      ⟨fun j => ⟨Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k),
        reesAlgebra.monomial_mem.mpr (hs j)⟩, fun _ => rfl⟩

    have hW : ((d₁.map (Ideal.Quotient.mk _)).map g').mulVec
        (fun j => Ideal.Quotient.mk (reesShiftIdeal I) (m j)) = 0 := by
      funext i
      have hmem : (∑ j, algebraMap R (reesAlgebra I) (d₁ i j) * m j) ∈ reesShiftIdeal I := by
        rw [mem_reesShiftIdeal]
        intro n
        rw [coeff_sum_algebraMap_mul_rees]
        simp only [hm, Polynomial.coeff_monomial]
        by_cases hn : e + 1 = n
        · subst hn
          simpa using hs2 i
        · simp [hn]
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, Pi.zero_apply,
        map_mul] using this

    obtain ⟨V, hV⟩ := hex _ hW
    choose P hP using fun k => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (V k)
    have hdiff : ∀ j, ∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k ∈
        I ^ (e + 1 + 1) := fun j => by
      have h := congrFun hV j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, ← hP] at h
      have h' : Ideal.Quotient.mk (reesShiftIdeal I)
          (∑ k, algebraMap R (reesAlgebra I) (d₀ j k) * P k) =
          Ideal.Quotient.mk (reesShiftIdeal I) (m j) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simpa only [map_mul] using h
      rw [Ideal.Quotient.eq, mem_reesShiftIdeal] at h'
      have h'' := h' (e + 1)
      rw [Subalgebra.coe_sub, Polynomial.coeff_sub, coeff_sum_algebraMap_mul_rees, hm,
        Polynomial.coeff_monomial, Finsupp.single_eq_same] at h''
      exact h''
    refine ⟨fun k => Ideal.Quotient.mk _ (r k - (P k : R[X]).coeff (e + 1)), ?_, ?_⟩
    · funext j
      have hmem : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) ∈ I ^ (e + 1 + 1) := by
        have heq : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) =
            -(∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        rw [heq]
        exact neg_mem (hdiff j)
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, map_mul] using this
    · intro k
      simp only [Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.eq, sub_sub_cancel_left]
      exact neg_mem ((P k).2 (e + 1))

end GlobalTheory
end
