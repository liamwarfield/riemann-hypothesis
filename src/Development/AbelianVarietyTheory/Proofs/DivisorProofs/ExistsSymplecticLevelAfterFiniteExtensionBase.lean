module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumLevel

theorem exists_galois_root (K K' : Type) [Field K] [CharZero K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E) (_ : IsGalois K E) (j : K' →ₐ[K] E) (ζ : E),
      IsPrimitiveRoot ζ m := by
  let Ω := AlgebraicClosure K'
  haveI : CharZero K' := (algebraMap K K').charZero_iff (algebraMap K K').injective |>.1 inferInstance
  haveI : CharZero Ω := (algebraMap K' Ω).charZero_iff (algebraMap K' Ω).injective |>.1 inferInstance
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  let K'' : IntermediateField K' Ω := IntermediateField.adjoin K' {ζ₀}
  haveI : FiniteDimensional K' K'' :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K') ζ₀)
  haveI : FiniteDimensional K K'' := Module.Finite.trans K' K''
  haveI : IsScalarTower K K'' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let E := IntermediateField.normalClosure K K'' Ω
  haveI : IsGalois K E := inferInstance
  haveI : FiniteDimensional K E := inferInstance
  let t : K'' →ₐ[K] E := (IsScalarTower.toAlgHom K K'' Ω).codRestrict _
    fun y => AlgHom.fieldRange_le_normalClosure _ ⟨y, rfl⟩
  have hz : ζ₀ ∈ K'' := IntermediateField.mem_adjoin_simple_self K' ζ₀
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, t.comp (IsScalarTower.toAlgHom K K' K''),
    t ⟨ζ₀, hz⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := E.val) (by exact hζ₀) Subtype.val_injective

end GlobalTheory.MumLevel

namespace GlobalTheory.MumLevel

def half (g : ℕ) (i : Fin (2 * g)) : Fin g ⊕ Fin g :=
  if h : (i : ℕ) < g then .inl ⟨i, h⟩ else .inr ⟨(i : ℕ) - g, by omega⟩

theorem omegaStd_single (g : ℕ) (a b : Fin g ⊕ Fin g) :
    omegaStd (Pi.single a (1 : ℤ)) (Pi.single b 1) =
      match a, b with
      | .inl p, .inr q => if p = q then 1 else 0
      | .inr p, .inl q => if p = q then -1 else 0
      | _, _ => 0 := by
  rcases a with p | p <;> rcases b with q | q <;>
    simp [omegaStd, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm] <;> split_ifs <;> simp

theorem stdSymp_eq (g : ℕ) (i j : Fin (2 * g)) :
    stdSymp g i j = omegaStd (Pi.single (half g i) (1 : ℤ)) (Pi.single (half g j) 1) := by
  rw [omegaStd_single]
  unfold half stdSymp
  by_cases hi : (i : ℕ) < g <;> by_cases hj : (j : ℕ) < g <;> simp only [hi, hj, dif_pos, dif_neg, not_false_eq_true, true_and, false_and, if_false]
  all_goals (try simp only [Fin.ext_iff, Fin.val_mk])
  all_goals (have := i.2; have := j.2; split_ifs <;> omega)

end GlobalTheory.MumLevel

namespace GlobalTheory.MumLevel

theorem exists_ring (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (E : Type) [Field E]
    [Algebra (FractionRing R) E] [FiniteDimensional (FractionRing R) E] [IsGalois (FractionRing R) E] (ζ : E) (m : ℕ)
    (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ m) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (e : E ≃+* FractionRing R₁)
      (ζ₁ : R₁ˣ), FinExt ρ ∧ (∀ r, e (algebraMap (FractionRing R) E (algebraMap R _ r)) = algebraMap R₁ _ (ρ r)) ∧
      e ζ = algebraMap R₁ _ ζ₁ ∧ IsPrimitiveRoot ζ₁ m := by
  letI : Algebra R E := (GalClosure.baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hloc, hfe⟩ := GalClosure.finExt_integralClosure (E := E) hR
  set R₁ := integralClosure R E
  haveI : IsFractionRing R₁ E := integralClosure.isFractionRing_of_finite_extension (FractionRing R) E
  let e : E ≃+* FractionRing R₁ := (FractionRing.algEquiv R₁ E).symm.toRingEquiv
  have he : ∀ x : R₁, e (algebraMap R₁ E x) = algebraMap R₁ _ x := fun x => (FractionRing.algEquiv R₁ E).symm.commutes x
  have hint : IsIntegral R ζ := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
    simp [hζ.pow_eq_one]
  let z : R₁ := ⟨ζ, hint⟩
  have hz : z ^ m = 1 := Subtype.ext (by simp [z, hζ.pow_eq_one])
  let ζ₁ : R₁ˣ := Units.ofPowEqOne z m hz (by omega)
  have hζ₁ : (ζ₁ : R₁) = z := Units.val_ofPowEqOne _ _ _ _
  refine ⟨R₁, inferInstance, inferInstance, hloc, algebraMap R R₁, e, ζ₁, hfe, fun r => ?_, ?_, ?_⟩
  · rw [← he]; rfl
  · rw [hζ₁, ← he]; rfl
  · refine IsPrimitiveRoot.coe_units_iff.1 ?_
    rw [hζ₁]
    exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap R₁ E) (by exact hζ) Subtype.val_injective

end GlobalTheory.MumLevel

namespace GlobalTheory.MumLevel

theorem exists_level_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∀ m : ℕ, 1 ≤ m → IsUnit (m : R) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (ζ : R₁ˣ) (_ : ReciprocityTheory.ChartRestriction.G.Out.Level A₁ m (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ))), FinExt ρ ∧ IsFib ρ A A₁ a ∧ A₁.g = A.g ∧ (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) := by
  intro R _ _ _ hR A hS m hm _
  haveI : CharZero R := hR.2
  obtain ⟨K', _, _, hfin, H⟩ := LevelAfterExt.exists_ext_level (FractionRing R) A m hm
  haveI : FiniteDimensional (FractionRing R) K' := hfin
  obtain ⟨E, _, _, _, _, j, ζ, hζ⟩ := exists_galois_root (FractionRing R) K' m hm
  obtain ⟨R₁, _, _, _, ρ, e, ζ₁, hρ, he, -, hζ₁⟩ := exists_ring R hR E ζ m hm hζ
  let f : FractionRing R →+* FractionRing R₁ := ArcPull.fracMap hρ.2.1
  let i : K' →+* FractionRing R₁ := e.toRingHom.comp j.toRingHom
  have hf : i.comp (algebraMap (FractionRing R) K') = f := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply]
    show e (j (algebraMap _ K' _)) = _
    rw [j.commutes, he, ArcPull.fracMap_algebraMap]
  haveI : CharZero (FractionRing R₁) := f.charZero_iff f.injective |>.1 inferInstance
  obtain ⟨A₁, ψ, hA⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 f A
  let ze : (FractionRing R₁)ˣ := Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ₁
  have hze : IsPrimitiveRoot (ze : FractionRing R₁) m :=
    IsPrimitiveRoot.coe_units_iff.2 (hζ₁.map_of_injective (Units.map_injective (IsFractionRing.injective R₁ _)))
  obtain ⟨lev, -, h₂, h₃⟩ := H (FractionRing R₁) i f hf A₁ ψ hA A₁.g rfl ze hze
  have hL := GlobalTheory.lawsAndExpansions.1.1
  have := A₁.isAb.comm
  have hM : (m : FractionRing R₁) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let ek := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R₁))).commRingCatIsoToRingEquiv.symm
  obtain ⟨L, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ A₁ m (unitOn ze)
    (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)) (fun F _ s => by
      have : Nontrivial Γ(Sp F, ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
      refine ⟨fun e₀ => hM ?_, (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)).map_of_injective
        (Units.map_injective fun a b hab => ek.symm.injective ((s.appTop.hom.comp ek.toRingHom).injective (by simpa using hab)))⟩
      refine (s.appTop.hom.comp ek.toRingHom).injective ?_
      refine (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective ?_
      rw [map_natCast, map_natCast, map_zero, map_zero]
      exact e₀)
    (fun k => lev (Pi.single (half A₁.g k) 1)) (fun k => h₂ _) (fun k l => by
      rw [stdSymp_eq, ← ZH.RealDimOne.unitOn_zpow]
      exact h₃ _ _)
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ, A₁, ψ, ζ₁, L, hρ,
    ⟨f, fun r => ArcPull.fracMap_algebraMap hρ.2.1 r, hA.2.1, hA.2.2.symm⟩, hA.1, ?_⟩
  have := A.isAb.comm
  exact SymBaseChange.hypS_baseChange _ _ _ _ _ ψ _ _ A.isLB A₁.isLB hA.2.1 hA.2.2.symm hS

end GlobalTheory.MumLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_after_finiteExtension_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∀ m : ℕ, 1 ≤ m → IsUnit (m : R) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (ζ : R₁ˣ) (_ : ReciprocityTheory.ChartRestriction.G.Out.Level A₁ m (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ))), FinExt ρ ∧ IsFib ρ A A₁ a ∧ A₁.g = A.g ∧ (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) := by
  first | exact @GlobalTheory.MumLevel.exists_level_finExt | exact GlobalTheory.MumLevel.exists_level_finExt | (intros; apply GlobalTheory.MumLevel.exists_level_finExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfDerHomEq
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.ParPt

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

def derHom (δ : Ω[B⁄R] →ₗ[B] B) : B →ₐ[R] DualNumber B where
  toFun b := TrivSqZeroExt.inl b + TrivSqZeroExt.inr (δ (D R B b))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [MulOpposite.smul_eq_mul_unop]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_derHom (δ : Ω[B⁄R] →ₗ[B] B) (b : B) : (derHom δ b).fst = b := by simp [derHom]

theorem snd_derHom (δ : Ω[B⁄R] →ₗ[B] B) (b : B) : (derHom δ b).snd = δ (D R B b) := by simp [derHom]

theorem eq_of_derHom_eq {δ₁ δ₂ : Ω[B⁄R] →ₗ[B] B} (h : ∀ b, derHom δ₁ b = derHom δ₂ b) : δ₁ = δ₂ := by
  have h' : ∀ b, δ₁ (D R B b) = δ₂ (D R B b) := fun b ↦ by
    rw [← snd_derHom, ← snd_derHom, h]
  exact Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext h')

end Alg

section Geo

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)

theorem eq_of_affPt_eq {δ₁ δ₂ : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] Sec s U.1}
    (h : spMap (derHom δ₁ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U =
      spMap (derHom δ₂ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U) : δ₁ = δ₂ := by
  have := GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := s) U.2 h
  exact eq_of_derHom_eq fun b ↦ RingHom.congr_fun this b

theorem exists_derHom (y : Sp (DualNumber (Sec s U.1)) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber (Sec s U.1))))
    (he : spMap (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom ≫ y = affPt s U) :
    ∃ δ : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] Sec s U.1,
      spMap (derHom δ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U = y := by
  have hsurj : Surjective (spMap (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom) := by
    refine ⟨fun x ↦ ?_⟩
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker
        (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom : Set (DualNumber (Sec s U.1))) :=
      fun a ha ↦ by
        have ha' : a.fst = 0 := ha
        have h2 : a * a = 0 := by ext <;> simp [ha']
        exact x.isPrime.mem_of_pow_mem 2 (by rw [pow_two, h2]; exact zero_mem _)
    rw [← range_comap_of_surjective _ _ (fun b ↦ ⟨TrivSqZeroExt.inl b, rfl⟩)] at hx
    exact hx
  have htop : ⊤ ≤ y ⁻¹ᵁ U.1 := by
    intro p _
    obtain ⟨q, rfl⟩ := hsurj.surj p
    change ((spMap _ ≫ y).base q) ∈ U.1
    rw [he]
    have k := IsAffineOpen.range_fromSpec U.2
    rw [Set.ext_iff] at k
    exact (k _).1 ⟨q, rfl⟩
  let α := GlobalTheory.CechKS.FormLocal.valHom y htop hy
  have hα : spMap (α : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U = y :=
    GlobalTheory.CechKS.FormLocal.valHom_pt U.2 y htop hy
  have hfst : ∀ b, (α b).fst = b := by
    have k : (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom.comp
        (α : Sec s U.1 →+* DualNumber (Sec s U.1)) = RingHom.id _ := by
      refine GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := s) U.2 ?_
      change spMap _ ≫ affPt s U = spMap _ ≫ affPt s U
      rw [Cris.spMap_comp, Category.assoc, hα, he, Cris.spMap_id, Category.id_comp]
    exact fun b ↦ RingHom.congr_fun k b
  let d : Derivation R (Sec s U.1) (Sec s U.1) :=
    { toFun := fun b ↦ (α b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl']
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul]
        simp [MulOpposite.smul_eq_mul_unop, hfst]
        ring }
  refine ⟨d.liftKaehlerDifferential, ?_⟩
  have hd : derHom d.liftKaehlerDifferential = α := by
    ext b
    · rw [fst_derHom, hfst]
    · rw [snd_derHom, Derivation.liftKaehlerDifferential_comp_D]; rfl
  rw [hd, hα]
end Geo

section Val

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)

theorem snd_val_derHom (δ : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] Sec s U.1) (y : Sp (DualNumber (Sec s U.1)) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber (Sec s U.1))))
    (e : spMap (derHom δ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U = y) (f : Form s) :
    TrivSqZeroExt.snd ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).val y hy f.1) =
      δ (connForm f.1 (affPt s U) (affPt_w s U)) := by
  have hx := affPt_w s U
  have hop : ∀ (b : Sec s U.1) (ω : Ω[Sec s U.1⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
  let Φ : TrivSqZeroExt (Sec s U.1) Ω[Sec s U.1⁄R] →ₐ[R] TrivSqZeroExt (Sec s U.1) (Sec s U.1) :=
    { toFun := fun c ↦ TrivSqZeroExt.inl c.fst + TrivSqZeroExt.inr (δ c.snd)
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b ↦ by ext <;> simp <;> ring
      map_mul' := fun a b ↦ by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, hop, map_add (f := _), map_smul, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul]
          simp [MulOpposite.smul_eq_mul_unop]
          ring
      commutes' := fun r ↦ by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl'] }
  let α₀ : Sec s U.1 →ₐ[R] Sec s U.1 := AlgHom.id R _
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R (Sec s U.1) (Sec s U.1)).π (Φ c) :=
    fun c ↦ by simp [Φ, α₀]
  have e₀ : spMap (α₀ : Sec s U.1 →+* Sec s U.1) ≫ affPt s U =
      spMap ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).π : TrivSqZeroExt (Sec s U.1) (Sec s U.1) →+* Sec s U.1) ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    ext b
    simp [α₀, fst_derHom]
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R (Sec s U.1) (Sec s U.1)) Φ α₀ hπ hx
    ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv (Sec s U.1) _ ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt (Sec s U.1) (Sec s U.1)) y hy :=
    Thick.trivHom (derHom δ) e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).secHom
    ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).red_w hy)
    (SqExt.ofModule R (Sec s U.1) (Sec s U.1)).i (SqExt.ofModule R (Sec s U.1) (Sec s U.1)).π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext <;> simp [Φ, α₀]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl fun c ↦ by
      change derHom δ c = Φ (diagSec R (Sec s U.1) c)
      ext
      · simp [Φ, fst_derHom, fst_derSec]
      · simp [Φ, snd_derHom, snd_derSec]
  have hΦ : ∀ z, TrivSqZeroExt.snd (Φ z) = δ z.snd := fun z ↦ by simp [Φ]
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = _
  rw [← map_sub, hΦ]
  rfl

end Val

end GlobalTheory.ParPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemLamOfExactClassSums
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemLamOfExactClassSums
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SepLam

theorem mem_of_forall_mem_sup_pow {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (I : Ideal V) (hI : I ≠ ⊤)
    (z : V) (h : ∀ j : ℕ, z ∈ I ⊔ maximalIdeal V ^ j) : z ∈ I := by
  haveI : Nontrivial (V ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (V ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) := Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal V).map (Ideal.Quotient.mk I) ≤ maximalIdeal (V ⧸ I) :=
    Ideal.map_le_iff_le_comap.mpr fun x hx hu => hx (isUnit_of_map_unit (Ideal.Quotient.mk I) x hu)
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (V ⧸ I)) (Ideal.IsMaximal.ne_top inferInstance)
  have hz : Ideal.Quotient.mk I z ∈ ⨅ j : ℕ, maximalIdeal (V ⧸ I) ^ j := by
    refine Ideal.mem_iInf.mpr fun j => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (h j)
    rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    refine pow_le_pow_left' hmax j ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hb
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hz
  exact hz

end GlobalTheory.Poinc.SepLam

namespace GlobalTheory.Poinc.SepLam

theorem lam_of_exact : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 1 ≤ s → 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ := by
  intro O _ bar q s W A _ _ Φ N₁ hs hN hE
  classical
  refine ⟨(W ⟨0, hs⟩ ⟨0, hs⟩).toNat, fun y hm i x hx => ?_⟩
  haveI : Subsingleton (Fin (Φ.m y)) := by rw [hm]; infer_instance
  have hsym : ∀ a b, Φ.δ y i a b = Φ.δ y i b a := (Φ.bal y i).1
  have hδpos : ∀ z, z ≠ 0 → 0 < Φ.δ y i z z := fun z hz => by
    obtain ⟨k, hk⟩ := Φ.pos y z hz
    rwa [Subsingleton.elim k i] at hk
  obtain ⟨c0, hc0, hge⟩ := QWDom.qW_ge s W Φ.posW
  have hqpos : ∀ mu : Fin s → Φ.X y, mu ≠ 0 → 0 < qW W (Φ.δ y i) mu := by
    intro mu hmu
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hmu
    have h1 : Φ.δ y i (mu v) (mu v) ≤ ∑ u, Φ.δ y i (mu u) (mu u) :=
      Finset.single_le_sum (f := fun u => Φ.δ y i (mu u) (mu u)) (fun u _ => Φ.nonneg y i _) (Finset.mem_univ v)
    have h2 : (0 : ℝ) < c0 * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) :=
      mul_pos hc0 (by exact_mod_cast (hδpos _ hv).trans_le h1)
    have h3 := hge (Φ.X y) (Φ.δ y i) hsym (Φ.nonneg y i) mu
    exact_mod_cast h2.trans_le h3
  have hqnn : ∀ mu : Fin s → Φ.X y, 0 ≤ qW W (Φ.δ y i) mu := fun mu =>
    GlobalTheory.Poinc.qW_nonneg Φ.posW hsym (Φ.nonneg y i) mu

  have hsne : (Pi.single ⟨0, hs⟩ x : Fin s → Φ.X y) ≠ 0 := fun h0 => hx (by simpa using congrFun h0 ⟨0, hs⟩)
  have hP : ∃ n : ℕ, ∃ mu : Fin s → Φ.X y, mu ≠ 0 ∧ (qW W (Φ.δ y i) mu).toNat = n :=
    ⟨_, Pi.single ⟨0, hs⟩ x, hsne, rfl⟩
  obtain ⟨mu₀, hmu₀, hq₀⟩ := Nat.find_spec hP
  have hmin : ∀ mu : Fin s → Φ.X y, mu ≠ 0 → qW W (Φ.δ y i) mu₀ ≤ qW W (Φ.δ y i) mu := by
    intro mu hmu
    have h1 := Nat.find_min' hP ⟨mu, hmu, rfl⟩
    rw [← hq₀] at h1
    have := hqnn mu₀
    have := hqnn mu
    omega
  have hlead : ∀ nu : Fin s → Φ.X y, nu ≠ 0 → qW W (Φ.δ y i) mu₀ < qW W (Φ.δ y i) (mu₀ + N₁ • nu) :=
    fun nu hnu => GlobalTheory.T.least_vector_unique_in_class_mod s W Φ.posW (Φ.X y) (Φ.δ y i) hsym (Φ.nonneg y i) ⊤ (fun mu _ h => hqpos mu h)
      mu₀ trivial hmu₀ (fun mu _ h => hmin mu h) N₁ hN nu trivial hnu
  set n₀ := (qW W (Φ.δ y i) mu₀).toNat with hn₀
  have hn₀z : (n₀ : ℤ) = qW W (Φ.δ y i) mu₀ := Int.toNat_of_nonneg (hqnn mu₀)
  have hn₀pos : 1 ≤ n₀ := by have := hqpos mu₀ hmu₀; omega
  have hmono : ∀ mu : Fin s → Φ.X y, mono W (Φ.t y) (Φ.δ y) mu = Φ.t y i ^ (qW W (Φ.δ y i) mu).toNat := by
    intro mu
    rw [mono, Fintype.prod_subsingleton _ i]
  have hsum : ∀ mu : Fin s → Φ.X y, ∑ k, qW W (Φ.δ y k) mu = qW W (Φ.δ y i) mu := fun mu =>
    Fintype.sum_subsingleton _ i
  obtain ⟨c, hc⟩ := Φ.u_unit y mu₀
  obtain ⟨h, hh⟩ := hE y mu₀ c
  have htm := (Φ.t_mem y i).1
  have hI : Ideal.span {Φ.t y i ^ (n₀ + 1)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun hu => (IsLocalRing.mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem _ htm _ (Nat.succ_pos _)) hu
  have key : Φ.ev y h - Φ.u y mu₀ c * Φ.t y i ^ n₀ ∈ Ideal.span {Φ.t y i ^ (n₀ + 1)} := by
    haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
    refine mem_of_forall_mem_sup_pow _ hI _ fun j => ?_
    obtain ⟨S, hS1, hS2, hS3⟩ := hh (max j (n₀ + 1))
    have hmem : mu₀ ∈ S := by
      by_contra hn
      have := hS2 mu₀ (fun v => ⟨0, by simp⟩) hn
      rw [hsum] at this
      omega
    have hsplit : Φ.ev y h - Φ.u y mu₀ c * Φ.t y i ^ n₀ =
        ∑ mu ∈ S.erase mu₀, Φ.term y mu c + (Φ.ev y h - RingHom.id _ (∑ mu ∈ S, Φ.term y mu c)) := by
      rw [← Finset.add_sum_erase S _ hmem, VPre.term, hmono, RingHom.id_apply]
      ring
    rw [hsplit]
    refine Submodule.add_mem_sup (Ideal.sum_mem _ fun mu hmu => ?_)
      (Ideal.pow_le_pow_right (le_max_left j (n₀ + 1)) hS3)
    obtain ⟨hne, hmuS⟩ := Finset.mem_erase.mp hmu
    have hcong := hS1 mu hmuS
    set nu : Fin s → Φ.X y := fun v => (hcong v).choose
    have hmu_eq : mu = mu₀ + N₁ • nu := funext fun v => (hcong v).choose_spec
    have hnu : nu ≠ 0 := by
      rintro h0
      rw [h0, smul_zero, add_zero] at hmu_eq
      exact hne hmu_eq
    have hlt := hlead nu hnu
    rw [← hmu_eq] at hlt
    rw [VPre.term, hmono, Ideal.mem_span_singleton]
    refine Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _
    have := hqnn mu
    omega
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp key
  have hev : Φ.ev y h = Φ.t y i ^ n₀ * (Φ.u y mu₀ c + r * Φ.t y i) := by linear_combination -hr
  have hunit : IsUnit (Φ.u y mu₀ c + r * Φ.t y i) := by
    by_contra hu
    have h1 : Φ.u y mu₀ c + r * Φ.t y i ∈ maximalIdeal (Φ.V y) := (IsLocalRing.mem_maximalIdeal _).mpr hu
    have h2 := (maximalIdeal (Φ.V y)).sub_mem h1 ((maximalIdeal (Φ.V y)).mul_mem_left r htm)
    rw [add_sub_cancel_right] at h2
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hc
  have hevm : Φ.ev y h ∈ maximalIdeal (Φ.V y) := by
    rw [hev]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ htm _ hn₀pos)
  refine ⟨h, ?_, ?_⟩
  · by_contra hA
    have hu : IsUnit h := by
      by_contra hu'
      exact hA ((IsLocalRing.mem_maximalIdeal _).mpr hu')
    exact (IsLocalRing.mem_maximalIdeal _).mp hevm (hu.map (Φ.ev y))
  · have hd : Φ.ev y h ∣ Φ.t y i ^ n₀ := by
      rw [hev]
      exact (hunit.mul_right_dvd).mpr dvd_rfl
    refine hd.trans (pow_dvd_pow _ ?_)
    have hsingle : qW W (Φ.δ y i) (Pi.single ⟨0, hs⟩ x) = W ⟨0, hs⟩ ⟨0, hs⟩ * Φ.δ y i x x := by
      simp only [qW]
      rw [Finset.sum_eq_single ⟨0, hs⟩ (fun u _ hu => Finset.sum_eq_zero fun v _ => by
          simp [Pi.single_eq_of_ne hu]) (by simp),
        Finset.sum_eq_single ⟨0, hs⟩ (fun v _ hv => by simp [Pi.single_eq_of_ne hv]) (by simp)]
      simp
    have hle := hmin _ hsne
    rw [hsingle] at hle
    have hdx := hδpos x hx
    have hW : 0 < W ⟨0, hs⟩ ⟨0, hs⟩ := by
      by_contra hW
      push_neg at hW
      have : W ⟨0, hs⟩ ⟨0, hs⟩ * Φ.δ y i x x ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hW hdx.le
      omega
    zify
    rw [Int.toNat_of_nonneg hW.le, Int.toNat_of_nonneg hdx.le, hn₀z]
    exact hle

end GlobalTheory.Poinc.SepLam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemLamOfExactClassSumsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 1 ≤ s → 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ := by
  first | exact @GlobalTheory.Poinc.SepLam.lam_of_exact | exact GlobalTheory.Poinc.SepLam.lam_of_exact | (intros; apply GlobalTheory.Poinc.SepLam.lam_of_exact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegeneration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegeneration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensPer

theorem prod_psum_two {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {U : Type} [CommGroup U]
    (H : ((G ⊗ G).left ⟶ G.left) → U) :
    ∏ K : ULift.{0} (Finset (Fin 2)), H (psum G (x2 G) K.down).left ^ ((-1 : ℤ) ^ (2 - K.down.card)) =
      H (psum G (x2 G) {0, 1}).left * (H (psum G (x2 G) {0}).left)⁻¹ * (H (psum G (x2 G) {1}).left)⁻¹ *
        H (psum G (x2 G) ∅).left := by
  refine (Fintype.prod_equiv Equiv.ulift _
    (fun I => H (psum G (x2 G) I).left ^ ((-1 : ℤ) ^ (2 - I.card))) fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q₂ : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₂, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem periods_alg {U : Type} [CommGroup U] {X : Type} [AddCommGroup X] {P : Type} [Mul P] (c : X → P)
    (c_add : ∀ x y, c (x + y) = c x * c y) (t : X → X → U) (θ : P → P → P → U) (symm : ∀ x y, t x y = t y x)
    (add : ∀ x x' y, t (x + x') y * θ (c x) (c x') (c y) = t x y * t x' y) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (a b : Fin r → X) :
    (∏ i, ∏ j, t (a i + b i) (a j + b j) ^ W i j) * (∏ i, ∏ j, t (a i) (a j) ^ W i j)⁻¹ *
        (∏ i, ∏ j, t (b i) (b j) ^ W i j)⁻¹ =
      (∏ i, ∏ j, (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j)) * ∏ i, ∏ j, t (a i) (b j) ^ ((W + W.transpose) i j) := by
  have base : ∀ x x' y y' : X, t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ =
      (θ (c x) (c x') (c y * c y') * θ (c y) (c y') (c x) * θ (c y) (c y') (c x'))⁻¹ * (t x y' * t y x') := by
    intro x x' y y'
    have e₁ := add x x' (y + y')
    have e₂ := add y y' x
    have e₃ := add y y' x'
    rw [c_add] at e₁
    have s₁ := symm x (y + y')
    have s₂ := symm x' (y + y')
    have s₃ := symm y x
    have s₄ := symm y' x
    have s₅ := symm y' x'
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃
    have b₁ := E s₁; have b₂ := E s₂; have b₃ := E s₃; have b₄ := E s₄; have b₅ := E s₅
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ b₃ b₄ b₅ ⊢
    linear_combination (norm := abel) a₁ + a₂ + a₃ + b₁ + b₂ + b₃ + b₄ + b₅
  have hij : ∀ i j, t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ * (t (b i) (b j) ^ W i j)⁻¹ =
      (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j) * (t (a i) (b j) ^ W i j * t (a j) (b i) ^ W i j) := by
    intro i j
    rw [← inv_zpow, ← inv_zpow, ← mul_zpow, ← mul_zpow, base, zpow_neg, ← inv_zpow, ← mul_zpow, mul_zpow]
  have hc : ∏ i, ∏ j, t (a j) (b i) ^ W i j = ∏ i, ∏ j, t (a i) (b j) ^ W j i := Finset.prod_comm
  calc _ = ∏ i, ∏ j, (t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ *
        (t (b i) (b j) ^ W i j)⁻¹) := by simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    _ = _ := Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hij i j
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Matrix.add_apply, Matrix.transpose_apply, zpow_add]
      rw [hc]

end GlobalTheory.Mum.TensPer

namespace GlobalTheory.Mum.TensPer
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem groupSchemePartialSum_twoPoints_empty : psum G (x2 G) ∅ = 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_first : psum G (x2 G) {0} = fst G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_second : psum G (x2 G) {1} = snd G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_both : psum G (x2 G) {0, 1} = fst G G * (snd G G * 1) := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] by decide]
  rfl

end GlobalTheory.Mum.TensPer


open GlobalTheory.Mum.TensPer in
theorem GlobalTheory.Mum.Tens.tau_periods : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (T.w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ T.pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j)) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I D D' r W T a b z J J' hJ hJ'
  have twist_vector_at_zero : ∀ (E : DegData R I) (K : ((TK R).left ⟶ E.toPre.P.A.left) → E.toPre.P.L.ι),
      Good E.toPre.P.L z K → val (E.toPre.tau 0 0) (𝟙 _) z K = 1 := by
    intro E K hK
    have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hK E.tau_bimult 0 0 0
    have f : th E.toPre z K (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) = 1 := by
      rw [cPoint_zero]; exact (isCub_cubV E.toPre.cub hK).face 1 1
    rw [f, _root_.mul_one] at e
    have h0 : val (E.toPre.tau (0 + 0) 0) (𝟙 _) z K = val (E.toPre.tau 0 0) (𝟙 _) z K :=
      congrArg (fun x => val (E.toPre.tau x 0) (𝟙 _) z K) (add_zero 0)
    exact mul_eq_left.1 (e.symm.trans h0)
  have hadd : ∀ x x' y : D.toPre.X, val (D.toPre.tau (x + x') y) (𝟙 _) z J *
      cubV D.toPre.cub z J (cP D.toPre (TK R) x) (cP D.toPre (TK R) x') (cP D.toPre (TK R) y) =
      val (D.toPre.tau x y) (𝟙 _) z J * val (D.toPre.tau x' y) (𝟙 _) z J :=
    fun x x' y => GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ D.tau_bimult x x' y
  have hsym : ∀ x y : D.toPre.X, val (D.toPre.tau x y) (𝟙 _) z J = val (D.toPre.tau y x) (𝟙 _) z J :=
    fun x y => GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ x y
  set ρ : TK R ⟶ D'.toPre.P.A ⊗ D'.toPre.P.A :=
    lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) with hρ
  have wv : ∀ (q : (D'.toPre.P.A ⊗ D'.toPre.P.A).left ⟶ D'.toPre.P.A.left) (y : D'.toPre.X),
      ρ.left ≫ q = D'.toPre.xK y →
      gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))) =
      gm (D'.toPre.xK y) z _ (T.w.s (fun k => J (D'.toPre.xK y ≫ tensφ T.pr k), J' (D'.toPre.xK y))) := by
    intro q y h
    have gen : ∀ m m' j j', m = m' → j = j' → gm m z _ (T.w.s j) = gm m' z _ (T.w.s j') := by
      rintro _ _ _ _ rfl rfl; rfl
    refine gen _ _ _ _ h ?_
    refine Prod.ext ?_ ?_
    · dsimp only
      funext k
      rw [← Category.assoc, h]
    · dsimp only
      rw [h]
  have hE : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) ∅).left = D'.toPre.xK 0 := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) 0).left
    rw [groupSchemePartialSum_twoPoints_empty, cPoint_zero, MonObj.comp_one]
  have h₀ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0}).left = D'.toPre.xK a := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) a).left
    rw [groupSchemePartialSum_twoPoints_first, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst]; rfl
  have h₁ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {1}).left = D'.toPre.xK b := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) b).left
    rw [groupSchemePartialSum_twoPoints_second, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_snd]; rfl
  have h₂ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0, 1}).left = D'.toPre.xK (a + b) := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) (a + b)).left
    rw [groupSchemePartialSum_twoPoints_both, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst, lift_snd, cPoint_add]; rfl
  have hA : ∀ i, ρ ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe a i) := fun i => by
    rw [hρ, lift_fst_assoc, Category.assoc, T.c_pr]; rfl
  have hB : ∀ i, ρ ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe b i) := fun i => by
    rw [hρ, lift_snd_assoc, Category.assoc, T.c_pr]; rfl
  have P := prod_psum_two (G := D'.toPre.P.A)
    (fun q => gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))))
  beta_reduce at P
  rw [P]
  rw [wv _ _ h₂, wv _ _ h₀, wv _ _ h₁, wv _ _ hE]
  simp only [hA, hB]
  rw [GlobalTheory.TauBalBox.tau_val D'.toPre hJ' a b (𝟙 _)]
  have hrig : (val D'.toPre.rigK (𝟙 _) z J')⁻¹ = val (D'.toPre.psi 0) (𝟙 _) z J' := by
    have e := GlobalTheory.TauBalBox.tau_val D'.toPre hJ' 0 0 (𝟙 _)
    rw [twist_vector_at_zero D' J' hJ'] at e
    have h0 : val (D'.toPre.psi (0 + 0)) (𝟙 _) z J' = val (D'.toPre.psi 0) (𝟙 _) z J' :=
      congrArg (fun x => val (D'.toPre.psi x) (𝟙 _) z J') (add_zero 0)
    rw [h0, mul_inv_cancel, _root_.one_mul] at e
    exact (inv_mul_eq_one.1 e.symm).symm
  rw [hrig, T.psi (a + b) z J J' hJ hJ', T.psi a z J J' hJ hJ', T.psi b z J J' hJ hJ', T.psi 0 z J J' hJ hJ']
  have hQ0 : ∏ i, ∏ j, val (D.toPre.tau (T.xe 0 i) (T.xe 0 j)) (𝟙 _) z J ^ W i j = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [show T.xe 0 = 0 from map_zero _]
      exact (congrArg (· ^ W i j) (twist_vector_at_zero D J hJ)).trans (one_zpow _)
  have hQab : ∏ i, ∏ j, val (D.toPre.tau (T.xe (a + b) i) (T.xe (a + b) j)) (𝟙 _) z J ^ W i j =
      ∏ i, ∏ j, val (D.toPre.tau (T.xe a i + T.xe b i) (T.xe a j + T.xe b j)) (𝟙 _) z J ^ W i j := by
    rw [map_add (f := _)]; rfl
  rw [hQ0, hQab]
  have key := periods_alg (cP D.toPre (TK R)) (cPoint_add D.toPre (TK R))
    (fun x y => val (D.toPre.tau x y) (𝟙 _) z J) (cubV D.toPre.cub z J) hsym hadd W (T.xe a) (T.xe b)
  beta_reduce at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k ⊢
  linear_combination (norm := abel) k
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegenerationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_value_product_formula_degeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (T.w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ T.pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j)) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  first | exact @GlobalTheory.Mum.Tens.tau_periods | exact GlobalTheory.Mum.Tens.tau_periods | (intros; apply GlobalTheory.Mum.Tens.tau_periods <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentElem
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ff_descent_elem : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (a : D'), a ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] a →
      ∃ e : D, algebraMap D D' e = a := by
  intro D D' _ _ _ _ a h
  have hx : FlatDescent.amitsurDiff (A := D) D' D (a ⊗ₜ[D] (1 : D)) = 0 := by
    apply (LinearEquiv.lTensor D' (TensorProduct.rid D D')).injective
    simp [FlatDescent.amitsurDiff_tmul, h]
  obtain ⟨m, hm⟩ := ((FlatDescent.amitsur_exact (A := D) (B := D') (M := D)).2 _).1 hx
  refine ⟨m, ?_⟩
  have := congrArg (TensorProduct.rid D D') hm
  simpa [Algebra.algebraMap_eq_smul_one] using this

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ff_descent_pairs : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Algebra R D]
    [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D'), (ψ : D →+* D').FaithfullyFlat → ∀ a : D',
    (∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → α a = β a) →
      ∃! e : D, ψ e = a := by
  intro R _ D D' _ _ _ _ ψ hψ a h
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
  have hinj : Function.Injective (algebraMap D D') := FaithfulSMul.algebraMap_injective D D'
  let α : D' →ₐ[R] D' ⊗[D] D' := Algebra.TensorProduct.includeLeft
  let β : D' →ₐ[R] D' ⊗[D] D' := (Algebra.TensorProduct.includeRight).restrictScalars R
  have hαβ : α.comp ψ = β.comp ψ := by
    ext x
    show ψ x ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] ψ x
    have : ψ x = algebraMap D D' x := rfl
    rw [this, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hab : a ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] a := h _ α β hαβ
  obtain ⟨e, he⟩ := GlobalTheory.ff_descent_elem D D' a hab
  exact ⟨e, he, fun e' he' => hinj (he'.trans he.symm)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixWeightedPairBundleRigidifiedAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixWeightedPairBundleRigidifiedAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.CechPic

noncomputable section
namespace GlobalTheory.PowFormProps

def preQ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left) (hQ : QHyp A Q) :
    SiegPre 0 1 (0 : ℤ) (specZIsTerminal.from S) where
  A := A
  ab := hQ.1
  P := Q
  isLB := hQ.2.1
  rig₁ := hQ.2.2.1
  rig₂ := hQ.2.2.2.1
  symm := hQ.2.2.2.2.1
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ hz => by
    rw [map_zero] at hz
    exact absurd hz z.ne_zero

theorem formLB_props : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q →
    ∀ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
      IsAbelianScheme (Out.powObj A r) ∧ (formLB A Q (Out.powPr A (n := r)) W).IsLB ∧
      Out.Rigidified (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) ∧
      Out.RelAmple (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) := by
  intro S A _ _ Q hQ r W hW
  let c := preQ A Q hQ
  have hA' : Out.RelAmple c.A c.diag := hQ.2.2.2.2.2
  let pr : Fin r → (Out.powObj A r ⟶ A) := Out.powPr A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin r → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A r, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit A r).lift (Fan.mk T y), fun u => (Out.powIsLimit A r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (formLB A Q pr W).IsLB := LB.isLB_linComb hQ.2.1 _ _
  have hLW : cls (formLB A Q pr W) hL = PrincipalIntegral.quad (cls c.P c.isLB) W pr := cls_linComb hQ.2.1 _ _ _
  have hadd := PrincipalIntegral.pair_mul c SemiRigid.globalFns hA'
  exact ⟨GlobalTheory.isAbelianScheme_powObj_of_isAbelianScheme A hQ.1 r, hL,
    PrincipalIntegral.rigidified hadd hmon hL hLW,
    PosDefAmple.relAmple_linComb_of_posDef SemiRigid.globalFns 0 1 r ℤ 0 S _ c (Out.powObj A r) pr W hmon huniv hA' hW⟩

end GlobalTheory.PowFormProps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixWeightedPairBundleRigidifiedAmpleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixWeightedPairBundle_rigidified_ample : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsAbelianScheme (Out.powObj A r) ∧ (formLB A Q (Out.powPr A (n := r)) W).IsLB ∧ Out.Rigidified (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) ∧ Out.RelAmple (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) := by
  first | (exact @GlobalTheory.PowFormProps.formLB_props) | (exact GlobalTheory.PowFormProps.formLB_props) | (intros; apply GlobalTheory.PowFormProps.formLB_props  <;> assumption)
end
end
