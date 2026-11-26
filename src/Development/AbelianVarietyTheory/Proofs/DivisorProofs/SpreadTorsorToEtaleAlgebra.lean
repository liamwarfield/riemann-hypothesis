module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorBaseChangeZmod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorBaseChangeZmod
open CategoryTheory Limits
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocAcyc

def zmodTensorAct (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type)
    [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)) :
    Multiplicative (ZMod q) →* (B ⊗[U] D ≃ₐ[B] B ⊗[U] D) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add (f := _)]
  map_mul' g h := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add (f := _)]

@[simp] theorem zmodTensorAct_tmul (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (b : B) (x : D) (g : Multiplicative (ZMod q)) :
    zmodTensorAct U B q D act g (b ⊗ₜ x) = b ⊗ₜ act g x := by simp [zmodTensorAct]

theorem isZModTorsor_tensorBase (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (hq : 0 < q) (hD : IsZModTorsor U D q act) :
    IsZModTorsor B (B ⊗[U] D) q (zmodTensorAct U B q D act) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨h1, h2, h3, h4⟩ := hD
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id U D))
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) with hΦ
  set ΦB := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D) (fun _ => AlgHom.id B (B ⊗[U] D)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D)
        (fun g => (zmodTensorAct U B q D act g).toAlgHom)) with hΦB
  let e1 := TensorProduct.AlgebraTensorModule.distribBaseChange U B D D
  let L := (LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B
  let e2 := TensorProduct.piRight U U B (fun _ : Multiplicative (ZMod q) => D)
  have key : ∀ z, ΦB (e1 z) = e2 (L z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        funext g
        simp [e1, L, e2, hΦ, hΦB, Algebra.TensorProduct.productMap_apply_tmul]
      | add w w' hw hw' =>
        simp only [TensorProduct.tmul_add, map_add (f := _), hw, hw']
    | add z w hz hw => simp only [map_add (f := _), hz, hw]
  have : (ΦB : _ → _) = e2 ∘ L ∘ e1.symm := by
    funext w
    simpa using key (e1.symm w)
  rw [this]
  exact e2.bijective.comp (L.bijective.comp e1.symm.bijective)

theorem exists_isZModTorsor_tensorBase : ∀ (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type) [CommRing D]
    [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)), 0 < q →
    GlobalTheory.LocAcyc.IsZModTorsor U D q act →
    ∃ actB : Multiplicative (ZMod q) →* (TensorProduct U B D ≃ₐ[B] TensorProduct U B D),
      GlobalTheory.LocAcyc.IsZModTorsor B (TensorProduct U B D) q actB :=
  fun U B _ _ _ q D _ _ act hq hD => ⟨_, isZModTorsor_tensorBase U B q D act hq hD⟩

end GlobalTheory.LocAcyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorBaseChangeZmodStatement
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_base_change_zmod : ∀ (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type) [CommRing D]
    [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)), 0 < q →
    GlobalTheory.LocAcyc.IsZModTorsor U D q act →
    ∃ actB : Multiplicative (ZMod q) →* (TensorProduct U B D ≃ₐ[B] TensorProduct U B D),
      GlobalTheory.LocAcyc.IsZModTorsor B (TensorProduct U B D) q actB := by
  first | exact @GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase | exact GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase | (intros; apply GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLiftGenericFibreOfFactorization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLiftGenericFibreOfFactorization
open CategoryTheory Limits

noncomputable section

namespace GlobalTheory.GenFibLift

open GlobalTheory.LocAcyc

theorem genFibMap_comp {T E F O : Type} [CommRing T] [CommRing E] [CommRing F] [CommRing O]
    [Algebra T E] [Algebra T F] [Algebra T O] (φ : E →ₐ[T] F) (ψ : F →ₐ[T] O) :
    genFibMap (ψ.comp φ) = (genFibMap ψ).comp (genFibMap φ) :=
  genFib_ringHom_ext (fun e => by
    simp only [RingHom.comp_apply, genFibMap_algebraMap, AlgHom.comp_apply])

def den {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (t : nonZeroDivisors T) :
    Algebra.algebraMapSubmonoid O (nonZeroDivisors T) :=
  ⟨algebraMap T O t, Submonoid.mem_map_of_mem _ t.2⟩

theorem exists_mk' {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (x : GenFib T O) :
    ∃ (a : O) (t : nonZeroDivisors T), x = IsLocalization.mk' (GenFib T O) a (den t) := by
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) x
  obtain ⟨t, ht, hm⟩ := Submonoid.mem_map.1 m.2
  refine ⟨a, ⟨t, ht⟩, ?_⟩
  rw [show m = den ⟨t, ht⟩ from Subtype.ext hm.symm]

theorem exists_of_mk'_eq_zero {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (a : O)
    (m : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    (h : IsLocalization.mk' (GenFib T O) a m = 0) :
    ∃ t : nonZeroDivisors T, algebraMap T O t * a = 0 := by
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff a m).1 h
  obtain ⟨t, ht, hct⟩ := Submonoid.mem_map.1 c.2
  exact ⟨⟨t, ht⟩, by simpa [hct] using hc⟩

theorem genFibMap_mk' {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) (t : nonZeroDivisors T) :
    genFibMap ψ (IsLocalization.mk' (GenFib T E) e (den t)) =
      IsLocalization.mk' (GenFib T O) (ψ e) (den t) := by
  simp only [genFibMap, IsLocalization.map_mk']
  congr 1
  ext
  exact ψ.commutes t

theorem exists_finitePresentation_lift (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O]
    (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GenFib T O) :
    ∃ (Z : Type) (_ : CommRing Z) (_ : Algebra R Z) (_ : Algebra T Z) (_ : IsScalarTower T R Z)
      (_ : Algebra.FinitePresentation R Z) (g : Z →ₐ[R] O) (w : U →+* GenFib T Z),
      (genFibMap (g.restrictScalars T)).comp w = u := by
  haveI : Algebra.FinitePresentation ℤ U := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, f, hf, s, hs⟩ := Algebra.FinitePresentation.out (R := ℤ) (A := U)

  choose a t ht using fun i : Fin n => exists_mk' (T := T) (u (f (MvPolynomial.X i)))
  let e : MvPolynomial (Fin n) R →ₐ[R] O := MvPolynomial.aeval a
  let θ : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R) :=
    MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun i => IsLocalization.mk' _ (MvPolynomial.X i : MvPolynomial (Fin n) R) (den (t i)))
  have key : (genFibMap (e.restrictScalars T)).comp θ = u.comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int
        (((genFibMap (e.restrictScalars T)).comp θ).comp MvPolynomial.C)
        ((u.comp f.toRingHom).comp MvPolynomial.C)) r
    · intro i
      simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_X', genFibMap_mk']
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ht i]
      simp [e]

  have hrel : ∀ r : s, ∃ (p : MvPolynomial (Fin n) R) (τ τ' : nonZeroDivisors T),
      θ r = IsLocalization.mk' _ p (den τ) ∧ e (algebraMap T _ τ' * p) = 0 := by
    intro r
    obtain ⟨p, τ, hp⟩ := exists_mk' (T := T) (θ r)
    have h0 : genFibMap (e.restrictScalars T) (θ r) = 0 := by
      have hr : (r : MvPolynomial (Fin n) ℤ) ∈ RingHom.ker f.toRingHom := hs ▸ Ideal.subset_span r.2
      rw [← RingHom.comp_apply, key, RingHom.comp_apply, RingHom.mem_ker.1 hr, map_zero]
    rw [hp, genFibMap_mk'] at h0
    obtain ⟨τ', hτ'⟩ := exists_of_mk'_eq_zero _ _ h0
    refine ⟨p, τ, τ', hp, ?_⟩
    rw [map_mul, ← hτ']
    simp [IsScalarTower.algebraMap_apply T R (MvPolynomial (Fin n) R),
      IsScalarTower.algebraMap_apply T R O]
  choose p τ τ' hθ he using hrel
  let I : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span (Set.range fun r : s => algebraMap T _ (τ' r : T) * p r)
  have hIe : ∀ x ∈ I, e x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker e := Ideal.span_le.2 (by rintro _ ⟨r, rfl⟩; exact he r)
    exact hle hx
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R) :=
    Algebra.FinitePresentation.mvPolynomial R R (Fin n)
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  let g : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] O := Ideal.Quotient.liftₐ I e hIe
  let q : MvPolynomial (Fin n) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) := Ideal.Quotient.mkₐ R I
  let w0 : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R ⧸ I) :=
    (genFibMap (q.restrictScalars T)).comp θ
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker w0 := by
    rw [← hs, Ideal.span_le]
    intro r hr
    rw [SetLike.mem_coe, RingHom.mem_ker]
    simp only [w0, RingHom.comp_apply]
    rw [hθ ⟨r, hr⟩, genFibMap_mk']
    have hu : IsUnit (algebraMap (MvPolynomial (Fin n) R ⧸ I) (GenFib T (MvPolynomial (Fin n) R ⧸ I))
        (algebraMap T _ (τ' ⟨r, hr⟩ : T))) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)) _ (den _)
    refine (hu.mul_right_eq_zero).1 ?_
    rw [← IsLocalization.mk'_one (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)),
      ← IsLocalization.mk'_mul, one_mul]
    have hz : (q.restrictScalars T) (algebraMap T _ (τ' ⟨r, hr⟩ : T) * p ⟨r, hr⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩)
    rw [map_mul, AlgHom.commutes] at hz
    rw [hz, IsLocalization.mk'_zero]

  refine ⟨MvPolynomial (Fin n) R ⧸ I, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g, RingHom.liftOfSurjective f.toRingHom hf ⟨w0, hker⟩, ?_⟩
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := hf x
  have hy : f y = f.toRingHom y := rfl
  rw [RingHom.comp_apply, hy, RingHom.liftOfSurjective_comp_apply]
  have hgq : (g.restrictScalars T).comp (q.restrictScalars T) = e.restrictScalars T := by
    exact AlgHom.ext fun x => AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I e hIe) x
  have hcomp : (genFibMap (g.restrictScalars T)).comp w0 = u.comp f.toRingHom := by
    simp only [w0]
    rw [← RingHom.comp_assoc, ← genFibMap_comp, hgq, key]
  exact RingHom.congr_fun hcomp y

theorem exists_etale_genFib_lift : ∀ (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O],
    (∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
        (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g) →
    ∀ (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GlobalTheory.LocAcyc.GenFib T O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra T W) (_ : IsScalarTower T R W)
      (_ : Algebra.Etale R W) (ψ : W →ₐ[R] O) (uW : U →+* GlobalTheory.LocAcyc.GenFib T W),
      (GlobalTheory.LocAcyc.genFibMap (ψ.restrictScalars T)).comp uW = u := by
  intro T R O _ _ _ _ _ _ _ H U _ _ u
  obtain ⟨Z, _, _, _, _, _, g, w, hw⟩ := exists_finitePresentation_lift T R O U u
  obtain ⟨W, _, _, _, u0, v, hv⟩ := H Z g
  letI : Algebra T W := ((algebraMap R W).comp (algebraMap T R)).toAlgebra
  haveI hTRW : IsScalarTower T R W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨W, inferInstance, inferInstance, inferInstance, hTRW, inferInstance, v,
    (genFibMap (u0.restrictScalars T)).comp w, ?_⟩
  rw [← RingHom.comp_assoc, ← genFibMap_comp]
  have hvu : (v.restrictScalars T).comp (u0.restrictScalars T) = g.restrictScalars T :=
    AlgHom.ext fun z => AlgHom.congr_fun hv z
  rw [hvu, hw]

end GlobalTheory.GenFibLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLiftGenericFibreOfFactorizationStatement
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_lift_genericFibre_of_factorization : ∀ (T R O : Type) [CommRing T] [CommRing R] [CommRing O] [Algebra T R] [Algebra R O]
    [Algebra T O] [IsScalarTower T R O],
    (∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
        (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g) →
    ∀ (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GlobalTheory.LocAcyc.GenFib T O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra T W) (_ : IsScalarTower T R W)
      (_ : Algebra.Etale R W) (ψ : W →ₐ[R] O) (uW : U →+* GlobalTheory.LocAcyc.GenFib T W),
      (GlobalTheory.LocAcyc.genFibMap (ψ.restrictScalars T)).comp uW = u := by
  first | exact @GlobalTheory.GenFibLift.exists_etale_genFib_lift | exact GlobalTheory.GenFibLift.exists_etale_genFib_lift | (intros; apply GlobalTheory.GenFibLift.exists_etale_genFib_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadTorsorToEtaleAlgebra
open IsLocalRing Polynomial CategoryTheory Limits
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocAcyc

theorem spread_torsor_to_etale : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  intro T O _ _ _ _ _ P _ φ hφ hind q hq D _ _ act hD
  classical

  obtain ⟨j, Dj, _, _, actj, hDj, ⟨e⟩⟩ := GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit _ _ _ (GlobalTheory.FiniteTypeColimit.isColimit
    (CommRingCat.of (GenFib T O))) q hq D act hD
  let U := (GlobalTheory.FiniteTypeColimit.diagram (CommRingCat.of (GenFib T O))).obj j
  let u : U →+* GenFib T O := ((GlobalTheory.FiniteTypeColimit.inclusions (CommRingCat.of (GenFib T O))).app j).hom
  haveI : Algebra.FiniteType ℤ U := GlobalTheory.FiniteTypeColimit.finiteType _ j

  have hfact := GlobalTheory.T.exists_etale_factorization_of_isIndEtale (Polynomial T) O P φ hφ hind
  have hl := GlobalTheory.T.exists_etale_lift_genericFibre_of_factorization T (Polynomial T) O hfact U u
  obtain ⟨W, _, _, _, _, _, ψ, uW, hcomp⟩ := hl
  letI : Algebra U (GenFib T W) := uW.toAlgebra
  obtain ⟨actE, hE⟩ := GlobalTheory.T.torsor_base_change_zmod U (GenFib T W) q Dj actj hq hDj
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ψ,
    TensorProduct U (GenFib T W) Dj, inferInstance, inferInstance, actE, hE, ?_⟩
  intro s hs
  have hs' : s.comp (algebraMap (GenFib T W) (TensorProduct U (GenFib T W) Dj)) =
      genFibMap (ψ.restrictScalars T) := by
    refine genFib_ringHom_ext (fun w => ?_)
    rw [RingHom.comp_apply, hs, genFibMap_algebraMap]
    rfl
  letI : Algebra U (GenFib T O) := u.toAlgebra
  let σ : Dj →ₐ[U] GenFib T O :=
    { s.comp (Algebra.TensorProduct.includeRight (R := U) (A := GenFib T W) (B := Dj)).toRingHom with
      commutes' := fun x => by
        change s (Algebra.TensorProduct.includeRight (algebraMap U Dj x)) = u x
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply U (GenFib T W)]
        rw [← RingHom.comp_apply s, hs', ← hcomp]
        rfl }
  let L : TensorProduct U (GenFib T O) Dj →ₐ[GenFib T O] GenFib T O :=
    Algebra.TensorProduct.lift (AlgHom.id (GenFib T O) (GenFib T O)) σ
      (fun _ _ => Commute.all _ _)
  exact ⟨L.comp e.symm.toAlgHom⟩

end GlobalTheory.LocAcyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadTorsorToEtaleAlgebraStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spread_torsor_to_etale_algebra : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  first | (exact @GlobalTheory.LocAcyc.spread_torsor_to_etale) | (exact GlobalTheory.LocAcyc.spread_torsor_to_etale) | (intros; apply GlobalTheory.LocAcyc.spread_torsor_to_etale  <;> assumption)
end
