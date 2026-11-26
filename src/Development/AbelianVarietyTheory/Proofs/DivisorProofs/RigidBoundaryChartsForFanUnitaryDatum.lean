module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanOfUnitarySeparation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationExistsBoundaryIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatio

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreNormalProjectiveAmpleCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSubalgebraContainingFinsetCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSubalgebraContainingFinsetCharZero
open scoped TensorProduct

namespace GlobalTheory

theorem exists_smooth_subalgebra_of_finset : ∀ (F K : Type) [Field F] [CharZero F] [Field K]
    [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧
      Algebra.Smooth F R := by
  intro F K _ _ _ _ s
  haveI : PerfectField F := PerfectField.ofCharZero
  let C : Subalgebra F K := Algebra.adjoin F (↑s : Set K)
  haveI : Algebra.FiniteType F C :=
    ⟨(Subalgebra.fg_top C).mpr (Subalgebra.fg_adjoin_finset s)⟩
  obtain ⟨f, hf0, hsm, -⟩ := GlobalTheory.SS.exists_smooth_free_away F C C
  have hinjC : Function.Injective (algebraMap C K) := Subtype.val_injective
  have hfK : IsUnit (algebraMap C K f) := by
    refine isUnit_iff_ne_zero.mpr ?_
    intro h
    exact hf0 (hinjC (by simpa using h))
  let g : Localization.Away f →ₐ[F] K :=
    { IsLocalization.Away.lift f hfK with
      commutes' := fun r => by
        show IsLocalization.Away.lift f hfK (algebraMap F (Localization.Away f) r) = algebraMap F K r
        rw [IsScalarTower.algebraMap_apply F C (Localization.Away f),
          IsLocalization.Away.lift_eq]
        rfl }
  have hginj : Function.Injective g := by
    show Function.Injective (IsLocalization.Away.lift f hfK)
    rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      rw [IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0) h]
    · intro h
      have : x = y := hinjC h
      rw [this]
  refine ⟨g.range, ?_, ?_⟩
  · intro x hx
    refine ⟨algebraMap C (Localization.Away f) ⟨x, Algebra.subset_adjoin hx⟩, ?_⟩
    show IsLocalization.Away.lift f hfK _ = x
    rw [IsLocalization.Away.lift_eq]
    rfl
  · exact Algebra.Smooth.of_equiv (AlgEquiv.ofInjective g hginj)
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSubalgebraContainingFinsetCharZeroStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R := by
  first | exact @GlobalTheory.exists_smooth_subalgebra_of_finset | exact GlobalTheory.exists_smooth_subalgebra_of_finset | (intros; apply GlobalTheory.exists_smooth_subalgebra_of_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNormalSchemePullbackSpMapOfAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNormalSchemePullbackSpMapOfAlgebra
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.isNormalScheme_pullback_spMap_of_algebra
    (halg : ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A]
      [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧
        IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
        IsIntegrallyClosed (Localization.AtPrime Q))
    (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0})
    (g : Y ⟶ Sp F) (hY : GlobalTheory.IsNormalScheme Y) : GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by
  let 𝒰 := Y.affineOpenCover.openCover
  refine (GlobalTheory.IsNormalScheme.iff_of_openCover (Scheme.Pullback.openCoverOfLeft 𝒰 g (spMap c))).mpr ?_
  intro i
  change GlobalTheory.IsNormalScheme (pullback (𝒰.f i ≫ g) (spMap c))
  let R := Y.affineOpenCover.X i
  have hR : GlobalTheory.IsNormalScheme (Spec R) :=
    @GlobalTheory.IsNormalScheme.of_isOpenImmersion _ _ (𝒰.f i) (𝒰.map_prop i) hY
  let φ := Spec.preimage (𝒰.f i ≫ g)
  letI : Algebra F R := φ.hom.toAlgebra
  letI : Algebra F K := c.toAlgebra
  have e1 : 𝒰.f i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F R)) :=
    (Spec.map_preimage (𝒰.f i ≫ g)).symm
  have e2 : spMap c = Spec.map (CommRingCat.ofHom (algebraMap F K)) := rfl
  rw [e1, e2]
  refine (GlobalTheory.IsNormalScheme.iff_of_iso (pullbackSpecIso F R K)).mpr ?_
  refine (GlobalTheory.IsNormalScheme.spec_iff _).mpr ?_
  exact halg F K R ((GlobalTheory.IsNormalScheme.spec_iff R).mp hR)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNormalSchemePullbackSpMapOfAlgebraStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNormalScheme_pullback_spMap_of_isNormalScheme : (∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0}) (g : Y ⟶ Sp F), GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by
  first | exact @GlobalTheory.isNormalScheme_pullback_spMap_of_algebra | exact GlobalTheory.isNormalScheme_pullback_spMap_of_algebra | (intros; apply GlobalTheory.isNormalScheme_pullback_spMap_of_algebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
open scoped TensorProduct

namespace GlobalTheory

namespace LocalizationIntegrallyClosedDomain

variable {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]

lemma algebraMap_eq_zero_of_sub (C : Subring B) (c : C)
    (h : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) c = 0) :
    algebraMap B (Localization.AtPrime Q) (c : B) = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Q.comap C.subtype).primeCompl] at h
  obtain ⟨⟨m, hm⟩, hmc⟩ := h
  rw [IsLocalization.map_eq_zero_iff Q.primeCompl]
  refine ⟨⟨(m : B), by exact hm⟩, ?_⟩
  simpa using congrArg Subtype.val hmc

lemma algebraMap_eq_zero_of_witness (C : Subring B) (u e : C) (hu : (u : B) ∉ Q)
    (h : u * e = 0) :
    algebraMap C (Localization.AtPrime (Q.comap C.subtype)) e = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Q.comap C.subtype).primeCompl]
  exact ⟨⟨u, by exact hu⟩, h⟩

variable {Q}

lemma noZeroDivisors
    (H : ∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
      ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧
        IsIntegrallyClosed (Localization.AtPrime q)) :
    NoZeroDivisors (Localization.AtPrime Q) := by
  classical
  refine ⟨fun {x y} hxy => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hxy
  obtain ⟨u, hu⟩ := hxy
  obtain ⟨C, hC, hCq⟩ := H {a, c, (u : B)}
  have ha : a ∈ C := hC (by simp)
  have hc : c ∈ C := hC (by simp)
  have hu' : (u : B) ∈ C := hC (by simp)
  haveI := (hCq (Q.comap C.subtype)).1
  have h0 : algebraMap C (Localization.AtPrime (Q.comap C.subtype))
      ((⟨a, ha⟩ : C) * ⟨c, hc⟩) = 0 :=
    algebraMap_eq_zero_of_witness Q C ⟨u, hu'⟩ _ u.2 (Subtype.ext (by simpa using hu))
  rw [map_mul] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · left
    have h1 := algebraMap_eq_zero_of_sub Q C _ h
    rw [IsLocalization.map_eq_zero_iff Q.primeCompl] at h1
    rw [IsLocalization.mk'_eq_zero_iff]
    exact h1
  · right
    have h1 := algebraMap_eq_zero_of_sub Q C _ h
    rw [IsLocalization.map_eq_zero_iff Q.primeCompl] at h1
    rw [IsLocalization.mk'_eq_zero_iff]
    exact h1

end LocalizationIntegrallyClosedDomain

end GlobalTheory

namespace GlobalTheory

namespace LocalizationIntegrallyClosedDomain

variable {B : Type} [CommRing B] {Q : Ideal B} [Q.IsPrime]


set_option maxHeartbeats 1600000 in
lemma isIntegrallyClosed
    (H : ∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
      ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧
        IsIntegrallyClosed (Localization.AtPrime q))
    [IsDomain (Localization.AtPrime Q)] :
    IsIntegrallyClosed (Localization.AtPrime Q) := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing (Localization.AtPrime Q))]
  intro z hz
  have hf : ∀ x ∈ Q.primeCompl, algebraMap B (FractionRing (Localization.AtPrime Q)) x ≠ 0 := by
    intro x hx
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q))]
    exact ((IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hx⟩ : Q.primeCompl)).map (algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)))).ne_zero
  have key : ∀ (b : B) (v : Q.primeCompl),
      algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) b v) * algebraMap B (FractionRing (Localization.AtPrime Q)) v = algebraMap B (FractionRing (Localization.AtPrime Q)) b := by
    intro b v
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) v, IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) b, ← map_mul,
      IsLocalization.mk'_spec]

  obtain ⟨D, A0, hD, hDz⟩ : ∃ D A0 : B, algebraMap B (FractionRing (Localization.AtPrime Q)) D ≠ 0 ∧
      algebraMap B (FractionRing (Localization.AtPrime Q)) D * z = algebraMap B (FractionRing (Localization.AtPrime Q)) A0 := by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := (Localization.AtPrime Q)) z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
    have hyK : algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) c t) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    have hcK : algebraMap B (FractionRing (Localization.AtPrime Q)) c ≠ 0 := by
      intro h0
      apply hyK
      have h1 := key c t
      rw [h0] at h1
      exact (mul_eq_zero.mp h1).resolve_right (hf _ t.2)
    refine ⟨c * s, a * t, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hcK (hf _ s.2)
    · have k1 := key a s
      have k2 := key c t
      rw [map_mul, map_mul, ← k1, ← k2]
      field_simp
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization Q.primeCompl z hz
  obtain ⟨p, hpm, hp⟩ := hm
  set A : B := (m : B) * A0 with hA
  have hDA : algebraMap B (FractionRing (Localization.AtPrime Q)) D * (m • z) = algebraMap B (FractionRing (Localization.AtPrime Q)) A := by
    rw [Submonoid.smul_def, Algebra.smul_def, hA, map_mul, ← hDz]; ring
  have hE : algebraMap B (Localization.AtPrime Q) (p.scaleRoots D |>.eval A) = 0 := by
    have h1 := Polynomial.scaleRoots_eval₂_mul (p := p) (algebraMap B (FractionRing (Localization.AtPrime Q))) (m • z) D
    rw [hp, mul_zero, hDA, Polynomial.eval₂_at_apply, IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q))] at h1
    exact (map_eq_zero_iff _ (IsFractionRing.injective (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)))).mp h1
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl (Localization.AtPrime Q) _).mp hE
  obtain ⟨C, hC, hCq⟩ := H (insert A (insert D (insert (u : B) p.coeffs)))
  have hAC : A ∈ C := hC (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hDC : D ∈ C := hC (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have huC : (u : B) ∈ C := hC (Finset.mem_coe.mpr
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
  have hcoef : (↑p.coeffs : Set B) ⊆ (C : Set B) := fun x hx => hC (Finset.mem_coe.mpr
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))))
  set p' := p.toSubring C hcoef with hp'
  have hp'm : p'.Monic := (Polynomial.monic_toSubring p C hcoef).mpr hpm
  set A' : C := ⟨A, hAC⟩
  set D' : C := ⟨D, hDC⟩
  set u' : C := ⟨u, huC⟩
  haveI : Nontrivial B := (algebraMap B (Localization.AtPrime Q)).domain_nontrivial
  have hlc : C.subtype p'.leadingCoeff ≠ 0 := by
    rw [hp'm.leadingCoeff, map_one]; exact one_ne_zero
  have hsub : C.subtype ((p'.scaleRoots D').eval A') = (p.scaleRoots D).eval A := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, Polynomial.map_scaleRoots _ _ _ hlc,
      Polynomial.map_toSubring]
    rfl
  have hE' : u' * (p'.scaleRoots D').eval A' = 0 := by
    apply Subtype.ext
    have : (u : B) * C.subtype ((p'.scaleRoots D').eval A') = 0 := by rw [hsub]; exact hu
    simpa using this
  haveI := (hCq (Q.comap C.subtype)).1
  haveI := (hCq (Q.comap C.subtype)).2
  have hgE : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) ((p'.scaleRoots D').eval A') = 0 :=
    algebraMap_eq_zero_of_witness Q C u' _ u.2 hE'
  have hgD : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D' ≠ 0 := by
    intro h0
    have h1 : algebraMap B (Localization.AtPrime Q) D = 0 := algebraMap_eq_zero_of_sub Q C D' h0
    apply hD
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)), h1, map_zero]
  have hhD : algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))))).mpr hgD
  set x : (FractionRing (Localization.AtPrime (Q.comap C.subtype))) := algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A') / algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') with hx
  have hxD : algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') * x = algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A') := by
    rw [hx]; field_simp
  have hlc2 : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) p'.leadingCoeff ≠ 0 := by
    rw [hp'm.leadingCoeff, map_one]; exact one_ne_zero
  have hxint : IsIntegral (Localization.AtPrime (Q.comap C.subtype)) x := by
    refine ⟨p'.map (algebraMap C (Localization.AtPrime (Q.comap C.subtype))), hp'm.map _, ?_⟩
    have h2 := Polynomial.scaleRoots_eval₂_mul (p := p'.map (algebraMap C (Localization.AtPrime (Q.comap C.subtype)))) (algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype)))) x
      (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D')
    rw [hxD, ← Polynomial.map_scaleRoots _ _ _ hlc2, Polynomial.eval₂_at_apply, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hgE, map_zero] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hhD)
  obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Localization.AtPrime (Q.comap C.subtype)) (K := FractionRing (Localization.AtPrime (Q.comap C.subtype)))).mp hxint
  have hwD : w * algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D' = algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A' := by
    apply IsFractionRing.injective (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype)))
    rw [map_mul, hw, mul_comm, hxD]
  obtain ⟨⟨e, v⟩, rfl⟩ := IsLocalization.mk'_surjective (Q.comap C.subtype).primeCompl w
  have hev : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) (e * D') = algebraMap C (Localization.AtPrime (Q.comap C.subtype)) (A' * v) := by
    rw [map_mul, map_mul, ← hwD, ← IsLocalization.mk'_spec (Localization.AtPrime (Q.comap C.subtype)) e v]; ring
  obtain ⟨n, hn⟩ := (IsLocalization.eq_iff_exists (Q.comap C.subtype).primeCompl (Localization.AtPrime (Q.comap C.subtype))).mp hev
  have hnB : ((n : C) : B) * ((e : B) * D) = ((n : C) : B) * (A * ((v : C) : B)) := by
    simpa using congrArg Subtype.val hn
  have hK := congrArg (algebraMap B (FractionRing (Localization.AtPrime Q))) hnB
  simp only [map_mul, hA] at hK
  have hfn : algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) ≠ 0 := hf _ (by exact n.2)
  have hfv : algebraMap B (FractionRing (Localization.AtPrime Q)) ((v : C) : B) ≠ 0 := hf _ (by exact v.2)
  have hfm : algebraMap B (FractionRing (Localization.AtPrime Q)) (m : B) ≠ 0 := hf _ m.2
  let v'' : Q.primeCompl := ⟨((v : C) : B), by exact v.2⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime Q) (e : B) (m * v''), ?_⟩
  have key2 := key (e : B) (m * v'')
  simp only [Submonoid.coe_mul, map_mul] at key2
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hfn hD) (mul_ne_zero hfm hfv))
  linear_combination (algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) D) * key2
    - (algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) (m : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) ((v : C) : B)) * hDz + hK

end LocalizationIntegrallyClosedDomain

theorem localization_isDomain_isIntegrallyClosed_of_finset_subring :
    ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro B _ Q _ H
  haveI : NoZeroDivisors (Localization.AtPrime Q) := LocalizationIntegrallyClosedDomain.noZeroDivisors H
  haveI : IsDomain (Localization.AtPrime Q) := NoZeroDivisors.to_isDomain _
  exact ⟨inferInstance, LocalizationIntegrallyClosedDomain.isIntegrallyClosed H⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIsDomainIsIntegrallyClosedOfFinsetSuStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | exact GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | (intros; apply GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA
open scoped TensorProduct

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv {D C : Type*} [CommRing D]
    [CommRing C] (e : D ≃+* C)
    (h : ∀ (q : Ideal D) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (q : Ideal C) [hq : q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let q' : Ideal D := q.comap (e : D →+* C)
  haveI : q'.IsPrime := Ideal.comap_isPrime _ _
  have H : q'.primeCompl.map e.toMonoidHom = q.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe, q', Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by simpa using hx, by simp⟩
  let f : Localization.AtPrime q' ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q') (Localization.AtPrime q) e H
  obtain ⟨h1, h2⟩ := h q'
  exact ⟨f.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv f⟩

end GlobalTheory

namespace GlobalTheory


open Algebra.TensorProduct in
theorem exists_finset_mem_range_map_val {F A K : Type*} [Field F] [CommRing A] [Algebra F A]
    [Field K] [Algebra F K] (x : A ⊗[F] K) :
    ∃ T : Finset K, ∀ R : Subalgebra F K, (↑T : Set K) ⊆ (R : Set K) →
      x ∈ (Algebra.TensorProduct.map (AlgHom.id F A) R.val).range := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun R _ ↦ Subalgebra.zero_mem _⟩
  | tmul a k =>
    refine ⟨{k}, fun R hR ↦ ⟨a ⊗ₜ ⟨k, hR (by simp)⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨T₁, h₁⟩ := hx
    obtain ⟨T₂, h₂⟩ := hy
    refine ⟨T₁ ∪ T₂, fun R hR ↦ Subalgebra.add_mem _ (h₁ R ?_) (h₂ R ?_)⟩
    · exact fun z hz ↦ hR (by simp [hz])
    · exact fun z hz ↦ hR (by simp [hz])

theorem isDomain_and_isIntegrallyClosed_atPrime_tensor_field
    (hL1 : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K),
      ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R)
    (hL2 : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime],
      (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
        ∀ (q : Ideal C) [q.IsPrime],
          IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) →
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) :
    ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A],
      (∀ (P : Ideal A) [P.IsPrime],
        IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime],
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro F K A _ _ _ _ _ _ hA Q _
  classical
  refine hL2 (TensorProduct F A K) Q fun s ↦ ?_
  choose T hT using fun x : A ⊗[F] K ↦ exists_finset_mem_range_map_val (F := F) x
  obtain ⟨R, hR, hsm⟩ := hL1 F K (s.biUnion T)
  let φ : A ⊗[F] R →ₐ[F] A ⊗[F] K := Algebra.TensorProduct.map (AlgHom.id F A) R.val
  have hφ : ⇑φ = ⇑(LinearMap.lTensor A (R.val.toLinearMap)) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a k => simp [φ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hinj : Function.Injective φ := by
    rw [hφ]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  refine ⟨φ.range.toSubring, fun x hx ↦ hT x R (fun z hz ↦ hR ?_), ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨x, hx, hz⟩
  · let e : A ⊗[F] R ≃+* φ.range.toSubring := (AlgEquiv.ofInjective φ hinj).toRingEquiv
    exact isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv e fun q _ ↦
      isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_forall A hA q _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldAStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt : (∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R) → (∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field | exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field | (intros; apply GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreNormalProjectiveAmpleCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.GenFibNormal

theorem genFibre_of_fieldChange (hd2 : ∀ (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0}) (g : Y ⟶ Sp F), GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme (pullback g (spMap c))) : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) := by
  intro o K _ _ _ _ b hb Z z L hP hN hL hA
  haveI hsa : IsAffineHom (spMap b) := inferInstance
  haveI : IsAffineHom (pullback.fst z (spMap b)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback z (spMap b)).flip hsa
  refine ⟨ProjSpace.isProjOver_pullback_snd b hP, ?_, LB.isLB_pull hL _, IsAmpleLB.pull_of_isAffineHom hA _⟩
  haveI : CharZero o := ⟨fun m n h => by
    have := congrArg b h; simp only [map_natCast] at this; exact_mod_cast this⟩
  let F := FractionRing o
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective o F)
  let b' : F →+* K := IsFractionRing.lift hb
  have hbb : b'.comp (algebraMap o F) = b := RingHom.ext fun x => IsFractionRing.lift_algebraMap hb x
  have hZF : GlobalTheory.IsNormalScheme (pullback z (spMap (algebraMap o F))) :=
    IsNormalScheme.of_pred (FlagCls.isNormalScheme_of_isPullback_fractionField o F Z _ z
      (pullback.fst z (spMap (algebraMap o F))) (pullback.snd z (spMap (algebraMap o F)))
      (IsPullback.of_hasPullback _ _) ((isNormalScheme_iff_pred Z).mp hN))
  have h1 := hd2 F K b' _ (pullback.snd z (spMap (algebraMap o F))) hZF
  have e := pullbackLeftPullbackSndIso z (spMap (algebraMap o F)) (spMap b')
  have hc : spMap b' ≫ spMap (algebraMap o F) = spMap b := by
    rw [← hbb]
    simp only [spMap, ← Spec.map_comp]
    rfl
  exact (IsNormalScheme.iff_of_iso (e ≪≫ pullback.congrHom rfl hc)).mp h1

theorem genericFibre_normal_projective_ample : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) :=
  genFibre_of_fieldChange (GlobalTheory.T.isNormalScheme_pullback_spMap_of_isNormalScheme (GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings))

end GlobalTheory.GenFibNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreNormalProjectiveAmpleCharZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_normal_projective_ample_charZero : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) := by
  first | exact @GlobalTheory.GenFibNormal.genericFibre_normal_projective_ample | exact GlobalTheory.GenFibNormal.genericFibre_normal_projective_ample | (intros; apply GlobalTheory.GenFibNormal.genericFibre_normal_projective_ample <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.NormBlowupField

theorem exists_normBl : ∀ (K : Type) [Field K] [CharZero K] (Z : Scheme.{0}) (z : Z ⟶ Sp K),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens),
    Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z)
    (BD : EffCartierData S), GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ IsProper π ∧
    BD.idealSheaf = J.comap π ∧ IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  intro K _ _ Z z hz hZ J W hWd hWJ
  obtain ⟨X', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  haveI : LocallyOfFiniteType (b ≫ z) := by
    obtain ⟨m, i, hi, e⟩ := hbs
    have := isProper_str K m
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)
  let V : X'.Opens := b ⁻¹ᵁ W
  haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx
  haveI hoi : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)
  haveI : IsReduced V.toScheme := by
    exact inferInstance
  haveI hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_of_genericPoints (o := CommRingCat.of K) V.ι (b ≫ z)
      (fun x _ => charZero_of_injective_ringHom (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (V.ι ≫ b ≫ z).appTop ≫ V.toScheme.presheaf.germ ⊤ x trivial ≫ V.toScheme.residue x).hom)
        (RingHom.injective _))
      fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap
  let ν := V.ι.fromNormalization
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization := IsNormalScheme.pred _
  have hν : IsIso (ν ∣_ V) := by
    have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  have hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization) := by
    refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2
  have hVd : Dense (V : Set X') := GlobalTheory.NormBlowupInt.dense_preimage_of_blowup J b hb hiso W hWd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)
    show ν t ∉ D.idealSheaf.support
    rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
    exact fun h => hWJ _ h ht
  have hproj : IsProjOver ((ν ≫ b) ≫ z) := by
    rw [Category.assoc]; exact isProjOver_comp_of_isFinite ν hbs
  have hprop : IsProper (ν ≫ b) := by
    haveI : IsProper z := by
      obtain ⟨m, i, hi, e⟩ := hz
      have := isProper_str K m
      rw [← e]; infer_instance
    haveI : IsProper ((ν ≫ b) ≫ z) := by
      obtain ⟨m, i, hi, e⟩ := hproj
      have := isProper_str K m
      rw [← e]; infer_instance
    exact IsProper.of_comp (ν ≫ b) z
  refine ⟨V.ι.normalization, ν ≫ b, D.pull ν hK,
    ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, hproj, hprop, ?_, ?_, ?_⟩
  · rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]
  · rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbW
  · convert hd using 1
    ext t
    simp [V]

end GlobalTheory.NormBlowupField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoincTop

theorem uPoinStX_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
    ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
      (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S)
      (BD : EffCartierData S), UPoinOnX Xo c φ zs i OZ N d J π j BD ∧ GlobalTheory.UChart.SepB Xo c φ j := by
  intro E _ _ _ H Dw hpq φ hφ hns l Xo c
  obtain ⟨C⟩ := GlobalTheory.T.unitary_integral_compactifications_exist E H Dw hpq l Xo c
  obtain ⟨d, J₀, hd, hJ₀, hval₀⟩ := GlobalTheory.T.unitaryCompactification_exists_boundary_ideal E H Dw hpq φ hφ l Xo c C
  haveI := C.ded
  haveI := C.iF_open
  have hgen := GlobalTheory.T.generic_fibre_normal_projective_ample_charZero C.o c.F C.b C.inj C.Z C.z C.OZ C.proj C.normal C.OZ_lb C.OZ_ample
  obtain ⟨hprojZ, hnormZ, hOZlb, hOZamp⟩ := hgen
  let Z := pullback C.z (spMap C.b)
  let fZ : Z ⟶ C.Z := pullback.fst C.z (spMap C.b)
  let J : Z.IdealSheafData := J₀.comap fZ
  let W : Z.Opens := C.iF.opensRange
  have hWset : (W : Set Z) = Set.range C.iF := by simp [W]
  have hJ : ∀ x ∈ J.support, x ∉ Set.range C.iF := by
    intro x hx hxr
    rw [Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨y, rfl⟩ := hxr
    exact hJ₀ _ hx ⟨y, rfl⟩
  have hval : UValOn Xo c C.iF φ J d := by
    intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval₀ W' hW ϖ hϖ (χ ≫ fZ) y
      (by rw [UCompact.i, ← Category.assoc, hy, Category.assoc]) t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  obtain ⟨S, π, BD, hbl, hpS, hprop, hBD, hiso, hdS⟩ :=
    GlobalTheory.NormBlowupField.exists_normBl c.F Z (pullback.snd C.z (spMap C.b)) hprojZ hnormZ J W (by rw [hWset]; exact C.iF_dense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : Xo.XF c ⟶ (π ⁻¹ᵁ W).toScheme := C.iF.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : Xo.XF c ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = C.iF := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range C.iF := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  have hjo : IsOpenImmersion j := inferInstance
  refine ⟨Z, pullback.snd C.z (spMap C.b), C.iF, C.OZ.pull fZ, C.N, d, J, S, π, j, BD, ⟨⟨hprojZ, hnormZ, C.iF_open,
    C.iF_dense, C.iF_over, hOZlb, hOZamp⟩, ⟨C.N_pos, ?_⟩, ?_, ⟨hd, hJ, hval⟩, ⟨hbl, hpS, hjo, ?_, hjπ, hrj.symm, hBD, ?_⟩, ?_⟩, ?_⟩
  · intro Y f hf hY
    have h := C.omega Y f hf hY
    exact LBIso.trans (pull_isLB hOZlb f) (pull_isLB C.OZ_lb _) (LB.isLB_linComb hY _ _)
      (LBIso.symm (GlobalTheory.FibreNef.lbIso_pull_comp C.OZ_lb fZ f)) h
  · intro R _ _ _ hR t hP y hy σ hσ
    obtain ⟨ξ₀, h₁, h₂⟩ := C.ext R hR t hP y hy (σ ≫ spMap C.b) (by rw [← Category.assoc, hσ, Category.assoc])
    refine ⟨pullback.lift ξ₀ σ (by rw [h₂]), ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact h₁
    · simp only [Category.assoc, pullback.lift_snd, C.iF_over]; exact hσ
  · rw [hrj, ← hWset]; exact hdS
  · intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval W' hW ϖ hϖ (χ ≫ π) y (by rw [← Category.assoc, ← hy, Category.assoc, hjπ])
      t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    obtain ⟨T₀, hT⟩ := GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup c.F Z S₀ S (pullback.snd C.z (spMap C.b)) J π₀ ν BD hprojZ hb hfin
      (by rw [hνπ]; exact hBD) (C.OZ.pull fZ) hOZamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h
  · exact GlobalTheory.T.separation_normalizedBlowup_unitaryCompactification E H Dw hpq φ hφ hns l Xo c C d J₀ hd hJ₀ hval₀ S π j hbl hprop hjπ hjo hrj.symm

theorem uStB : GlobalTheory.UChart.UStB := uPoinStX_sep

end GlobalTheory.UPoincTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBaseStatement
open GlobalTheory.UChart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToroidalSeparation_of_base : UStB := by
  first | exact @GlobalTheory.UPoincTop.uStB | exact GlobalTheory.UPoincTop.uStB | (intros; apply GlobalTheory.UPoincTop.uStB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanUnitaryDatum
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigChart

theorem rigidForFan_holds : GlobalTheory.RigChart.RigidForFan :=
  GlobalTheory.T.rigidBoundaryChartsForFan_of_unitarySeparation GlobalTheory.T.unitaryToroidalSeparation_of_base

end GlobalTheory.RigChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanUnitaryDatumStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidBoundaryChartsForFan_unitaryDatum : GlobalTheory.RigChart.RigidForFan := by
  first | exact @GlobalTheory.RigChart.rigidForFan_holds | exact GlobalTheory.RigChart.rigidForFan_holds | (intros; apply GlobalTheory.RigChart.rigidForFan_holds <;> assumption)
end
