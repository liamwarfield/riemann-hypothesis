module

public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

@[expose] public section

section -- merged from ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyMax
namespace ReciprocityTheory.CA

open Polynomial IsLocalRing

variable {P : Type*} [CommRing P] [IsLocalRing P]

theorem isIntegral_quotient_of_isMaximal_of_comap_eq {S : Type*} [CommRing S] [Algebra P S]
    [Algebra.FiniteType P S] (𝔑 : Ideal S) [𝔑.IsMaximal]
    (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) : Algebra.IsIntegral P (S ⧸ 𝔑) := by
  classical
  letI : Field (P ⧸ maximalIdeal P) := Ideal.Quotient.field _
  letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _
  letI : Algebra (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    (Ideal.quotientMap 𝔑 (algebraMap P S) h.ge).toAlgebra
  haveI : IsScalarTower P (P ⧸ maximalIdeal P) (S ⧸ 𝔑) := by
    first
    | exact IsScalarTower.of_algebraMap_eq (fun p => rfl)
    | exact IsScalarTower.of_algebraMap_eq (fun p => by simp [Ideal.quotientMap_mk])
  haveI : Algebra.FiniteType P (S ⧸ 𝔑) := by
    first
    | infer_instance
    | exact Algebra.FiniteType.of_surjective inferInstance (Ideal.Quotient.mkₐ P 𝔑)
        (Ideal.Quotient.mkₐ_surjective P 𝔑)
  haveI : Algebra.FiniteType (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    Algebra.FiniteType.of_restrictScalars_finiteType P _ _
  haveI : Module.Finite (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  haveI : Algebra.IsIntegral P (P ⧸ maximalIdeal P) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ P (maximalIdeal P))
        (Ideal.Quotient.mkₐ_surjective P _)
  exact Algebra.IsIntegral.trans (P ⧸ maximalIdeal P)

theorem isMaximal_comap_of_isMaximal_of_comap_eq {S' S : Type*} [CommRing S'] [CommRing S]
    [Algebra P S'] [Algebra P S] [Algebra S' S] [IsScalarTower P S' S] [Algebra.FiniteType P S]
    (𝔑 : Ideal S) [𝔑.IsMaximal] (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) :
    (𝔑.comap (algebraMap S' S)).IsMaximal := by
  haveI := isIntegral_quotient_of_isMaximal_of_comap_eq 𝔑 h
  haveI : Algebra.IsIntegral S' (S ⧸ 𝔑) := by
    first
    | exact Algebra.IsIntegral.tower_top P
    | exact Algebra.IsIntegral.tower_top (R := P)
  letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _
  have hbot := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := S') (⊥ : Ideal (S ⧸ 𝔑))
  have heq : (⊥ : Ideal (S ⧸ 𝔑)).comap (algebraMap S' (S ⧸ 𝔑)) = 𝔑.comap (algebraMap S' S) := by
    ext y
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap]
    first
    | exact Ideal.Quotient.eq_zero_iff_mem
    | (rw [IsScalarTower.algebraMap_apply S' S (S ⧸ 𝔑), Ideal.Quotient.algebraMap_eq]
       exact Ideal.Quotient.eq_zero_iff_mem)
  rw [← heq]
  exact hbot

theorem exists_monic_aeval_mem_of_isMaximal {S : Type*} [CommRing S] [Algebra P S]
    [Algebra.FiniteType P S] (𝔑 : Ideal S) [𝔑.IsMaximal]
    (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) (x : S) :
    ∃ g : P[X], g.Monic ∧ aeval x g ∈ 𝔑 := by
  haveI := isIntegral_quotient_of_isMaximal_of_comap_eq 𝔑 h
  obtain ⟨g, hg, hgx⟩ := Algebra.IsIntegral.isIntegral (R := P) (Ideal.Quotient.mk 𝔑 x)
  refine ⟨g, hg, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have key : Ideal.Quotient.mk 𝔑 (aeval x g) = aeval (Ideal.Quotient.mk 𝔑 x) g := by
    first
    | exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ P 𝔑) x g).symm
    | simpa using (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ P 𝔑) x g).symm
  rw [key, Polynomial.aeval_def]
  exact hgx

end ReciprocityTheory.CA
end

section -- merged from ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyStep
namespace ReciprocityTheory.CA

open Polynomial RingTheory.Sequence

theorem pstep_monic_mem_of_mul {S : Type*} [CommRing S] (J : Ideal S) {g h : S[X]} (hg : g.Monic)
    (hgh : g * h ∈ J.map (C : S →+* S[X])) : h ∈ J.map (C : S →+* S[X]) := by

  have hk : RingHom.ker (mapRingHom (Ideal.Quotient.mk J)) = J.map (C : S →+* S[X]) := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  rw [← hk, RingHom.mem_ker] at hgh ⊢
  simp only [map_mul, coe_mapRingHom] at hgh
  rw [coe_mapRingHom]
  exact ((hg.map (Ideal.Quotient.mk J)).mul_right_eq_zero_iff).mp hgh

theorem isWeaklyRegular_map_C_append_monic {S : Type*} [CommRing S] {rs : List S}
    (hrs : IsWeaklyRegular S rs) {g : S[X]} (hg : g.Monic) :
    IsWeaklyRegular S[X] (rs.map C ++ [g]) := by
  rw [isWeaklyRegular_append_iff]
  refine ⟨?_, ?_⟩
  · have h := hrs.of_flat (S := S[X])
    rwa [Polynomial.algebraMap_eq] at h
  · rw [isWeaklyRegular_singleton_iff]
    have hI : (Ideal.ofList (rs.map C) • ⊤ : Submodule S[X] S[X]) =
        (Ideal.ofList rs).map (C : S →+* S[X]) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_ofList]
    intro a b hab
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    change g • Submodule.Quotient.mk a = g • Submodule.Quotient.mk b at hab
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hI] at hab
    rw [smul_eq_mul, smul_eq_mul, ← mul_sub] at hab
    rw [Submodule.Quotient.eq, hI]
    exact pstep_monic_mem_of_mul _ hg hab

theorem isWeaklyRegular_map_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T)
    {rs : List S} (hrs : IsWeaklyRegular S rs) : IsWeaklyRegular T (rs.map e) := by
  letI : Algebra S T := e.toRingHom.toAlgebra

  let l : T ≃ₗ[S] S :=
    { e.symm.toAddEquiv with
      map_smul' := fun c t => by
        change e.symm (algebraMap S T c * t) = c * e.symm t
        rw [RingHom.algebraMap_toAlgebra, map_mul]
        simp }
  haveI : Module.Flat S T := Module.Flat.of_linearEquiv l
  exact hrs.of_flat

end ReciprocityTheory.CA
end

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

theorem exists_isWeaklyRegular_mvPolynomial {P : Type*} [CommRing P] [IsLocalRing P] {rs : List P}
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal P) (hrs : IsWeaklyRegular P rs) (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) P)) [𝔑.IsMaximal]
    (h : 𝔑.comap MvPolynomial.C = maximalIdeal P) :
    ∃ ss : List (MvPolynomial (Fin N) P), ss.length = rs.length + N ∧ (∀ s ∈ ss, s ∈ 𝔑) ∧
      IsWeaklyRegular (MvPolynomial (Fin N) P) ss := by
  induction N with
  | zero =>
    let e : P ≃ₐ[P] MvPolynomial (Fin 0) P := (MvPolynomial.isEmptyAlgEquiv P (Fin 0)).symm
    have he : ∀ r, e r = MvPolynomial.C r := fun r => by simpa using e.commutes r
    refine ⟨rs.map MvPolynomial.C, by simp, ?_, ?_⟩
    · intro s hs
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
      have hr' : r ∈ 𝔑.comap MvPolynomial.C := h.symm ▸ hmem r hr
      exact Ideal.mem_comap.1 hr'
    · have hmap : rs.map (e.toRingEquiv : P → MvPolynomial (Fin 0) P) = rs.map MvPolynomial.C :=
        List.map_congr_left fun r _ => he r
      have := isWeaklyRegular_map_ringEquiv e.toRingEquiv hrs
      rw [hmap] at this
      exact this
  | succ N ih =>
    let e : MvPolynomial (Fin (N + 1)) P ≃ₐ[P] Polynomial (MvPolynomial (Fin N) P) :=
      MvPolynomial.finSuccEquiv P N
    haveI : Algebra.FiniteType P (Polynomial (MvPolynomial (Fin N) P)) :=
      Algebra.FiniteType.trans (S := MvPolynomial (Fin N) P) inferInstance inferInstance
    let 𝔑' : Ideal (Polynomial (MvPolynomial (Fin N) P)) := 𝔑.map e.toRingEquiv
    haveI : 𝔑'.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    have hc' : 𝔑'.comap (algebraMap P (Polynomial (MvPolynomial (Fin N) P))) = maximalIdeal P := by
      have hA : algebraMap P (Polynomial (MvPolynomial (Fin N) P)) =
          (e.toRingEquiv : MvPolynomial (Fin (N + 1)) P →+* Polynomial (MvPolynomial (Fin N) P)).comp
            (algebraMap P (MvPolynomial (Fin (N + 1)) P)) :=
        RingHom.ext fun r => (e.commutes r).symm
      rw [hA, ← Ideal.comap_comap]
      show Ideal.comap _ (Ideal.comap (e.toRingEquiv : MvPolynomial (Fin (N + 1)) P →+* Polynomial (MvPolynomial (Fin N) P))
        (Ideal.map e.toRingEquiv 𝔑)) = _
      rw [Ideal.comap_coe, Ideal.comap_map_of_bijective _ e.toRingEquiv.bijective]
      exact h
    let 𝔐 : Ideal (MvPolynomial (Fin N) P) := 𝔑'.comap (algebraMap (MvPolynomial (Fin N) P) (Polynomial (MvPolynomial (Fin N) P)))
    haveI : 𝔐.IsMaximal := isMaximal_comap_of_isMaximal_of_comap_eq (S' := MvPolynomial (Fin N) P) 𝔑' hc'
    have hc'' : 𝔐.comap MvPolynomial.C = maximalIdeal P := by
      show (𝔑'.comap (algebraMap (MvPolynomial (Fin N) P) (Polynomial (MvPolynomial (Fin N) P)))).comap
        (algebraMap P (MvPolynomial (Fin N) P)) = maximalIdeal P
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hc'
    obtain ⟨ss', hlen, hmem', hreg'⟩ := ih 𝔐 hc''
    obtain ⟨g, hg, hgN⟩ := exists_monic_aeval_mem_of_isMaximal 𝔑' hc' (Polynomial.X)
    rw [Polynomial.aeval_X_left_eq_map] at hgN
    have hgm : (g.map (algebraMap P (MvPolynomial (Fin N) P))).Monic := hg.map _
    have hreg := isWeaklyRegular_map_C_append_monic hreg' hgm
    refine ⟨(ss'.map Polynomial.C ++ [g.map (algebraMap P (MvPolynomial (Fin N) P))]).map e.symm.toRingEquiv,
      ?_, ?_, isWeaklyRegular_map_ringEquiv e.symm.toRingEquiv hreg⟩
    · simp [hlen]
      omega
    · intro s hs
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
      have hy' : y ∈ 𝔑' := by
        rcases List.mem_append.1 hy with h1 | h1
        · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 h1
          exact Ideal.mem_comap.1 (hmem' s' hs')
        · rw [List.mem_singleton] at h1
          rw [h1]
          exact hgN
      obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv e.toRingEquiv y).1 hy'
      simpa using hx

end ReciprocityTheory.CA
