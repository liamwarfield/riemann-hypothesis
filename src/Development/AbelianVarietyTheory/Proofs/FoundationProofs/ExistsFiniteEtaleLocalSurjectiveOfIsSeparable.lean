module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
namespace GlobalTheory

open Polynomial IsLocalRing

private lemma mem_smul_top_iff_of_linearEquiv_pi {V M ι : Type*} [CommRing V] [AddCommGroup M]
    [Module V M] [Fintype ι] [DecidableEq ι] (e : M ≃ₗ[V] (ι → V)) (J : Ideal V) (x : M) :
    x ∈ J • (⊤ : Submodule V M) ↔ ∀ i, e x i ∈ J := by
  constructor
  · intro hx
    have hle : J • (⊤ : Submodule V M) ≤
        (Submodule.pi Set.univ (fun _ : ι => J)).comap e.toLinearMap := by
      refine Submodule.smul_le.mpr fun r hr m _ => ?_
      simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact fun i => J.mul_mem_right _ hr
    intro i
    have := hle hx
    simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearEquiv.coe_coe] at this
    exact this i
  · intro hx
    have hsum : x = ∑ i, e x i • e.symm (fun j => if i = j then 1 else 0) := by
      apply e.injective
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
      exact pi_eq_sum_univ (e x)
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private lemma ideal_smul_top_eq_self {V : Type*} [CommRing V] (J : Ideal V) :
    J • (⊤ : Submodule V V) = J := by
  rw [smul_eq_mul, Ideal.mul_top]

private lemma isAdicComplete_of_linearEquiv_pi {V M ι : Type*} [CommRing V] [AddCommGroup M]
    [Module V M] [Fintype ι] (e : M ≃ₗ[V] (ι → V)) (J : Ideal V) [IsAdicComplete J V] :
    IsAdicComplete J M := by
  classical
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD J ^ n • (⊤ : Submodule V M)] ↔
      ∀ i, e x i ≡ e y i [SMOD J ^ n • (⊤ : Submodule V V)] := by
    intro n x y
    simp only [SModEq.sub_mem, mem_smul_top_iff_of_linearEquiv_pi e, map_sub, Pi.sub_apply,
      ideal_smul_top_eq_self]
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · apply e.injective
    funext i
    rw [map_zero]
    exact IsHausdorff.haus' (I := J) (e x i) fun n => by
      simpa using (key n x 0).1 (hx n) i
  · choose L hL using fun i => IsPrecomplete.prec' (I := J) (fun n => e (f n) i)
      (fun {m n} hmn => (key m _ _).1 (hf hmn) i)
    refine ⟨e.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    simpa using hL i n

theorem _root_.GlobalTheory.unramExt : _root_.ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt
  intro V _ _ _ _ k' _ _ _ _
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (ResidueField V) k'
  have hint : IsIntegral (ResidueField V) θ := .of_finite _ _
  obtain ⟨μ, hμmap, hμdeg, hμ⟩ := lifts_and_degree_eq_and_monic
    (map_surjective _ (residue_surjective (R := V)) (minpoly (ResidueField V) θ))
    (minpoly.monic hint)
  letI : Algebra V k' := ((algebraMap (ResidueField V) k').comp (residue V)).toAlgebra
  haveI : IsScalarTower V (ResidueField V) k' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hroot : eval₂ (algebraMap V k') θ μ = 0 := by
    rw [show algebraMap V k' = (algebraMap (ResidueField V) k').comp (residue V) from rfl,
      ← eval₂_map, hμmap]
    exact minpoly.aeval _ _
  let φ : AdjoinRoot μ →+* k' := AdjoinRoot.lift (algebraMap V k') θ hroot
  have hφ : ∀ g : V[X], φ (AdjoinRoot.mk μ g) = aeval θ g := fun g => by
    simp [φ, AdjoinRoot.lift_mk, aeval_def]
  have hadj : Algebra.adjoin (ResidueField V) {θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ]; rfl
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Algebra.adjoin (ResidueField V) {θ} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := map_surjective _ (residue_surjective (R := V)) p
    refine ⟨AdjoinRoot.mk μ q, ?_⟩
    rw [hφ]
    simp [aeval_def, eval₂_map, IsScalarTower.algebraMap_eq V (ResidueField V) k']
  haveI : Nontrivial (AdjoinRoot μ) := φ.domain_nontrivial
  have hnon : ∀ w : AdjoinRoot μ, w ∈ nonunits (AdjoinRoot μ) ↔ φ w = 0 := by
    intro w
    refine ⟨fun hw => ?_, fun hw hu => (hu.map φ).ne_zero hw⟩
    by_contra hne
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
    rw [hφ] at hne
    exact hw (_root_.GlobalTheory.isUnit_adjoinRoot_mk_of_aeval_ne_zero hint hμ hμmap hne)
  haveI : IsLocalRing (AdjoinRoot μ) := IsLocalRing.of_nonunits_add fun a b ha hb => by
    rw [hnon] at ha hb ⊢
    rw [map_add (f := _), ha, hb, add_zero]
  have hmax : maximalIdeal (AdjoinRoot μ) = RingHom.ker φ := by
    ext w
    rw [mem_maximalIdeal, hnon, RingHom.mem_ker]
  have hCm : (AdjoinRoot.mk μ).comp C = algebraMap V (AdjoinRoot μ) := rfl
  have hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V (AdjoinRoot μ)) := by
    apply le_antisymm
    · intro w hw
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
      rw [RingHom.mem_ker, hφ] at hw
      have hdvd : minpoly (ResidueField V) θ ∣ g.map (residue V) := by
        apply minpoly.dvd
        rw [← IsLocalRing.ResidueField.algebraMap_eq, aeval_map_algebraMap]
        exact hw
      obtain ⟨h', hh'⟩ := hdvd
      obtain ⟨h, rfl⟩ := map_surjective _ (residue_surjective (R := V)) h'
      have hcoeff : ∀ n, (g - μ * h).coeff n ∈ maximalIdeal V := by
        intro n
        rw [← residue_eq_zero_iff, ← coeff_map, Polynomial.map_sub, Polynomial.map_mul, hμmap,
          hh', sub_self, coeff_zero]
      have hmk : AdjoinRoot.mk μ g = AdjoinRoot.mk μ (g - μ * h) := by
        simp [AdjoinRoot.mk_self]
      rw [hmk, ← hCm, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_C_iff.2 hcoeff)
    · rw [Ideal.map_le_iff_le_comap]
      intro v hv
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hCm, RingHom.comp_apply, hφ, aeval_C,
        IsScalarTower.algebraMap_apply V (ResidueField V) k',
        IsLocalRing.ResidueField.algebraMap_eq, (residue_eq_zero_iff v).2 hv, map_zero]
  have hmW : maximalIdeal (AdjoinRoot μ) = (maximalIdeal V).map (algebraMap V (AdjoinRoot μ)) :=
    hmax.trans hker
  let pb := AdjoinRoot.powerBasis' hμ
  haveI : Module.Finite V (AdjoinRoot μ) := pb.finite
  haveI : Module.Free V (AdjoinRoot μ) := Module.Free.of_basis pb.basis
  haveI : IsNoetherianRing (AdjoinRoot μ) := inferInstance
  have hinj : Function.Injective (algebraMap V (AdjoinRoot μ)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    rw [← hCm, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hv
    by_contra hne
    have hle := degree_le_of_dvd hv (C_ne_zero.2 hne)
    rw [degree_C hne, hμdeg] at hle
    exact absurd hle (not_le.2 (minpoly.degree_pos hint))
  haveI hlh : IsLocalHom (algebraMap V (AdjoinRoot μ)) := by
    refine ⟨fun v hv => ?_⟩
    by_contra hnu
    have hvm : v ∈ maximalIdeal V := (mem_maximalIdeal v).2 hnu
    have := Ideal.mem_map_of_mem (algebraMap V (AdjoinRoot μ)) hvm
    rw [← hmW] at this
    exact (mem_maximalIdeal _).1 this hv
  let e : ResidueField (AdjoinRoot μ) ≃+* k' :=
    (Ideal.quotEquivOfEq hmax).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ w, e (residue (AdjoinRoot μ) w) = φ w := fun w => rfl
  have he' : ∀ v : V, e (residue (AdjoinRoot μ) (algebraMap V (AdjoinRoot μ) v)) =
      algebraMap (ResidueField V) k' (residue V v) := by
    intro v
    rw [he, ← hCm, RingHom.comp_apply, hφ, aeval_C]
    rfl
  let eAlg : ResidueField (AdjoinRoot μ) →ₐ[ResidueField V] k' :=
    { e.toRingHom with
      commutes' := fun r => by
        obtain ⟨v, rfl⟩ := residue_surjective r
        simpa using he' v }
  haveI : Algebra.IsSeparable (ResidueField V) (ResidueField (AdjoinRoot μ)) :=
    Algebra.IsSeparable.of_algHom _ _ eAlg
  haveI : Algebra.FormallyUnramified V (AdjoinRoot μ) :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmW.symm
  obtain ⟨hdom, hdvr⟩ := _root_.GlobalTheory.exists_isDiscreteValuationRing_of_flat V (AdjoinRoot μ) hmW.symm
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top)
  have hcompl : IsAdicComplete (maximalIdeal (AdjoinRoot μ)) (AdjoinRoot μ) := by
    rw [hmW, IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_linearEquiv_pi pb.basis.equivFun _
  exact ⟨AdjoinRoot μ, inferInstance, hdom, hdvr, hcompl, inferInstance, pb.finite, hinj, hlh,
    inferInstance, e, he'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorPolynomialGrowthQExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorPolynomialGrowthQExpansion
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem Vo_polyB_qs : ∀ (l : ℕ) (a : ℕ → ℂ), 0 < l → PolyB a →
    PolyB (Vo l a) ∧ ∀ τ σ : ℍ, (σ : ℂ) = l * τ → qs (Vo l a) τ = qs a σ := by
  intro l a hl ha
  refine ⟨?_, ?_⟩
  · obtain ⟨C, A, h⟩ := ha
    have hC : 0 ≤ C := by
      have := h 0
      simp at this
      exact le_trans (norm_nonneg _) this
    refine ⟨C, A, fun n => ?_⟩
    unfold Vo
    split_ifs with hd
    · refine (h (n / l)).trans ?_
      gcongr
      exact_mod_cast Nat.div_le_self n l
    · simp only [norm_zero]; positivity
  · intro τ σ hσ
    unfold qs
    have hinj : Function.Injective (fun m : ℕ => l * m) :=
      fun x y hxy => Nat.eq_of_mul_eq_mul_left hl hxy
    have hsupp : Function.support (fun n : ℕ => Vo l a n * cexp (2 * π * Complex.I * n * τ)) ⊆
        Set.range (fun m : ℕ => l * m) := by
      intro n hn
      by_contra hr
      apply hn
      have : ¬ l ∣ n := by
        rintro ⟨m, rfl⟩
        exact hr ⟨m, rfl⟩
      simp [Vo, this]
    rw [← hinj.tsum_eq hsupp]
    congr 1
    ext m
    have hl' : l ≠ 0 := hl.ne'
    simp only [Vo, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl, hσ]
    congr 2
    push_cast
    ring

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorPolynomialGrowthQExpansionStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion : ∀ (l : ℕ) (a : ℕ → ℂ), 0 < l → PolyB a → PolyB (Vo l a) ∧ ∀ τ σ : ℍ, (σ : ℂ) = l * τ → qs (Vo l a) τ = qs a σ := by
  first | exact @GlobalTheory.EisM.Vo_polyB_qs | exact GlobalTheory.EisM.Vo_polyB_qs | (intros; apply GlobalTheory.EisM.Vo_polyB_qs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetCoverMatrixValuationOne
open NumberField IsDedekindDomain
open Formalism.UG (GLint)

noncomputable section
namespace GlobalTheory.GLintCover

section
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem v_eq_one_of_mul {x y : v.adicCompletion F} (hx : x ∈ Formalism.UG.Ov F v) (hy : y ∈ Formalism.UG.Ov F v)
    (hxy : x * y = 1) : Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, hxy, map_one]
  have hy1 : Valued.v y ≤ 1 := hy
  have hx1 : Valued.v x ≤ 1 := hx
  refine le_antisymm hx1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v y := h1.symm
    _ ≤ Valued.v x := mul_le_of_le_one_right' hy1

theorem det_v {n : ℕ} {X : GL (Fin n) (v.adicCompletion F)} (hX : X ∈ GLint (Fin n) (Formalism.UG.Ov F v)) :
    Valued.v (X : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
  obtain ⟨y, rfl⟩ := hX
  have hd : ∀ z : GL (Fin n) (Formalism.UG.Ov F v),
      ((Formalism.UG.bc (n := Fin n) (Formalism.UG.Ov F v).subtype z : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).det
      = (((z : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det : Formalism.UG.Ov F v) : v.adicCompletion F) := by
    intro z
    rw [← (Formalism.UG.Ov F v).subtype_apply, RingHom.map_det]; rfl
  have hdi : (y : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det *
      ((y⁻¹ : GL (Fin n) (Formalism.UG.Ov F v)) : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [hd]
  refine v_eq_one_of_mul (SetLike.coe_mem _)
    (SetLike.coe_mem (((y⁻¹ : GL (Fin n) (Formalism.UG.Ov F v)) : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det)) ?_
  have := congrArg (fun z : Formalism.UG.Ov F v => (z : v.adicCompletion F)) hdi
  exact_mod_cast this

variable {n : ℕ} {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end
end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

section Count
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end Count
end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

section Main
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end Main

end GlobalTheory.GLintCover
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
open Polynomial

namespace GlobalTheory

theorem exists_ne_zero_forall_point_extend_subalgebra :
    ∀ (k A R : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [Algebra k R] (ξ : A →ₐ[k] R),
    Function.Injective ξ → ∀ T : Finset R,
    ∃ (a : A) (S : Subalgebra k R) (hξ : ∀ u, ξ u ∈ S), a ≠ 0 ∧ (∀ t ∈ T, t ∈ S) ∧
      ∀ φ : A →ₐ[k] k, φ a ≠ 0 → ∃ ψ : S →ₐ[k] k, ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := by
  intro k A R _ _ _ _ _ _ _ _ _ ξ hinj T
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  set S : Subalgebra k R := Algebra.adjoin k (ξ '' (s : Set A) ∪ (T : Set R)) with hSdef
  have hξ : ∀ u, ξ u ∈ S := by
    intro u
    have hu : u ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have : ξ u ∈ (Algebra.adjoin k (s : Set A)).map ξ := ⟨u, hu, rfl⟩
    rw [AlgHom.map_adjoin] at this
    exact Algebra.adjoin_mono Set.subset_union_left this
  have hT : ∀ t ∈ T, t ∈ S := fun t ht => Algebra.subset_adjoin (Set.subset_union_right ht)
  have hSfg : S.FG := Subalgebra.fg_def.2
    ⟨_, (s.finite_toSet.image ξ).union T.finite_toSet, rfl⟩
  haveI : Algebra.FiniteType k S := (Subalgebra.fg_iff_finiteType S).1 hSfg
  let f : A →ₐ[k] S := ξ.codRestrict S hξ
  letI : Algebra A S := f.toRingHom.toAlgebra
  haveI : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  haveI : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType k A S
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfinj : Function.Injective (algebraMap A S) := by
    intro x y h
    apply hinj
    have := congrArg Subtype.val h
    exact this
  have hfp : Algebra.FinitePresentation A S := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  have hc := PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr hfp)
  obtain ⟨q, hq, H⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem hc
    ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hfinj)⟩
  refine ⟨q, S, hξ, hq, hT, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extend_of_ker_mem_range_comap (A := S) φ.toRingHom
    (H ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩ (by simpa [RingHom.mem_ker] using hφ))
  have hψu : ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := fun u => by
    have := RingHom.congr_fun hψ u
    exact this
  refine ⟨{ ψ with commutes' := fun c => ?_ }, hψu⟩
  have h1 : (algebraMap k S c) = ⟨ξ (algebraMap k A c), hξ _⟩ := by
    ext; simp
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  rw [h1, hψu, φ.commutes]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebraStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_point_extends_to_subalgebra : ∀ (k A R : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [Algebra k R] (ξ : A →ₐ[k] R), Function.Injective ξ → ∀ T : Finset R,
 ∃ (a : A) (S : Subalgebra k R) (hξ : ∀ u, ξ u ∈ S), a ≠ 0 ∧ (∀ t ∈ T, t ∈ S) ∧ ∀ φ : A →ₐ[k] k, φ a ≠ 0 → ∃ ψ : S →ₐ[k] k, ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := by
  first | exact @GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra | exact GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra | (intros; apply GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem polyB_summable_norm_mul_pow {a : ℕ → ℂ} (ha : PolyB a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ‖a n‖ * r ^ n := by
  obtain ⟨C, A, h⟩ := ha
  have hs : Summable fun n : ℕ => C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by
    refine Summable.mul_left _ (Summable.add ?_ ?_)
    · exact summable_pow_mul_geometric_of_norm_lt_one A (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    · exact summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 _)) (fun n => ?_) hs
  have hb : ((n : ℝ) + 1) ^ A ≤ 2 ^ A * ((n : ℝ) ^ A + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_add, one_pow]
      have : (1 : ℝ) ≤ 2 ^ A := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg (le_refl (0:ℝ)) A]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : ((n : ℝ) + 1) ^ A ≤ (2 * n) ^ A := pow_le_pow_left₀ (by positivity) (by linarith) A
      rw [mul_pow] at this
      nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) A]
  have hC : 0 ≤ C := le_trans (norm_nonneg _) ((h 0).trans (by simp))
  calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
        mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 _)
    _ ≤ C * (2 ^ A * ((n : ℝ) ^ A + 1)) * r ^ n := by gcongr
    _ = C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by ring

theorem exists_upperHalfPlane_exp_eq {q : ℂ} (h0 : q ≠ 0) (h1 : ‖q‖ < 1) :
    ∃ τ : ℍ, ∀ n : ℕ, cexp (2 * π * Complex.I * n * τ) = q ^ n := by
  have hπ : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have him : 0 < (Complex.log q / (2 * π * Complex.I)).im := by
    have e : Complex.log q / (2 * π * Complex.I) = -Complex.I * Complex.log q / (2 * π) := by
      field_simp
      ring_nf
      simp [Complex.I_sq]
    rw [e]
    have : (-Complex.I * Complex.log q / (2 * π)).im = - (Complex.log q).re / (2 * π) := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
      simp
    rw [this, Complex.log_re]
    have hl : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr h0) h1
    have : 0 < 2 * π := by positivity
    apply div_pos (by simpa using hl) this
  refine ⟨⟨_, him⟩, fun n => ?_⟩
  have : 2 * π * Complex.I * (n : ℂ) * ((⟨_, him⟩ : ℍ) : ℂ) = n * Complex.log q := by
    field_simp
  rw [this, Complex.exp_nat_mul, Complex.exp_log h0]

theorem qs_injective : ∀ a b : ℕ → ℂ, PolyB a → PolyB b → qs a = qs b → a = b := by
  intro a b ha hb hab
  set c : ℕ → ℂ := fun n => a n - b n with hcdef
  have hsum : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n : ℕ => ‖c n‖ * r ^ n := by
    intro r h0 h1
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg h0 _)) (fun n => ?_)
      ((polyB_summable_norm_mul_pow ha h0 h1).add (polyB_summable_norm_mul_pow hb h0 h1))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg h0 _)
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hrad : ((1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    have := hsum (1 / 2) (by norm_num) (by norm_num)
    refine this.congr (fun n => ?_)
    rw [hp, FormalMultilinearSeries.ofScalars_norm]
    simp
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simp) hrad
  have hP := p.hasFPowerSeriesOnBall hpos
  have hval : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → p.sum q = 0 := by
    intro q h0 h1
    obtain ⟨τ, hτ⟩ := exists_upperHalfPlane_exp_eq h0 h1
    have ha' : Summable fun n => a n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow ha (norm_nonneg q) h1)
    have hb' : Summable fun n => b n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow hb (norm_nonneg q) h1)
    have e := congrFun hab τ
    simp only [qs, hτ] at e
    show ∑' n, p n (fun _ => q) = 0
    simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, hcdef, sub_mul]
    rw [Summable.tsum_sub ha' hb', e, sub_self]
  have hcont : ContinuousAt p.sum 0 := hP.continuousOn.continuousAt (Metric.eball_mem_nhds 0 hpos)
  have h0 : p.sum 0 = 0 := by
    have hev : p.sum =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
        with q hq0 hq1
      exact hval q hq0 (by simpa using hq1)
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev.symm)
  have hloc : p.sum =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact h0
    · exact hval q hq0 (by simpa using hq)
  have hpz : p = 0 := hP.hasFPowerSeriesAt.eq_zero_of_eventually hloc
  funext n
  have hn : p n = 0 := by rw [hpz]; rfl
  have : c n = 0 := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp hn
  exact sub_eq_zero.mp this

end GlobalTheory.EisM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowthStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth : ∀ a b : ℕ → ℂ, PolyB a → PolyB b → qs a = qs b → a = b := by
  first | exact @GlobalTheory.EisM.qs_injective | exact GlobalTheory.EisM.qs_injective | (intros; apply GlobalTheory.EisM.qs_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlane
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlane
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem summable_norm_mul_pow_of_polyB {a : ℕ → ℂ} (ha : PolyB a) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖a n * q ^ n‖ := by
  obtain ⟨C, A, hC⟩ := ha
  rcases eq_or_ne q 0 with rfl | hq0
  · exact (hasSum_single 0 (fun n hn => by simp [zero_pow hn])).summable
  · have hr0 : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have hr : ‖‖q‖‖ < 1 := by rwa [norm_norm]
    have h := (summable_nat_add_iff 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one A hr : Summable fun m : ℕ => (m : ℝ) ^ A * ‖q‖ ^ m)
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (h.mul_left (C * ‖q‖⁻¹))
    rw [norm_mul, norm_pow]
    have hq' : ‖q‖ ≠ 0 := hr0.ne'
    have e : C * ‖q‖⁻¹ * (((n + 1 : ℕ) : ℝ) ^ A * ‖q‖ ^ (n + 1)) = C * ((n : ℝ) + 1) ^ A * ‖q‖ ^ n := by
      push_cast
      rw [pow_succ]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (hC n) (by positivity)

theorem qs_term_eq (a : ℕ → ℂ) (τ : ℍ) (n : ℕ) :
    a n * cexp (2 * π * Complex.I * n * τ) = a n • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n := by
  simp only [smul_eq_mul, Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem hasSum_qs {a : ℕ → ℂ} (ha : PolyB a) (τ : ℍ) :
    HasSum (fun n : ℕ => a n • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n) (qs a τ) := by
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hs : Summable fun n => a n • Function.Periodic.qParam 1 (τ : ℂ) ^ n := by
    simpa only [smul_eq_mul] using (summable_norm_mul_pow_of_polyB ha hq).of_norm
  convert hs.hasSum using 1
  show ∑' n, a n * cexp (2 * π * Complex.I * n * τ) = _
  exact tsum_congr fun n => qs_term_eq a τ n

private theorem mdifferentiable_qs_of_polyB {a : ℕ → ℂ} (ha : PolyB a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := hz
  set y0 := z.im / 2 with hy0def
  have hy0 : 0 < y0 := by positivity
  set U : Set ℂ := {w | y0 < w.im} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by
    show y0 < z.im
    linarith
  set r : ℝ := Real.exp (-(2 * π * y0)) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hrdef, Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_norm_mul_pow_of_polyB ha hr1)
      (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => a n * cexp (2 * π * Complex.I * n * w)).differentiableOn)
      hU ?_
    intro n w hw
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, hrdef, ← Real.exp_nat_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.exp_le_exp]
    have hre : (2 * π * Complex.I * n * w).re = -(2 * π * n * w.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hw' : y0 < w.im := hw
    have := mul_nonneg (mul_nonneg Real.pi_pos.le hn) (sub_pos.2 hw').le
    nlinarith
  have hDz := (hD z hzU).differentiableAt (hU.mem_nhds hzU)
  apply DifferentiableAt.differentiableWithinAt
  apply hDz.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with w hw
  have hw' : 0 < w.im := lt_trans hy0 hw
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  rfl

private theorem periodic_qs_comp_ofComplex_one (a : ℕ → ℂ) :
    Function.Periodic (qs a ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    show ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (w + 1))
      = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)
    refine tsum_congr fun n => ?_
    congr 1
    rw [show 2 * π * Complex.I * n * (w + 1) = 2 * π * Complex.I * n * w + n * (2 * π * Complex.I) by ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · push_neg at hw
    have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw1, ofComplex_apply_of_im_nonpos hw]

theorem analyticAt_cuspFunction_qs {a : ℕ → ℂ} (ha : PolyB a) :
    AnalyticAt ℂ (cuspFunction 1 (qs a)) 0 := by
  exact analyticAt_cuspFunction_zero one_pos (periodic_qs_comp_ofComplex_one a)
    (mdifferentiable_qs_of_polyB ha) (isBoundedAtImInfty_of_hasSum_qExpansion one_pos (hasSum_qs ha))

theorem coef_qs : ∀ a : ℕ → ℂ, PolyB a → ∀ n, coef (qs a) n = a n := by
  intro a ha n
  have hb := analyticAt_cuspFunction_qs ha
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos hb (hasSum_qs ha)).hasFPowerSeriesAt
  have h2 := hb.hasFPowerSeriesAt
  have e := congr_arg (FormalMultilinearSeries.coeff · n) (h1.eq_formalMultilinearSeries h2)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at e
  show (qExpansion 1 (qs a)).coeff n = a n
  rw [qExpansion_coeff, e, div_eq_inv_mul]

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlaneStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane : ∀ a : ℕ → ℂ, PolyB a → ∀ n, coef (qs a) n = a n := by
  first | exact @GlobalTheory.EisM.coef_qs | exact GlobalTheory.EisM.coef_qs | (intros; apply GlobalTheory.EisM.coef_qs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUVCauchyProductIdentities
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUVCauchyProductIdentities
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.FormalId

variable {R : Type} [CommRing R]

theorem uo_mul_vo (l : ℕ) (hl : 0 < l) (a b : ℕ → R) : Uo l (mul a (Vo l b)) = mul (Uo l a) b := by
  funext n
  simp only [Uo, mul, Vo, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun p => (l * p.1, l * p.2)) (fun p => (p.1 / l, p.2 / l))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    exact ⟨by rw [← mul_add, hp], dvd_mul_right _ _⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    rw [← Nat.add_div_of_dvd_right h3, h1, Nat.mul_div_cancel_left _ hl]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    ext <;> simp [Nat.mul_div_cancel' h3, Nat.mul_div_cancel' h2]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]

theorem mul_comm' (a b : ℕ → R) : mul a b = mul b a := by
  funext n
  simp only [mul]
  conv_lhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  simp [_root_.mul_comm]

theorem mul_add_right' (a b b' : ℕ → R) : mul a (b + b') = mul a b + mul a b' := by
  funext n
  simp [mul, _root_.mul_add, Finset.sum_add_distrib]

theorem mul_add_left' (a a' b : ℕ → R) : mul (a + a') b = mul a b + mul a' b := by
  rw [mul_comm', mul_add_right', mul_comm' b, mul_comm' b]

theorem mul_lin (a b b' : ℕ → R) (c c' : R) :
    mul a (c • b + c' • b') = c • mul a b + c' • mul a b' := by
  funext n
  simp only [mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

theorem zero_mul' (b : ℕ → R) : mul 0 b = 0 := by
  funext n; simp [mul]

theorem uo_dep (l : ℕ) (a : ℕ → R) : Uo l (dep l a) = 0 := by
  funext n; simp [Uo, dep]

theorem uo_vo (l : ℕ) (hl : 0 < l) (a : ℕ → R) : Uo l (Vo l a) = a := by
  funext n; simp [Uo, Vo, Nat.mul_div_cancel_left _ hl]

theorem dep_add (l : ℕ) (hl : 0 < l) (a : ℕ → R) : a = dep l a + Vo l (Uo l a) := by
  funext n
  by_cases h : l ∣ n
  · simp [dep, Vo, Uo, h, Nat.mul_div_cancel' h]
  · simp [dep, Vo, Uo, h]

theorem uo_add (l : ℕ) (x y : ℕ → R) : Uo l (x + y) = Uo l x + Uo l y := rfl

theorem uo_mul_dep (l : ℕ) (hl : 0 < l) (a b : ℕ → R) :
    Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b) := by
  have e : Uo l (mul a b) = Uo l (mul (dep l a) (dep l b)) + mul (Uo l a) (Uo l b) := by
    conv_lhs => rw [dep_add l hl a, dep_add l hl b]
    rw [mul_add_left', mul_add_right', mul_add_right', uo_add, uo_add, uo_add,
      uo_mul_vo l hl, uo_dep, zero_mul', mul_comm' (Vo l (Uo l a)) (dep l b), uo_mul_vo l hl, uo_dep,
      zero_mul', uo_mul_vo l hl, uo_vo l hl]
    abel
  rw [e]; abel

theorem to_vo (l k q : ℕ) (c : R) (a : ℕ → R) (hq : q.Coprime l) (hq0 : 0 < q) :
    To k c q (Vo l a) = Vo l (To k c q a) := by
  funext n
  simp only [To, Vo]
  by_cases hn : l ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp
    have h1 : l ∣ q * (l * m) := ⟨q * m, by ring⟩
    rw [if_pos h1, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl,
      show q * (l * m) = l * (q * m) by ring, Nat.mul_div_cancel_left _ hl]
    congr 1
    by_cases hqm : q ∣ m
    · obtain ⟨t, rfl⟩ := hqm
      rw [if_pos ⟨l * t, by ring⟩, if_pos (dvd_mul_right _ _),
        show l * (q * t) = q * (l * t) by ring, Nat.mul_div_cancel_left _ hq0, Nat.mul_div_cancel_left _ hq0,
        if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl]
    · rw [if_neg hqm, if_neg]
      intro h
      exact hqm ((Nat.Coprime.dvd_of_dvd_mul_left hq h))
  · have h1 : ¬ l ∣ q * n := fun h => hn (Nat.Coprime.dvd_of_dvd_mul_left hq.symm h)
    rw [if_neg h1, if_neg hn]
    by_cases hqn : q ∣ n
    · rw [if_pos hqn, if_neg]
      · simp
      · intro h
        obtain ⟨t, ht⟩ := hqn
        apply hn
        rw [ht, Nat.mul_div_cancel_left _ hq0] at h
        exact Dvd.dvd.mul_left h q |> fun h' => by rw [ht]; exact h'
    · simp [hqn]

theorem lam_lin (B : ℕ) (c a b : ℕ → R) (x y : R) :
    lam B c (x • a + y • b) = x * lam B c a + y * lam B c b := by
  simp only [lam, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.EisM.FormalId

theorem GlobalTheory.EisM.formal_identities : ∀ (R : Type) [CommRing R] (l : ℕ), 0 < l → (∀ a b : ℕ → R, Uo l (mul a (Vo l b)) = mul (Uo l a) b) ∧ (∀ a b : ℕ → R, Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b)) ∧ (∀ a b : ℕ → R, mul a b = mul b a) ∧ (∀ (a b b' : ℕ → R) (c c' : R), mul a (c • b + c' • b') = c • mul a b + c' • mul a b') ∧ (∀ (k q : ℕ) (c : R) (a : ℕ → R), q.Coprime l → 0 < q → To k c q (Vo l a) = Vo l (To k c q a)) ∧ (∀ (B : ℕ) (c a b : ℕ → R) (x y : R), lam B c (x • a + y • b) = x * lam B c a + y * lam B c b) := by
  intro R _ l hl
  exact ⟨FormalId.uo_mul_vo l hl, FormalId.uo_mul_dep l hl, FormalId.mul_comm', FormalId.mul_lin,
    fun k q c a hq hq0 => FormalId.to_vo l k q c a hq hq0, FormalId.lam_lin⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUVCauchyProductIdentitiesStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities : ∀ (R : Type) [CommRing R] (l : ℕ), 0 < l → (∀ a b : ℕ → R, Uo l (mul a (Vo l b)) = mul (Uo l a) b) ∧ (∀ a b : ℕ → R, Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b)) ∧ (∀ a b : ℕ → R, mul a b = mul b a) ∧ (∀ (a b b' : ℕ → R) (c c' : R), mul a (c • b + c' • b') = c • mul a b + c' • mul a b') ∧ (∀ (k q : ℕ) (c : R) (a : ℕ → R), q.Coprime l → 0 < q → To k c q (Vo l a) = Vo l (To k c q a)) ∧ (∀ (B : ℕ) (c a b : ℕ → R) (x y : R), lam B c (x • a + y • b) = x * lam B c a + y * lam B c b) := by
  first | exact @GlobalTheory.EisM.formal_identities | exact GlobalTheory.EisM.formal_identities | (intros; apply GlobalTheory.EisM.formal_identities <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightAction
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightAction
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_sl_right_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ f, T.sl 1 f = f) ∧ ∀ g h f, T.sl (g * h) f = T.sl h (T.sl g f) := by
  intro Ω _ _ _ ε T
  obtain ⟨hext, hcl, -, -⟩ := GlobalTheory.T.fractionField_ext_closure_injective Ω ε T
  obtain ⟨c1, cmul, -, -⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob
  refine ⟨fun f => ?_, fun g h f => ?_⟩
  · have e : (T.sl 1 : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom = RingHom.id T.K := by
      apply hext
      intro a
      exact T.sl_io 1 a a (c1 a).symm
    exact congrArg (fun φ : T.K →+* T.K => φ f) e
  · have e : (T.sl (g * h) : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom =
        ((T.sl h : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom).comp ((T.sl g : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom) := by
      apply hext
      intro a
      obtain ⟨a', ha', hga⟩ := hcl g a
      obtain ⟨a'', ha'', hha⟩ := hcl h a'
      have : (a'' : ℍ → ℂ) = cmp (g * h) a := by rw [ha'', ha', cmul]
      simp only [RingHom.comp_apply]
      show T.sl (g * h) (T.io a) = T.sl h (T.sl g (T.io a))
      rw [T.sl_io (g * h) a a'' this, hga, hha]
    exact congrArg (fun φ : T.K →+* T.K => φ f) e

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightActionStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_sl_rightAction : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ f, T.sl 1 f = f) ∧ ∀ g h f, T.sl (g * h) f = T.sl h (T.sl g f) := by
  first | exact @GlobalTheory.FN.frac_sl_right_action | exact GlobalTheory.FN.frac_sl_right_action | (intros; apply GlobalTheory.FN.frac_sl_right_action <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeStableCongruenceConjDiamondMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeStableCongruenceConjDiamondMatrix
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ.StabHecke

theorem congruenceCondition_conj_diamond : ∀ (N l d : ℕ) (σ : SL(2, ℤ)) (r : Matrix (Fin 2) (Fin 2) ℤ), IsDiam N l d σ → PP N l r →
    PP N l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  intro N l d σ r hσ hr
  obtain ⟨h1, h2, -, h4⟩ := diam_facts hσ
  obtain ⟨r1, r2, r3, r4⟩ := hr
  have e00 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 =
      r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (r 0 0) * h4
  have e10 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      σ 1 0 * (σ 1 1 * r 0 0 - σ 1 0 * r 0 1 - σ 1 1 * r 1 1) + σ 1 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, show r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 - 1 =
        (r 0 0 - 1) + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 by ring]
    exact dvd_add (dvd_add r1 (dvd_mul_of_dvd_left h1 _)) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right r3 _)
  · rw [e00]
    obtain ⟨s, hs⟩ := h2
    obtain ⟨t, ht⟩ := r3
    have e : r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 =
        r 0 0 + (l : ℤ) * (s * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * t) := by
      rw [hs, ht]; ring
    rw [e]
    exact r4.add_mul_left_left _

end GlobalTheory.KZ.StabHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeStableCongruenceConjDiamondMatrixStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStableCongruence_conj_diamondMatrix : ∀ (N l d : ℕ) (σ : SL(2, ℤ)) (r : Matrix (Fin 2) (Fin 2) ℤ), IsDiam N l d σ → PP N l r → PP N l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  first | exact @GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond | exact GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond | (intros; apply GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond <;> assumption)
end
end
