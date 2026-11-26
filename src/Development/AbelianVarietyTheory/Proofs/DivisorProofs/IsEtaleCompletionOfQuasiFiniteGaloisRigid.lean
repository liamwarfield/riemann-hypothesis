module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFiniteOfQuasiFiniteCompleteLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFiniteOfQuasiFiniteCompleteLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QuasiFiniteLocal

theorem finite_quotient_of_pow_le_of_span {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (T : Set S) (hT : T.Finite)
    (h : ∀ s : S, ∃ t ∈ Submodule.span A T, s - t ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  have key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤ := by
    intro N
    induction N with
    | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
    | succ N ih =>
      obtain ⟨F, hF, hF'⟩ := ih
      obtain ⟨G, hG⟩ : (I ^ N).FG := IsNoetherian.noetherian _
      refine ⟨F ⊔ Submodule.span A (Set.image2 (· * ·) T (G : Set S)),
        hF.sup (Submodule.fg_span (hT.image2 _ G.finite_toSet)), ?_⟩
      rw [eq_top_iff, ← hF', sup_assoc]
      refine sup_le_sup_left (fun x hx => ?_) _
      have hx' : x ∈ Submodule.span S (G : Set S) := hG.ge hx
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hx'
      refine sum_mem fun y hy => ?_
      obtain ⟨t, ht, ha⟩ := h (c y)
      have e : c y • y = t * y + y * (c y - t) := by rw [smul_eq_mul]; ring
      rw [e]
      refine Submodule.add_mem_sup ?_ ?_
      · have hmul : ∀ u ∈ Submodule.span A T,
            u * y ∈ Submodule.span A (Set.image2 (· * ·) T (G : Set S)) := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem u hu => exact Submodule.subset_span (Set.mem_image2_of_mem hu hy)
          | zero => simp
          | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
          | smul a u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu
        exact hmul t ht
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha
  obtain ⟨F, hF, hF'⟩ := key N
  have : Module.Finite A F := Module.Finite.iff_fg.2 hF
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))
  exact ⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩

theorem finite_of_quasiFinite : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (b : A →+* R) [IsLocalHom b], IsAdicComplete (maximalIdeal A) A → (∀ p : Ideal R, p.IsPrime → (maximalIdeal A).map b ≤ p → p = maximalIdeal R) → ((residue R).comp b).Finite → b.Finite := by
  intro A R _ _ _ _ _ _ b _ hc hq hres
  letI : Algebra A R := b.toAlgebra
  have hb : algebraMap A R = b := rfl
  have hle : (maximalIdeal A).map (algebraMap A R) ≤ maximalIdeal R := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [Ideal.mem_comap, hb, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit b a h)
  have hrad : maximalIdeal R ≤ ((maximalIdeal A).map (algebraMap A R)).radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun p ⟨hJp, hp⟩ => (hq p hp hJp).ge
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

  obtain ⟨T0, hT0⟩ : (⊤ : Submodule A (ResidueField R)).FG := by
    letI : Algebra A (ResidueField R) := ((residue R).comp b).toAlgebra
    exact hres.fg_top
  classical
  let lift : ResidueField R → R := Function.surjInv (residue_surjective (R := R))
  have hlift : ∀ t, residue R (lift t) = t := Function.surjInv_eq _
  let L : R →ₗ[A] ResidueField R :=
    { toFun := residue R
      map_add' := map_add _
      map_smul' := fun a x => by
        show residue R (b a * x) = residue R (b a) * residue R x
        exact map_mul _ _ _ }
  have hfin : Module.Finite A (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
    refine finite_quotient_of_pow_le_of_span (I := maximalIdeal R) (lift '' (T0 : Set _))
      ((T0.finite_toSet).image _) (fun s => ?_) hN
    have hs : residue R s ∈ Submodule.map L (Submodule.span A (lift '' (T0 : Set _))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      have e : (⇑L ∘ lift) = id := funext fun t => hlift t
      rw [e, Set.image_id, hT0]
      trivial
    obtain ⟨t, ht, hts⟩ := hs
    refine ⟨t, ht, ?_⟩
    rw [← residue_eq_zero_iff, map_sub]
    exact sub_eq_zero.2 hts.symm
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A R)) R :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  haveI := hc
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)

end GlobalTheory.QuasiFiniteLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFiniteOfQuasiFiniteCompleteLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_finite_of_quasiFinite_complete_local : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (b : A →+* R) [IsLocalHom b], IsAdicComplete (maximalIdeal A) A → (∀ p : Ideal R, p.IsPrime → (maximalIdeal A).map b ≤ p → p = maximalIdeal R) → ((residue R).comp b).Finite → b.Finite := by
  first | exact @GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite | exact GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite | (intros; apply GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCompletionResidueEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCompletionResidueEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EtaleCompletionResidue

open Polynomial

theorem exists_finite_free_local_residue_equiv (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (M : Type)
    [Field M] (m : ResidueField B →+* M) (hmf : m.Finite) (hmu : m.FormallyUnramified) :
    ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (ψ₀ : B →+* C) (_ : IsLocalHom ψ₀) (E : M ≃+* ResidueField C),
      IsNoetherianRing C ∧ Function.Injective ψ₀ ∧ ψ₀.Flat ∧ (maximalIdeal B).map ψ₀ = maximalIdeal C ∧
      ((residue C).comp ψ₀).Finite ∧ ((residue C).comp ψ₀).FormallyUnramified ∧ (E : M →+* ResidueField C).comp m = ResidueField.map ψ₀ := by
  letI : Algebra (ResidueField B) M := m.toAlgebra
  haveI : FiniteDimensional (ResidueField B) M := hmf
  haveI : Algebra.FormallyUnramified (ResidueField B) M := hmu
  haveI : Algebra.IsSeparable (ResidueField B) M := (Algebra.FormallyUnramified.iff_isSeparable _ _).1 inferInstance
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField B) M
  have hm := minpoly.monic pb.isIntegral_gen
  have hirr := minpoly.irreducible pb.isIntegral_gen
  obtain ⟨F, hF, hdeg, hFm⟩ := Polynomial.lifts_and_degree_eq_and_monic (f := residue B)
    (Polynomial.mem_lifts_of_surjective residue_surjective _) hm
  have hg : Irreducible (F.map (residue B)) := hF ▸ hirr
  haveI : Fact (Irreducible (F.map (residue B))) := ⟨hg⟩
  haveI hfin : Module.Finite B (AdjoinRoot F) := .of_basis (AdjoinRoot.powerBasis' hFm).basis
  haveI : Module.Free B (AdjoinRoot F) := .of_basis (AdjoinRoot.powerBasis' hFm).basis
  have hqf : IsField (AdjoinRoot F ⧸ (maximalIdeal B).map (AdjoinRoot.of F)) := by
    have hR : IsField (AdjoinRoot (F.map (residue B))) := Field.toIsField _
    exact MulEquiv.isField hR (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).toRingEquiv.toMulEquiv
  have hJ : ((maximalIdeal B).map (algebraMap B (AdjoinRoot F))).IsMaximal := by
    rw [AdjoinRoot.algebraMap_eq]
    exact Ideal.Quotient.maximal_of_isField _ hqf
  haveI : IsLocalRing (AdjoinRoot F) := by
    haveI : Algebra.IsIntegral B (AdjoinRoot F) := inferInstance
    refine IsLocalRing.of_unique_max_ideal ⟨_, hJ, fun P hP => ?_⟩
    have hc : (P.comap (algebraMap B (AdjoinRoot F))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
    have h1 : P.comap (algebraMap B (AdjoinRoot F)) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hc
    have hle : (maximalIdeal B).map (algebraMap B (AdjoinRoot F)) ≤ P := Ideal.map_le_iff_le_comap.2 h1.ge
    exact (hJ.eq_of_le hP.ne_top hle).symm
  have hmax : maximalIdeal (AdjoinRoot F) = (maximalIdeal B).map (algebraMap B (AdjoinRoot F)) :=
    (IsLocalRing.eq_maximalIdeal hJ).symm
  haveI hloc : IsLocalHom (algebraMap B (AdjoinRoot F)) := by
    constructor
    intro x hx
    by_contra h
    have h2 : algebraMap B (AdjoinRoot F) x ∈ maximalIdeal (AdjoinRoot F) := by
      rw [hmax]; exact Ideal.mem_map_of_mem _ h
    exact h2 hx
  have hinj : Function.Injective (algebraMap B (AdjoinRoot F)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    change AdjoinRoot.mk F (C x) = 0 at hx
    rw [AdjoinRoot.mk_eq_zero] at hx
    refine hFm.not_dvd_of_natDegree_lt (Polynomial.C_ne_zero.2 h0) ?_ hx
    rw [natDegree_C, natDegree_eq_of_degree_eq hdeg]
    exact minpoly.natDegree_pos pb.isIntegral_gen
  haveI : IsNoetherianRing (AdjoinRoot F) := isNoetherian_of_tower B inferInstance
  let e₁ : ResidueField (AdjoinRoot F) ≃+* AdjoinRoot (F.map (residue B)) :=
    (Ideal.quotEquivOfEq hmax).trans (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).toRingEquiv
  have he₁ : e₁.toRingHom.comp (ResidueField.map (algebraMap B (AdjoinRoot F))) = AdjoinRoot.of (F.map (residue B)) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    show e₁ (ResidueField.map _ (residue B x)) = _
    rw [ResidueField.map_residue]
    exact (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).commutes x
  let pb' := AdjoinRoot.powerBasis (hFm.map (residue B)).ne_zero
  have hmin : minpoly (ResidueField B) pb.gen = minpoly (ResidueField B) pb'.gen := by
    rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic (hFm.map (residue B)), hF]
  let e₂ : M ≃ₐ[ResidueField B] AdjoinRoot (F.map (residue B)) := pb.equivOfMinpoly pb' hmin
  let Eq' : M ≃+* ResidueField (AdjoinRoot F) := e₂.toRingEquiv.trans e₁.symm
  have hE : Eq'.toRingHom.comp m = ResidueField.map (algebraMap B (AdjoinRoot F)) := by
    ext x
    have h1 : e₁ (ResidueField.map (algebraMap B (AdjoinRoot F)) x) = AdjoinRoot.of (F.map (residue B)) x :=
      congrArg (fun q => q x) he₁
    have h2 : e₂ (m x) = AdjoinRoot.of (F.map (residue B)) x := by
      rw [← AdjoinRoot.algebraMap_eq]
      exact e₂.commutes x
    show e₁.symm (e₂ (m x)) = _
    rw [h2, ← h1, RingEquiv.symm_apply_apply]
  have hψfin : (algebraMap B (AdjoinRoot F)).Finite := RingHom.finite_algebraMap.mpr hfin
  refine ⟨AdjoinRoot F, inferInstance, inferInstance, algebraMap B (AdjoinRoot F), hloc, Eq', inferInstance,
    hinj, RingHom.flat_algebraMap_iff.mpr inferInstance, hmax.symm,
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ residue_surjective) hψfin, ?_, hE⟩
  rw [← ResidueField.map_comp_residue, ← hE]
  exact RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective)
    (RingHom.FormallyUnramified.comp hmu (RingHom.FormallyUnramified.of_surjective Eq'.surjective))

theorem exists_etaleCompletion_residue_equiv : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (M : Type) [Field M] (m : ResidueField O →+* M), m.Finite → m.FormallyUnramified → ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ψ : O →+* A) (_ : IsLocalHom ψ) (E : M ≃+* ResidueField A), IsCN A ∧ IsEtaleCompletion ψ ∧ ((residue A).comp ψ).FormallyUnramified ∧ (E : M →+* ResidueField A).comp m = ResidueField.map ψ := by
  intro O _ _ _ _ _ _ M _ m hmf hmu
  have hOn : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  obtain ⟨C, _, _, ψ₀, hψl, E₀, hCn, hψi, hψf, hψm, hψfin, hψfu, hE⟩ :=
    exists_finite_free_local_residue_equiv O M m hmf hmu
  haveI := hCn
  haveI := hψl
  let A := AdicCompletion (maximalIdeal C) C
  let j : C →+* A := algebraMap C A
  haveI : Module.Flat C A := AdicCompletion.flat_of_isNoetherian _
  have hbij : Function.Bijective (ResidueField.map j) := AdicCompletion.residueField_map_bijective C
  have hcomp : (residue A).comp (j.comp ψ₀) = (ResidueField.map j).comp ((residue C).comp ψ₀) := by
    ext b
    simp [ResidueField.map_residue]
  have hAn : IsNoetherianRing A := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _
  have hAc : IsAdicComplete (maximalIdeal A) A := inferInstance
  have hjl : IsLocalHom j := inferInstance
  have hji : Function.Injective j := AdicCompletion.of_injective (maximalIdeal C) C
  let ψ : O →+* A := j.comp ψ₀
  have hloc : IsLocalHom ψ := inferInstance
  have het : IsEtaleCompletion ψ := by
    refine ⟨?_, ?_, ?_⟩
    · exact RingHom.Flat.comp hψf (RingHom.flat_algebraMap_iff.2 inferInstance)
    · show (maximalIdeal O).map (j.comp ψ₀) = _
      rw [← Ideal.map_map, hψm, AdicCompletion.maximalIdeal_eq_map]
    · show ((residue A).comp (j.comp ψ₀)).Finite
      rw [hcomp]
      exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ hbij.2) hψfin
  have hur : ((residue A).comp ψ).FormallyUnramified := by
    show ((residue A).comp (j.comp ψ₀)).FormallyUnramified
    rw [hcomp]
    exact RingHom.FormallyUnramified.comp hψfu (RingHom.FormallyUnramified.of_surjective hbij.2)
  obtain ⟨hd, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed O
  obtain ⟨hAd, hAi⟩ := GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed O A ψ hOn hd hic hAn hAc hloc het hur
  haveI := hAd
  have hψinj : Function.Injective ψ := hji.comp hψi
  haveI : CharZero A := charZero_of_injective_ringHom hψinj
  let E : M ≃+* ResidueField A := E₀.trans (RingEquiv.ofBijective _ hbij)
  refine ⟨A, inferInstance, hAd, inferInstance, ψ, hloc, E, ⟨hAn, hAi, hAc, inferInstance⟩, het, hur, ?_⟩
  ext x
  obtain ⟨b, rfl⟩ := residue_surjective x
  have h2 := congrArg (fun t => t (residue O b)) hE
  simp only [RingHom.comp_apply, ResidueField.map_residue] at h2
  show ResidueField.map j (E₀ (m (residue O b))) = _
  have h3 : E₀ (m (residue O b)) = residue C (ψ₀ b) := h2
  rw [h3]
  simp only [ψ, ResidueField.map_residue, RingHom.comp_apply]

end GlobalTheory.EtaleCompletionResidue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCompletionResidueEquivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleCompletion_with_residueField_equiv : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (M : Type) [Field M] (m : ResidueField O →+* M), m.Finite → m.FormallyUnramified → ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ψ : O →+* A) (_ : IsLocalHom ψ) (E : M ≃+* ResidueField A), IsCN A ∧ IsEtaleCompletion ψ ∧ ((residue A).comp ψ).FormallyUnramified ∧ (E : M →+* ResidueField A).comp m = ResidueField.map ψ := by
  first | exact @GlobalTheory.EtaleCompletionResidue.exists_etaleCompletion_residue_equiv | exact GlobalTheory.EtaleCompletionResidue.exists_etaleCompletion_residue_equiv | (intros; apply GlobalTheory.EtaleCompletionResidue.exists_etaleCompletion_residue_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteMapInj

theorem injective_of_finite_of_ringKrullDim_le (A R : Type) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] (b : A →+* R) :
    b.Finite → ringKrullDim A ≤ ringKrullDim R → Function.Injective b := by
  intro hfin hdim
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  set I := RingHom.ker b
  have hxI : x ∈ I := hx

  have hcomp : b.kerLift.comp (Ideal.Quotient.mk I) = b := by
    ext a; rfl
  have hfin' : b.kerLift.Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  letI : Algebra (A ⧸ I) R := b.kerLift.toAlgebra
  haveI : Algebra.IsIntegral (A ⧸ I) R := ⟨hfin'.to_isIntegral⟩
  have h1 : ringKrullDim R ≤ ringKrullDim (A ⧸ I) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ I) R))
      fun P Q h => Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) h
  have h2 : ringKrullDim (A ⧸ I) + 1 ≤ ringKrullDim A :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hxI)
  have h3 : ringKrullDim R + 1 ≤ ringKrullDim R :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans hdim
  have htop : ringKrullDim R + 1 < ⊤ :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans_lt
      ringKrullDim_lt_top
  have hbot : ringKrullDim R ≠ ⊥ := fun h => by
    have := ringKrullDim_nonneg_of_nontrivial (R := R)
    rw [h] at this
    exact absurd this (by simp)
  generalize ringKrullDim R = d at h3 htop hbot
  induction d with
  | bot => exact hbot rfl
  | coe e =>
    induction e with
    | top =>
      exact absurd htop (by rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]; exact lt_irrefl _)
    | coe n =>
      have : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h3
      norm_cast at this
      omega

end GlobalTheory.FiniteMapInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimLeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_finite_of_ringKrullDim_le' : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] (b : A →+* R), b.Finite → ringKrullDim A ≤ ringKrullDim R → Function.Injective b := by
  first | exact @GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le | exact GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le | (intros; apply GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivSubMemMaximalIdealOfPurelyInsepResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivSubMemMaximalIdealOfPurelyInsepResidue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ResFix

theorem sigma_fix_mod_max : ∀ (A R R' : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (b : A →+* R) (θ : R →+* R') [IsLocalHom θ] (q : ℕ) [ExpChar (ResidueField R) q] (σ : R' ≃+* R'), (∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a)) → (∀ a, σ (θ (b a)) = θ (b a)) → ∀ r, σ (θ r) - θ r ∈ maximalIdeal R' := by
  intro A R R' _ _ _ _ _ b θ _ q _ σ hins hfix r
  obtain ⟨n, a, ha⟩ := hins (residue R r)
  have h1 : r ^ q ^ n - b a ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_pow, ha, sub_self]
  have h2 : θ r ^ q ^ n - θ (b a) ∈ maximalIdeal R' := by
    have := map_nonunit θ _ h1
    simpa [map_sub, map_pow] using this
  have h3 : σ (θ r) ^ q ^ n - θ (b a) ∈ maximalIdeal R' := by
    have := map_nonunit (σ : R' →+* R') _ h2
    simpa [map_sub, map_pow, hfix a] using this
  haveI : ExpChar (ResidueField R') q :=
    expChar_of_injective_ringHom (ResidueField.map θ).injective q
  have e2 : residue R' (θ r) ^ q ^ n = residue R' (θ (b a)) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h2
  have e3 : residue R' (σ (θ r)) ^ q ^ n = residue R' (θ (b a)) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h3
  have e4 : (residue R' (σ (θ r)) - residue R' (θ r)) ^ q ^ n = 0 := by
    rw [sub_pow_expChar_pow, e2, e3, sub_self]
  rw [← residue_eq_zero_iff, map_sub]
  exact pow_eq_zero_iff (pow_ne_zero _ (expChar_pos (ResidueField R') q).ne') |>.mp e4

end GlobalTheory.ResFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivSubMemMaximalIdealOfPurelyInsepResidueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringEquiv_sub_mem_maximalIdeal_of_purelyInsep_residue : ∀ (A R R' : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (b : A →+* R) (θ : R →+* R') [IsLocalHom θ] (q : ℕ) [ExpChar (ResidueField R) q] (σ : R' ≃+* R'), (∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a)) → (∀ a, σ (θ (b a)) = θ (b a)) → ∀ r, σ (θ r) - θ r ∈ maximalIdeal R' := by
  first | exact @GlobalTheory.ResFix.sigma_fix_mod_max | exact GlobalTheory.ResFix.sigma_fix_mod_max | (intros; apply GlobalTheory.ResFix.sigma_fix_mod_max <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLeOfIsEtaleCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLeOfIsEtaleCompletion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ringKrullDim_le_of_isEtaleCompletion : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ψ : O →+* A) [IsLocalHom ψ], IsEtaleCompletion ψ → ringKrullDim A ≤ ringKrullDim O := by
  intro O A _ _ _ _ _ _ ψ _ h
  letI : Algebra O A := ψ.toAlgebra
  have hmap : (maximalIdeal O).map (algebraMap O A) = maximalIdeal A := h.2.1
  have hlo : (maximalIdeal A).LiesOver (maximalIdeal O) := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    exact (IsLocalRing.maximalIdeal_comap ψ).symm
  have key := Ideal.height_le_height_add_of_liesOver (maximalIdeal O) (maximalIdeal A)
  rw [hmap, Ideal.map_quotient_self] at key
  have h0 : (⊥ : Ideal (A ⧸ maximalIdeal A)).height = 0 := by
    simp
  rw [h0, add_zero] at key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLeOfIsEtaleCompletionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_le_of_isEtaleCompletion' : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ψ : O →+* A) [IsLocalHom ψ], IsEtaleCompletion ψ → ringKrullDim A ≤ ringKrullDim O := by
  first | exact @GlobalTheory.ringKrullDim_le_of_isEtaleCompletion | exact GlobalTheory.ringKrullDim_le_of_isEtaleCompletion | (intros; apply GlobalTheory.ringKrullDim_le_of_isEtaleCompletion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalGaloisCoverOfFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalGaloisCoverOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GalCover

theorem exists_isCN_galois_of_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R] [IsDomain R] (b : A →+* R), IsCN A → b.Finite → Function.Injective b → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (θ : R →+* R'), IsCN R' ∧ IsLocalHom θ ∧ Function.Injective θ ∧ θ.Finite ∧ ∀ r : R, (∀ σ : R' ≃+* R', IsOfFinOrder σ → (∀ a, σ (θ (b a)) = θ (b a)) → σ (θ r) = θ r) → r ∈ b.range := by
  intro A R _ _ _ _ _ b hA hfin hinj
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hA
  letI : Algebra A R := b.toAlgebra
  haveI : Module.Finite A R := hfin
  haveI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  let K := FractionRing A
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  let Ω := AlgebraicClosure K
  have hιK : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K)
  haveI : Module.IsTorsionFree A R := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree A Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hιK
  haveI : Algebra.IsAlgebraic A R := Algebra.IsIntegral.isAlgebraic
  let φ : R →ₐ[A] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hφinj : Function.Injective φ := by
    have hk : (RingHom.ker (φ : R →+* Ω)).comap (algebraMap A R) = ⊥ := by
      refine eq_bot_iff.2 fun a ha => ?_
      have h1 : φ (algebraMap A R a) = 0 := ha
      rw [φ.commutes] at h1
      exact (Ideal.mem_bot).2 (hιK (h1.trans (map_zero _).symm))
    have h2 := Ideal.eq_bot_of_under_eq_bot hk
    exact (RingHom.injective_iff_ker_eq_bot _).2 h2
  have hint : ∀ x : R, IsIntegral A (φ x) := fun x => (Algebra.IsIntegral.isIntegral (R := A) x).map φ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := R)
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((φ '' (s : Set R)) : Set Ω)
  have hintK : ∀ x : R, IsIntegral K (φ x) := fun x => (hint x).tower_top
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨x, -, rfl⟩
    exact hintK x)
  have hmemL : ∀ x : R, φ x ∈ L := fun x => by
    have hx : x ∈ Submodule.span A (s : Set R) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem L
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [map_smul, Algebra.smul_def]
      refine mul_mem ?_ hy
      rw [IsScalarTower.algebraMap_apply A K Ω]
      exact L.algebraMap_mem _
  let M : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  have hmem : ∀ x : R, φ x ∈ M := fun x => IntermediateField.le_normalClosure L (hmemL x)
  let W := integralClosure A M
  haveI hWf : Module.Finite A W := IsIntegralClosure.finite A K M W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := A) W
  have hAM : Function.Injective (algebraMap A M) := by
    rw [IsScalarTower.algebraMap_eq A K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective A K)
  have hinjW : Function.Injective (algebraMap A W) := fun x y h => hAM (congrArg Subtype.val h)
  let φM : R →+* M := (φ : R →+* Ω).codRestrict M hmem
  have hran : ∀ x : R, φM x ∈ W := fun x => by
    show IsIntegral A (φM x)
    exact (isIntegral_algHom_iff ((IntermediateField.val M).restrictScalars A) Subtype.val_injective).1 (hint x)
  let θ : R →+* W := φM.codRestrict W hran
  have hθval : ∀ x : R, (((θ x : M)) : Ω) = φ x := fun x => rfl
  have hθinj : Function.Injective θ := fun x y h => hφinj (by
    rw [← hθval, ← hθval, h])
  have hcomm : θ.comp b = algebraMap A W := RingHom.ext fun a => by
    apply Subtype.val_injective
    apply Subtype.val_injective
    exact φ.commutes a
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have hθfin : θ.Finite := RingHom.Finite.of_comp_finite (f := b) (by rw [hcomm]; exact RingHom.finite_algebraMap.2 hWf)
  have hθloc : IsLocalHom θ := RingHom.IsIntegral.isLocalHom hθfin.to_isIntegral hθinj

  let res : (M ≃ₐ[K] M) →* (W ≃+* W) :=
    { toFun := fun σ =>
        { toFun := fun x => ⟨σ (x : M), x.2.map ((σ : M →ₐ[K] M).restrictScalars A)⟩
          invFun := fun x => ⟨σ.symm (x : M), x.2.map ((σ.symm : M →ₐ[K] M).restrictScalars A)⟩
          left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : M))
          right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : M))
          map_mul' := fun x y => Subtype.ext (map_mul σ (x : M) y)
          map_add' := fun x y => Subtype.ext (map_add σ (x : M) y) }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨W, inferInstance, inferInstance, inferInstance, θ,
    ⟨IsNoetherianRing.of_finite A W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local A W, inferInstance⟩,
    hθloc, hθinj, hθfin, fun r hr => ?_⟩
  have hfix : ∀ σ : M ≃ₐ[K] M, σ (θ r : M) = (θ r : M) := fun σ => by
    have h1 := hr (res σ) (res.isOfFinOrder (isOfFinOrder_of_finite σ)) (fun a => by
      rw [← RingHom.comp_apply θ b, hcomm]
      apply Subtype.ext
      show σ (algebraMap A M a) = algebraMap A M a
      rw [IsScalarTower.algebraMap_apply A K M]
      exact σ.commutes _)
    exact congrArg Subtype.val h1
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (θ r : M)).2 hfix
  have hkint : IsIntegral A k := by
    have : IsIntegral A (algebraMap K M k) := hk ▸ (θ r).2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K M) (algebraMap K M).injective).1 this
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hkint
  refine ⟨a, hφinj ?_⟩
  show φ (algebraMap A R a) = φ r
  rw [φ.commutes, ← hθval, ← hk, ← ha, IsScalarTower.algebraMap_apply A K Ω]
  rfl

end GlobalTheory.GalCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalGaloisCoverOfFiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeNormal_galois_cover_of_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R] [IsDomain R] (b : A →+* R), IsCN A → b.Finite → Function.Injective b → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (θ : R →+* R'), IsCN R' ∧ IsLocalHom θ ∧ Function.Injective θ ∧ θ.Finite ∧ ∀ r : R, (∀ σ : R' ≃+* R', IsOfFinOrder σ → (∀ a, σ (θ (b a)) = θ (b a)) → σ (θ r) = θ r) → r ∈ b.range := by
  first | exact @GlobalTheory.GalCover.exists_isCN_galois_of_finite | exact GlobalTheory.GalCover.exists_isCN_galois_of_finite | (intros; apply GlobalTheory.GalCover.exists_isCN_galois_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCompletionOfQuasiFiniteGaloisRigid
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QFEtale

theorem isEtaleCompletion_of_galRigid : ∀ (O R : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (f : O →+* R) [IsLocalHom f], IsAdicComplete (maximalIdeal R) R → (∀ p : Ideal R, p.IsPrime → (maximalIdeal O).map f ≤ p → p = maximalIdeal R) → ((residue R).comp f).Finite → ringKrullDim O ≤ ringKrullDim R → GalRigid f → IsEtaleCompletion f ∧ ((residue R).comp f).FormallyUnramified := by
  intro O R _ _ _ _ _ _ _ _ _ _ f _ hRc hqf hfin hdim hrig
  haveI hOn : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  letI : Algebra (ResidueField O) (ResidueField R) := (ResidueField.map f).toAlgebra
  have hres : (residue R).comp f = (ResidueField.map f).comp (residue O) := by
    ext o; simp [ResidueField.map_residue]
  have hfin' : (ResidueField.map f).Finite := by
    rw [hres] at hfin; exact RingHom.Finite.of_comp_finite hfin
  haveI : Module.Finite (ResidueField O) (ResidueField R) := hfin'
  let M := separableClosure (ResidueField O) (ResidueField R)
  let m : ResidueField O →+* M := algebraMap (ResidueField O) M
  have hmf : m.Finite := RingHom.finite_algebraMap.2 inferInstance
  haveI : Algebra.IsSeparable (ResidueField O) M := inferInstance
  haveI : Algebra.FormallyUnramified (ResidueField O) M := Algebra.FormallyUnramified.of_isSeparable _ _
  have hmu : m.FormallyUnramified := RingHom.formallyUnramified_algebraMap.2 inferInstance
  obtain ⟨A, _, _, _, ψ, hψl, E, hAcn, hψe, hψu, hE⟩ := GlobalTheory.T.exists_etaleCompletion_with_residueField_equiv O M m hmf hmu
  obtain ⟨hAn, hAi, hAc, hA0⟩ := hAcn
  let u' : A →+* ResidueField R := (algebraMap M (ResidueField R)).comp ((E.symm : ResidueField A →+* M).comp (residue A))
  have hu' : ∀ a, u' a = 0 ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff _ (algebraMap M (ResidueField R)).injective,
      map_eq_zero_iff _ E.symm.injective]
  have hker : RingHom.ker u' = maximalIdeal A := by ext a; exact hu' a
  have hc : (residue R).comp f = u'.comp ψ := by
    ext o
    have h1 := RingHom.congr_fun hE (residue O o)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ResidueField.map_residue] at h1
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ← h1, RingEquiv.symm_apply_apply, m]
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.EtaleCompletionLift.exists_extension O A R (ResidueField R) ψ f u' (residue R) hψe hψu hRc
    inferInstance hker (ker_residue) hc (fun r => residue_surjective _)
  have hbm : ∀ a, b a ∈ maximalIdeal R ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff, ← hu', ← RingHom.comp_apply, hb2]
  haveI hbl : IsLocalHom b := ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((hbm a).2 ((mem_maximalIdeal a).2 h)) ha⟩
  have hbfin : b.Finite := by
    refine GlobalTheory.T.ringHom_finite_of_quasiFinite_complete_local A R b hAc (fun p hp h => hqf p hp ?_) ?_
    · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact h
    · refine RingHom.Finite.of_comp_finite (f := ψ) ?_
      rw [RingHom.comp_assoc, hb1]; exact hfin
  have hbinj : Function.Injective b := GlobalTheory.T.injective_of_finite_of_ringKrullDim_le' A R b hbfin ((GlobalTheory.T.ringKrullDim_le_of_isEtaleCompletion' O A ψ hψe).trans hdim)
  obtain ⟨R', _, _, _, θ, hR'cn, hθl, hθi, hθf, hfix⟩ := GlobalTheory.T.exists_completeNormal_galois_cover_of_finite A R b ⟨hAn, hAi, hAc, hA0⟩ hbfin hbinj
  let q := ringExpChar M
  haveI : ExpChar M q := ringExpChar.expChar M
  haveI : ExpChar (ResidueField R) q := expChar_of_injective_algebraMap (algebraMap M (ResidueField R)).injective q
  have hpi : ∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a) := by
    intro x
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem M q x
    obtain ⟨a, ha⟩ := residue_surjective (E y)
    refine ⟨n, a, ?_⟩
    rw [← RingHom.comp_apply, hb2, ← hy]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ha, RingEquiv.symm_apply_apply]
  have hbsurj : Function.Surjective b := by
    intro r
    refine hfix r fun σ hσ hσb => hrig R' θ σ hR'cn hθi hθf hσ (fun o => ?_) (fun r => GlobalTheory.T.ringEquiv_sub_mem_maximalIdeal_of_purelyInsep_residue A R R' b θ q σ hpi hσb r) r
    rw [← hb1]; exact hσb (ψ o)
  have hmapsurj : Function.Surjective (ResidueField.map b) := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hbsurj r
    exact ⟨residue A a, ResidueField.map_residue _ _⟩
  have hres2 : (residue R).comp f = (ResidueField.map b).comp ((residue A).comp ψ) := by
    rw [← hb1]; ext o; simp [ResidueField.map_residue]
  refine ⟨⟨?_, ?_, hfin⟩, ?_⟩
  · rw [← hb1]; exact RingHom.Flat.comp hψe.1 (RingHom.Flat.of_bijective ⟨hbinj, hbsurj⟩)
  · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact map_maximalIdeal_of_surjective b hbsurj
  · rw [hres2]; exact RingHom.FormallyUnramified.comp hψu (RingHom.FormallyUnramified.of_surjective hmapsurj)

end GlobalTheory.QFEtale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCompletionOfQuasiFiniteGaloisRigidStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCompletion_of_quasiFinite_galoisRigid : ∀ (O R : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (f : O →+* R) [IsLocalHom f], IsAdicComplete (maximalIdeal R) R → (∀ p : Ideal R, p.IsPrime → (maximalIdeal O).map f ≤ p → p = maximalIdeal R) → ((residue R).comp f).Finite → ringKrullDim O ≤ ringKrullDim R → GalRigid f → IsEtaleCompletion f ∧ ((residue R).comp f).FormallyUnramified := by
  first | exact @GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid | exact GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid | (intros; apply GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid <;> assumption)
end
