module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealOfFlatStalkPullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAdding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanSupPowOfForallCompleteDvrLocalTest
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanSupPowOfForallCompleteDvrLocalTest
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem dvd_of_forall_mem_span_sup_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {x y : V} (hx : x ≠ 0) (h : ∀ e, y ∈ Ideal.span {x} ⊔ maximalIdeal V ^ e) : x ∣ y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  have hs : Ideal.span {x} = maximalIdeal V ^ k := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hk
  have := h k
  rw [← hs, sup_idem] at this
  exact Ideal.mem_span_singleton.mp this

theorem mem_span_sup_pow_of_forall_complete_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (g : O) (b : ℕ → O), g ≠ 0 → (∀ m n, m ≤ n → b m - b n ∈ maximalIdeal O ^ m) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ ρ : O →+* V, Function.Injective ρ → IsLocalHom ρ → ∀ e, ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e) → ∀ n, b n ∈ Ideal.span {g} ⊔ maximalIdeal O ^ n := by
  intro O _ _ _ _ _ _ g b hg hb hV n
  haveI : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  set m := maximalIdeal O with hm
  let R := AdicCompletion m O
  let ι : O →+* R := algebraMap O R
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion O m
  obtain ⟨hdom, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed O
  have fg : m.FG := m.fg_of_isNoetherianRing
  haveI : Module.Flat O R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsLocalHom (algebraMap O R) := AdicCompletion.algebraMap_isLocalHom_of_fg fg
  haveI : Module.FaithfullyFlat O R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective ι := FaithfulSMul.algebraMap_injective O R
  haveI : CharZero R := charZero_of_injective_ringHom hinj
  have hmR : maximalIdeal R = m.map ι := AdicCompletion.maximalIdeal_eq_map

  have hc : IsAdicComplete (m.map ι) R := AdicCompletion.isAdicComplete_self m fg
  obtain ⟨F, hF⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := fun k => ι (b k)) (by
    intro k l hkl
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hb k l hkl))
  have hF' : ∀ k, ι (b k) - F ∈ maximalIdeal R ^ k := by
    intro k
    have := hF k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← hmR] at this

  have hgR : ι g ≠ 0 := fun h => hg (hinj (by rw [h, map_zero]))
  have hdvd : ι g ∣ F := by
    refine GlobalTheory.T.dvd_of_forall_complete_dvr_dominating R F (ι g) hgR ?_
    intro V _ _ _ hVc ρ' hρ' _
    let ρ : O →+* V := ρ'.comp ι
    have hρ : Function.Injective ρ := hρ'.comp hinj
    haveI : IsLocalHom ρ := inferInstance
    haveI : CharZero V := charZero_of_injective_ringHom hρ
    have hgV : ρ' (ι g) ≠ 0 := fun h => hgR (hρ' (by rw [h, map_zero]))
    refine dvd_of_forall_mem_span_sup_pow hgV fun e => ?_
    have h1 : ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e := hV V hVc ρ hρ inferInstance e
    have hmap : ∀ x ∈ maximalIdeal R, ρ' x ∈ maximalIdeal V := by
      intro x hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      exact fun h => hx (isUnit_of_map_unit ρ' x h)
    have h2 : ρ' (ι (b e) - F) ∈ maximalIdeal V ^ e := by
      have hle : (maximalIdeal R ^ e).map ρ' ≤ maximalIdeal V ^ e := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hmap) e
      exact hle (Ideal.mem_map_of_mem _ (hF' e))
    have : ρ' F = ρ (b e) - ρ' (ι (b e) - F) := by
      simp [ρ, map_sub]
    rw [this]
    exact Ideal.sub_mem _ h1 (Ideal.mem_sup_right h2)

  have hmem : ι (b n) ∈ (Ideal.span {g} ⊔ m ^ n).map ι := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow, ← hmR]
    have h3 : F ∈ Ideal.span {ι g} := Ideal.mem_span_singleton.mpr hdvd
    have : ι (b n) = F + (ι (b n) - F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right (hF' n))
  rwa [← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanSupPowOfForallCompleteDvrLocalTestStatement
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_sup_pow_of_forall_complete_dvr_local_test : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (g : O) (b : ℕ → O), g ≠ 0 → (∀ m n, m ≤ n → b m - b n ∈ maximalIdeal O ^ m) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ ρ : O →+* V, Function.Injective ρ → IsLocalHom ρ → ∀ e, ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e) → ∀ n, b n ∈ Ideal.span {g} ⊔ maximalIdeal O ^ n := by
  first | exact @GlobalTheory.Poinc.mem_span_sup_pow_of_forall_complete_dvr | exact GlobalTheory.Poinc.mem_span_sup_pow_of_forall_complete_dvr | (intros; apply GlobalTheory.Poinc.mem_span_sup_pow_of_forall_complete_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemIdealSheafStalkOfClosedFibreUnivClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemIdealSheafStalkOfClosedFibreUnivClosed
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.SpreadIdeal

theorem exists_open_nhds_mem_stalkId (P : Scheme.{0}) (I : P.IdealSheafData) (s : Γ(P, ⊤)) (v : P)
    (hv : (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) :
    ∃ O : P.Opens, v ∈ O ∧ ∀ y ∈ O, (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
  obtain ⟨U, hU, hvU, -⟩ := exists_isAffineOpen_mem_and_subset (x := v) (U := ⊤) trivial
  letI : Algebra Γ(P, U) (P.presheaf.stalk v) := P.presheaf.algebra_section_stalk ⟨v, hvU⟩
  haveI hlocv := hU.isLocalization_stalk ⟨v, hvU⟩
  set t : Γ(P, U) := P.presheaf.map (homOfLE le_top).op s with ht
  have hgerm : ∀ (y : P) (hy : y ∈ U), (P.presheaf.germ ⊤ y trivial).hom s =
      (P.presheaf.germ U y hy).hom t := fun y hy => by
    rw [ht, ← CommRingCat.comp_apply, P.presheaf.germ_res]
  rw [hgerm v hvU, ds_stalkId_eq_map I ⟨U, hU⟩ v hvU] at hv
  change algebraMap Γ(P, U) (P.presheaf.stalk v) t ∈
    Ideal.map (algebraMap Γ(P, U) (P.presheaf.stalk v)) (I.ideal ⟨U, hU⟩) at hv
  obtain ⟨⟨a, w⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff
    (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl _).mp hv
  rw [← map_mul] at e
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl) e
  set σ : Γ(P, U) := (c : Γ(P, U)) * w with hσ
  have hσt : σ * t ∈ I.ideal ⟨U, hU⟩ := by
    rw [hσ, show (c : Γ(P, U)) * w * t = c * (t * w) by ring, hc]
    exact Ideal.mul_mem_left _ _ a.2
  have hσunit : IsUnit (algebraMap Γ(P, U) (P.presheaf.stalk v) σ) :=
    IsLocalization.map_units (M := (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl) _
      (c * w : (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl)
  refine ⟨P.basicOpen σ, ?_, fun y hy => ?_⟩
  · exact (P.mem_basicOpen σ v hvU).mpr hσunit
  · have hyU : y ∈ U := P.basicOpen_le σ hy
    have hyu : IsUnit ((P.presheaf.germ U y hyU).hom σ) := (P.mem_basicOpen σ y hyU).mp hy
    rw [hgerm y hyU, ← Ideal.unit_mul_mem_iff_mem _ hyu, ← map_mul,
      ds_stalkId_eq_map I ⟨U, hU⟩ y hyU]
    exact Ideal.mem_map_of_mem _ hσt

end GlobalTheory.SpreadIdeal

namespace GlobalTheory.SpreadIdeal

theorem mem_stalkId_of_closedFibre : ∀ (P : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (p : P ⟶ Sp R) [UniversallyClosed p] (I : P.IdealSheafData) (s : Γ(P, ⊤)), (∀ v : P, p v = closedPoint R → (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) → ∀ v : P, (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  intro P R _ _ p _ I s hs v
  by_contra hv
  set Z : Set P := {y | (P.presheaf.germ ⊤ y trivial).hom s ∉ FinalTheorems.stalkId I y} with hZ
  have hZc : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    have hy' : (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
      simpa [hZ] using hy
    obtain ⟨O, hyO, hO⟩ := exists_open_nhds_mem_stalkId P I s y hy'
    exact ⟨O, fun z hz => by simpa [hZ] using hO z hz, O.2, hyO⟩
  have himg : IsClosed (p.base '' Z) := p.isClosedMap _ hZc
  have hmem : closedPoint R ∈ p.base '' Z :=
    (IsLocalRing.specializes_closedPoint (p.base v)).mem_closed himg ⟨v, hv, rfl⟩
  obtain ⟨w, hwZ, hw⟩ := hmem
  exact hwZ (hs w hw)

end GlobalTheory.SpreadIdeal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemIdealSheafStalkOfClosedFibreUnivClosedStatement
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_mem_idealSheaf_stalk_of_closedFibre_univClosed : ∀ (P : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (p : P ⟶ Sp R) [UniversallyClosed p] (I : P.IdealSheafData) (s : Γ(P, ⊤)), (∀ v : P, p v = closedPoint R → (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) → ∀ v : P, (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  first | exact @GlobalTheory.SpreadIdeal.mem_stalkId_of_closedFibre | exact GlobalTheory.SpreadIdeal.mem_stalkId_of_closedFibre | (intros; apply GlobalTheory.SpreadIdeal.mem_stalkId_of_closedFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionApproximateIdealSections
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.ApproxCorr

theorem map_mem_pow {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    {n : ℕ} {a : A} (h : a ∈ maximalIdeal A ^ n) : φ a ∈ maximalIdeal B ^ n := by
  have h1 := Ideal.mem_map_of_mem φ h
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le φ) n h1

theorem mem_of_forall_mem_sup {C : Type} [CommRing C] [IsLocalRing C] [IsNoetherianRing C] (I : Ideal C) (c : C)
    (h : ∀ n : ℕ, c ∈ I ⊔ maximalIdeal C ^ n) : c ∈ I := by
  have k := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := C ⧸ I) (maximalIdeal C) (maximalIdeal.isMaximal C).ne_top
  have : Submodule.mkQ I c ∈ (⊥ : Submodule C (C ⧸ I)) := by
    rw [← k, Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h n)
    have e : Submodule.mkQ I (a + b) = b • Submodule.mkQ I 1 := by
      rw [map_add (f := _), ← map_smul, smul_eq_mul, mul_one, (Submodule.Quotient.mk_eq_zero I).2 ha |> (Submodule.mkQ_apply I a).trans,
        zero_add]
    rw [e]
    exact Submodule.smul_mem_smul hb trivial
  exact (Submodule.Quotient.mk_eq_zero I).1 ((Submodule.mem_bot C).1 this)

theorem exists_stalk_map {Z S : Scheme.{0}} (π : S ⟶ Z) (x : S) (z : Z) (h : π x = z) :
    ∃ ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x, IsLocalHom ψ ∧
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π := by
  subst h
  exact ⟨(π.stalkMap x).hom, π.toLRSHom.prop x, Scheme.SpecMap_stalkMap_fromSpecStalk π⟩

theorem mem_map_of_approx {Z S : Scheme.{0}} (π : S ⟶ Z) [IsProper π] (I : S.IdealSheafData) (z : Z)
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (i : Z.presheaf.stalk z →+* R) [IsLocalHom i] (hi : i.Flat)
    (F : R) (a : ℕ → Z.presheaf.stalk z) (ha : ∀ n, F - i (a n) ∈ maximalIdeal R ^ n)
    (H : ∀ (x : S) (ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x), IsLocalHom ψ →
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π → ∀ n, ψ (a n) ∈ FinalTheorems.stalkId I x ⊔ maximalIdeal _ ^ n) :
    F ∈ (FinalTheorems.stalkId (I.map π) z).map i := by
  rw [← GlobalTheory.PolDiv.idlAlong_fromSpecStalk]
  generalize hξ : Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecStalk z = ξ
  have hfl : Flat ξ := by
    rw [← hξ]
    haveI := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk Z z
    haveI : Flat (Spec.map (CommRingCat.ofHom i)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hi
    infer_instance
  have hξc : ξ (closedPoint R) = z := by
    rw [← hξ]
    have : Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Z.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint i
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Z.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)
  refine GlobalTheory.FlatPush.mem_idlAlong_map_of_flat π I ξ ?_ F ?_
  · rw [Scheme.stalkClosedPointTo, CommRingCat.hom_comp]
    exact RingHom.Flat.comp (Flat.stalkMap ξ _) (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
  refine GlobalTheory.T.germ_mem_idealSheaf_stalk_of_closedFibre_univClosed _ R (Limits.pullback.fst ξ π) _ _ fun v hv => ?_
  haveI : IsLocallyNoetherian (Limits.pullback ξ π) := LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst ξ π)
  set p := Limits.pullback.fst ξ π with hp
  set q := Limits.pullback.snd ξ π with hq
  have hpq : p ≫ ξ = q ≫ π := Limits.pullback.condition
  have hx : π (q v) = z := by
    rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hv, hξc]
  obtain ⟨ψ, hψ, hψc⟩ := exists_stalk_map π (q v) z hx
  let α : CommRingCat.of R ⟶ (Limits.pullback ξ π).presheaf.stalk v :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p v) trivial) ≫ p.stalkMap v
  have hα : Spec.map α = (Limits.pullback ξ π).fromSpecStalk v ≫ p := by
    rw [Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
  haveI : IsLocalHom α.hom := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 ?_
    change Spec.map α (closedPoint _) = _
    rw [hα]
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg p Scheme.fromSpecStalk_closedPoint).trans hv)
  haveI : IsLocalHom (q.stalkMap v).hom := q.toLRSHom.prop v
  have hc : CommRingCat.ofHom i ≫ α = CommRingCat.ofHom ψ ≫ q.stalkMap v := by
    refine Spec.map_injective ((cancel_mono (Z.fromSpecStalk z)).1 ?_)
    rw [Spec.map_comp _ α, Spec.map_comp _ (q.stalkMap v), Category.assoc, Category.assoc, hξ, hα, Category.assoc, hpq]
    erw [hψc]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  have hc' : ∀ t, α.hom (i t) = (q.stalkMap v).hom (ψ t) := fun t => congrArg (fun f => f.hom t) hc
  have e : ((Limits.pullback ξ π).presheaf.germ ⊤ v trivial).hom (p.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom F)) = α.hom F :=
    (Scheme.Hom.germ_stalkMap_apply p ⊤ v trivial _).symm
  rw [e]
  refine mem_of_forall_mem_sup _ _ fun n => ?_
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 (H (q v) ψ hψ hψc n)
  have e2 : α.hom F = (q.stalkMap v).hom b + ((q.stalkMap v).hom c + α.hom (F - i (a n))) := by
    rw [← add_assoc, ← map_add (f := _), hbc, ← hc', map_sub]; ring
  rw [e2]
  exact Submodule.add_mem_sup (GlobalTheory.VanStalk.map_le_stalkId_comap q I v (Ideal.mem_map_of_mem _ hb))
    (add_mem (map_mem_pow _ hc) (map_mem_pow _ (ha n)))

theorem charZero_essFiniteType {S : Scheme.{0}} (s : S ⟶ Sp ℤ) [Flat s] [LocallyOfFiniteType s] (x : S) :
    CharZero (S.presheaf.stalk x) ∧ Algebra.EssFiniteType ℤ (S.presheaf.stalk x) := by
  let y : PrimeSpectrum ℤ := s x
  letI A : Algebra ℤ ((Sp ℤ).presheaf.stalk (s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime ℤ _ ((Sp ℤ).presheaf.stalk (s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap ℤ ((Sp ℤ).presheaf.stalk (s x)) _ _ A
  have h₁ : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp ℤ).presheaf.stalk (s x)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsLocalHom (s.stalkMap x).hom := s.toLRSHom.prop x
  have hσ : Function.Injective (s.stalkMap x).hom := by
    have h := Flat.stalkMap s x
    algebraize [(s.stalkMap x).hom]
    have : IsLocalHom (algebraMap ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x)) := this
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp ℤ).presheaf.stalk (s x)) (B := S.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x)
  refine ⟨charZero_of_injective_ringHom (f := (s.stalkMap x).hom.comp φ) (hσ.comp hφ), ?_⟩
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert h₂.comp h₁ using 1
  exact Subsingleton.elim _ _

theorem range_subset {S : Scheme.{0}} [IsIntegral S] (U : S.Opens) (hU : (U : Set S).Nonempty) (x : S)
    {V : Type} [CommRing V] [IsDomain V] (ρ : S.presheaf.stalk x →+* V) (hρ : Function.Injective ρ) :
    Set.range (jK V ≫ spMap ρ ≫ S.fromSpecStalk x) ⊆ U := by
  rintro _ ⟨t, rfl⟩
  have hg : genericPoint S ∈ Set.range (S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes x
  obtain ⟨w, hw⟩ := hg
  have ht : (jK V ≫ spMap ρ) t ⤳ w := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_
    have h0 : algebraMap V (FractionRing V) (ρ r) ∈ t.asIdeal := hr
    have h1 : algebraMap V (FractionRing V) (ρ r) = 0 := by
      by_contra hne
      exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 (Ne.isUnit hne))
    have h2 : r = 0 := hρ (by rw [map_zero]; exact IsFractionRing.injective V (FractionRing V) (by rw [h1, map_zero]))
    rw [h2]; exact zero_mem _
  have h3 := ht.map (S.fromSpecStalk x).continuous
  rw [← Category.assoc, Scheme.Hom.comp_apply]
  have h4 : S.fromSpecStalk x ((jK V ≫ spMap ρ) t) = genericPoint S :=
    ((show _ ⤳ genericPoint S from hw ▸ h3).antisymm (genericPoint_specializes _)).eq
  rw [h4]
  exact ((genericPoint_spec S).mem_open_set_iff U.2).2 (by simpa using hU)

theorem exists_correction : ∀ (Z S : Scheme.{0}) [IsIntegral Z] [IsIntegral S] (sZ : Z ⟶ Sp ℤ) [LocallyOfFiniteType sZ] [QuasiCompact sZ] (π : S ⟶ Z) [IsProper π] [IsDominant π] [Flat (π ≫ sZ)], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (E : GlobalTheory.EffCartierData S) (z : Z) (k : ℕ), ∃ e : ℕ, ∀ f : Z.presheaf.stalk z, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev → spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U → ev f ∈ idlAlong E.idealSheaf ξ ⊔ ((maximalIdeal _).map ev) ^ e) → f ∈ FinalTheorems.stalkId (E.idealSheaf.map π) z ⊔ maximalIdeal _ ^ k := by
  intro Z S _ _ sZ _ _ π _ _ _ hS U hU E z k
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  let K : ℕ → Ideal (Z.presheaf.stalk z) := fun e =>
    { carrier := {f | ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev →
        spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U →
        ev f ∈ idlAlong E.idealSheaf ξ ⊔ ((maximalIdeal _).map ev) ^ e}
      add_mem' := fun ha hb V _ _ _ _ hV ξ ev h1 h2 h3 => by
        rw [map_add]; exact add_mem (ha V hV ξ ev h1 h2 h3) (hb V hV ξ ev h1 h2 h3)
      zero_mem' := fun V _ _ _ _ hV ξ ev h1 h2 h3 => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun c a ha V _ _ _ _ hV ξ ev h1 h2 h3 => by
        rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ (ha V hV ξ ev h1 h2 h3) }
  refine GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone (Z.presheaf.stalk z) K (FinalTheorems.stalkId (E.idealSheaf.map π) z) ?_ ?_ ?_ k
  · intro m n hmn f hf V _ _ _ _ hV ξ ev h1 h2 h3
    exact (show _ ≤ (_ : Ideal V) from sup_le_sup_left (Ideal.pow_le_pow_right hmn) _) (hf V hV ξ ev h1 h2 h3)
  · intro e f hf V _ _ _ _ hV ξ ev h1 h2 h3
    refine Ideal.mem_sup_right ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hf
  intro F a ha hK
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ (maximalIdeal (Z.presheaf.stalk z))
  haveI : Module.FaithfullyFlat (Z.presheaf.stalk z) (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine mem_map_of_approx π E.idealSheaf z _ (RingHom.flat_algebraMap_iff.2 inferInstance) F a ha fun x ψ hψ hc => ?_
  obtain ⟨i, hi⟩ : ∃ i, x ∈ E.U i := TopologicalSpace.Opens.mem_iSup.1 (E.cover ▸ trivial)
  obtain ⟨h0, hft⟩ := charZero_essFiniteType (π ≫ sZ) x
  haveI := (hS x).2
  have hI := E.stalkId_idealSheaf i x hi
  rw [hI]
  refine GlobalTheory.T.mem_span_sup_pow_of_forall_complete_dvr_local_test (S.presheaf.stalk x) _ (fun n => ψ (a n))
    (nonZeroDivisors.ne_zero (GlobalTheory.Cartier.isRegularFn_iff_germ.1 (E.regular i) x hi)) ?_ ?_
  · intro m n hmn
    rw [← map_sub]
    refine map_mem_pow ψ ?_
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z))
      (maximalIdeal (Z.presheaf.stalk z) ^ m), Ideal.mem_comap, Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map, map_sub]
    have := sub_mem (Ideal.pow_le_pow_right hmn (ha n)) (ha m)
    rwa [sub_sub_sub_cancel_left] at this
  · intro V _ _ _ _ hV ρ hρ hl e
    have hl' : IsLocalHom (ρ.comp ψ) := inferInstance
    have h1 := hK e V hV (spMap ρ ≫ S.fromSpecStalk x) (ρ.comp ψ) hl' (by
      rw [Category.assoc, ← hc, ← Category.assoc, spMap, CommRingCat.ofHom_comp, Spec.map_comp]) (range_subset U hU x ρ hρ)
    rw [GlobalTheory.PolDiv.idlAlong_fromSpecStalk, hI, Ideal.map_span, Set.image_singleton] at h1
    exact (show _ ≤ (_ : Ideal V) from
      sup_le_sup_left (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le (ρ.comp ψ)) e) _) h1

end GlobalTheory.ApproxCorr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionApproximateIdealSectionsStatement
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_correction_approximate_ideal_sections : ∀ (Z S : Scheme.{0}) [IsIntegral Z] [IsIntegral S] (sZ : Z ⟶ Sp ℤ) [LocallyOfFiniteType sZ] [QuasiCompact sZ] (π : S ⟶ Z) [IsProper π] [IsDominant π] [Flat (π ≫ sZ)], IsNormalScheme S → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (E : GlobalTheory.EffCartierData S) (z : Z) (k : ℕ), ∃ e : ℕ, ∀ f : Z.presheaf.stalk z, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev → spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U → ev f ∈ idlAlong E.idealSheaf ξ ⊔ ((maximalIdeal _).map ev) ^ e) → f ∈ FinalTheorems.stalkId (E.idealSheaf.map π) z ⊔ maximalIdeal _ ^ k := by
  first | exact @GlobalTheory.ApproxCorr.exists_correction | exact GlobalTheory.ApproxCorr.exists_correction | (intros; apply GlobalTheory.ApproxCorr.exists_correction <;> assumption)
end
