module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateFromSandwich
public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictlySemistableChartAtOfSmooth
section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsStrictlySemistableIff
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SSG

def ChartAt {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton
      ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
        MvPolynomial.C ϖ))) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.SSG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictlySemistableChartAtOfSmooth
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SmChart

open MvPolynomial

noncomputable def subst {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (i : Fin (n + 1)) : MvPolynomial (Fin n) O :=
  Fin.cases (C ϖ) (fun j => X j) i

theorem prod_lt_one {O : Type} [CommRing O] (n : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), (X i : MvPolynomial (Fin (n + 1)) O)) = X 0 := by
  have : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1) = {0} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact Fin.ext (by simpa using h)
    · rintro rfl; simp
  rw [this, Finset.prod_singleton]

noncomputable abbrev gen {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Ideal (MvPolynomial (Fin (n + 1)) O) :=
  Ideal.span {X 0 - C ϖ}

theorem subst_vanish {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    ∀ a ∈ gen ϖ n, (aeval (subst ϖ n)).toRingHom a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  simp [subst, algebraMap_eq]

noncomputable def quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) →+* MvPolynomial (Fin n) O :=
  Ideal.Quotient.lift _ (aeval (subst ϖ n)).toRingHom (subst_vanish ϖ n)

noncomputable def quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    MvPolynomial (Fin n) O →+* (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) :=
  (Ideal.Quotient.mk _).comp (rename Fin.succ).toRingHom

theorem quotMap_mk {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (a : MvPolynomial (Fin (n + 1)) O) :
    quotMap ϖ n (Ideal.Quotient.mk _ a) = aeval (subst ϖ n) a := rfl

theorem quotMap_quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (quotInv ϖ n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    simp [quotInv, quotMap_mk, subst]

theorem quotInv_quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotInv ϖ n).comp (quotMap ϖ n) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [RingHom.comp_apply, quotMap_mk, aeval_X, subst, Fin.cases_zero, RingHom.id_apply]
      simp only [quotInv, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_C]
      rw [Ideal.Quotient.eq]
      rw [← neg_sub]; exact neg_mem (Ideal.subset_span rfl)
    · simp [quotInv, quotMap_mk, subst]

theorem quotMap_bijective {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Function.Bijective (quotMap ϖ n) :=
  ⟨Function.LeftInverse.injective (g := quotInv ϖ n) (fun a => congr($(quotInv_quotMap ϖ n) a)),
    Function.RightInverse.surjective (g := quotInv ϖ n) (fun a => congr($(quotMap_quotInv ϖ n) a))⟩

theorem quotMap_algebraMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (algebraMap O _) = C := by
  refine RingHom.ext fun c => ?_
  change quotMap ϖ n (Ideal.Quotient.mk _ (C c)) = C c
  rw [quotMap_mk, aeval_C, algebraMap_eq]

end GlobalTheory.SmChart


open GlobalTheory.SmChart in
theorem GlobalTheory.SSG.chartAt_of_smooth : ∀ (O : Type) [CommRing O] (ϖ : O) (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (x : X), x ∈ V → Smooth (V.ι ≫ p) →
    GlobalTheory.SSG.ChartAt ϖ p x := by
  intro O _ ϖ X p V x hx hsm
  set f := V.ι ≫ p with hf
  let x' : V.toScheme := ⟨x, hx⟩
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.toScheme.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x')
  have hW : IsAffineOpen W := hW
  have e : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hφ : (f.appLE ⊤ W e).hom.Smooth := f.smooth_appLE (isAffineOpen_top _) hW e
  rw [RingHom.smooth_iff_locally_isStandardSmooth,
    RingHom.locally_iff_isLocalization RingHom.isStandardSmooth_respectsIso] at hφ
  obtain ⟨s, hs, hfs⟩ := hφ
  have hs' := iSup_basicOpen_of_span_eq_top W (s : Set Γ(V.toScheme, W)) hs
  have hmem : x' ∈ (⨆ i ∈ (s : Set Γ(V.toScheme, W)), V.toScheme.basicOpen i) := hs'.symm ▸ hxW
  obtain ⟨r, hr, hxr⟩ : ∃ r ∈ s, x' ∈ V.toScheme.basicOpen r := by simpa using hmem
  have hW' : IsAffineOpen (V.toScheme.basicOpen r) := hW.basicOpen r
  have e' : V.toScheme.basicOpen r ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  haveI : IsLocalization.Away r Γ(V.toScheme, V.toScheme.basicOpen r) := hW.isLocalization_basicOpen r
  have hst : (f.appLE ⊤ _ e').hom.IsStandardSmooth := by
    rw [← f.appLE_map e (homOfLE (V.toScheme.basicOpen_le r)).op]
    exact hfs r hr _
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hst
  let c : O →+* Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hc : Function.Bijective c := (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.bijective
  let k := V.ι.appIso (V.toScheme.basicOpen r)
  have hk : Function.Bijective k.inv.hom := k.symm.commRingCatIsoToRingEquiv.bijective
  have hU : IsAffineOpen (V.ι ''ᵁ V.toScheme.basicOpen r) := hW'.image_of_isOpenImmersion V.ι
  have hxU : x ∈ V.ι ''ᵁ V.toScheme.basicOpen r := ⟨x', hxr, rfl⟩
  have hcomp : p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top ≫ k.hom = f.appLE ⊤ _ e' := by
    have h1 := Scheme.Hom.appLE_comp_appLE V.ι p ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) (V.toScheme.basicOpen r)
      le_top (V.ι.preimage_image_eq _).ge
    have h2 : k.hom = V.ι.appLE _ _ (V.ι.preimage_image_eq _).ge := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]; rfl
    rw [h2]; exact h1
  refine ⟨_, hU, hxU, n + 1, 1, le_rfl, by omega, ?_⟩
  rw [prod_lt_one]
  refine ⟨k.inv.hom.comp (g.comp ((MvPolynomial.map c).comp (quotMap ϖ n))), ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _
        (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (quotMap_bijective ϖ n))
          (RingHom.Etale.of_bijective ⟨MvPolynomial.map_injective _ hc.1, MvPolynomial.map_surjective _ hc.2⟩))
        hg) (RingHom.Etale.of_bijective hk)
  · refine RingHom.ext fun a => ?_
    change k.inv.hom (g (MvPolynomial.map c (quotMap ϖ n (algebraMap O _ a)))) =
      (p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top).hom (c a)
    rw [show quotMap ϖ n (algebraMap O _ a) = MvPolynomial.C a from congr($(quotMap_algebraMap ϖ n) a),
      MvPolynomial.map_C, show g (MvPolynomial.C (c a)) = (f.appLE ⊤ _ e').hom (c a) from congr($hgC (c a)),
      ← hcomp]
    simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictlySemistableChartAtOfSmoothStatement
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasStrictlySemistableChartAt_of_smooth : ∀ (O : Type) [CommRing O] (ϖ : O) (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (x : X), x ∈ V → Smooth (V.ι ≫ p) → GlobalTheory.SSG.ChartAt ϖ p x := by
  first | (exact @GlobalTheory.SSG.chartAt_of_smooth) | (exact GlobalTheory.SSG.chartAt_of_smooth) | (intros; apply GlobalTheory.SSG.chartAt_of_smooth  <;> assumption)
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace Sp spMap IsProjOver)

def retractPt (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    Spec (CommRingCat.of (OK l K)) ⟶ PSpace (OK l K) 2 :=
  GlobalTheory.ProjSpace.pt (RingHom.id (OK l K)) (fun _ => 1)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one)

theorem retractPt_str (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    retractPt l K ≫ PSpace.str (OK l K) 2 = 𝟙 _ := by
  have hstr : ∀ (v : Fin (2 + 1) → OK l K) (hv : Ideal.span (Set.range v) = ⊤),
      GlobalTheory.ProjSpace.pt (RingHom.id (OK l K)) v hv ≫ PSpace.str (OK l K) 2 =
        spMap (RingHom.id (OK l K)) := by
    intro v hv
    rw [GlobalTheory.ProjSpace.pt, PSpace.str, GlobalTheory.ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C _ v r
  rw [retractPt, hstr]
  simp [spMap]

theorem retract_pf : Retract := by
  intro l _ K _ M d hM hd
  let N : Model l K := ⟨pullback M.p (PSpace.str (OK l K) 2), pullback.fst _ _ ≫ M.p⟩
  have h2 : SmoothOfRelativeDimension 2 (pullback.fst M.p (PSpace.str (OK l K) 2)) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 2)
    MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 2) _ _
      (GlobalTheory.Adelic.smoothOfRelativeDimension_pspace _ 2)
  have hN : SmoothOfRelativeDimension (d + 1 + 1) N.p := by
    have := h2
    have := hd
    have : SmoothOfRelativeDimension (2 + d) (pullback.fst M.p (PSpace.str (OK l K) 2) ≫ M.p) :=
      smoothOfRelativeDimension_comp 2 d _ _
    rw [show d + 1 + 1 = 2 + d by omega]
    exact this
  have hsm : Smooth N.p := SmoothOfRelativeDimension.smooth (d + 1 + 1) N.p
  obtain ⟨⟨hproj, ϖ, hϖ, -⟩, -⟩ := hM
  refine ⟨N, pullback.fst _ _, pullback.lift (𝟙 _) (M.p ≫ retractPt l K) ?_, rfl, pullback.lift_fst _ _ _,
    ⟨⟨?_, ϖ, hϖ, ?_⟩, hsm⟩, hN⟩
  · rw [Category.assoc, retractPt_str, Category.comp_id, Category.id_comp]
  · exact GlobalTheory.ProjSpace.isProjOver_pullback hproj (GlobalTheory.ProjSpace.isProjOver_pspace_str _ 2)
  · intro x
    exact GlobalTheory.T.hasStrictlySemistableChartAt_of_smooth _ ϖ N.X N.p ⊤ x trivial inferInstance

end CrystallineSemistableComparison.Onto

end
