module

public import Development.EtaleCohomology.EtaleSheaves.LeafTw0GenFreeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafInclPiecePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf LateralTheory.E.LeafInclDescendPf

namespace LateralTheory.E.LeafInclPiecePf

theorem incl_comp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1)
    (h : R ≤ R'') (h1' : R1 ≤ R'') : incl h1' ≫ incl h1 = incl h := by
  simp only [incl]
  rw [← Spec.map_comp]
  rfl

def lvl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R'')
    (h1' : R1 ≤ R'') {D : Scheme.{0}} (q : D ⟶ Sp R) : pullback q (incl h) ⟶ pullback q (incl h1) :=
  pullback.lift (pullback.fst q (incl h)) (pullback.snd q (incl h) ≫ incl h1') (by
    rw [pullback.condition, Category.assoc, incl_comp h1 h h1'])

def descMap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R'')
    (h1' : R1 ≤ R'') {DU DW : Scheme.{0}} (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R)
    (ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1)) (hψ : ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1)) :
    pullback qW (incl h) ⟶ pullback qU (incl h) :=
  pullback.lift (lvl h1 h h1' qW ≫ ψ ≫ pullback.fst qU (incl h1)) (pullback.snd qW (incl h)) (by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hψ, lvl, pullback.lift_snd_assoc, Category.assoc, incl_comp h1 h h1'])

theorem bcLift_lvl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1)
    (h : R ≤ R'') (h1' : R1 ≤ R'') {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D}
    (w : v ≫ q = g ≫ toR R) : bcLift h w ≫ lvl h1 h h1' q = bcLift h1 w := by
  apply pullback.hom_ext
  · unfold lvl bcLift
    rw [Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
  · unfold lvl bcLift
    rw [Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc, toR_eq]

def LeafInclMap : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R)),
    ∃ (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG ∧
      ∃ ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1),
        ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1) ∧
        bcLift h1 hW.w ≫ ψ = X.homOfLE hWU ≫ bcLift h1 hU.w

def LeafInclOpen : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R))
    (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG →
    ∀ (ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1))
      (hψ : ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1)),
      bcLift h1 hW.w ≫ ψ = X.homOfLE hWU ≫ bcLift h1 hU.w →
    ∃ R' : Subalgebra k Ω, R1 ≤ R' ∧ R'.FG ∧ ∀ (R'' : Subalgebra k Ω) (h : R ≤ R'') (h1' : R1 ≤ R''), R' ≤ R'' →
      IsOpenImmersion (descMap h1 h h1' qU qW ψ hψ)

theorem LeafInclPiece_of (hA : LeafInclMap) (hB : LeafInclOpen) : LeafInclPiece := by
  intro k _ Ω _ _ X f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R1, h1, hR1, ψ, hψ, hc⟩ := hA k Ω f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R', h1R', hR', H⟩ := hB k Ω f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW R1 h1 hR1 ψ hψ hc
  refine ⟨R', h1.trans h1R', hR', fun R'' h hR'' => ?_⟩
  have h1' : R1 ≤ R'' := h1R'.trans hR''
  refine ⟨descMap h1 h h1' qU qW ψ hψ, H R'' h h1' hR'', pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · simp only [descMap, Category.assoc, pullback.lift_fst]
    rw [reassoc_of% (bcLift_lvl h1 h h1' hW.w), reassoc_of% hc]
    unfold bcLift
    erw [pullback.lift_fst, pullback.lift_fst]
  · simp only [descMap, Category.assoc, pullback.lift_snd]
    unfold bcLift
    erw [pullback.lift_snd, pullback.lift_snd]
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc]

end LateralTheory.E.LeafInclPiecePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpreadLQFMapVtuPfG
namespace LateralTheory.E.LeafSpreadLQFMap_vtuPfG


open LateralTheory.E.SpreadingOutLocallyQuasiFinite in
theorem LeafSpreadLQFMap_of (hD : LeafQFAtDescend) (hO : LeafOpenSpread) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap :=
  LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafSpreadLQFMap_of quasi_finite_at_base_change_of_finite_type hD hO

end LateralTheory.E.LeafSpreadLQFMap_vtuPfG
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.OpenSpreadingOut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut Topology

namespace LateralTheory.E.OpenSpreadingOut

lemma toR_apply_bot {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    (toR R) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R Ω) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R Ω)

theorem etale_open_spreading_out_over_finitely_generated_subalgebra : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafOpenSpread := by
  intro k _ Ω _ _ R hR C A c p v U hp sq hU
  obtain ⟨hfp, hqc, hqs⟩ := hp
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : LocallyOfFiniteType p := inferInstance
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian A := {}
  have hZ : IsConstructible ((U : Set A)ᶜ) := by
    rw [isConstructible_compl]
    exact IsRetrocompact.isConstructible U.isOpen
      (fun W _ _ => TopologicalSpace.NoetherianSpace.isCompact _)
  have hI : IsConstructible (p '' (U : Set A)ᶜ) := p.isConstructible_image hZ
  have hT : IsConstructible (p '' (U : Set A)ᶜ)ᶜ := isConstructible_compl.mpr hI
  have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ (p '' (U : Set A)ᶜ)ᶜ := by
    rintro ⟨a, ha, hpa⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := toR R) a
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) (by rw [hpa, toR_apply_bot])
    apply ha
    have := hU (sq.isoPullback.inv z)
    rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz] at this
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.exists_basicOpen_subset_of_isConstructible_of_bot_mem hT hη
  have hs' : (s : Ω) ≠ 0 := fun h => hs0 (Subtype.ext h)
  refine ⟨R ⊔ Algebra.adjoin k {(s : Ω)⁻¹}, le_sup_left, hR.sup ⟨{(s : Ω)⁻¹}, by simp⟩, ?_⟩
  intro R' hSR' hRR' E q' r sq' z
  by_contra hz
  have hw : p (r z) = (incl hRR') (q' z) := by
    rw [← Scheme.Hom.comp_apply, sq'.w, Scheme.Hom.comp_apply]
  have hmem := hs ((incl hRR') (q' z)) ?_
  · exact hmem ⟨r z, hz, hw⟩
  · intro hsp
    change Subalgebra.inclusion hRR' s ∈ (q' z).asIdeal at hsp
    have hinv : (s : Ω)⁻¹ ∈ R' := hSR' (le_sup_right (a := R) (Algebra.subset_adjoin rfl))
    have hu : IsUnit (Subalgebra.inclusion hRR' s) :=
      IsUnit.of_mul_eq_one ⟨(s : Ω)⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hs'))
    exact (q' z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hsp hu)

end LateralTheory.E.OpenSpreadingOut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTw0TwFreeOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0TwFreePf

def aug (q : ℕ) (A : CommRingCat.{0}) : (twF q 0).obj A →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Submodule.liftQ (twRel q 0 A) (Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q)))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, _, rfl⟩
    simp [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_single]
    exact sub_self (1 : ULift.{1} (ZMod q)))

theorem aug_mk (q : ℕ) (A : CommRingCat.{0}) (ζ : Prim q A) :
    aug q A (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  show Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q))) (Finsupp.single ζ 1) = 1
  rw [Finsupp.linearCombination_single, one_smul]

theorem aug_map (q : ℕ) (A B : CommRingCat.{0}) (g : A ⟶ B) (ζ : Prim q A) :
    aug q B (((twF q 0).map g).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))) = 1 := by
  show aug q B (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.hom) (Finsupp.single ζ 1))) = 1
  rw [Finsupp.mapDomain_single]
  exact aug_mk q B _

theorem LeafTw0TwFree_of : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := by
  intro q _ V ζ
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q 0
  let x : P.obj (op V) := (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q 0).obj Γ(V, ⊤))
  let φ := ((toSheafify Scheme.etaleTopology P).app (op V)).hom
  by_cases hS : ∃ (c : ULift.{1} (ZMod q)), c • twGen 0 ζ = 0 ∧ c ≠ 0
  · obtain ⟨c, hc, hc0⟩ := hS
    have heq : φ (c • x) = φ 0 := by
      rw [φ.map_smul, φ.map_zero]; exact hc
    have hmem := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c • x) 0 heq
    by_cases hne : ∃ (U : Scheme.{0}) (f : U ⟶ V), (Presheaf.equalizerSieve (F := P) (X := op V) (c • x) 0).arrows f
    · exfalso
      obtain ⟨U, f, hf⟩ := hne
      apply hc0
      have h1 : (P.map f.op).hom (c • x) = (P.map f.op).hom 0 := hf
      rw [(P.map f.op).hom.map_smul, (P.map f.op).hom.map_zero] at h1
      let y : (twF q 0).obj Γ(U, ⊤) := ((twF q 0).map (Scheme.Γ.map f.op)).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))
      have h3 : aug q Γ(U, ⊤) y = 1 := aug_map q _ _ _ ζ
      have h4 : aug q Γ(U, ⊤) (c • y) = c • aug q Γ(U, ⊤) y := (aug q _).map_smul c y
      have h5 : c • y = 0 := h1
      rw [h5, h3, map_zero, smul_eq_mul, mul_one] at h4
      exact h4.symm
    · left
      push Not at hne
      exact (tw q 0).isSeparated V _ hmem _ _ (fun U f hf => absurd hf (hne U f))
  · right
    intro c hc
    by_contra h0
    exact hS ⟨c, hc, h0⟩

end LateralTheory.E.LeafTw0TwFreePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafStalkOfAlgOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut TensorProduct

namespace LateralTheory.E.StalkOfAlgebra

theorem stalk_of_smoothAt {R A : CommRingCat.{0}} (φ : R ⟶ A) (p : PrimeSpectrum A)
    (h : letI := φ.hom.toAlgebra; Algebra.IsSmoothAt R p.asIdeal) :
    ((Spec.map φ).stalkMap p).hom.FormallySmooth := by
  letI := φ.hom.toAlgebra
  let P := (p.comap φ.hom).asIdeal
  haveI : p.asIdeal.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P p.asIdeal
  rw [RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ p)]
  have : Algebra.FormallySmooth (Localization.AtPrime P) (Localization.AtPrime p.asIdeal) :=
    (Algebra.FormallySmooth.iff_restrictScalars (R := R) (A := Localization.AtPrime P)).mp h
  exact this

theorem core (hA : LateralTheory.E.SpreadingOutSmoothness.LeafAlgDescend) (k : Type) [Field k] (Ω : Type) [Field Ω]
    [Algebra k Ω] (R : Subalgebra k Ω) {C : Scheme.{0}} {A : CommRingCat.{0}} (φ : CommRingCat.of R ⟶ A)
    (c : C ⟶ Sp Ω) (v : C ⟶ Spec A) [LocallyOfFinitePresentation (Spec.map φ)] (hs : Smooth c)
    (hv : IsPullback v c (Spec.map φ) (toR R)) (y : C) : v y ∈ (Spec.map φ).smoothLocus := by
  letI : Algebra R A := φ.hom.toAlgebra
  have hfp0 : φ.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp inferInstance
  have hfp : Algebra.FinitePresentation R A := hfp0
  have hpo := (CommRingCat.isPushout_tensorProduct R Ω A)
  have hφ : CommRingCat.ofHom (algebraMap R A) = φ := rfl
  rw [hφ] at hpo
  have hstd := (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip
  let e := hv.isoIsPullback _ _ hstd
  have h1 : e.hom ≫ Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeRight.toRingHom) = v :=
    hv.isoIsPullback_hom_fst _ _ hstd
  have h2 : e.hom ≫ Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom) = c :=
    hv.isoIsPullback_hom_snd _ _ hstd
  haveI := hs
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom) = e.inv ≫ c := by
      rw [← h2, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  have hrs := (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom)).mp hsm
  have hinc : (Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[R] A) = algebraMap Ω (Ω ⊗[R] A) := by
    ext x; rfl
  have hsA : Algebra.Smooth Ω (Ω ⊗[R] A) := by
    rw [← RingHom.smooth_algebraMap, ← hinc]; exact hrs
  have key := hA k Ω R A hfp hsA (e.hom y)
  rw [← h1, Scheme.Hom.comp_apply]
  exact stalk_of_smoothAt φ _ key

theorem LeafStalkOfAlg_of : LateralTheory.E.SpreadingOutSmoothness.LeafStalkOfAlg := by
  intro hA k _ Ω _ _ R _ C D c q v hD _ hs hv y
  let e := D.isoSpec
  let φ := Spec.preimage (e.inv ≫ q)
  have hq : Spec.map φ = e.inv ≫ q := Spec.map_preimage _
  haveI : LocallyOfFinitePresentation (Spec.map φ) := by rw [hq]; infer_instance
  have hv' : IsPullback (v ≫ e.hom) c (Spec.map φ) (toR R) := by
    rw [hq]
    exact hv.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have key := core hA k Ω R φ c (v ≫ e.hom) hs.smooth hv' y
  have h2 := Scheme.Hom.preimage_smoothLocus_eq e.hom (Spec.map φ)
  have h3 : e.hom ≫ Spec.map φ = q := by rw [hq, Iso.hom_inv_id_assoc]
  have h4 : v y ∈ (e.hom ≫ Spec.map φ).smoothLocus := by
    rw [← h2]; simpa [Scheme.Hom.comp_apply] using key
  rw [Scheme.Hom.mem_smoothLocus] at h4 ⊢
  rwa [h3] at h4

end LateralTheory.E.StalkOfAlgebra

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPfQS
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPfFP
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf GlobalTheory.GlueModels

namespace LateralTheory.E.LeafGlueTwoPf

def LeafPushoutFP : Prop := ∀ {DW DU DV S : Scheme.{0}} (φU : DW ⟶ DU) (φV : DW ⟶ DV) [IsOpenImmersion φU]
    [IsOpenImmersion φV] (qU : DU ⟶ S) (qV : DV ⟶ S) (h : φU ≫ qU = φV ≫ qV), IsAffine S →
    FP qU → FP qV → FP (φU ≫ qU) → FP (pushout.desc qU qV h)

set_option backward.isDefEq.respectTransparency false in
theorem LeafGlueTwo_of (hF : LeafPushoutFP) : LeafGlueTwo := by
  intro k _ Ω _ _ X f U V R hUV ⟨DU, DV, DW, qU, qV, qW, vU, vV, vW, φU, φV, hqU, hqV, hqW, hφU, hφV, eU, eV,
    pU, pV, pW, cU, cV⟩
  have hc : ∀ x : X, x ∈ Set.range U.ι ∨ x ∈ Set.range V.ι := by
    intro x
    have hx : x ∈ (U ⊔ V : X.Opens) := by rw [hUV]; trivial
    rcases hx with hx | hx
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (by simpa using hx)
  have hsq : IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι := isPullback_opens_inf U V
  have hab : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ vU ≫ pushout.inl φU φV =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ vV ≫ pushout.inr φU φV := by
    rw [← Category.assoc, ← Category.assoc, ← cU, ← cV, Category.assoc, Category.assoc, pushout.condition]
  obtain ⟨v, h1, h2⟩ := exists_glue hsq hc _ _ hab
  have hh : φU ≫ qU = φV ≫ qV := eU.trans eV.symm
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV

  have HV : IsPullback vW (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) φV vV := by
    refine IsPullback.of_bot ?_ cV pV
    rw [← Category.assoc, Scheme.homOfLE_ι, eV]; exact pW
  have HU : IsPullback vW (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) φU vU := by
    refine IsPullback.of_bot ?_ cU pU
    rw [← Category.assoc, Scheme.homOfLE_ι, eU]; exact pW
  have e1 (x : U.toScheme) : v (U.ι x) = pushout.inl φU φV (vU x) := congrArg (fun g => g x) h1
  have e2 (x : V.toScheme) : v (V.ι x) = pushout.inr φU φV (vV x) := congrArg (fun g => g x) h2
  refine ⟨pushout φU φV, pushout.desc qU qV hh, v, hF φU φV qU qV hh inferInstance hqU hqV (eU ▸ hqW), ?_⟩
  refine isPullback_of_two (pushout_cover φU φV) (u' := U.ι) (v' := V.ι) (aU := vU) (aV := vV) ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback HV w x hw
        refine ⟨X.homOfLE inf_le_left z, ?_⟩
        exact congrArg (fun g => g z) hsq.w
    · rintro ⟨y, rfl⟩
      exact ⟨vU y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback HU w x hw
        refine ⟨X.homOfLE inf_le_right z, ?_⟩
        exact (congrArg (fun g => g z) hsq.w).symm
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨vV y, (e2 y).symm⟩
  · simpa only [pushout.inl_desc] using pU
  · simpa only [pushout.inr_desc] using pV

end LateralTheory.E.LeafGlueTwoPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafGlueTwoPf GlobalTheory.GlueModels

namespace LateralTheory.E.LeafGlueTwoPfFP

def LeafPushoutQS : Prop := ∀ {DW DU DV : Scheme.{0}} (φU : DW ⟶ DU) (φV : DW ⟶ DV) [IsOpenImmersion φU]
    [IsOpenImmersion φV], CompactSpace DW → QuasiSeparatedSpace DW → QuasiSeparatedSpace DU →
    QuasiSeparatedSpace DV → QuasiSeparatedSpace (pushout φU φV : Scheme.{0})

set_option backward.isDefEq.respectTransparency false in
theorem pushout_finitePresentation_of_quasiSeparated (hQ : LeafPushoutQS) : LeafPushoutFP := by
  intro DW DU DV S φU φV _ _ qU qV h hS ⟨l1, c1, s1⟩ ⟨l2, c2, s2⟩ ⟨l3, c3, s3⟩
  have : CompactSpace DU := QuasiCompact.compactSpace_of_compactSpace qU
  have : CompactSpace DV := QuasiCompact.compactSpace_of_compactSpace qV
  have : CompactSpace DW := QuasiCompact.compactSpace_of_compactSpace (φU ≫ qU)
  have : QuasiSeparatedSpace DU := quasiSeparatedSpace_of_quasiSeparated qU
  have : QuasiSeparatedSpace DV := quasiSeparatedSpace_of_quasiSeparated qV
  have : QuasiSeparatedSpace DW := quasiSeparatedSpace_of_quasiSeparated (φU ≫ qU)
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV
  let T : Bool → Scheme.{0} := fun i => Bool.rec DU DV i
  let t : ∀ i, T i ⟶ pushout φU φV := fun i => Bool.rec (motive := fun i => T i ⟶ pushout φU φV)
    (pushout.inl φU φV) (pushout.inr φU φV) i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : (pushout φU φV).OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases pushout_cover φU φV x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  have hL : LocallyOfFinitePresentation (pushout.desc qU qV h) := by
    refine IsZariskiLocalAtSource.of_openCover 𝒰 ?_
    rintro (_ | _)
    · change LocallyOfFinitePresentation (pushout.inl φU φV ≫ pushout.desc qU qV h)
      rw [pushout.inl_desc]; exact l1
    · change LocallyOfFinitePresentation (pushout.inr φU φV ≫ pushout.desc qU qV h)
      rw [pushout.inr_desc]; exact l2
  have hC : CompactSpace (pushout φU φV : Scheme.{0}) := by
    refine ⟨?_⟩
    have hu : (Set.univ : Set (pushout φU φV : Scheme.{0})) =
        Set.range (pushout.inl φU φV) ∪ Set.range (pushout.inr φU φV) := by
      ext x; simpa using pushout_cover φU φV x
    rw [hu]
    exact (isCompact_range (pushout.inl φU φV).continuous).union (isCompact_range (pushout.inr φU φV).continuous)
  have hQS := hQ φU φV inferInstance inferInstance inferInstance inferInstance
  exact ⟨hL, inferInstance, inferInstance⟩

end LateralTheory.E.LeafGlueTwoPfFP

theorem LateralTheory.E.LeafGlueTwoPfFP.LeafGlueTwo_of' (hQ : LateralTheory.E.LeafGlueTwoPfFP.LeafPushoutQS) :
    LateralTheory.E.LeafObjGluePf.LeafGlueTwo :=
  LateralTheory.E.LeafGlueTwoPf.LeafGlueTwo_of (LateralTheory.E.LeafGlueTwoPfFP.pushout_finitePresentation_of_quasiSeparated hQ)

end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology GlobalTheory.GlueModels LateralTheory.E.LeafGlueTwoPfFP

namespace LateralTheory.E.LeafGlueTwoPfQS

theorem qs_range {A D : Scheme.{0}} (e : A ⟶ D) [IsOpenImmersion e] [QuasiSeparatedSpace A] :
    IsQuasiSeparated (Set.range e) := by
  simpa [Set.image_univ] using (isQuasiSeparated_univ (α := A)).image_of_isEmbedding e.isOpenEmbedding.isEmbedding

theorem compact_pre {A D : Scheme.{0}} (e : A ⟶ D) [IsOpenImmersion e] {s : Set D} (hs : IsCompact s)
    (h : s ⊆ Set.range e) : IsCompact (e ⁻¹' s) :=
  (e.isOpenEmbedding.isInducing.isCompact_preimage_iff h).2 hs

theorem compact_inter_range {W A D : Scheme.{0}} (φ : W ⟶ A) (e : A ⟶ D) [IsOpenImmersion e] [QuasiCompact φ]
    {s : Set D} (hs : IsCompact s) (ho : IsOpen s) (h : s ⊆ Set.range e) :
    IsCompact (s ∩ Set.range (φ ≫ e)) := by
  rw [← Set.image_preimage_eq_inter_range]
  refine IsCompact.image ?_ (φ ≫ e).continuous
  have hp : ((φ ≫ e) ⁻¹' s) = φ ⁻¹' (e ⁻¹' s) := by ext x; simp
  rw [hp]
  exact QuasiCompact.isCompact_preimage (f := φ) _ (e.continuous.isOpen_preimage _ ho) (compact_pre e hs h)

set_option backward.isDefEq.respectTransparency false in
theorem leafPushoutQS : LeafPushoutQS := by
  intro DW DU DV φU φV _ _ hW hWs hUs hVs
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV
  have : QuasiCompact φU := quasiCompact_of_compactSpace φU
  have : QuasiCompact φV := quasiCompact_of_compactSpace φV
  let good : Set (pushout φU φV : Scheme.{0}) → Prop := fun s => IsOpen s ∧ IsCompact s ∧
    (s ⊆ Set.range (pushout.inl φU φV) ∨ s ⊆ Set.range (pushout.inr φU φV))
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := fun s : {s // good s} => s.1) ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨s, rfl⟩; exact s.2.1
    · intro x u hx hu
      rcases pushout_cover φU φV x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · have hb : ∀ {U : TopologicalSpace.Opens DU} {x : DU}, x ∈ U → ∃ U' ∈ DU.affineOpens, x ∈ U' ∧ U' ≤ U :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp DU.isBasis_affineOpens
        obtain ⟨U', hU', hyU', hle⟩ := hb (U := ⟨pushout.inl φU φV ⁻¹' u, (pushout.inl φU φV).continuous.isOpen_preimage u hu⟩) (x := y) hx
        refine ⟨pushout.inl φU φV '' U', ⟨⟨_, (pushout.inl φU φV).isOpenEmbedding.isOpenMap _ U'.2,
          (show IsAffineOpen U' from hU').isCompact.image (pushout.inl φU φV).continuous, Or.inl (Set.image_subset_range _ _)⟩,
          rfl⟩, ⟨y, hyU', rfl⟩, Set.image_subset_iff.2 hle⟩
      · have hb : ∀ {U : TopologicalSpace.Opens DV} {x : DV}, x ∈ U → ∃ U' ∈ DV.affineOpens, x ∈ U' ∧ U' ≤ U :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp DV.isBasis_affineOpens
        obtain ⟨U', hU', hyU', hle⟩ := hb (U := ⟨pushout.inr φU φV ⁻¹' u, (pushout.inr φU φV).continuous.isOpen_preimage u hu⟩) (x := y) hx
        refine ⟨pushout.inr φU φV '' U', ⟨⟨_, (pushout.inr φU φV).isOpenEmbedding.isOpenMap _ U'.2,
          (show IsAffineOpen U' from hU').isCompact.image (pushout.inr φU φV).continuous, Or.inr (Set.image_subset_range _ _)⟩,
          rfl⟩, ⟨y, hyU', rfl⟩, Set.image_subset_iff.2 hle⟩
  · have e : Set.range (φU ≫ pushout.inl φU φV) = Set.range (φV ≫ pushout.inr φU φV) := by
      rw [pushout.condition]
    have hWo : IsOpen (Set.range (φU ≫ pushout.inl φU φV)) := (φU ≫ pushout.inl φU φV).isOpenEmbedding.isOpen_range
    have mixed : ∀ s t : Set (pushout φU φV : Scheme.{0}), IsOpen s → IsCompact s →
        s ⊆ Set.range (pushout.inl φU φV) → IsOpen t → IsCompact t → t ⊆ Set.range (pushout.inr φU φV) →
        IsCompact (s ∩ t) := by
      intro s t so sc hs tO tc ht
      have hsub : s ∩ t ⊆ Set.range (φU ≫ pushout.inl φU φV) := by
        rintro x ⟨h1, h2⟩
        obtain ⟨a, rfl⟩ := hs h1
        obtain ⟨b, hb⟩ := ht h2
        obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr φU φV hb.symm
        exact ⟨w, by rw [Scheme.Hom.comp_apply, hw]⟩
      have hst : s ∩ t = (s ∩ Set.range (φU ≫ pushout.inl φU φV)) ∩ (t ∩ Set.range (φU ≫ pushout.inl φU φV)) := by
        ext x; constructor
        · intro hx; exact ⟨⟨hx.1, hsub hx⟩, ⟨hx.2, hsub hx⟩⟩
        · intro hx; exact ⟨hx.1.1, hx.2.1⟩
      rw [hst]
      refine qs_range (φU ≫ pushout.inl φU φV) _ _ Set.inter_subset_right (so.inter hWo)
        (compact_inter_range φU _ sc so hs) Set.inter_subset_right (tO.inter hWo) ?_
      rw [e]; exact compact_inter_range φV _ tc tO ht
    rintro ⟨s, so, sc, hs⟩ ⟨t, tO, tc, ht⟩
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact qs_range (pushout.inl φU φV) s t hs so sc ht tO tc
    · exact mixed s t so sc hs tO tc ht
    · show IsCompact (s ∩ t); rw [Set.inter_comm]; exact mixed t s tO tc ht so sc hs
    · exact qs_range (pushout.inr φU φV) s t hs so sc ht tO tc

theorem LeafGlueTwo_of : LateralTheory.E.LeafObjGluePf.LeafGlueTwo :=
  LateralTheory.E.LeafGlueTwoPfFP.LeafGlueTwo_of' leafPushoutQS

end LateralTheory.E.LeafGlueTwoPfQS
end
end
