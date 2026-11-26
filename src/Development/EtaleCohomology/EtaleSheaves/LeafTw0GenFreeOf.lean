module

public import Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTw0GenFreeOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPfM

theorem iso_inv_mono' {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) : Mono e.inv := inferInstance

theorem resι_mono {R : Type} [CommRing R] (F : Shv R) : Mono (resι R F) := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  have h0 : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  exact @mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ h0 _ (iso_inv_mono' _)))

theorem sec_inj {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have h1 : Mono ((sheafToPresheaf _ _).map φ) := inferInstance
  have h2 : Mono (((sheafToPresheaf _ _).map φ).app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 h2

def LeafTw0TwFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • twGen 0 ζ = 0 → c = 0

theorem LeafTw0GenFree_of (h : LeafTw0TwFree) : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := by
  intro q _ V ζ
  rcases h q V ζ with h0 | h1
  · exact Or.inl h0
  · right
    intro c hc
    apply h1 c
    have : Mono (resι (ZMod q) (tw q 0)) := resι_mono _
    apply sec_inj (resι (ZMod q) (tw q 0)) V
    show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = Sec.map (resι (ZMod q) (tw q 0)) 0
    rw [show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = c • resGen 0 ζ from
      map_smul ((resι (ZMod q) (tw q 0)).hom.app (op V)).hom c _, hc]
    simp [Sec.map]

end LateralTheory.E.LeafTw0LocSplitPfM
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafInclDescendPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf

namespace LateralTheory.E.LeafInclDescendPf

def bcLift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R'' : Subalgebra k Ω} (h : R ≤ R'')
    {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D} (w : v ≫ q = g ≫ toR R) :
    Y ⟶ pullback q (incl h) :=
  pullback.lift v (g ≫ toR R'') (by rw [Category.assoc, toR_eq, w])

theorem bcLift_isPullback {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R'' : Subalgebra k Ω} (h : R ≤ R'')
    {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D} (hp : IsPullback v g q (toR R)) :
    IsPullback (bcLift h hp.w) g (pullback.snd q (incl h)) (toR R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (v₁₃ := q) (h₂₂ := incl h) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h))
  dsimp only [bcLift]
  rw [pullback.lift_fst, toR_eq]
  exact hp

def LeafInclPiece : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R)),
    ∃ R' : Subalgebra k Ω, R ≤ R' ∧ R'.FG ∧ ∀ (R'' : Subalgebra k Ω) (h : R ≤ R''), R' ≤ R'' →
      ∃ φ : pullback qW (incl h) ⟶ pullback qU (incl h), IsOpenImmersion φ ∧
        φ ≫ pullback.snd qU (incl h) = pullback.snd qW (incl h) ∧
        bcLift h hW.w ≫ φ = X.homOfLE hWU ≫ bcLift h hU.w

theorem LeafInclDescend_of (hP : LeafInclPiece) : LeafInclDescend := by
  intro k _ Ω _ _ X f hf U V R hR ⟨DU, qU, vU, hqU, pU⟩ ⟨DV, qV, vV, hqV, pV⟩ ⟨DW, qW, vW, hqW, pW⟩
  obtain ⟨R1, h1, hR1, H1⟩ := hP k Ω f hf U (U ⊓ V) inf_le_left R hR DU DW qU qW vU vW hqU hqW pU pW
  obtain ⟨R2, h2, hR2, H2⟩ := hP k Ω f hf V (U ⊓ V) inf_le_right R hR DV DW qV qW vV vW hqV hqW pV pW
  have hle : R ≤ R1 ⊔ R2 := h1.trans le_sup_left
  obtain ⟨φU, oU, sU, cU⟩ := H1 (R1 ⊔ R2) hle le_sup_left
  obtain ⟨φV, oV, sV, cV⟩ := H2 (R1 ⊔ R2) hle le_sup_right
  exact ⟨R1 ⊔ R2, hle, hR1.sup hR2, _, _, _, pullback.snd qU (incl hle), pullback.snd qV (incl hle),
    pullback.snd qW (incl hle), bcLift hle pU.w, bcLift hle pV.w, bcLift hle pW.w, φU, φV,
    fp_snd _ _ hqU, fp_snd _ _ hqV, fp_snd _ _ hqW, oU, oV, sU, sV,
    bcLift_isPullback hle pU, bcLift_isPullback hle pV, bcLift_isPullback hle pW, cU, cV⟩

end LateralTheory.E.LeafInclDescendPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SpreadingOutLocallyQuasiFinite
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutLocallyQuasiFinite

def LeafQFAtBaseChange : Prop := ∀ {EA EB A B : Scheme.{0}} (h : EA ⟶ EB) (g : A ⟶ B) (rA : EA ⟶ A) (rB : EB ⟶ B),
    IsPullback rA h g rB → LocallyOfFiniteType g → ∀ x : EA, g.QuasiFiniteAt (rA x) → h.QuasiFiniteAt x

def LeafQFAtDescend : Prop := ∀ {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B),
    IsPullback vA γ g vB → LocallyOfFiniteType g → ∀ x : CA, γ.QuasiFiniteAt x → g.QuasiFiniteAt (vA x)

def LeafOpenSpread : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C A : Scheme.{0}} (c : C ⟶ Sp Ω) (p : A ⟶ Sp R) (v : C ⟶ A) (U : A.Opens),
    (LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p) → IsPullback v c p (toR R) →
    (∀ x : C, v x ∈ U) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ A), IsPullback r q' p (incl hR) → ∀ z : E, r z ∈ U

theorem quasi_finite_at_base_change_of_finite_type : LeafQFAtBaseChange := by
  intro EA EB A B h g rA rB sq hg x hx
  let U := g.quasiFiniteLocus
  have sq2 : IsPullback (rA ∣_ U) ((rA ⁻¹ᵁ U).ι ≫ h) (U.ι ≫ g) rB :=
    (isPullback_morphismRestrict rA U).paste_vert sq
  have : LocallyQuasiFinite ((rA ⁻¹ᵁ U).ι ≫ h) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq2 inferInstance
  have hxV : x ∈ rA ⁻¹ᵁ U := hx
  have := ((rA ⁻¹ᵁ U).ι ≫ h).quasiFiniteAt ⟨x, hxV⟩
  have h2 := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion (f := (rA ⁻¹ᵁ U).ι) (g := h)
    (x := ⟨x, hxV⟩)).mp this
  simpa using h2

theorem LeafSpreadLQFMap_of (hBC : LeafQFAtBaseChange) (hD : LeafQFAtDescend) (hO : LeafOpenSpread) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap := by
  intro k _ Ω _ _ R hR CA CB A B cB γ qB g vA vB hB hA pB pA hw hγ
  have : LocallyOfFinitePresentation (g ≫ qB) := hA.1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g qB
  have sqC : IsPullback vA γ g vB := IsPullback.of_bot pA hw.symm pB
  have hU : ∀ x : CA, vA x ∈ g.quasiFiniteLocus := fun x =>
    hD γ g vA vB sqC inferInstance x (γ.quasiFiniteAt x)
  obtain ⟨S, hRS, hS, H⟩ := hO k Ω R hR (γ ≫ cB) (g ≫ qB) vA g.quasiFiniteLocus hA pA hU
  refine ⟨S, hRS, hS, ?_⟩
  intro R' hSR' hRR' EA EB qB' h rA rB QB QA hc
  have sqE : IsPullback rA h g rB := IsPullback.of_bot QA hc.symm QB
  have : LocallyOfFiniteType h :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqE inferInstance
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  refine top_le_iff.mp fun z _ => ?_
  exact hBC h g rA rB sqE inferInstance z (H R' hSR' hRR' EA (h ≫ qB') rA QA z)

end LateralTheory.E.SpreadingOutLocallyQuasiFinite

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmooth1Of
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothAffSmPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf LateralTheory.E.LeafPropsDescendPf.Split LateralTheory.E.LeafSpreadSmoothPf Topology

namespace LateralTheory.E.LeafSpreadSmoothAffSmPf

def LeafGenericSmooth : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    ∀ [LocallyOfFinitePresentation q], SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∀ x : D, q.base x ∈ Set.range (toR R).base → x ∈ q.smoothLocus

def LeafSpreadOpen : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), IsAffine D → LocallyOfFinitePresentation q →
    ∀ U : D.Opens, (∀ x : D, q.base x ∈ Set.range (toR R).base → x ∈ U) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧
      ∀ y : (pullback q (incl h) : Scheme.{0}), (pullback.fst q (incl h)).base y ∈ U

def LeafSmoothOfLocus : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {R S : Subalgebra k Ω}
    (h : R ≤ S) {D : Scheme.{0}} (q : D ⟶ Sp R) [LocallyOfFinitePresentation q],
    (∀ y : (pullback q (incl h) : Scheme.{0}), (pullback.fst q (incl h)).base y ∈ q.smoothLocus) →
    Smooth (pullback.snd q (incl h))

theorem leafSmoothOfLocus : LeafSmoothOfLocus := by
  intro k _ Ω _ _ R S h D q _ hy
  have hU : Smooth (q.smoothLocus.ι ≫ q) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self _
  have sq := (isPullback_morphismRestrict (pullback.fst q (incl h)) q.smoothLocus).paste_vert
    (IsPullback.of_hasPullback q (incl h))
  have hs : Smooth (((pullback.fst q (incl h)) ⁻¹ᵁ q.smoothLocus).ι ≫ pullback.snd q (incl h)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hU
  have hL : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun _ : Unit => (pullback.fst q (incl h)) ⁻¹ᵁ q.smoothLocus) ?_ (fun _ => hs)
  exact top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨(), hy y⟩

def LeafClosedConstructible : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), IsAffine D → LocallyOfFinitePresentation q →
    ∀ Z : Set D, IsClosed Z → IsConstructible Z

def LeafAvoidConstructible : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ T : Set (Sp R), IsConstructible T → (∀ z ∈ T, z ∉ Set.range (toR R).base) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ ∀ w : (Sp S : Scheme.{0}), (incl h).base w ∉ T

theorem leafClosedConstructible : LeafClosedConstructible := by
  intro k _ Ω _ _ R hR D q hD hlfp Z hZ
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  have : IsNoetherianRing (CommRingCat.of R) := this
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian D := ⟨⟩
  have hc : IsConstructible (Zᶜ) := (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible hZ.isOpen_compl
  simpa using hc

def LeafGenericNbhd : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ T : Set (Sp R), IsConstructible T → (∀ z ∈ T, z ∉ Set.range (toR R).base) →
    ∃ f : R, f ≠ 0 ∧ ∀ z ∈ T, f ∈ (show PrimeSpectrum R from z).asIdeal

theorem leafInvert (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (hR : R.FG)
    (f : R) (hf : f ≠ 0) : ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧
      ∀ w : (Sp S : Scheme.{0}), f ∉ (show PrimeSpectrum R from (incl h).base w).asIdeal := by
  have hf0 : (f : Ω) ≠ 0 := fun e => hf (Subtype.ext e)
  refine ⟨R ⊔ Algebra.adjoin k {(f : Ω)⁻¹}, le_sup_left, hR.sup ⟨{(f : Ω)⁻¹}, by simp⟩, fun w hw => ?_⟩
  have hi : (f : Ω)⁻¹ ∈ R ⊔ Algebra.adjoin k {(f : Ω)⁻¹} :=
    (le_sup_right : Algebra.adjoin k {(f : Ω)⁻¹} ≤ _) (Algebra.subset_adjoin rfl)
  have hu : IsUnit (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ Algebra.adjoin k {(f : Ω)⁻¹}) f) := by
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : ↥(R ⊔ Algebra.adjoin k {(f : Ω)⁻¹})) ?_
    apply Subtype.ext
    simp [hf0]
  have hw' : Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ Algebra.adjoin k {(f : Ω)⁻¹}) f ∈ w.asIdeal := hw
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hw' hu)

theorem leafGenericNbhd : LeafGenericNbhd := by
  classical
  intro k _ Ω _ _ R hR T hT hgen
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : (show Sp R from η) ∈ Set.range (toR R).base := by
    refine ⟨(show Sp Ω from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R Ω) ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective
  obtain ⟨C, hC⟩ := (PrimeSpectrum.exists_constructibleSetData_iff (R := R) (s := T)).mpr hT
  have hne : ∀ c ∈ C, ∃ a : R, a ≠ 0 ∧ ∀ z ∈ c.toSet, a ∈ z.asIdeal := by
    intro c hc
    by_cases h0 : c.f = 0
    · refine ⟨1, one_ne_zero, fun z hz => absurd ?_ hz.2⟩
      simp [h0, PrimeSpectrum.mem_zeroLocus]
    · by_cases hg : ∃ i, c.g i ≠ 0
      · obtain ⟨i, hi⟩ := hg
        exact ⟨c.g i, hi, fun z hz => hz.1 ⟨i, rfl⟩⟩
      · simp only [not_exists, not_not] at hg
        exfalso
        have hηc : η ∈ c.toSet := by
          refine ⟨?_, ?_⟩
          · rintro _ ⟨i, rfl⟩
            simp [η, hg i]
          · intro h
            exact h0 (by simpa [η, PrimeSpectrum.mem_zeroLocus] using h)
        have hηT : η ∈ T := by
          rw [← hC]
          simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion]
          exact Set.mem_iUnion₂.mpr ⟨c, hc, hηc⟩
        exact hgen _ hηT hη
  choose! a ha using hne
  refine ⟨∏ c ∈ C, a c, Finset.prod_ne_zero_iff.mpr (fun c hc => (ha c hc).1), fun z hz => ?_⟩
  rw [← hC] at hz
  simp only [PrimeSpectrum.ConstructibleSetData.toSet] at hz
  obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hz
  rw [← Finset.mul_prod_erase C a hc]
  exact Ideal.mul_mem_right _ _ ((ha c hc).2 z hzc)

theorem leafAvoidConstructible_of (hN : LeafGenericNbhd) : LeafAvoidConstructible := by
  intro k _ Ω _ _ R hR T hT hgen
  obtain ⟨f, hf, hfT⟩ := hN k Ω R hR T hT hgen
  obtain ⟨S, h, hS, hw⟩ := leafInvert k Ω R hR f hf
  exact ⟨S, h, hS, fun w hwT => hw w (hfT _ hwT)⟩

theorem leafSpreadOpen_of (hC : LeafClosedConstructible) (hA : LeafAvoidConstructible) : LeafSpreadOpen := by
  intro k _ Ω _ _ R hR D q hD hlfp U hU
  have : QuasiCompact q := inferInstance
  have hT := q.isConstructible_image (hC k Ω R hR q hD hlfp ((U : Set D)ᶜ) U.isOpen.isClosed_compl)
  obtain ⟨S, h, hS, hw⟩ := hA k Ω R hR _ hT (by
    rintro z ⟨x, hx, rfl⟩ hz
    exact hx (hU x hz))
  refine ⟨S, h, hS, fun y => ?_⟩
  by_contra hy
  apply hw ((pullback.snd q (incl h)).base y)
  refine ⟨(pullback.fst q (incl h)).base y, hy, ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

theorem LeafSpreadSmoothAffSm_of_cut (hG : LeafGenericSmooth) (hO : LeafSpreadOpen) (hL : LeafSmoothOfLocus) :
    LeafSpreadSmoothAffSm := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hs hv
  obtain ⟨S, h, hS, hy⟩ := hO k Ω R hR q hD hlfp q.smoothLocus (hG k Ω R hR c q v hD hs hv)
  exact ⟨S, h, hS, hL k Ω h q hy⟩

def LeafStalkDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    ∀ [LocallyOfFinitePresentation q], SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) → ∀ y : C, v.base y ∈ q.smoothLocus

theorem leafGenericSmooth_of (hS : LeafStalkDescend) : LeafGenericSmooth := by
  intro k _ Ω _ _ R hR C D c q v hD _ hs hv x ⟨w, hw⟩
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
  have := hS k Ω R hR c q v hD hs hv (hv.isoPullback.inv.base z)
  rwa [← Scheme.Hom.comp_apply, hv.isoPullback_inv_fst, hz1] at this

theorem LeafSpreadSmoothAffSm_of (hD : LeafStalkDescend) :
    LeafSpreadSmoothAffSm :=
  LeafSpreadSmoothAffSm_of_cut (leafGenericSmooth_of hD) (leafSpreadOpen_of leafClosedConstructible (leafAvoidConstructible_of leafGenericNbhd))
    leafSmoothOfLocus

end LateralTheory.E.LeafSpreadSmoothAffSmPf

end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut TensorProduct

namespace LateralTheory.E.SpreadingOutSmoothness

theorem stepB {R K B A : Type} [CommRing R] [CommRing K] [CommRing B] [CommRing A] [Algebra R K] [Algebra R A]
    [Algebra R B] [Algebra K B] [IsScalarTower R K B] [Algebra A B] [IsScalarTower R A B] (M : Submonoid R)
    [IsLocalization M K] [IsLocalization (Algebra.algebraMapSubmonoid A M) B] [Algebra.Smooth K B]
    (Q : Ideal B) [Q.IsPrime] : Algebra.IsSmoothAt R (Q.comap (algebraMap A B)) := by
  haveI : Algebra.FormallySmooth R K := Algebra.FormallySmooth.of_isLocalization M
  haveI : Algebra.FormallySmooth K (Localization.AtPrime Q) := inferInstance
  haveI : Algebra.FormallySmooth R (Localization.AtPrime Q) := Algebra.FormallySmooth.comp R K _
  haveI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid A M) (Localization.AtPrime Q) Q
  exact Algebra.FormallySmooth.of_equiv ((IsLocalization.algEquiv (Q.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime Q) _).restrictScalars R)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem algDescend (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A] (hfp : Algebra.FinitePresentation R A) (hs : Algebra.Smooth Ω (Ω ⊗[R] A))
    (P : PrimeSpectrum (Ω ⊗[R] A)) :
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A := by
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  let e := Algebra.TensorProduct.cancelBaseChange R (FractionRing R) Ω Ω A
  haveI : Algebra.Smooth Ω (Ω ⊗[FractionRing R] (FractionRing R ⊗[R] A)) := Algebra.Smooth.of_equiv e.symm
  haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ Ω
  haveI : Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A) :=
    Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat Ω
  letI : Algebra A (FractionRing R ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (FractionRing R ⊗[R] A) :=
    IsLocalization.tensorRight _ _
  let φ : FractionRing R ⊗[R] A →+* Ω ⊗[R] A := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : FractionRing R ⊗[R] A →ₐ[FractionRing R] Ω ⊗[FractionRing R] _).toRingHom
  haveI : (P.asIdeal.comap φ).IsPrime := Ideal.comap_isPrime _ _
  have hφ : φ.comp (algebraMap A (FractionRing R ⊗[R] A)) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom := by
    ext a
    show e (1 ⊗ₜ (1 ⊗ₜ a)) = 1 ⊗ₜ a
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  have hc : PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P =
      ⟨(P.asIdeal.comap φ).comap (algebraMap A (FractionRing R ⊗[R] A)), inferInstance⟩ := by
    ext1; simp only [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, hφ]
  rw [hc]
  exact stepB (K := FractionRing R) (nonZeroDivisors R) (P.asIdeal.comap φ)

def LeafAlgDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A], Algebra.FinitePresentation R A → Algebra.Smooth Ω (Ω ⊗[R] A) →
    ∀ P : PrimeSpectrum (Ω ⊗[R] A),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A

def LeafStalkOfAlg : Prop := LeafAlgDescend → LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafStalkDescend

theorem leafAlgDescend : LeafAlgDescend := fun k _ Ω _ _ R A _ _ hfp hs P => algDescend k Ω R A hfp hs P

theorem LeafSpreadSmooth1_of (hB : LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadRelDim) (hT : LeafStalkOfAlg) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1 :=
  LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadSmooth_of
    (LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafSpreadSmoothAffSm_of (hT leafAlgDescend)) hB

end LateralTheory.E.SpreadingOutSmoothness

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSHSievePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHSievePf

theorem LeafSHSieve_of : LateralTheory.E.LeafClosedSH0Pf.LeafSHSieve := by
  intro X _ hSH S hS
  obtain ⟨hHens, hSep⟩ := hSH
  let A : Type := Γ(X, ⊤)
  let K : Type := IsLocalRing.ResidueField A
  let π : A →+* K := IsLocalRing.residue A
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  let x : Spec (.of K) ⟶ X := Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber K).jointly_surjective _
    (Scheme.Cover.mem_grothendieckTopology 𝒰) x
  obtain ⟨Z, h, _, ⟨i⟩, rfl⟩ := hg
  have hy' : (y ≫ h) ≫ 𝒰.f i = Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv := by
    exact (Category.assoc _ _ _).trans hy
  obtain ⟨l, ⟨-, hl⟩, -⟩ := GlobalTheory.existsUnique_lift_of_etale_of_henselian (𝒰.f i) π
    IsLocalRing.residue_surjective (y ≫ h) X.isoSpec.inv hy'
  have hmem : S (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have := S.downward_closed hmem (X.isoSpec.hom ≫ l)
  have e : (X.isoSpec.hom ≫ l) ≫ 𝒰.f i = 𝟙 X := by rw [Category.assoc, hl, Iso.hom_inv_id]
  rwa [e] at this

end LateralTheory.E.LeafSHSievePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpreadLQFGraphOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

theorem toR_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    toR R ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [← Spec.map_comp]; rfl

theorem incl_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

abbrev cmp {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    pullback c p ⟶ pullback b p :=
  pullback.lift (pullback.fst c p ≫ a) (pullback.snd _ _)
    (by rw [Category.assoc, h]; exact pullback.condition)

theorem paste {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    IsPullback (cmp p a b c h) (pullback.fst c p) (pullback.fst b p) a := by
  subst h
  refine IsPullback.of_right (h₁₂ := pullback.snd b p) (v₁₃ := p) (h₂₂ := b) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback b p).flip
  rw [pullback.lift_snd]; exact (IsPullback.of_hasPullback (a ≫ b) p).flip

theorem LeafSpreadLQFGraph_of (hM : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph := by
  intro k _ X p _ Ω _ _ R hRfg C0 D0 c0 q v0 f e he hf hq hpb hve hlqf
  have hLFT : LocallyOfFinitePresentation (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) := by
    infer_instance
  obtain ⟨S, hRS, hSfg, hS⟩ := hM k Ω R hRfg
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm)
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) (pullback.lift q f hf.symm) v0
    (cmp p (toR R) _ _ (toR_sk R))
    ⟨hLFT, inferInstance, inferInstance⟩ (by rw [pullback.lift_fst]; exact hq) (paste p _ _ _ (toR_sk R))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hpb) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hpb.w.symm
      · simp only [Category.assoc, pullback.lift_snd]; exact hve.symm) hlqf
  refine ⟨S, hRS, hSfg, fun R' hSR' hR E0 q' r hr hf' => ?_⟩
  refine hS R' hSR' hR E0 _ (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R'))) p)
    (pullback.lift q' (r ≫ f) hf'.symm) r (cmp p (incl hR) _ _ (incl_sk hR)) (paste p _ _ _ (incl_sk hR))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hr) ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hr.w.symm
  · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFinitenessBaseChange
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    toR R' ≫ incl hR = toR R := by
  rw [← Spec.map_comp]; rfl

theorem sq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {q : D ⟶ Sp R} {v : C ⟶ D} (hv : IsPullback v c q (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hv.w)) c
      (pullback.snd q (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl hR))
  rw [pullback.lift_fst, toR_incl]; exact hv

theorem spread_chain_base_change_to_larger_subalgebra : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafBaseChangePreR := by
  intro k _ Ω _ _ R R' hR C0 C1 C2 c0 γ1 γ2 D0 D1 D2 q d1 d2 v0 v1 v2 hpre
  obtain ⟨-, -, -, p0, p1, p2, m1, m2⟩ := hpre
  let e1 : pullback (d1 ≫ q) (incl hR) ⟶ pullback q (incl hR) :=
    pullback.lift (pullback.fst _ _ ≫ d1) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl hR) ⟶ pullback (d1 ≫ q) (incl hR) :=
    pullback.lift (pullback.fst _ _ ≫ d2) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have t1 : e1 ≫ pullback.snd q (incl hR) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have t2 : e2 ≫ pullback.snd (d1 ≫ q) (incl hR) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have t12 : e2 ≫ e1 ≫ pullback.snd q (incl hR) = pullback.snd _ _ := by rw [t1, t2]
  have P0 := sq hR p0
  have P1 := sq hR p1
  have P2 := sq hR p2
  refine ⟨_, _, _, pullback.snd q (incl hR), e1, e2, _, pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact p1.w), pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact p2.w), pullback.fst _ _, pullback.fst _ _, pullback.fst _ _,
    ⟨P0, ?_, ?_, ?_, ?_⟩, IsPullback.of_hasPullback _ _, ?_, ?_, pullback.lift_fst _ _ _,
    pullback.lift_fst _ _ _, pullback.lift_fst _ _ _⟩
  · rw [t1]; exact P1
  · rw [t12]; exact P2
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, e1, pullback.lift_fst_assoc]; exact m1
    · simp only [Category.assoc, pullback.lift_snd, e1]
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, e2, pullback.lift_fst_assoc]; exact m2
    · simp only [Category.assoc, pullback.lift_snd, e2]
  · rw [t1]; exact IsPullback.of_hasPullback _ _
  · rw [t12]; exact IsPullback.of_hasPullback _ _

theorem LeafSpreadQF_of (hSep : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated)
    (hSm : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1) (hG : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph)
    (hM : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap) : LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF :=
  LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadQF_of hSep hSm hG hM spread_chain_base_change_to_larger_subalgebra

end LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StrictHenselianLocalization
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf

namespace LateralTheory.E.StrictHenselianLocalization
open LateralTheory.E.StrictHenselianNeighbourhood

lemma isUnit_of_forall_prime {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (y : R)
    (h : ∀ p : PrimeSpectrum S, ψ y ∉ p.asIdeal) : IsUnit (ψ y) := by
  by_contra hu
  obtain ⟨M, hM, hyM⟩ := exists_max_ideal_of_mem_nonunits hu
  exact h ⟨M, hM.isPrime⟩ hyM

theorem key {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left) (hP : IsPtNb U x Ω s D c V a l e t)
    (j : J) (y : D.obj j) (hy : (Spec.preimage (l j)).hom y ≠ 0) :
    ∃ (n : J) (f : j ⟶ n), IsUnit (D.map f y) := by
  obtain ⟨-, he, hl, hcomp, -, hlc, hcof, heq⟩ := hP
  have _ : ∀ j, IsIso (e j) := he
  let O : (Sp (D.obj j)).Opens := PrimeSpectrum.basicOpen y
  have hrange : Set.range (l j).base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [← Spec.map_preimage (l j)]
    show y ∉ Ideal.comap (Spec.preimage (l j)).hom q.asIdeal
    rw [hq, Ideal.mem_comap, Ideal.mem_bot]
    exact hy
  have : Etale (V j).hom := (V j).prop
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ e j ≫ (V j).hom) (by
    show Etale (O.ι ≫ e j ≫ (V j).hom); infer_instance)
  let b : U' ⟶ U := MorphismProperty.Over.homMk (O.ι ≫ e j ≫ (a j).left) (by
    have hw : (a j).left ≫ U.hom = (V j).hom := MorphismProperty.Over.w (a j)
    show _ = O.ι ≫ e j ≫ (V j).hom
    exact (Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) ((Category.assoc _ _ _).trans (congrArg (e j ≫ ·) hw)))) trivial
  have hOI : IsOpenImmersion O.ι := inferInstance
  let l' := IsOpenImmersion.lift O.ι (l j) hrange
  have hl' : l' ≫ O.ι = l j := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨k, g, hg', hlg'⟩ : ∃ (k : J) (g : (V k).left ⟶ (O : Scheme)),
      g ≫ O.ι ≫ e j ≫ (a j).left = (a k).left ∧ l k ≫ e k ≫ g = l' := by
    obtain ⟨k, g, hg, hlg⟩ := hcof U' b l' (by
      show l' ≫ (O.ι ≫ e j ≫ (a j).left) = s
      rw [← Category.assoc, hl', hl j])
    exact ⟨k, g, hg, hlg⟩
  clear_value b U' l'
  let m := IsFiltered.max j k
  let f1 : j ⟶ m := IsFiltered.leftToMax j k
  let f2 : k ⟶ m := IsFiltered.rightToMax j k
  have h1 := hlc j m f1
  have h2 := hlc k m f2
  obtain ⟨n, f3, h3⟩ := heq (V j) (a j) m
    (inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom) ≫ e j)
    (inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map f2).hom) ≫ e k ≫ g ≫ O.ι ≫ e j)
    (by simp only [Category.assoc]; rw [hcomp j m f1, IsIso.inv_hom_id_assoc])
    (by simp only [Category.assoc]; rw [hg', hcomp k m f2, IsIso.inv_hom_id_assoc])
    (by
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% hlg', reassoc_of% hl'])
  simp only [IsIso.hom_inv_id_assoc] at h3
  have hfac : Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom) =
      (Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f2).hom) ≫ e k ≫ g) ≫ O.ι := by
    rw [← cancel_mono (e j)]
    simpa only [Category.assoc] using h3
  refine ⟨n, f1 ≫ f3, ?_⟩
  rw [D.map_comp, CommRingCat.comp_apply]
  apply isUnit_of_forall_prime (D.map f3).hom
  intro p
  have hp : (Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom)).base p ∈
      Set.range O.ι.base := by
    rw [hfac]; exact ⟨_, rfl⟩
  rw [Scheme.Opens.range_ι] at hp
  exact hp

theorem LeafSHLoc_of : LeafSHLoc := by
  intro B U x Ω _ _ s J _ _ D c hc V a l e t hP
  have hunit : ∀ (j : J) (y : D.obj j), (Spec.preimage (l j)).hom y ≠ 0 → IsUnit (c.ι.app j y) := by
    intro j y hy
    obtain ⟨n, f, hf⟩ := key U x Ω s D c V a l e t hP j y hy
    have h : c.ι.app j y = c.ι.app n (D.map f y) := by
      rw [← c.w f]; rfl
    rw [h]; exact hf.map _
  have hrep : ∀ z : c.pt, ∃ (j : J) (y : D.obj j), c.ι.app j y = z := fun z =>
    Concrete.isColimit_exists_rep D hc z
  have : Nontrivial c.pt := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' : c.ι.app j 0 = c.ι.app j 1 := by rw [map_zero, map_one]; exact h
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc _ _ h'
    have := congrArg (Spec.preimage (l k)).hom hfg
    rw [map_zero, map_one, map_zero, map_one] at this
    exact zero_ne_one this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨j, y, rfl⟩ := hrep z
  by_cases hy : (Spec.preimage (l j)).hom y = 0
  · right
    have h1 : (Spec.preimage (l j)).hom (1 - y) ≠ 0 := by
      rw [map_sub, map_one, hy, sub_zero]; exact one_ne_zero
    have := hunit j (1 - y) h1
    rwa [map_sub, map_one] at this
  · left; exact hunit j y hy

end LateralTheory.E.StrictHenselianLocalization
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSHNbSysOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf LateralTheory.E.StrictHenselianNeighbourhood

namespace LateralTheory.E.EtaleNeighbourhoodSystem

section
variable {S : Scheme.{0}} {Ω : Type} [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)

abbrev Fb : S.Etale ⥤ Type := Scheme.Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))

lemma exists_affine (i : (Fb s).Elements) :
    ∃ j : (Fb s).Elements, IsAffine j.1.left ∧ Nonempty (j ⟶ i) := by
  rcases i with ⟨x⟩
  rename_i X
  cases X with | _ Y f
  obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
  dsimp at y hy
  obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec R ⟶ Y)
      (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
    obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (x := y.base default) (U := ⊤) (by simp)
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  refine ⟨Functor.elementsMk (Fb s) ((Scheme.AffineEtale.Spec S).obj (Scheme.AffineEtale.mk (j ≫ f))) (Over.homMk y'), ?_,
    ⟨⟨MorphismProperty.Over.homMk j rfl trivial, by cat_disch⟩⟩⟩
  change IsAffine (Spec R)
  infer_instance

lemma exists_small : ∃ (Q : Set (Fb s).Elements), Small.{0} Q ∧ (∀ j ∈ Q, IsAffine j.1.left) ∧
    ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i) := by
  haveI : InitiallySmall.{0} (Fb s).Elements := (Scheme.pointSmallEtale s).initiallySmall
  obtain ⟨Q0, hQ0, h0⟩ := InitiallySmall.exists_small_weakly_initial_set.{0} (Fb s).Elements
  choose g hg hg' using exists_affine s
  refine ⟨g '' Q0, ?_, ?_, ?_⟩
  · haveI := hQ0; infer_instance
  · rintro _ ⟨i, -, rfl⟩; exact hg i
  · intro i
    obtain ⟨k, hk, ⟨f⟩⟩ := h0 i
    exact ⟨g k, ⟨k, hk, rfl⟩, ⟨(hg' k).some ≫ f⟩⟩

variable (Q : Set (Fb s).Elements) [Small.{0} Q]

def ι : Shrink.{0} Q → (Fb s).Elements := fun q => ((equivShrink Q).symm q).1
lemma ι_mem (q : Shrink.{0} Q) : ι s Q q ∈ Q := ((equivShrink Q).symm q).2

abbrev Jc := InducedCategory (Fb s).Elements (ι s Q)

lemma exists_of_wi (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) (d : (Fb s).Elements) :
    ∃ c : Jc s Q, Nonempty ((ι s Q c) ⟶ d) := by
  obtain ⟨j, hj, ⟨f⟩⟩ := hwi d
  exact ⟨equivShrink Q ⟨j, hj⟩, ⟨eqToHom (by simp [ι]) ≫ f⟩⟩

lemma cof (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) : IsCofiltered (Jc s Q) := by
  have h := exists_of_wi s Q hwi
  obtain ⟨d⟩ := IsCofiltered.nonempty (C := (Fb s).Elements)
  exact
  { cone_objs := fun a b => by
      obtain ⟨c, ⟨hc⟩⟩ := h (IsCofiltered.min (ι s Q a) (ι s Q b))
      exact ⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.minToLeft _ _),
        InducedCategory.homMk (hc ≫ IsCofiltered.minToRight _ _), trivial⟩
    cone_maps := fun a b f g => by
      obtain ⟨c, ⟨hc⟩⟩ := h (IsCofiltered.eq f.hom g.hom)
      refine ⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.eqHom f.hom g.hom), ?_⟩
      apply InducedCategory.hom_ext
      show (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ f.hom = (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ g.hom
      rw [Category.assoc, Category.assoc, IsCofiltered.eq_condition]
    nonempty := ⟨(h d).choose⟩ }

def G : Jc s Q ⥤ Scheme.{0} :=
  inducedFunctor (ι s Q) ⋙ CategoryOfElements.π (Fb s) ⋙ Scheme.Etale.forget S ⋙ Over.forget S

def D : (Jc s Q)ᵒᵖ ⥤ CommRingCat.{0} := (G s Q).op ⋙ Scheme.Γ

end

section Sys
variable {B : Scheme.{0}} {U : B.Etale} {Ω : Type} [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) (Q : Set (Fb s).Elements) [Small.{0} Q]

def pt (j : Jc s Q) : Spec (CommRingCat.of Ω) ⟶ (G s Q).obj j := (ι s Q j).2.left

lemma pt_w (j : Jc s Q) : pt s Q j ≫ (ι s Q j).1.hom = s := Over.w (ι s Q j).2

lemma G_w {j k : Jc s Q} (m : k ⟶ j) : (G s Q).map m ≫ (ι s Q j).1.hom = (ι s Q k).1.hom :=
  MorphismProperty.Over.w m.hom.1

lemma pt_map {j k : Jc s Q} (m : k ⟶ j) : pt s Q k ≫ (G s Q).map m = pt s Q j :=
  congrArg CommaMorphism.left m.hom.2

def V (j : (Jc s Q)ᵒᵖ) : B.Etale :=
  MorphismProperty.Over.mk ⊤ ((ι s Q j.unop).1.hom ≫ U.hom)
    (by have := (ι s Q j.unop).1.prop; have := U.prop; exact Etale.etale_comp _ _)

def a (j : (Jc s Q)ᵒᵖ) : V s Q j ⟶ U :=
  MorphismProperty.Over.homMk (ι s Q j.unop).1.hom rfl trivial

variable (haff : ∀ j ∈ Q, IsAffine j.1.left)
include haff

lemma aff (j : Jc s Q) : IsAffine ((G s Q).obj j) := haff _ (ι_mem s Q j)

def e (j : (Jc s Q)ᵒᵖ) : Sp ((D s Q).obj j) ⟶ (G s Q).obj j.unop :=
  haveI := aff s Q haff j.unop; ((G s Q).obj j.unop).isoSpec.inv

lemma e_iso (j : (Jc s Q)ᵒᵖ) : IsIso (e s Q haff j) := by unfold e; exact Iso.isIso_inv _

def l (j : (Jc s Q)ᵒᵖ) : Spec (CommRingCat.of Ω) ⟶ Sp ((D s Q).obj j) :=
  haveI := aff s Q haff j.unop; pt s Q j.unop ≫ ((G s Q).obj j.unop).isoSpec.hom

lemma l_e (j : (Jc s Q)ᵒᵖ) : l s Q haff j ≫ e s Q haff j = pt s Q j.unop := by
  unfold l e
  exact (Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))

lemma nat {j k : (Jc s Q)ᵒᵖ} (f : j ⟶ k) :
    Spec.map ((D s Q).map f) ≫ e s Q haff j = e s Q haff k ≫ (G s Q).map f.unop := by
  haveI := aff s Q haff j.unop; haveI := aff s Q haff k.unop
  exact Scheme.isoSpec_inv_naturality ((G s Q).map f.unop)

def t (j0 : (Jc s Q)ᵒᵖ) : Sp (colimit.cocone (D s Q)).pt ⟶ U.left :=
  Spec.map ((colimit.cocone (D s Q)).ι.app j0) ≫ e s Q haff j0 ≫ (ι s Q j0.unop).1.hom

lemma main (x : U.left) (hx : s default = x) (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (_ : IsColimit c) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t := by
  haveI := cof s Q hwi
  obtain ⟨j0⟩ := IsFiltered.nonempty (C := (Jc s Q)ᵒᵖ)
  have hcomp0 : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k),
      Spec.map ((D s Q).map f) ≫ e s Q haff j ≫ (a s Q j).left = e s Q haff k ≫ (a s Q k).left := by
    intro j k f
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (a s Q j).left) (nat s Q haff f)).trans
      ((Category.assoc _ _ _).trans (congrArg (e s Q haff k ≫ ·) (G_w s Q f.unop))))
  have key : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k),
      Spec.map ((colimit.cocone (D s Q)).ι.app j) ≫ e s Q haff j ≫ (a s Q j).left =
        Spec.map ((colimit.cocone (D s Q)).ι.app k) ≫ e s Q haff k ≫ (a s Q k).left := by
    intro j k f
    rw [← (colimit.cocone (D s Q)).w f, Spec.map_comp, Category.assoc, hcomp0 j k f]
  refine ⟨(Jc s Q)ᵒᵖ, inferInstance, inferInstance, D s Q, colimit.cocone _, colimit.isColimit _,
    V s Q, a s Q, l s Q haff, e s Q haff, t s Q haff j0, hx, e_iso s Q haff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    erw [reassoc_of% (l_e s Q haff j)]
    exact pt_w s Q j.unop
  · intro j k f
    have := hcomp0 j k f
    simp only [CommRingCat.ofHom_hom]
    exact this
  · intro j
    simp only [CommRingCat.ofHom_hom]
    obtain ⟨k, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs j j0
    erw [key j k f, ← key j0 k g]
    rfl
  · intro j k f
    haveI := e_iso s Q haff j
    rw [← cancel_mono (e s Q haff j)]
    simp only [CommRingCat.ofHom_hom, Category.assoc]
    rw [nat, reassoc_of% (l_e s Q haff k), l_e, pt_map]
  · intro U' b l' hl'
    let X' : U.left.Etale := MorphismProperty.Over.mk ⊤ b.left inferInstance
    obtain ⟨c, ⟨hc⟩⟩ := exists_of_wi s Q hwi (Functor.elementsMk (Fb s) X' (Over.homMk l' hl'))
    refine ⟨op c, hc.1.left, MorphismProperty.Over.w hc.1, ?_⟩
    erw [reassoc_of% (l_e s Q haff (op c))]
    exact congrArg CommaMorphism.left hc.2
  · intro U' b j g g' hg hg' heq
    erw [reassoc_of% (l_e s Q haff j), reassoc_of% (l_e s Q haff j)] at heq
    let X' : U.left.Etale := MorphismProperty.Over.mk ⊤ b.left inferInstance
    have hy : (pt s Q j.unop ≫ g) ≫ b.left = s := by
      exact (Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) hg).trans (pt_w s Q j.unop))
    let y : (Fb s).Elements := Functor.elementsMk (Fb s) X' (Over.homMk (pt s Q j.unop ≫ g) hy)
    let u : ι s Q j.unop ⟶ y := ⟨MorphismProperty.Over.homMk (B := X') g hg trivial,
      by apply Over.OverMorphism.ext; rfl⟩
    let u' : ι s Q j.unop ⟶ y := ⟨MorphismProperty.Over.homMk (B := X') g' hg' trivial,
      by apply Over.OverMorphism.ext; exact heq.symm⟩
    obtain ⟨c, ⟨hc⟩⟩ := exists_of_wi s Q hwi (IsCofiltered.eq u u')
    let m : c ⟶ j.unop := InducedCategory.homMk (hc ≫ IsCofiltered.eqHom u u')
    refine ⟨op c, m.op, ?_⟩
    have h0 : (hc ≫ IsCofiltered.eqHom u u') ≫ u = (hc ≫ IsCofiltered.eqHom u u') ≫ u' := by
      rw [Category.assoc, Category.assoc, IsCofiltered.eq_condition]
    have h1 := congrArg (fun z => z.1.left) h0
    simp only [CommRingCat.ofHom_hom]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) (nat s Q haff m.op)).trans ((Category.assoc _ _ _).trans
      ((congrArg (e s Q haff (op c) ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g') (nat s Q haff m.op)).symm.trans (Category.assoc _ _ _))))))

end Sys

theorem LeafSHNbSys_of : LeafSHNbSys := by
  intro B U x
  let Ω := SeparableClosure (U.left.residueField x)
  let s : Spec (CommRingCat.of Ω) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)) ≫ U.left.fromSpecResidueField x
  have hx : s default = x := by
    first | exact Scheme.fromSpecResidueField_apply x _ | (simp [s]; exact Scheme.fromSpecResidueField_apply x _)
  obtain ⟨Q, hQs, haff, hwi⟩ := exists_small s
  haveI := hQs
  exact ⟨Ω, inferInstance, inferInstance, s, main s Q haff x hx hwi⟩

end LateralTheory.E.EtaleNeighbourhoodSystem
end
end
