module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafMapFPPf
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafPairFPPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafPairFPPf

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') :
    toR R' ≫ incl h = toR R := by
  simp only [toR, incl, ← Spec.map_comp]
  congr 1

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem raise {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R')
    {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D) (hq : FP q)
    (hs : IsPullback v c q (toR R)) :
    ∃ (E : Scheme.{0}) (q' : E ⟶ Sp R') (w : C ⟶ E), FP q' ∧ IsPullback w c q' (toR R') := by
  refine ⟨pullback q (incl h), pullback.snd _ _, pullback.lift v (c ≫ toR R') ?_, fp_snd _ _ hq, ?_⟩
  · rw [Category.assoc, toR_incl, hs.w]
  · refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (h₂₂ := incl h) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, toR_incl]
    exact hs

def LeafMapFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) {D0 D1 : Scheme.{0}} (q : D0 ⟶ Sp R) (q1 : D1 ⟶ Sp R)
    (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1), FP q → FP q1 → IsPullback v0 c0 q (toR R) →
    IsPullback v1 (γ1 ≫ c0) q1 (toR R) →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (w0 : C0 ⟶ E0)
      (w1 : C1 ⟶ E1), FP q' ∧ FP (e1 ≫ q') ∧ IsPullback w0 c0 q' (toR R') ∧
      IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1

theorem pairDescent_of_objects_morphisms (hO : LeafObjFP) (hM : LeafMapFP) : LeafPairFP := by
  intro k _ Ω _ _ R hR C0 C1 c0 γ1 h1 D0 q v0 hq hsq
  obtain ⟨R1, hR1, D1, q1, v1, hq1, hs1⟩ := hO k Ω (γ1 ≫ c0) h1
  obtain ⟨E0, q0', w0, hq0', hs0'⟩ := raise (le_sup_left : R ≤ R ⊔ R1) c0 q v0 hq hsq
  obtain ⟨E1, q1', w1, hq1', hs1'⟩ := raise (le_sup_right : R1 ≤ R ⊔ R1) (γ1 ≫ c0) q1 v1 hq1 hs1
  exact hM k Ω (R ⊔ R1) (hR.sup hR1) c0 γ1 q0' q1' w0 w1 hq0' hq1' hs0' hs1'

end LateralTheory.E.LeafPairFPPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf

namespace LateralTheory.E.LeafMapFPPf

section
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

theorem incl_comp {R S T : Subalgebra k Ω} (h1 : R ≤ S) (h2 : S ≤ T) :
    incl h2 ≫ incl h1 = incl (h1.trans h2) := by
  simp only [incl, ← Spec.map_comp]
  congr 1

theorem incl_refl (R : Subalgebra k Ω) : incl (le_refl R) = 𝟙 _ := by
  simp only [incl]
  rw [← Spec.map_id]
  congr 1

theorem sq {R S : Subalgebra k Ω} (h : R ≤ S) {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {q : D ⟶ Sp R} {v : C ⟶ D}
    (hs : IsPullback v c q (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR S) (by rw [Category.assoc, toR_incl, hs.w])) c
      (pullback.snd q (incl h)) (toR S) :=
  IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (h₂₂ := incl h)
    (by rw [pullback.lift_fst, toR_incl]; exact hs) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

def dgMap {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S)
    (hT : R ≤ T) (h : S ≤ T) : pullback q1 (incl hT) ⟶ pullback q1 (incl hS) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ incl h) (by
    rw [pullback.condition, Category.assoc, incl_comp])

@[reassoc (attr := simp)]
theorem dgMap_fst {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S)
    (hT : R ≤ T) (h : S ≤ T) : dgMap q1 hS hT h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem dgMap_snd {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S)
    (hT : R ≤ T) (h : S ≤ T) : dgMap q1 hS hT h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ incl h :=
  pullback.lift_snd _ _ _

def dg {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) : (GlobalTheory.FGAbove R)ᵒᵖ ⥤ Scheme.{0} where
  obj S := pullback q1 (incl S.unop.2.2)
  map {S T} f := dgMap q1 _ _ (show T.unop.1 ≤ S.unop.1 from leOfHom f.unop)
  map_id S := by apply pullback.hom_ext <;> simp [incl_refl]
  map_comp f g := by apply pullback.hom_ext <;> simp [incl_comp]

def dgT {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) : dg q1 ⟶ (Functor.const _).obj (Sp R) where
  app S := pullback.fst _ _ ≫ q1
  naturality S T f := by simp [dg]

theorem dgπ_map {R : Subalgebra k Ω} {C1 D1 : Scheme.{0}} (c1 : C1 ⟶ Sp Ω) (q1 : D1 ⟶ Sp R) (v1 : C1 ⟶ D1)
    (hs : IsPullback v1 c1 q1 (toR R)) {S T : Subalgebra k Ω} (hS : R ≤ S) (hT : R ≤ T) (h : S ≤ T) :
    pullback.lift v1 (c1 ≫ toR T) (by rw [Category.assoc, toR_incl, hs.w]) ≫ dgMap q1 hS hT h =
      (pullback.lift v1 (c1 ≫ toR S) (by rw [Category.assoc, toR_incl, hs.w]) : C1 ⟶ pullback q1 (incl hS)) := by
  apply pullback.hom_ext
  · erw [Category.assoc, dgMap_fst, pullback.lift_fst, pullback.lift_fst]
  · erw [Category.assoc, dgMap_snd, pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc, toR_incl]

def dgCone {R : Subalgebra k Ω} {C1 D1 : Scheme.{0}} (c1 : C1 ⟶ Sp Ω) (q1 : D1 ⟶ Sp R) (v1 : C1 ⟶ D1)
    (hs : IsPullback v1 c1 q1 (toR R)) : Cone (dg q1) where
  pt := C1
  π := { app S := pullback.lift v1 (c1 ≫ toR S.unop.1) (by rw [Category.assoc, toR_incl, hs.w])
         naturality S T f := by
           exact (Category.id_comp _).trans (dgπ_map c1 q1 v1 hs _ _ _).symm }

end

def LeafLimFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C1 D1 : Scheme.{0}} (c1 : C1 ⟶ Sp Ω) (q1 : D1 ⟶ Sp R) (v1 : C1 ⟶ D1) (hs : IsPullback v1 c1 q1 (toR R)),
    FP q1 → Nonempty (IsLimit (dgCone c1 q1 v1 hs))

def LeafStagesFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R), FP q1 →
    (∀ S : (GlobalTheory.FGAbove R)ᵒᵖ, CompactSpace ((dg q1).obj S) ∧ QuasiSeparatedSpace ((dg q1).obj S)) ∧
    ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1), IsAffineHom (dgMap q1 S.2.2 T.2.2 h)

theorem morphismDescent_of_isLimit (hL : LeafLimFP) (hI : LeafStagesFP) : LeafMapFP := by
  intro k _ Ω _ _ R hR C0 C1 c0 γ1 D0 D1 q q1 v0 v1 hq hq1 hs0 hs1
  haveI := GlobalTheory.FGAbove.isFiltered hR
  obtain ⟨hc⟩ := hL k Ω R hR (γ1 ≫ c0) q1 v1 hs1 hq1
  obtain ⟨hcs, haf⟩ := hI k Ω R q1 hq1
  haveI := hq.1
  haveI : ∀ S : (GlobalTheory.FGAbove R)ᵒᵖ, CompactSpace ((dg q1).obj S) := fun S => (hcs S).1
  haveI : ∀ S : (GlobalTheory.FGAbove R)ᵒᵖ, QuasiSeparatedSpace ((dg q1).obj S) := fun S => (hcs S).2
  haveI : ∀ {S T : (GlobalTheory.FGAbove R)ᵒᵖ} (f : S ⟶ T), IsAffineHom ((dg q1).map f) := fun f => haf _ _ _
  obtain ⟨S, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (D := dg q1)
    (t := dgT q1) (f := q) (c := dgCone (γ1 ≫ c0) q1 v1 hs1) hc (γ1 ≫ v0) (by
      ext S
      dsimp [dgCone, dgT, dg]
      rw [← Category.assoc, pullback.lift_fst, hs1.w]
      simp only [Category.assoc, hs0.w])
  let P := pullback q1 (incl S.unop.2.2)
  let g' : P ⟶ D0 := g
  let w1 : C1 ⟶ P := pullback.lift v1 ((γ1 ≫ c0) ≫ toR S.unop.1) (by rw [Category.assoc, toR_incl, hs1.w])
  have hg1' : w1 ≫ g' = γ1 ≫ v0 := hg1
  have hg2' : g' ≫ q = pullback.snd q1 (incl S.unop.2.2) ≫ incl S.unop.2.2 := by
    rw [show g' ≫ q = pullback.fst q1 (incl S.unop.2.2) ≫ q1 from hg2]; exact pullback.condition
  refine ⟨S.unop.1, S.unop.2.1, pullback q (incl S.unop.2.2), P, pullback.snd _ _,
    pullback.lift g' (pullback.snd _ _) hg2', pullback.lift v0 (c0 ≫ toR S.unop.1)
      (by rw [Category.assoc, toR_incl, hs0.w]), w1, fp_snd _ _ hq, ?_, sq S.unop.2.2 hs0, ?_, ?_⟩
  · rw [pullback.lift_snd]; exact fp_snd _ _ hq1
  · rw [pullback.lift_snd]; exact sq S.unop.2.2 hs1
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact hg1'.symm
    · simp only [Category.assoc, pullback.lift_snd, w1]

end LateralTheory.E.LeafMapFPPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpreadRelDimPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf LateralTheory.E.LeafPropsDescendPf.Split LateralTheory.E.LeafSpreadSmoothPf

namespace LateralTheory.E.LeafSpreadRelDimPf

def LeafRelDimAtImage : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → Smooth q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∀ y : C, ∃ V : D.Opens, v y ∈ V ∧ SmoothOfRelativeDimension 1 (V.ι ≫ q)

def LeafGenericOpenSpread : Prop := ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] (D : Scheme.{0}) (q : D ⟶ Sp A),
    IsAffine D → LocallyOfFinitePresentation q → ∀ U : D.Opens,
    (∀ x : D, (show PrimeSpectrum A from q x).asIdeal = ⊥ → x ∈ U) →
    ∃ f : A, f ≠ 0 ∧ ∀ x : D, f ∉ (show PrimeSpectrum A from q x).asIdeal → x ∈ U

theorem generic_pt {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (ω : Sp Ω) :
    (show PrimeSpectrum R from toR R ω).asIdeal = ⊥ := by
  have h0 : (show PrimeSpectrum Ω from ω).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change Ideal.comap (algebraMap R Ω) (show PrimeSpectrum Ω from ω).asIdeal = ⊥
  rw [h0]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R Ω)

theorem LeafSpreadRelDim_of_sub (hA : LeafRelDimAtImage) (hB : LeafGenericOpenSpread) : LeafSpreadRelDim := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hsm hs hv
  let U : D.Opens := sSup {V : D.Opens | SmoothOfRelativeDimension 1 (V.ι ≫ q)}
  have hU : ∀ x : D, (show PrimeSpectrum R from q x).asIdeal = ⊥ → x ∈ U := by
    intro x hx
    let ω : Sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
    have he : q x = toR R ω := PrimeSpectrum.ext (hx.trans (generic_pt R ω).symm)
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x ω he
    obtain ⟨V, hV, hVs⟩ := hA k Ω R hR c q v hD hlfp hsm hs hv (hv.isoPullback.inv z)
    have : v (hv.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz1]
    rw [this] at hV
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨V, hVs, hV⟩
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨f, hf0, hf⟩ := hB R D q hD hlfp U hU
  have hf0' : (f : Ω) ≠ 0 := fun h => hf0 (Subtype.ext h)
  let T : Subalgebra k Ω := Algebra.adjoin k ((({((f : Ω))⁻¹} : Finset Ω)) : Set Ω)
  refine ⟨R ⊔ T, le_sup_left, hR.sup (Subalgebra.fg_adjoin_finset _), ?_⟩
  intro R' hR' hRR E q' r hE
  have hinv : ((f : Ω))⁻¹ ∈ R' :=
    hR' (le_sup_right (a := R) (Algebra.subset_adjoin (by simp)))
  have hunit : IsUnit (Subalgebra.inclusion hRR f) := by
    have h1 : Subalgebra.inclusion hRR f * (⟨_, hinv⟩ : R') = 1 := Subtype.ext (mul_inv_cancel₀ hf0')
    exact isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  have hL : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun V : {V : D.Opens // SmoothOfRelativeDimension 1 (V.ι ≫ q)} => r ⁻¹ᵁ V.1) ?_ ?_
  · refine top_le_iff.mp fun e _ => ?_
    have hq : q (r e) = incl hRR (q' e) := by
      rw [← Scheme.Hom.comp_apply, hE.w, Scheme.Hom.comp_apply]
    have hx : f ∉ (show PrimeSpectrum R from q (r e)).asIdeal := by
      rw [hq]
      change Subalgebra.inclusion hRR f ∉ (show PrimeSpectrum R' from q' e).asIdeal
      exact fun h => (show PrimeSpectrum R' from q' e).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ h hunit)
    obtain ⟨V, hVs, hV⟩ := TopologicalSpace.Opens.mem_sSup.mp (hf (r e) hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVs⟩, hV⟩
  · intro V
    have h2 := (isPullback_morphismRestrict r V.1).paste_vert hE
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback h2 V.2

end LateralTheory.E.LeafSpreadRelDimPf

namespace LateralTheory.E.LeafSpreadRelDimPf.Spread
open Topology TopologicalSpace

theorem exists_ne_zero_of_constructible {A : Type} [CommRing A] [IsDomain A] (T : Set (PrimeSpectrum A))
    (hT : IsConstructible T) (h : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉ T) :
    ∃ f : A, f ≠ 0 ∧ ∀ p ∈ T, f ∈ p.asIdeal := by
  revert h
  induction T, hT using IsConstructible.induction_of_isTopologicalBasis
    (fun f : A => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)))
    PrimeSpectrum.isTopologicalBasis_basic_opens (fun f => PrimeSpectrum.isCompact_basicOpen f) with
  | sdiff g s hs =>
    intro h
    by_cases hg : g = 0
    · refine ⟨1, one_ne_zero, fun p hp => ?_⟩
      have := hp.1
      simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hg] at this
      exact absurd p.asIdeal.zero_mem this
    · have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
        simpa [PrimeSpectrum.mem_basicOpen] using hg
      have : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ ⋃ j ∈ s, (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum A)) := by
        by_contra hn; exact h ⟨hη, hn⟩
      obtain ⟨j, hj, hηj⟩ := Set.mem_iUnion₂.mp this
      have hj0 : j ≠ 0 := by simpa [PrimeSpectrum.mem_basicOpen] using hηj
      refine ⟨j, hj0, fun p hp => ?_⟩
      have h2 := hp.2
      by_contra hn
      exact h2 (Set.mem_iUnion₂.mpr ⟨j, hj, by simpa [PrimeSpectrum.mem_basicOpen] using hn⟩)
  | union s hs t ht ihs iht =>
    intro h
    obtain ⟨f1, h1, hf1⟩ := ihs (fun hh => h (Or.inl hh))
    obtain ⟨f2, h2, hf2⟩ := iht (fun hh => h (Or.inr hh))
    refine ⟨f1 * f2, mul_ne_zero h1 h2, fun p hp => ?_⟩
    rcases hp with hp | hp
    · exact Ideal.mul_mem_right _ _ (hf1 p hp)
    · exact Ideal.mul_mem_left _ _ (hf2 p hp)

theorem LeafGenericOpenSpread_pf : LeafGenericOpenSpread := by
  intro A _ _ _ D q hD hlfp U hU
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian D := {}
  have hZ : IsConstructible ((U : Set D)ᶜ) :=
    ((NoetherianSpace.isCompact (U : Set D)).isConstructible U.isOpen).compl
  have : QuasiCompact q := inferInstance
  have hI := q.isConstructible_image hZ
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_of_constructible (A := A) (q '' ((U : Set D)ᶜ)) hI (by
    rintro ⟨x, hx, hqx⟩
    exact hx (hU x (by rw [hqx])))
  refine ⟨f, hf0, fun x hx => ?_⟩
  by_contra hxU
  exact hx (hf (q x) ⟨x, hxU, rfl⟩)

end LateralTheory.E.LeafSpreadRelDimPf.Spread

namespace LateralTheory.E.LeafSpreadRelDimPf

theorem LeafRelDimAtImage_pf : LeafRelDimAtImage := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hsm hs hv y
  obtain ⟨n, W, hW, hWs⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim q (v y)
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_base hv hWs hs y hW
  subst this
  exact ⟨W, hW, hWs⟩

theorem LeafSpreadRelDim_of : LeafSpreadRelDim :=
  LeafSpreadRelDim_of_sub LeafRelDimAtImage_pf Spread.LeafGenericOpenSpread_pf

end LateralTheory.E.LeafSpreadRelDimPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CurveKrullDim
section -- merged from Development.EtaleCohomology.EtaleSheaves.CurveKrullDimTopology
open Set Topology TopologicalSpace

namespace LateralTheory.E.CurveKrullDim

variable {X : Type} [TopologicalSpace X]

theorem two_le_dim (A B : IrreducibleCloseds X) (hAB : (A : Set X) ⊂ B) (hB : (B : Set X) ≠ univ)
    [IrreducibleSpace X] : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let T : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h1 : A < B := by
    rw [← SetLike.coe_ssubset_coe]; exact hAB
  have h2 : B < T := by
    rw [← SetLike.coe_ssubset_coe]; exact ssubset_univ_iff.mpr hB
  let l : LTSeries (IrreducibleCloseds X) := ⟨2, ![A, B, T], fun i => by
    fin_cases i
    · exact h1
    · exact h2⟩
  have hl : l.length = 2 := rfl
  unfold topologicalKrullDim
  exact Order.le_krullDim_iff.mpr ⟨l, hl⟩

theorem closed_of_ne_univ [IrreducibleSpace X] [T0Space X] (hd : topologicalKrullDim X ≤ 1) (z : X)
    (hz : closure ({z} : Set X) ≠ univ) : IsClosed ({z} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hne
  have hyz : closure ({y} : Set X) ⊂ closure {z} := by
    refine ⟨closure_minimal (by simpa using hy) isClosed_closure, fun h => hne ?_⟩
    have h1 : z ⤳ y := specializes_iff_mem_closure.mpr hy
    have h2 : y ⤳ z := specializes_iff_mem_closure.mpr (h (subset_closure rfl))
    exact (h1.antisymm h2).eq.symm
  have := two_le_dim ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ hyz hz
  have h3 := this.trans hd
  norm_cast at h3

theorem finite_of_closed [IrreducibleSpace X] [T0Space X] [QuasiSober X] [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) (Z : Set X) (hZ : IsClosed Z) (hne : Z ≠ univ) : Z.Finite := by
  have hpt : ∀ z ∈ Z, IsClosed ({z} : Set X) := fun z hz => closed_of_ne_univ hd z
    (fun h => hne (eq_univ_of_univ_subset (h ▸ closure_minimal (by simpa using hz) hZ)))
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Z)
  have hsub : ∀ S ∈ irreducibleComponents Z, (Subtype.val '' S).Subsingleton := by
    intro S hS
    have hirr : IsIrreducible (Subtype.val '' S) := hS.1.image _ continuous_subtype_val.continuousOn
    obtain ⟨g, hg⟩ := QuasiSober.sober hirr.closure isClosed_closure
    have hgZ : g ∈ Z := closure_minimal (by rintro _ ⟨x, -, rfl⟩; exact x.2) hZ (hg.mem)
    have : closure (Subtype.val '' S) = {g} := by
      rw [← hg.def, (hpt g hgZ).closure_eq]
    intro a ha b hb
    have ha' := subset_closure ha; have hb' := subset_closure hb
    rw [this] at ha' hb'
    exact ha'.trans hb'.symm
  have : Z = ⋃ S ∈ irreducibleComponents Z, Subtype.val '' S := by
    ext x; constructor
    · intro hx
      have : (⟨x, hx⟩ : Z) ∈ ⋃₀ irreducibleComponents Z := by rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨S, hS, hxS⟩ := this
      exact mem_iUnion₂.mpr ⟨S, hS, ⟨_, hxS, rfl⟩⟩
    · intro hx
      obtain ⟨S, -, y, -, rfl⟩ := mem_iUnion₂.mp hx
      exact y.2
  rw [this]
  exact hfin.biUnion fun S hS => (hsub S hS).finite

end LateralTheory.E.CurveKrullDim
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 Set Topology TopologicalSpace

namespace LateralTheory.E.CurveKrullDim

def LeafCurveNotPoint : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsCurve c → ¬ Subsingleton C

theorem dim_le_one (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) {Ω : Type} [Field Ω] {C : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hc : SmoothOfRelativeDimension 1 c) : topologicalKrullDim C ≤ 1 := by
  let e : (⊥ : Subalgebra Ω Ω) ≃+* Ω := (Algebra.botEquiv Ω Ω).toRingEquiv
  let φ : Sp Ω ⟶ Sp (⊥ : Subalgebra Ω Ω) := Spec.map e.toCommRingCatIso.hom
  have : IsIso φ := inferInstance
  have : SmoothOfRelativeDimension 1 (c ≫ φ) := inferInstanceAs (SmoothOfRelativeDimension (1 + 0) (c ≫ φ))
  have h := hD Ω Ω (⊥ : Subalgebra Ω Ω) Subalgebra.fg_bot (c ≫ φ) this
  rwa [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_zero_of_field, zero_add] at h

theorem LeafCurveSmall_of_cut (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) (hP : LeafCurveNotPoint) :
    LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall := by
  intro Ω _ _ C c hc
  obtain ⟨hI, hPr, hS⟩ := id hc
  have : LocallyOfFiniteType c := inferInstance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have : CompactSpace C := by
    have : QuasiCompact c := inferInstance
    exact (quasiCompact_iff_compactSpace c).mp this
  have : IsNoetherian C := by constructor
  have : NoetherianSpace C := inferInstance
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  have hd := dim_le_one hD c hS
  refine ⟨fun hfin => hP Ω c hc ?_, fun Z hZ hinf => ?_⟩
  · have hcp : closedPoints C = univ := by
      have : IsClosed (closedPoints C) := by
        have : closedPoints C = ⋃ x ∈ (hfin.subset (subset_univ (closedPoints C))).toFinset, {x} := by
          ext; simp
        rw [this]; exact isClosed_biUnion_finset fun x hx => by simpa using hx
      rw [← this.closure_eq]; exact closure_closedPoints
    have hη : IsClosed ({genericPoint C} : Set C) := by
      rw [← mem_closedPoints_iff, hcp]; trivial
    have : ({genericPoint C} : Set C) = univ := by
      rw [← hη.closure_eq]; exact (genericPoint_spec C).def
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ ({genericPoint C} : Set C) := this ▸ mem_univ a
    have hb : b ∈ ({genericPoint C} : Set C) := this ▸ mem_univ b
    exact ha.trans hb.symm
  · by_contra hne
    exact hinf (finite_of_closed hd Z hZ hne)

theorem curveNotPoint : LeafCurveNotPoint := by
  intro Ω _ _ C c hc hsub
  obtain ⟨hI, hPr, hS⟩ := id hc
  obtain ⟨x⟩ : Nonempty C := inferInstance
  have : IsAffine C := inferInstance
  let _ : Field Γ(C, ⊤) := (isField_of_isIntegral_of_subsingleton C).toField
  have hft : (c.appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let ι := (Scheme.ΓSpecIso (CommRingCat.of Ω))
  let φ : Ω →+* Γ(C, ⊤) := (c.appTop).hom.comp ι.inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso ι.inv).2)
  let _ : Algebra Ω Γ(C, ⊤) := φ.toAlgebra
  have : Algebra.FiniteType Ω Γ(C, ⊤) := hφ
  have : Module.Finite Ω Γ(C, ⊤) := finite_of_finite_type_of_isJacobsonRing Ω Γ(C, ⊤)
  have hb : Function.Bijective φ := IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hb2 : Function.Bijective (c.appTop).hom := by
    have : (c.appTop).hom = φ.comp ι.hom.hom := by
      ext a; simp [φ]
    rw [this]; exact hb.comp (ConcreteCategory.bijective_of_isIso ι.hom)
  have : IsIso c.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hb2
  have : IsIso c := by
    have h := Scheme.isoSpec_hom_naturality c
    have : c = C.isoSpec.hom ≫ Spec.map c.appTop ≫ (Sp Ω).isoSpec.inv := by
      rw [reassoc_of% h]; simp
    rw [this]; infer_instance
  have h0 : SmoothOfRelativeDimension 0 c := inferInstance
  exact absurd (ReciprocityTheory.ChartRestriction.G.H1.dim_unique c hS h0 x) (by norm_num)

theorem LeafCurveSmall_of (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) :
    LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall :=
  LeafCurveSmall_of_cut hD curveNotPoint

end LateralTheory.E.CurveKrullDim
end
end
