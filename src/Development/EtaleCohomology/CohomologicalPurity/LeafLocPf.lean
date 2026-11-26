module

public import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLocPf
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem LeafLoc_of : LeafLoc := by
  intro d P x W hxW
  have := P.cl; have := P.smX; have := P.smZ
  obtain ⟨T, hT, hxT, -⟩ := exists_isAffineOpen_mem_and_subset (x := P.p.base x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := W ⊓ P.p ⁻¹ᵁ T) ⟨hxW, hxT⟩
  have e : V ≤ P.p ⁻¹ᵁ T := fun y hy => (hVW hy).2
  refine ⟨⟨V, hV⟩, hxV, fun y hy => (hVW hy).1, Γ(P.S, T), inferInstance, (P.p.appLE T V e).hom, ?_, ?_⟩
  · exact HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension (P.e + d)) P.p P.smX ⟨T, hT⟩ ⟨V, hV⟩ e
  · have hV' : IsAffineOpen (P.ι ⁻¹ᵁ V) := hV.preimage P.ι
    have e2 : P.ι ⁻¹ᵁ V ≤ (P.ι ≫ P.p) ⁻¹ᵁ T := fun y hy => e hy
    have h2 := HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension P.e) (P.ι ≫ P.p) P.smZ
      ⟨T, hT⟩ ⟨P.ι ⁻¹ᵁ V, hV'⟩ e2
    have hc : (P.ι ≫ P.p).appLE T (P.ι ⁻¹ᵁ V) e2 = P.p.appLE T V e ≫ P.ι.app V := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [hc] at h2
    have hs : Function.Surjective (P.ι.app V).hom := P.ι.app_surjective V hV
    have hk : P.ι.ker.ideal ⟨V, hV⟩ = RingHom.ker (P.ι.app V).hom := P.ι.ker_apply ⟨V, hV⟩
    rw [hk]
    let eqv := RingHom.quotientKerEquivOfSurjective hs
    have heq : (Ideal.Quotient.mk (RingHom.ker (P.ι.app V).hom)).comp (P.p.appLE T V e).hom =
        eqv.symm.toRingHom.comp ((P.p.appLE T V e ≫ P.ι.app V).hom) := by
      ext a
      simp only [RingHom.comp_apply, CommRingCat.hom_comp]
      apply eqv.injective
      simp [eqv]
    rw [heq]
    exact (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left _ _ h2

end LateralTheory.CohomologicalPurity.ChartCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHsContPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def HtOffCont (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) {J : Type} [SmallCategory J]
    (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
    (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)) (n i : ℤ) : Prop :=
  (∀ x : Ht q (opn (off B (I.map φ))).left n i, ∃ j h, ∃ y,
    pull _ (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h).left (tw q i) n y = x) ∧
  (∀ j h y, pull _ (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h).left
      (tw q i) n y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), pull _ (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h').left (tw q i) n y = 0)

def LeafOffCont : Prop := A1 → A4 → B1 → LeafBd → LeafExc → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (I : Ideal A), I.FG → IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ, HtOffCont q φ I D s t n i

def LeafHsFive : Prop := A1 → B1 → LeafBd → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
  (I : Ideal A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ i : ℤ,
  (∀ m : ℤ, HtOffCont q φ I D s t m i) → ∀ n : ℤ,
  (∀ x : Hs q (opn (off B (I.map φ))) n i, ∃ j h, ∃ y,
    Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = x) ∧
  (∀ j h y, Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), Hs.pull q (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h') n i y = 0)

theorem opn_mono {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  unfold sch
  infer_instance

theorem spec_cont (b1 : B1) (q : ℕ) {B : Type} [CommRing B] {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)) (hc : IsColimit (Cocone.mk _ t))
    (hq : IsUnit (q : B)) (hqj : ∀ j, IsUnit (q : D.obj j)) (n i : ℤ) :
    (∀ x : Ht q (sp B) n i, ∃ j, ∃ y, pull _ (sch.map (Spec.map (t.app j))) (tw q i) n y = x) ∧
    ∀ j (y : Ht q (sch.obj (Spec (D.obj j))) n i), pull _ (sch.map (Spec.map (t.app j))) (tw q i) n y = 0 →
      ∃ (k : J) (f : j ⟶ k), pull _ (sch.map (Spec.map (D.map f))) (tw q i) n y = 0 := by
  have h := b1 q D _ hc n i
  exact ⟨fun x => h.1 x hq, fun j y hy => h.2 j y (hqj j) hy⟩

theorem leafHsCont_of (hB : LeafBd) (hE : LeafExc) (hO : LeafOffCont) (hF : LeafHsFive) : LeafHsCont := by
  intro a1 a4 b1 q A B _ _ φ I hI hq J _ _ D s t hc he n i
  exact hF a1 b1 hB q φ I hq J D s t hc he i (fun m => hO a1 a4 b1 hB hE q φ I hI hq J D s t hc he m i) n

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafSecPf
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafSecPf

theorem LeafSec_of : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  intro A T _ _ φ I μ hφ hμ
  algebraize [φ]
  have : Algebra.Etale A T := RingHom.etale_algebraMap.mp hφ
  set J : Ideal T := I.map φ with hJ
  have hle : I ≤ J.comap φ := Ideal.le_comap_map
  have hker : ∀ a ∈ J, μ a = 0 := by
    intro a ha
    have : J ≤ RingHom.ker μ := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro c hc
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      rw [← RingHom.comp_apply, hμ]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
    exact this ha
  let q : A ⧸ I →+* T ⧸ J := Ideal.quotientMap J φ hle
  let μb : T ⧸ J →+* A ⧸ I := Ideal.Quotient.lift J μ hker
  have hμq : ∀ z, μb (q z) = z := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    show μb (Ideal.Quotient.mk J (φ c)) = _
    simp only [μb, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply, hμ]
  let g : T →ₐ[A] T ⧸ J :=
    { (q.comp μ) with
      commutes' := fun a => by
        show q (μ (φ a)) = Ideal.Quotient.mk J (φ a)
        rw [← RingHom.comp_apply μ φ, hμ]; rfl }
  let f : T →ₐ[A] T ⧸ J := Ideal.Quotient.mkₐ A J
  let ψ : T ⊗[A] T →ₐ[A] T ⧸ J := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have key : ∀ x : T ⊗[A] T, μb (ψ x) = μ (Algebra.TensorProduct.lmul' A x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [ψ, Algebra.TensorProduct.lift_tmul, map_mul, Algebra.TensorProduct.lmul'_apply_tmul]
      congr 1
      all_goals first | rfl | exact hμq _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (ψ (Algebra.FormallyUnramified.elem A T))
  refine ⟨t, ?_, ?_⟩
  · have h1 : μb (Ideal.Quotient.mk J t) = μ t := Ideal.Quotient.lift_mk _ _ _
    rw [← h1, ht, key, Algebra.FormallyUnramified.lmul_elem, map_one]
  · intro s hs
    have h2 := congrArg ψ (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) s)
    simp only [map_mul, ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at h2
    have hg : g s = 0 := by show q (μ s) = 0; rw [hs, map_zero]
    rw [hg, zero_mul] at h2
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht, mul_comm]
    exact h2.symm

end LateralTheory.CohomologicalPurity.LeafSecPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLocCutAug
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafLocCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def EtaleLocBase : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (Y : Scheme.{0}) (g : Y ⟶ X),
  ∃ (D' : J ⥤ Scheme.{0}) (c' : ∀ j, D'.obj j ⟶ Y), (∀ j, IsOpenImmersion (c' j)) ∧
    (∀ y : Y, ∃ j, y ∈ Set.range (c' j)) ∧
    (∀ (y : Y) j k, y ∈ Set.range (c' j) → y ∈ Set.range (c' k) → ∃ l, l ≤ j ∧ l ≤ k ∧ y ∈ Set.range (c' l)) ∧
    ∃ hc' : Coc (D' ⋙ yoneda) (fun j => yoneda.map (c' j)),
      Nonempty (Arrow.mk (pullback.snd (aug _ hc) (sch.map g)) ≅ Arrow.mk (aug _ hc'))

def EtaleLocAug : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R], QuasiIso ((chains R).map (aug _ hc))

theorem LeafLocCut.goal_of (hb : EtaleLocBase) (ha : EtaleLocAug) : LeafLoc := by
  intro J _ D X c ho hcov hdir hc R _ Y g
  obtain ⟨D', c', ho', hcov', hdir', hc', ⟨e⟩⟩ := hb J D X c ho hcov hdir hc Y g
  have h := ha J D' Y c' ho' hcov' hdir' hc' R
  exact (quasiIso_iff_of_arrow_mk_iso _ _ ((chains R).mapArrow.mapIso e.symm)).1 h

end LateralTheory.CohomologicalPurity.TubeCut
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def chainsP (R : Type) [CommRing R] : Spc ⥤ ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ :=
  (SimplicialObject.whiskering _ _).obj (freeP R) ⋙ AlgebraicTopology.alternatingFaceMapComplex _

def LeafQisLocal : Prop := ∀ (R : Type) [CommRing R] (E E' : Spc) (f : E ⟶ E'),
  (∀ n, Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map f) n)) →
  (∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map f) n)) →
  QuasiIso ((chains R).map f)

def LeafAugLocal : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map (aug _ hc)) n) ∧
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map (aug _ hc)) n)

theorem LeafLocCutAug.goal_of (hq : LeafQisLocal) (hl : LeafAugLocal) : EtaleLocAug := by
  intro J _ D X c ho hcov hdir hc R _
  exact hq R _ _ (aug _ hc) (fun n => (hl J D X c ho hcov hdir hc R n).1) (fun n => (hl J D X c ho hcov hdir hc R n).2)

theorem LeafLocCutAll.goal_of (hb : EtaleLocBase) (hq : LeafQisLocal) (hl : LeafAugLocal) : LeafLoc :=
  LeafLocCut.goal_of hb (LeafLocCutAug.goal_of hq hl)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafShrinkPf
noncomputable section

namespace LateralTheory.CohomologicalPurity.ChartCut


open RingHom in
theorem shrink_away {n : ℕ} {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (u v : S)
    (T : Type) [CommRing T] [Algebra S T] [IsLocalization.Away (u * v) T]
    (h : ((algebraMap S (Localization.Away u)).comp ψ).IsStandardSmoothOfRelativeDimension n) :
    ((algebraMap S T).comp ψ).IsStandardSmoothOfRelativeDimension n := by
  let B := Localization.Away (algebraMap S (Localization.Away u) v)
  have h2 : ((algebraMap (Localization.Away u) B).comp
      ((algebraMap S (Localization.Away u)).comp ψ)).IsStandardSmoothOfRelativeDimension n :=
    zero_add n ▸ (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
      (algebraMap S (Localization.Away u) v)).comp h
  have hB : IsLocalization.Away (u * v) B := inferInstance
  let eT : B ≃ₐ[S] T := IsLocalization.algEquiv (Submonoid.powers (u * v)) B T
  have h3 : ((algebraMap S B).comp ψ).IsStandardSmoothOfRelativeDimension n := by
    rw [IsScalarTower.algebraMap_eq S (Localization.Away u) B, RingHom.comp_assoc]; exact h2
  have h4 := (isStandardSmoothOfRelativeDimension_respectsIso (n := n)).left _ eT.toRingEquiv h3
  have hT : algebraMap S T = (eT.toRingEquiv.toRingHom).comp (algebraMap S B) := by
    ext x; exact (eT.commutes x).symm
  rw [hT, RingHom.comp_assoc]; exact h4

theorem LeafShrink_of : LeafShrink := by
  intro e d R A _ _ φ I p hp hIp ⟨h1, h2⟩
  obtain ⟨a, ha1, hap⟩ : ∃ a : A, ((algebraMap A (Localization.Away a)).comp φ).IsStandardSmoothOfRelativeDimension (e + d) ∧ a ∉ p := by
    by_contra hcon
    push Not at hcon
    apply hp.ne_top
    rw [eq_top_iff, ← h1.span_eq_top, Ideal.span_le]
    intro g hg; exact hcon g hg
  have hq : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  obtain ⟨c, hc1, hcq⟩ : ∃ c : A ⧸ I, ((algebraMap (A ⧸ I) (Localization.Away c)).comp ((Ideal.Quotient.mk I).comp φ)).IsStandardSmoothOfRelativeDimension e ∧ c ∉ p.map (Ideal.Quotient.mk I) := by
    by_contra hcon
    push Not at hcon
    apply hq.ne_top
    rw [eq_top_iff, ← h2.span_eq_top, Ideal.span_le]
    intro g hg; exact hcon g hg
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hbp : b ∉ p := fun hb => hcq (Ideal.mem_map_of_mem _ hb)
  refine ⟨a * b, fun h => (hp.mem_or_mem h).elim hap hbp, ?_⟩
  intro A' _ _ _
  refine ⟨shrink_away φ a b A' ha1, ?_⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b)))
      (A' ⧸ I.map (algebraMap A A')) := inferInstance
  have key : Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b)) =
      Submonoid.powers (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, mul_comm a b, map_mul]; rfl
  have : IsLocalization.Away (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a)
      (A' ⧸ I.map (algebraMap A A')) := by
    unfold IsLocalization.Away; rw [← key]; exact hloc
  have hcomp : (Ideal.Quotient.mk (I.map (algebraMap A A'))).comp ((algebraMap A A').comp φ) =
      (algebraMap (A ⧸ I) (A' ⧸ I.map (algebraMap A A'))).comp ((Ideal.Quotient.mk I).comp φ) := by
    ext x; rfl
  rw [hcomp]
  exact shrink_away _ _ (Ideal.Quotient.mk I a) _ hc1

end LateralTheory.CohomologicalPurity.ChartCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPickPf
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem pick_span_top (A M K : Type) [CommRing A] [AddCommGroup M] [Module A M] [Field K] [Algebra A K] :
    Submodule.span K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  induction v using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul k m =>
    have : k ⊗ₜ[A] m = k • ((1 : K) ⊗ₜ[A] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add a c ha hc => exact add_mem (ha trivial) (hc trivial)

theorem LeafPick_of : LeafPick := by
  intro d A M _ _ _ _ p _ hd
  set K := p.ResidueField
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m)
  rw [pick_span_top] at hbspan
  let B : Module.Basis b K (K ⊗[A] M) := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  let _ : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = d := by rw [← hd, Module.finrank_eq_card_basis B]
  let B' := B.reindex (Fintype.equivFinOfCardEq hcard)
  have hmem : ∀ i, ∃ m : M, (1 : K) ⊗ₜ[A] m = B' i := by
    intro i
    have : B' i ∈ b := by simp [B', B]
    obtain ⟨m, hm⟩ := hbs this
    exact ⟨m, hm⟩
  choose x hx using hmem
  set N := Submodule.span A (Set.range x)
  let g : K ⊗[A] M →ₗ[K] K ⊗[A] (M ⧸ N) := (N.mkQ).baseChange K
  have hgsurj : Function.Surjective g :=
    LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N)
  have hg0 : ∀ v, g v = 0 := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range B') := by rw [B'.span_eq]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i, rfl⟩
      rw [← hx i]
      simp [g, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨i, rfl⟩)]
    · simp
    · intro a c _ _ ha hc; simp [ha, hc]
    · intro r a _ ha; simp [ha]
  have hsub : Subsingleton (K ⊗[A] (M ⧸ N)) := by
    constructor; intro u w
    obtain ⟨u', rfl⟩ := hgsurj u
    obtain ⟨w', rfl⟩ := hgsurj w
    rw [hg0, hg0]
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A (M ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    intro h
    exact (not_nontrivial_iff_subsingleton.2 hsub) h
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.1 hnot
  refine ⟨x, f, hfp, fun m => ?_⟩
  rw [SetLike.mem_coe, Module.mem_annihilator] at hf
  have := hf (Submodule.Quotient.mk m)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

end LateralTheory.CohomologicalPurity.ChartCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafEtPf
noncomputable section
open TensorProduct KaehlerDifferential

namespace LateralTheory.CohomologicalPurity.LeafEtPf

theorem etale_main (n : ℕ) (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (z : ι → A)
    (hn : Fintype.card ι = n) (hA : Algebra.IsStandardSmoothOfRelativeDimension n R A)
    (hspan : Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (z k)) = ⊤) :
    (MvPolynomial.eval₂Hom (algebraMap R A) z).Etale := by
  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · exact ChartCut.etale_of_subsingleton _
  letI : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval z).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.aeval_C z r).symm
  have := hA
  have : Algebra.IsStandardSmooth R A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have hD : ∀ k, mapBaseChange R (MvPolynomial ι R) A
      ((1 : A) ⊗ₜ D R (MvPolynomial ι R) (MvPolynomial.X k)) = D R A (z k) := by
    intro k
    rw [mapBaseChange_tmul, one_smul, map_D]
    congr 1
    exact MvPolynomial.aeval_X z k
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial ι R) A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hD k⟩
  haveI hΩ : Subsingleton Ω[A⁄MvPolynomial ι R] := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial ι R) A ω
    obtain ⟨u, rfl⟩ := hsurj w
    exact (exact_mapBaseChange_map R (MvPolynomial ι R) A).apply_apply_eq_zero u
  have hfin : Module.finrank A Ω[A⁄R] = n :=
    Module.finrank_eq_of_rank_eq (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)
  let b := Algebra.TensorProduct.basis A (mvPolynomialBasis R ι)
  have hli : LinearIndependent A (mapBaseChange R (MvPolynomial ι R) A ∘ b) := by
    have : (mapBaseChange R (MvPolynomial ι R) A ∘ b) = fun k => D R A (z k) := by
      funext k
      simp only [Function.comp_apply, b, Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply, hD]
    rw [this]
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (hn.trans hfin.symm)
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial ι R) A) :=
    LinearMap.injective_of_linearIndependent b.span_eq hli
  haveI hH1 : Subsingleton (Algebra.H1Cotangent (MvPolynomial ι R) A) := by
    refine subsingleton_of_forall_eq 0 fun h => ?_
    have h1 : Algebra.H1Cotangent.δ R (MvPolynomial ι R) A h = 0 := by
      apply hinj
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R (MvPolynomial ι R) A).apply_apply_eq_zero h
    obtain ⟨g, rfl⟩ := ((Algebra.H1Cotangent.exact_map_δ R (MvPolynomial ι R) A) h).mp h1
    rw [Subsingleton.elim g 0, map_zero]
  have : Algebra.FinitePresentation (MvPolynomial ι R) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A
  have : Algebra.IsStandardSmooth (MvPolynomial ι R) A :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential (I := Empty) (Module.Basis.empty _) (by rintro _ ⟨i, _⟩; exact i.elim)
  have : Algebra.FormallyUnramified (MvPolynomial ι R) A := ⟨hΩ⟩
  have : Algebra.Etale (MvPolynomial ι R) A :=
    Algebra.Etale.iff_formallyUnramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩
  exact RingHom.etale_algebraMap.mpr this

theorem LeafEt_of : ChartCut.LeafEt := by
  intro n R A ι _ _ _ _ z hn hA hspan
  exact etale_main n R A ι z hn hA hspan

end LateralTheory.CohomologicalPurity.LeafEtPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTauNatPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem tn_pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem tn_red_cast {q r : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E n i) : red q r E _ _ (x.cast hn hi) = Ht.cast hn hi (red q r E _ _ x) := by
  subst hn; subst hi; rfl

theorem tn_pull_cpow (h : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, tn_pull_cast, (h q).2.1 f hI]
  | succ k ih => rw [cpow_succ, cpow_succ, tn_pull_cast, (h q).1, ih]

theorem tn_red_cpow (h : A11) (q r : ℕ) [NeZero q] (hr : r ∣ q) {E : Spc} (hI : Inv q E)
    (L : E ⟶ ofCat (glCat 1)) (k : ℕ) : red q r E _ _ (cpow q (c1 q L) k) = cpow r (c1 r L) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, tn_red_cast, ((h q r hr E).2.1 hI).1]
  | succ k ih => rw [cpow_succ, cpow_succ, tn_red_cast, (h q r hr E).1, ih, ((h q r hr E).2.1 hI).2]

theorem tn_pull_hyp (h : DivisorNaturality) (q : ℕ) [NeZero q] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (f : PR N 0 B ⟶ PR N 0 A) (hI : Inv q (PR N 0 A))
    (hl : f ≫ prod.fst ≫ Pj.line N 0 = prod.fst ≫ Pj.line N 0) :
    pull _ f _ _ (hyp q N 0 A) = hyp q N 0 B := by
  unfold hyp
  rw [(h q).2.2.1 f _ hI, hl]

theorem tn_pull_poly (h : DivisorNaturality) (q : ℕ) [NeZero q] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (f : PR N 0 B ⟶ PR N 0 A) (hI : Inv q (PR N 0 A))
    (hl : f ≫ prod.fst ≫ Pj.line N 0 = prod.fst ≫ Pj.line N 0)
    (hs : f ≫ prod.snd = prod.snd ≫ spMap φ) (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp A) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ f _ _ (poly q N 0 A m n i a) = poly q N 0 B m n i (fun j => pull _ (spMap φ) _ _ (a j)) := by
  unfold poly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tn_pull_cast, (h q).1, ← pull_comp, hs, pull_comp, tn_pull_cpow h q f hI, tn_pull_hyp h q N f hI hl]

theorem tn_red_poly (h : A11) (q r : ℕ) [NeZero q] (hr : r ∣ q) (N : ℕ) {A : Type} [CommRing A]
    (hI : Inv q (PR N 0 A)) (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp A) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    red q r _ _ _ (poly q N 0 A m n i a) = poly r N 0 A m n i (fun j => red q r _ _ _ (a j)) := by
  unfold poly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tn_red_cast, (h q r hr _).1, ← pull_red]
  unfold hyp
  rw [tn_red_cpow h q r hr hI]

theorem LeafTauNat_of (hG : LeafGeo) : LeafTauNat := by
  intro h6 h11 q _ d A _ hq τ hτ
  obtain ⟨a, ha⟩ := hτ
  have hI : Inv q (PR (d + 1) 0 A) := hG.2.1 q (d + 1) 0 A hq
  refine ⟨fun B _ φ g hl hs => ⟨fun j => pull _ (spMap φ) _ _ (a j), ?_⟩,
    fun r hr τ' hτ' => ⟨fun j => red q r _ _ _ (a j), ?_⟩⟩
  · have e : Hs.fgt q (pr d B) _ _ (Hs.pull q g _ _ τ) =
        pull (E := PR (d + 1) 0 B) (E' := PR (d + 1) 0 A) _ g.right _ _
          (show Ht q (PR (d + 1) 0 A) _ _ from Hs.fgt q (pr d A) _ _ τ) := by
      change pull _ (dbl.inl _) _ _ (pull _ (dbl.map g) _ _ τ.1) =
        pull _ g.right _ _ (pull _ (dbl.inl _) _ _ τ.1)
      rw [← pull_comp, ← pull_comp, inl_map]
    rw [e, ha, map_add (f := _), tn_pull_cpow h6 q (E := PR (d + 1) 0 B) (E' := PR (d + 1) 0 A) g.right hI,
      tn_pull_hyp h6 q (d + 1) g.right hI hl, tn_pull_poly h6 q (d + 1) φ g.right hI hl hs]
  · have e : Hs.fgt r (pr d A) _ _ τ' = red q r (PR (d + 1) 0 A) _ _
        (show Ht q (PR (d + 1) 0 A) _ _ from Hs.fgt q (pr d A) _ _ τ) := by
      change pull _ (dbl.inl _) _ _ τ'.1 = red q r _ _ _ (pull _ (dbl.inl _) _ _ τ.1)
      rw [hτ', pull_red]
    rw [e, ha, map_add (f := _), tn_red_poly h11 q r hr (d + 1) hI]
    unfold hyp
    rw [tn_red_cpow h11 q r hr hI]

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafRankPf
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafRankPf

theorem finrank_tensor_surj {A B K X : Type*} [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
    [Algebra B K] [IsScalarTower A B K] [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    (h : Function.Surjective (algebraMap A B)) :
    Module.finrank K (K ⊗[A] X) = Module.finrank K (K ⊗[B] X) := by
  have : CompatibleSMul A B K X := CompatibleSMul.of_algebraMap_surjective K X h
  exact (LinearEquiv.finrank_eq (equivOfCompatibleSMul A B K K X)).symm

theorem finrank_tensor_cotangent {A K : Type*} [CommRing A] [Field K] [Algebra A K] (J : Ideal A)
    (hJ : ∀ a ∈ J, algebraMap A K a = 0) :
    Module.finrank K (K ⊗[A] J) = Module.finrank K (K ⊗[A] J.Cotangent) := by
  have hex := lTensor_exact K (LinearMap.exact_subtype_mkQ (J • (⊤ : Submodule A J)))
    (Submodule.mkQ_surjective _)
  have hz : ∀ (x : K) (z : J), z ∈ J • (⊤ : Submodule A J) → (x ⊗ₜ[A] z : K ⊗[A] J) = 0 := by
    intro x z hz
    refine Submodule.smul_induction_on (p := fun z => (x ⊗ₜ[A] z : K ⊗[A] J) = 0) hz ?_ ?_
    · intro a ha m _
      rw [← smul_tmul, Algebra.smul_def, hJ a ha, zero_mul, zero_tmul]
    · intro u v hu hv
      rw [tmul_add, hu, hv, add_zero]
  have h0 : LinearMap.lTensor K (J • (⊤ : Submodule A J)).subtype = 0 := by
    ext x z; exact hz x z z.2
  have hinj : Function.Injective (LinearMap.baseChange K (Ideal.toCotangent J)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have : y ∈ LinearMap.range (LinearMap.lTensor K (J • (⊤ : Submodule A J)).subtype) :=
      (hex y).mp (by rw [LinearMap.baseChange_eq_ltensor] at hy; exact hy)
    rw [h0, LinearMap.range_zero] at this
    simpa using this
  have hsurj : Function.Surjective (LinearMap.baseChange K (Ideal.toCotangent J)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective K (Submodule.mkQ_surjective _)
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)

theorem _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of : LateralTheory.CohomologicalPurity.ChartCut.LeafRank := by
  intro e d R A _ _ _ I p _ hIp hA hB
  have hk : ∀ a ∈ I, algebraMap A p.ResidueField a = 0 := fun a ha =>
    Ideal.algebraMap_residueField_eq_zero.mpr (hIp ha)
  letI : Algebra (A ⧸ I) p.ResidueField := (Ideal.Quotient.lift I (algebraMap A p.ResidueField) hk).toAlgebra
  haveI : IsScalarTower A (A ⧸ I) p.ResidueField := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top ‹_›) hIp)
  haveI : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  haveI : Algebra.IsStandardSmooth R A := hA.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R (A ⧸ I) := hB.isStandardSmooth
  have rA : Module.finrank A Ω[A⁄R] = e + d := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (e + d))
  have rB : Module.finrank (A ⧸ I) Ω[(A ⧸ I)⁄R] = e := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential e)
  have eqv := AlgebraTensorModule.cancelBaseChange A (A ⧸ I) p.ResidueField p.ResidueField Ω[A⁄R]
  have h1 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] ((A ⧸ I) ⊗[A] Ω[A⁄R])) = e + d := by
    rw [finrank_tensor_surj hsurj, LinearEquiv.finrank_eq eqv, Module.finrank_baseChange, rA]
  have h2 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[(A ⧸ I)⁄R]) = e := by
    rw [finrank_tensor_surj hsurj, Module.finrank_baseChange, rB]
  have hK : RingHom.ker (algebraMap A (A ⧸ I)) = I := Ideal.mk_ker
  have h3 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] I) =
      Module.finrank p.ResidueField (p.ResidueField ⊗[A] (RingHom.ker (algebraMap A (A ⧸ I))).Cotangent) := by
    rw [← finrank_tensor_cotangent _ (by rw [hK]; exact hk), hK]
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := R) (P := A) (A := A ⧸ I) hsurj).mp inferInstance
  have e0 : Function.Exact (KaehlerDifferential.kerCotangentToTensor R A (A ⧸ I))
      ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A) :=
    KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A (A ⧸ I) hsurj
  have s0 : Function.Surjective ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A) :=
    KaehlerDifferential.mapBaseChange_surjective R A (A ⧸ I) hsurj
  set f := (KaehlerDifferential.kerCotangentToTensor R A (A ⧸ I)).baseChange p.ResidueField
  set g := ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A).baseChange p.ResidueField
  have hex : Function.Exact f g := by
    simpa only [f, g, LinearMap.baseChange_eq_ltensor] using lTensor_exact p.ResidueField e0 s0
  have hg : Function.Surjective g := by
    simpa only [g, LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective p.ResidueField s0
  have hf : Function.Injective f := by
    have hc : (l.baseChange p.ResidueField).comp f = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hl, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (g := l.baseChange p.ResidueField) (fun x => by
      simpa using LinearMap.congr_fun hc x)
  have : CompatibleSMul A (A ⧸ I) p.ResidueField ((A ⧸ I) ⊗[A] Ω[A⁄R]) :=
    CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  haveI : Module.Finite p.ResidueField (p.ResidueField ⊗[A] ((A ⧸ I) ⊗[A] Ω[A⁄R])) :=
    Module.Finite.equiv ((LinearEquiv.restrictScalars p.ResidueField
      (equivOfCompatibleSMul A (A ⧸ I) p.ResidueField p.ResidueField ((A ⧸ I) ⊗[A] Ω[A⁄R])).symm).trans
      eqv).symm
  have hrk := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf,
    h1, h2] at hrk
  rw [h3]; omega

end LateralTheory.CohomologicalPurity.LeafRankPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafGenPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

def LeafGenCart : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (r : Γ(X, V.1)),
  ∃ z : Spec (CommRingCat.of (Localization.Away r ⧸ (ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))) ⟶ Z,
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))) z
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ι

def LeafGenKer : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (r : Γ(X, V.1)),
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))).ker =
    ι.ker.comap (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)

theorem LeafGenCart_of (hK : LeafGenKer) : LeafGenCart := by
  intro X Z ι _ V r
  have hK' := hK ι V r
  have hm : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of (Localization.Away r)) _
  have hfst := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion ι
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)
  let e := IsClosedImmersion.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1)
    (Localization.Away r))) ≫ V.2.fromSpec) ι) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))) (by rw [hfst, hK'])
  refine ⟨e ≫ pullback.snd _ _, isPullback_of_isClosedImmersion _ ι _ _ ?_ hK'.symm⟩
  rw [Category.assoc, ← pullback.condition, IsClosedImmersion.lift_fac_assoc]

theorem span_loc {d : ℕ} {A : Type} [CommRing A] (I : Ideal A) (a : Fin d → A) (r : A) (ha : ∀ j, a j ∈ I)
    (hra : ∀ y ∈ I, r * y ∈ Ideal.span (Set.range a)) :
    Ideal.span (Set.range (algebraMap A (Localization.Away r) ∘ a)) = I.map (algebraMap A (Localization.Away r)) := by
  rw [Set.range_comp, ← Ideal.map_span]
  apply le_antisymm
  · exact Ideal.map_mono (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact ha j))
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap A (Localization.Away r) r) := IsLocalization.Away.algebraMap_isUnit r
    have h1 : algebraMap A (Localization.Away r) (r * y) ∈ (Ideal.span (Set.range a)).map (algebraMap A (Localization.Away r)) :=
      Ideal.mem_map_of_mem _ (hra y hy)
    rw [map_mul] at h1
    obtain ⟨u, hu'⟩ := hu
    have := Ideal.mul_mem_left _ (↑u⁻¹ : Localization.Away r) h1
    rwa [← hu', ← mul_assoc, Units.inv_mul, one_mul] at this

theorem LeafGen_of (hC : LeafChart) (hGR : LeafGenRing) (hKer : LeafGenKer) : LeafGen := by
  have hCart : LeafGenCart := LeafGenCart_of @hKer
  intro d P x hx
  obtain ⟨V, hxV, -, hfg, hch⟩ := hC d P x ⊤ trivial
  obtain ⟨a, r, hr1, ha, hra⟩ := hGR d Γ(P.X, V.1) (P.ι.ker.ideal V) hfg hch
  have := P.cl
  obtain ⟨z, hz⟩ := hCart P.ι V r
  have hxr : x ∈ Set.range P.ι := by
    by_contra h; exact hx (by rw [← SetLike.mem_coe, P.hU]; exact h)
  refine ⟨⟨Localization.Away r, (P.ι.ker.ideal V).map (algebraMap _ _), algebraMap _ _ ∘ a,
    span_loc _ a r ha hra, Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ V.2.fromSpec, z, ?_, hz⟩, ?_, ?_⟩
  · intro y hy
    change (_ ≫ V.2.fromSpec) y ∈ P.U
    rw [← SetLike.mem_coe, P.hU]
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, -⟩ := Scheme.exists_preimage_of_isPullback hz y t ht.symm
    apply hy
    rw [← hs]
    intro g hg
    change Ideal.Quotient.mk _ g ∈ s.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]; exact zero_mem _
  · change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ V.2.fromSpec)
    have h1 := Scheme.isOpenImmersion_SpecMap_localizationAway (R := Γ(P.X, V.1)) r
    have h2 := V.2.isOpenImmersion_fromSpec
    infer_instance
  · have hxV' : x ∈ (V.1 : Set P.X) := hxV
    rw [← V.2.range_fromSpec] at hxV'
    obtain ⟨p, hp⟩ := hxV'
    have hz0 : x ∈ P.X.zeroLocus (U := V.1) (P.ι.ker.ideal V) := by
      rw [← Scheme.IdealSheafData.mem_support_iff_of_mem hxV, ← SetLike.mem_coe, Scheme.Hom.support_ker]; exact subset_closure hxr
    have hIp : ∀ g ∈ P.ι.ker.ideal V, g ∈ p.asIdeal := by
      intro g hg
      have h1 := (Scheme.mem_zeroLocus_iff _ _ _).1 hz0 g hg
      by_contra h2
      apply h1
      rw [← hp]
      change p ∈ V.2.fromSpec ⁻¹ᵁ P.X.basicOpen g
      rw [V.2.fromSpec_preimage_basicOpen]; exact h2
    have hr : p ∈ PrimeSpectrum.basicOpen r := by
      intro h; apply p.2.ne_top; rw [Ideal.eq_top_iff_one]
      have := p.asIdeal.sub_mem h (hIp _ hr1); simpa using this
    have hr' : p ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(P.X, V.1) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]; exact hr
    obtain ⟨q, hq⟩ := hr'
    refine ⟨q, ?_⟩
    show V.2.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap Γ(P.X, V.1) (Localization.Away r)))) q) = x
    rw [← hp]
    exact congrArg V.2.fromSpec hq

end LateralTheory.CohomologicalPurity.Cl
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafCoordPf
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

lemma kd_span {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra A A']
    [Algebra R A'] [IsScalarTower R A A'] (f : A) [IsLocalization.Away f A'] (N : Submodule A' Ω[A'⁄R])
    (hN : ∀ a : A, KaehlerDifferential.D R A' (algebraMap A A' a) ∈ N) : N = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨a', rfl⟩
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) a'
  simp only at hs
  have hu : IsUnit (algebraMap A A' (s : A)) := IsLocalization.map_units A' s
  have h1 : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' ∈ N := by
    have h := congrArg (KaehlerDifferential.D R A') hs
    rw [Derivation.leibniz] at h
    have e : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' =
        KaehlerDifferential.D R A' (algebraMap A A' a) - a' • KaehlerDifferential.D R A' (algebraMap A A' s) := by
      rw [← h]; abel
    rw [e]; exact N.sub_mem (hN a) (N.smul_mem _ (hN s))
  obtain ⟨u, hu'⟩ := hu
  have h2 := N.smul_mem (↑u⁻¹ : A') h1
  rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

theorem LeafCoord_of (hR : LeafRank) (hP : LeafPick) (hS : LeafSpan) (hE : LeafEt) : LeafCoord := by
  intro e d R A _ _ φ I p hp hIp hstd
  letI : Algebra R A := φ.toAlgebra
  haveI h1 : Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A := hstd.1
  haveI h2 : Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) := hstd.2
  haveI : Algebra.IsStandardSmooth R A := h1.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R (A ⧸ I) := h2.isStandardSmooth
  have hfg : I.FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ_surjective R I)
    simpa [Ideal.Quotient.mkₐ_ker] using this
  haveI : Module.Finite A I := Module.Finite.iff_fg.mpr hfg
  haveI := hp
  have hrank := hR e d R A I p hIp h1 h2
  obtain ⟨x, f, hf, hx⟩ := hP d A I p hrank
  set x' : Fin d → A := fun j => (x j : A) with hx'
  have hxI : ∀ j, x' j ∈ I := fun j => (x j).2
  have hfx : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x') := by
    intro a ha
    have h := Submodule.mem_map_of_mem (f := I.subtype) (hx ⟨a, ha⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  obtain ⟨y, g, hg, hy⟩ := hS e d R A I p hp hIp h2 x' f hxI hf hfx
  refine ⟨f * g, fun h => (hp.mem_or_mem h).elim hf hg, ?_⟩
  intro A' _ _ _
  letI : Algebra R A' := ((algebraMap A A').comp φ).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hfgu : IsUnit (algebraMap A A' (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at hfgu
  have hfu : IsUnit (algebraMap A A' f) := isUnit_of_mul_isUnit_left hfgu
  have hgu : IsUnit (algebraMap A A' g) := isUnit_of_mul_isUnit_right hfgu
  refine ⟨fun j => algebraMap A A' (x' j), fun k => algebraMap A A' (y k), ?_, ?_⟩
  · haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 A A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.localization_away (f * g)
    have h3 : Algebra.IsStandardSmoothOfRelativeDimension (0 + (e + d)) R A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := A) (T := A') (n := e + d) (m := 0)
    rw [zero_add] at h3
    refine hE (e + d) R A' (Fin d ⊕ Fin e) _ (by simp [add_comm]) h3 ?_
    apply kd_span (R := R) (A := A) (f * g)
    intro a
    have hm := Submodule.mem_map_of_mem (f := KaehlerDifferential.map R R A A')
      (hy (KaehlerDifferential.D R A a))
    rw [Submodule.map_span, LinearMap.map_smul, KaehlerDifferential.map_D] at hm
    have hle : Submodule.span A (KaehlerDifferential.map R R A A' ''
        Set.range fun k => KaehlerDifferential.D R A (Sum.elim x' y k)) ≤
        (Submodule.span A' (Set.range fun k => KaehlerDifferential.D R A'
          (Sum.elim (fun j => algebraMap A A' (x' j)) (fun k => algebraMap A A' (y k)) k))).restrictScalars A := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      rw [KaehlerDifferential.map_D]
      apply Submodule.subset_span
      exact ⟨k, by cases k <;> rfl⟩
    have h5 := hle hm
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul A'] at h5
    obtain ⟨u, hu⟩ := hgu
    have h6 := Submodule.smul_mem _ (↑u⁻¹ : A') h5
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h6
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h := Ideal.mem_map_of_mem (algebraMap A A') (hfx a ha)
      rw [Ideal.map_span, map_mul, ← Set.range_comp] at h
      obtain ⟨u, hu⟩ := hfu
      have h6 := Ideal.mul_mem_left _ (↑u⁻¹ : A') h
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h6
      exact h6
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (hxI j)

end LateralTheory.CohomologicalPurity.ChartCut
end
end
