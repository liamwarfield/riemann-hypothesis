module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuFrameExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplaneMid
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDouble
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZColumns
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleSnapper
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTail
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleHilbert
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeFinite
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Imports
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Ml

theorem spMap_field_pt {R K : Type} [CommRing R] [Field K] (δ : R →+* K) (z : Sp K) :
    (spMap δ z).asIdeal = RingHom.ker δ := by
  have hz : z.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := z.2)
  show Ideal.comap δ z.asIdeal = _
  rw [hz]; rfl

theorem preimm_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) : IsPreimmersion (spMap β) := by
  letI := β.toAlgebra
  haveI := h
  exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)

theorem lift_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) {X : Scheme.{0}} (s : X ⟶ Sp O) {K : Type} [Field K]
    (x : Sp K ⟶ X) (hx : Set.range x ⊆ Set.range (pullback.fst s (spMap β))) :
    ∃ y : Sp K ⟶ pullback s (spMap β), y ≫ pullback.fst _ _ = x := by
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  obtain ⟨⟨p, a⟩, rfl⟩ := (X.SpecToEquivOfField K).symm.surjective x
  have hp : p ∈ Set.range (pullback.fst s (spMap β)) := by
    apply hx
    exact ⟨IsLocalRing.closedPoint K, Scheme.fromSpecResidueField_apply p _⟩
  obtain ⟨q, rfl⟩ := hp
  have hsurj : Function.Surjective (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) := by
    have h1 : Function.Surjective
        (Scheme.Hom.stalkMap (pullback.fst s (spMap β)) q ≫ (pullback s (spMap β)).residue q) :=
      ((pullback s (spMap β)).residue_surjective q).comp
        (Scheme.Hom.stalkMap_surjective (pullback.fst s (spMap β)) q)
    rw [← Scheme.residue_residueFieldMap] at h1
    intro b
    obtain ⟨c, hc⟩ := h1 b
    exact ⟨X.residue _ c, hc⟩
  haveI : IsIso (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨(Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q).hom.injective, hsurj⟩
  refine ⟨Spec.map (inv (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) ≫ a) ≫
    (pullback s (spMap β)).fromSpecResidueField q, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp]
  simp [Scheme.SpecToEquivOfField]

theorem lift_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x := by
  intro E _ _ _ H D l Xo c O _ β Y h K _ x hx
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  haveI := Y.jQ_open
  have hx' : Set.range x ⊆ Set.range (pullback.fst Y.s (spMap β)) := by
    refine hx.trans ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨Y.jQ w, by simp [Model.j]⟩
  obtain ⟨y1, hy1⟩ := lift_frac β h Y.s x hx'
  have hr : Set.range y1 ⊆ Set.range Y.jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hx ⟨z, rfl⟩
    refine ⟨w, (pullback.fst Y.s (spMap β)).isEmbedding.injective ?_⟩
    rw [← hy1] at hw
    simpa [Model.j] using hw
  refine ⟨IsOpenImmersion.lift Y.jQ y1 hr, ?_⟩
  simp [Model.j, hy1]

theorem generic_max {X : Type} [TopologicalSpace X] [T0Space X] {v v' : X} (h : v ∈ genericPoints X)
    (hs : v' ⤳ v) : v' = v := by
  have h1 : closure {v} ⊆ closure {v'} := specializes_iff_closure_subset.1 hs
  have h2 : closure {v'} ⊆ closure {v} := h.2 isIrreducible_singleton.closure h1
  exact (hs.antisymm (specializes_iff_closure_subset.2 h2)).eq

theorem mem_of_dense_of_max {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (ho : IsOpen U) (hd : Dense U) {z : X} (hz : ∀ z', z' ⤳ z → z' = z) : z ∈ U := by
  have hC := irreducibleComponent_mem_irreducibleComponents z
  obtain ⟨o, hoo, ⟨u, hu⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨w, hwo, hwU⟩ := hd.inter_open_nonempty o hoo ⟨u, hu⟩
  have hg := hC.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ hC).closure_eq] at hg
  have hgz : hC.1.genericPoint = z := hz _ (hg.specializes mem_irreducibleComponent)
  have hzw : z ⤳ w := hgz ▸ hg.specializes (hoC hwo)
  exact hzw.mem_open ho hwU

private theorem isLocallyNoetherian_of_closedImmersion_pSpace (O F : Type) [CommRing O] [Field F] (β : O →+* F) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (hp : IsProjOver s) : TopologicalSpace.NoetherianSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) := by
  haveI : IsProper s := projProper O X s hp
  haveI : IsLocallyNoetherian (pullback s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β))
  haveI : CompactSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (spMap β))
  haveI : IsNoetherian (pullback s (spMap β)) := {}
  infer_instance

theorem generic_points_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y hO h v hv
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  haveI := Y.flat
  haveI := Y.jQ_open
  haveI := isLocallyNoetherian_of_closedImmersion_pSpace O c.F β Y.X Y.s Y.proj
  have hβ : Function.Injective β := by
    letI := β.toAlgebra
    haveI := h
    exact IsFractionRing.injective O c.F
  let z0 : Sp c.F := IsLocalRing.closedPoint c.F
  have hgen : (spMap β z0).asIdeal = ⊥ := by
    rw [spMap_field_pt]
    exact (RingHom.injective_iff_ker_eq_bot β).mp hβ
  have hle : (spMap β z0).asIdeal ≤ (Y.s v).asIdeal := by
    rw [hgen]
    exact bot_le
  have hspec : spMap β z0 ⤳ Y.s v := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨v', hv'v, hv'⟩ := Flat.generalizingMap Y.s hspec
  rw [generic_max hv hv'v] at hv'
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback v z0 hv'
  have hqmax : ∀ q', q' ⤳ q → q' = q := by
    intro q' hq'
    apply (pullback.fst Y.s (spMap β)).isEmbedding.injective
    rw [hq]
    exact generic_max hv (hq ▸ hq'.map (pullback.fst Y.s (spMap β)).continuous)
  obtain ⟨w, hw⟩ := mem_of_dense_of_max Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hqmax
  refine ⟨w, ?_⟩
  rw [← hq, ← hw]
  simp [Model.j]

end PositivityTheory.HtPt.Ml
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.A36
namespace PositivityTheory.HtPt.Ktw

theorem a29 :
    GroundTheory.Heights₂.Heights.Kleiman.InterNumTie.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.InterNumTie.of_restrictQuot
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof

theorem a30 :
    GroundTheory.Heights₂.Heights.Kleiman.SnapperDevissage.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SnapperDevissage.proof
    GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotDevissage.closed

theorem a31 :
    GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplane.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplane.proof
    GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotAdd.closed
    GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotDevissage.closed
    GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid.proof

theorem a32 :
    GroundTheory.Heights₂.Heights.Kleiman.Snapper.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.Snapper.proof a30 a31
    GroundTheory.Heights₂.Heights.Kleiman.SnapperSection.full
    GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly.proof

theorem a34 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleCech.Statement.{0, 0, 0} := open GroundTheory.Heights₂.Heights.Kleiman in by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H r h hH
  obtain ⟨F', hF'⟩ := VeryAmpleZFamily.proof S Ω N x E F H r h hH
  have hmem : ∀ (J : Chart h) (y : E), y ∈ F'.sub J ↔ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
    intro J y
    rw [← hF' J, Submodule.restrictScalars_mem]
  refine ⟨F', fun J => ?_, fun a i => ?_⟩
  · obtain ⟨t, ht1, ht2⟩ := VeryAmpleZFinite.proof VeryAmpleZExtend.proof VeryAmpleZChartSpan.proof
      VeryAmpleZChartRing.proof S Ω N x E F hF H r h hH J
    refine ⟨t, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      exact (hmem J y).2 (ht1 hy)
    · intro y hy
      have := ht2 ((hmem J y).1 hy)
      rwa [Submodule.restrictScalars_mem] at this
  · obtain ⟨G, hG⟩ := SubFamilyTwistPow.proof S Ω N x E F H.toSubFamily a
    have hB : (fun J : Chart h => secsOnZ G.toSubSystem H.toSubSystem h J) =
        fun J : Chart h => Submodule.restrictScalars S ((F'.twist (twistSys S h a)).sub J) := by
      funext J
      rw [hG, ← VeryAmpleZTwist.proof_closed S Ω N x E F H r h hH a J]
      congr 2
      ext z
      simp only [Set.mem_setOf_eq, SubSystem.twist, twistSys, hmem]
    obtain ⟨e1⟩ := CechHdegOfSub.proof S Ω N x E G.toSubSystem i
    obtain ⟨e2⟩ := CechDouble.proof S Ω N r x h E (fun I => Submodule.restrictScalars S (G.sub I))
      (fun J => secsOnZ G.toSubSystem H.toSubSystem h J)
      (fun I J => secsOnZChart G.toSubSystem H.toSubSystem h I J)
      (fun I I' J hII' => (VeryAmpleZRows.proof_closed S Ω N x E G H r h hH J).1 I I' hII')
      (fun I J J' hJJ' => (VeryAmpleZColumns.proof S Ω N x E G H r h hH I).1 J J' hJJ')
      (fun I => (VeryAmpleZColumns.proof S Ω N x E G H r h hH I).2)
      (fun J => (VeryAmpleZRows.proof_closed S Ω N x E G H r h hH J).2) i
    obtain ⟨e3⟩ := CechHdegOfSub.proof S Ω r h E (F'.twist (twistSys S h a)) i
    rw [hB] at e2
    rw [← hG]
    exact ⟨(e1.trans e2).trans e3.symm⟩

theorem a35 :
    GroundTheory.Heights₂.Heights.Kleiman.AmpleVanish.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.AmpleVanish.proof a34
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof a2

theorem a36 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSnapper.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSnapper.proof
    GroundTheory.Heights₂.Heights.Kleiman.SnapperFinite.closed a32
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.twistVanishAll_closed a35

theorem a37 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleHilbert.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleHilbert.proof a36

theorem a38 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDegree.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDegree.proof
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim.proof
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs.proof a37

theorem a39 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Top.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Top.proof
    GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive.full a29
    GroundTheory.Heights₂.Heights.Kleiman.TwistFinite.full
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim.proof a38

theorem a40 :
    GroundTheory.Heights₂.Heights.Kleiman.TildeTail.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.TildeTail.proof
    GroundTheory.Heights₂.Heights.Kleiman.SerreTail.full

theorem a41 :
    GroundTheory.Heights₂.Heights.Kleiman.FiniteSections.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.FiniteSections.proof
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof a40

theorem a42 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Finite.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Finite.proof
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections.proof a41

theorem a43 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Kernel.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Step.proof a42

theorem a44 :
    GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal.proof
    GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen.proof

theorem a45 :
    GroundTheory.Heights₂.Heights.Kleiman.GeneratedAmple.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.GeneratedAmple.proof
    GroundTheory.Heights₂.Heights.Kleiman.AmpleCover.proof a44

theorem a46 :
    GroundTheory.Heights₂.Heights.Kleiman.TildeFinite.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.TildeFinite.proof
    GroundTheory.Heights₂.Heights.Kleiman.SerreFinite.full

theorem a47 :
    GroundTheory.Heights₂.Heights.Kleiman.QuotSectionsFinite.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.QuotSectionsFinite.proof
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof
    GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily.proof a46
    GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Finite.proof

theorem a48 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term.proof a45 a47

theorem a49 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleEmbed.Numbers.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleEmbed.Numbers.proof
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs.proof a37

theorem a50 :
    GroundTheory.Heights₂.Heights.Kleiman.InterNumPoint.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.InterNumPoint.proof
    GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint.proof

theorem a51 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.HilbW.Statement.{0, 0} := open GroundTheory.Heights₂.Heights.Kleiman in by
  intro k _ Ω _ _ N x Nb pp e hNb hpp
  obtain ⟨r, h, hh⟩ := hNb
  obtain ⟨j, hXj⟩ := hpp.relevant
  have hj : x j ≠ 0 := by
    intro h0
    apply hXj
    apply hpp.le
    rw [primeOf_eq, RingHom.mem_ker, cone_of_isHomogeneous x (MvPolynomial.isHomogeneous_X k j)]
    simp [h0]
  obtain ⟨hP, hPy⟩ := PrimeFiltration.Point.proof k Ω N x pp hpp.isPrime hpp.homog hpp.le j hj hXj
  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra k K')
      (ψ : chartRing k x (singleChart hj) →ₐ[k] K'), RingHom.ker ψ = chartPrime pp hj := by
    let R := chartRing k x (singleChart hj)
    let P := chartPrime pp hj
    haveI : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
    refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
      (IsScalarTower.toAlgHom k (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ k P), ?_⟩
    ext z
    simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [← map_zero (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))),
      (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))).eq_iff]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hy : primeOf (fun i => ψ (ratio hj i)) = pp := hPy K' ψ hker
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i hi h0
    apply hi
    have h1 : ratio (S := k) hj i = 0 := Subtype.ext (by simp [ratio, h0])
    rw [h1, map_zero]
  have hy0 : (fun i => ψ (ratio hj i)) ≠ 0 := by
    intro h0
    have h1 : ratio (S := k) hj j = 1 := Subtype.ext (by simp [ratio, hj])
    have h2 : ψ (ratio hj j) = 0 := congrFun h0 j
    rw [h1, map_one] at h2
    exact one_ne_zero h2
  obtain ⟨Q', ρ, hρ, hQ'h, -⟩ :=
    Restriction.proof k Ω N x Nb r h hh pp hpp.isPrime hpp.homog hpp.le j hj hXj K' ψ hker hxy
  have hle : primeOf x ≤ primeOf (fun i => ψ (ratio hj i)) := hy ▸ hpp.le
  have hpow : ∀ m : ℕ, ∃ ρm : Ω → K',
      RestrictData (Nb.tpow m).toSubSystem hxy (Q'.tpow m).toSubSystem ρm := by
    intro m
    induction m with
    | zero =>
      rw [LineBundle.tpow_toSubSystem, LineBundle.tpow_toSubSystem]
      exact RestrictTwist.proof.1 k Ω N x K' (fun i => ψ (ratio hj i)) hxy hle 0
    | succ n ih =>
      obtain ⟨ρn, hn⟩ := ih
      obtain ⟨ρ', h'⟩ := RestrictTwist.proof.2 k Ω N x K' (fun i => ψ (ratio hj i)) hxy (Nb.tpow n) Nb (Q'.tpow n) Q' ρn ρ hn hρ
      refine ⟨ρ', ?_⟩
      rw [LineBundle.tpow_toSubSystem, LineBundle.tpow_toSubSystem]
      rw [LineBundle.tpow_toSubSystem, LineBundle.tpow_toSubSystem] at h'
      exact h'
  have hsub : IsSubvar (fun i => ψ (ratio hj i)) pp e := ⟨hpp.isPrime, hpp.homog, hy.le, hpp.relevant, hpp.dim⟩
  have hsub' : IsSubvar (fun i => ψ (ratio hj i)) (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by rw [hy]; exact hsub
  obtain ⟨hsubh, hnum⟩ := a49 k K' N (fun i => ψ (ratio hj i)) Q' r (ρ ∘ h) hQ'h e hsub'
  have hres := a5 k Ω N x K' (fun i => ψ (ratio hj i)) hxy hle pp e hsub (fun _ => Nb) (fun _ => Q') (fun _ => ρ) (fun _ => hρ)
  have hI0 : (interNum pp fun _ : Fin e => Nb.toSubSystem) =
      interNum (primeOf (ρ ∘ h)) fun _ : Fin e => twistSys k (ρ ∘ h) 1 := by
    rw [← hres, ← hnum, hy]
  have hdim : ∀ m : ℕ, Module.finrank k ((twistMul Nb.toSubSystem m 0).quotH
      ((twistMul Nb.toSubSystem m 0).twist (idealSys x pp)) 0) =
      Module.finrank k (twistSys k (ρ ∘ h) m).secs := by
    intro m
    obtain ⟨ρm, hm⟩ := hpow m
    obtain ⟨e1⟩ := PrimeFiltration.RestrictQuot.proof k Ω N x pp hpp.isPrime hpp.homog hpp.le j hj hXj
      K' ψ hker hxy (Nb.tpow m) (Q'.tpow m) ρm hm 0 0
    obtain ⟨e2⟩ := CechZerothCohomologySections.proof k K' N (fun i => ψ (ratio hj i)) K' ((Q'.tpow m).toSubSystem.twist (twistSys k (fun i => ψ (ratio hj i)) 0)) hy0
    have h3 := VeryAmpleEmbed.Sections.proof k K' N (fun i => ψ (ratio hj i)) Q' r (ρ ∘ h) hy0 hQ'h m
    have h4 : twistMul Nb.toSubSystem m 0 = (Nb.tpow m).toSubSystem.twist (twistSys k x 0) := by
      rw [LineBundle.tpow_toSubSystem]
      rfl
    rw [h4, e1.finrank_eq, e2.finrank_eq, SubSystem.twist_twistSys_zero, LineBundle.tpow_toSubSystem, h3]
  rcases e with _ | e
  · obtain ⟨-, hev1, hev2⟩ := HilbertPoint.proof k K' r (ρ ∘ h) hsubh
    have hpt := a50 k K' r (ρ ∘ h) hsubh (fun _ => twistSys k (ρ ∘ h) 1)
    refine ⟨0, ?_⟩
    filter_upwards [hev1, hev2] with m h1 h2
    rw [hdim m, h2, h1, hI0, hpt]
    simp
  · obtain ⟨⟨C, hC⟩, -, hev2⟩ := HilbertPositive.full k K' r (ρ ∘ h) (e + 1) (by omega) hsubh
    have htie := a29 k K' r (ρ ∘ h) (e + 1) (primeOf (ρ ∘ h)) (fun _ => 1) hsubh
    have hI : (interNum pp fun _ : Fin (e + 1) => Nb.toSubSystem) =
        GroundTheory.Heights₂.Heights.NumbersDVR.intNum k (primeOfOne (ρ ∘ h)) fun (_ : Fin (e + 1)) (_ : Unit) => (1 : ℤ) := by
      rw [hI0]
      exact htie
    refine ⟨C, ?_⟩
    filter_upwards [hC, hev2, Filter.eventually_gt_atTop 0] with m h1 h2 hm
    rw [hdim m, h2, hI]
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    calc _ ≤ C * (m : ℝ) ^ (e + 1 - 1) := h1
      _ = C * (m : ℝ) ^ (e + 1) / m := by
        rw [Nat.add_sub_cancel, pow_succ]
        field_simp

end PositivityTheory.HtPt.Ktw
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1PointPowerExpand
noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

section Alg

variable {k : Type} [CommRing k]

theorem aug_mk {κ : Type} (m : ℕ) (P : MvPolynomial κ k) :
    (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = MvPolynomial.constantCoeff P := by
  have : (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (fun _ => (0 : k)) P := rfl
  rw [this, MvPolynomial.aeval_zero']
  rfl

theorem substP_X {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' k) (i : κ) :
    jetSubstP m φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) := by
  rw [jetSubstP, jetMap_mk, MvPolynomial.aeval_X]

theorem psTrunc_expand {σ : Type} [Fintype σ] [DecidableEq σ] (p : ℕ) (hp : p ≠ 0) (V : MvPowerSeries σ k)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    psTrunc p (MvPowerSeries.expand p hp V) =
      ∑ j, MvPolynomial.C (MvPowerSeries.coeff (Finsupp.single j 1) V) * MvPolynomial.X j ^ p := by
  ext e
  have hR : AddMonoidAlgebra.coeff (∑ j, MvPolynomial.C (MvPowerSeries.coeff (Finsupp.single j 1) V) * MvPolynomial.X j ^ p : MvPolynomial σ k)
      e =
      ∑ j, if Finsupp.single j p = e then MvPowerSeries.coeff (Finsupp.single j 1) V else 0 := by
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
    split_ifs <;> simp
  rw [hR]
  by_cases hs : ∃ j, Finsupp.single j p = e
  · obtain ⟨j, rfl⟩ := hs
    rw [GermFun.coeff_psTrunc _ _ _ (by simp), Finset.sum_eq_single j, if_pos rfl]
    · have : Finsupp.single j p = p • Finsupp.single j 1 := by simp
      rw [this, MvPowerSeries.coeff_expand_smul]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb ((Finsupp.single_left_inj hp).1 h)
    · simp
  · rw [Finset.sum_eq_zero fun j _ => if_neg fun h => hs ⟨j, h⟩]
    by_cases hd : e.degree ≤ p
    · rw [GermFun.coeff_psTrunc _ _ _ hd]
      by_cases hdv : ∀ i, p ∣ e i
      · choose c hc using hdv
        let e' : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm c
        have he : e = p • e' := by ext i; simp [e', hc]
        have hdeg : e'.degree ≤ 1 := by
          rw [he, map_nsmul, smul_eq_mul] at hd
          by_contra hh
          have : p * 2 ≤ p * e'.degree := Nat.mul_le_mul_left _ (by omega)
          omega
        rw [he, MvPowerSeries.coeff_expand_smul]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hdeg with h0 | h1
        · rw [(Finsupp.degree_eq_zero_iff _).1 h0]
          simpa using hV
        · exfalso
          have h1' : e' ∈ {d : σ →₀ ℕ | d.degree = 1} := h1
          rw [← Finsupp.range_single_one] at h1'
          obtain ⟨j, hj⟩ := h1'
          exact hs ⟨j, by rw [he, ← hj]; simp⟩
      · push Not at hdv
        obtain ⟨i, hi⟩ := hdv
        exact MvPowerSeries.coeff_expand_of_not_dvd _ _ _ hi
    · rw [psTrunc, MvPolynomial.coeff_sum]
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [MvPolynomial.coeff_monomial, if_neg]
      rintro rfl
      apply hd
      have := (Finset.mem_filter.1 hb).2
      simpa [Finsupp.degree_apply, Finsupp.sum] using this

theorem comp1_point_power_expand {d : ℕ} (p : ℕ) (hp : p ≠ 0) (V : Germ.Pt k 1 d) (i : Fin d) :
    Germ.comp1 V (ptPow k d p (0 : Fin 1)) i = MvPowerSeries.expand p hp (V i) := by
  have : (fun q : Fin 1 × Fin d => (![ptPow k d p (0 : Fin 1)] : Fin 1 → Germ.Pt k 1 d) q.1 q.2) =
      fun q => MvPowerSeries.X q ^ p := by
    funext ⟨a, b⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  rw [Germ.comp1, Germ.ev, this, MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]

def trTo (k : Type) [CommRing k] (κ : Type) {m n : ℕ} (h : n ≤ m) : Jet k κ m →ₐ[k] Jet k κ n :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem trTo_mk {κ : Type} {m n : ℕ} (h : n ≤ m) (P : MvPolynomial κ k) :
    trTo k κ h (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ P := rfl

theorem mem_orig_of_aug {κ : Type} {m : ℕ} {P : MvPolynomial κ k}
    (h : (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = 0) : P ∈ orig k κ := by
  rw [aug_mk] at h
  simpa [h] using sub_const_mem_orig P

theorem exists_low {κ κ' : Type} {m n : ℕ} (h : n ≤ m) (χ : Jet k κ m →ₐ[k] Jet k κ' m)
    (hχ : ∀ q, (jetAug : Jet k κ' m →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) :
    ∃ χ' : Jet k κ n →ₐ[k] Jet k κ' n,
      (∀ q, (jetAug : Jet k κ' n →ₐ[k] k) (χ' (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧
      χ'.comp (trTo k κ h) = (trTo k κ' h).comp χ := by
  choose P hP using fun q => Ideal.Quotient.mk_surjective (χ (Ideal.Quotient.mk _ (MvPolynomial.X q)))
  have hm : ∀ q, P q ∈ orig k κ' := fun q => mem_orig_of_aug (by rw [hP]; exact hχ q)
  refine ⟨jetMap P hm, fun q => ?_, jet_hom_ext fun q => ?_⟩
  · rw [jetMap_mk, MvPolynomial.aeval_X, aug_mk, ← aug_mk m, hP]
    exact hχ q
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, trTo_mk, jetMap_mk, MvPolynomial.aeval_X, ← hP, trTo_mk]

theorem pow_eq_of_first {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) {κ : Type}
    (a b : Jet k κ p) (h : trTo k κ hp a = trTo k κ hp b) : a ^ p = b ^ p := by
  haveI : CharP (MvPolynomial κ k) p := inferInstance
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [trTo_mk, trTo_mk, Ideal.Quotient.eq] at h
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq, ← sub_pow_char]
  have := Ideal.pow_mem_pow h p
  rw [← pow_mul] at this
  exact Ideal.pow_le_pow_right (by omega) this

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0}

theorem act_nat (t : SAB H X0) (n : ℕ) : t.act.act (n : 𝓞 E) = (𝟙 t.G) ^ n := by
  induction n with
  | zero =>
    have := t.act.add 0 0
    rw [add_zero] at this
    simpa using this
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]

theorem pow_eq_act {T : Over X0} (y : T ⟶ t.G) (n : ℕ) : y ^ n = y ≫ t.act.act (n : 𝓞 E) := by
  rw [act_nat, MonObj.comp_pow, Category.comp_id]

variable {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d)

theorem x_trTo {m n : ℕ} (h : n ≤ m) : homAt x (trTo S (Fin 1 × Fin d) h) ≫ g.x m = g.x n := by
  induction m, h using Nat.le_induction with
  | base =>
    have : trTo S (Fin 1 × Fin d) (le_refl n) = AlgHom.id S _ := jet_hom_ext fun _ => rfl
    rw [this, Formalism.L2.Pj.homAt_id, Category.id_comp]
  | succ m h ih =>
    have : trTo S (Fin 1 × Fin d) (h.trans (Nat.le_succ m)) = (trTo S (Fin 1 × Fin d) h).comp jetTrunc :=
      jet_hom_ext fun _ => rfl
    rw [this, ← Formalism.L2.Pj.homAt_comp, Category.assoc, g.chart.trunc, ih]

theorem x_zero {A : Type} [CommRing A] [Algebra S A] {m : ℕ} (χ : Jet S (Fin 1 × Fin d) m →ₐ[S] A)
    (hχ : ∀ q, χ (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0) : homAt x χ ≫ g.x m = 1 := by
  have : χ = (Algebra.ofId S A).comp jetAug := jet_hom_ext fun q => by
    rw [hχ, AlgHom.comp_apply, aug_mk]
    simp
  rw [this, ← Formalism.L2.Pj.homAt_comp, Category.assoc, g.chart.zero, MonObj.comp_one]

theorem pow_coord {A : Type} [CommRing A] [Algebra S A] (p : ℕ) (hp : p ≠ 0)
    (hV : ∃ V : Germ.Pt S 1 d, (∀ i, MvPowerSeries.constantCoeff (V i) = 0) ∧
      g.B.A.act (p : 𝓞 E) = Germ.comp1 V (ptPow S d p 0) ∧ lin V 1 = hw g.B p)
    (χ : Jet S (Fin 1 × Fin d) p →ₐ[S] A) :
    ∃ ψ : Jet S (Fin 1 × Fin d) p →ₐ[S] A, (homAt x χ ≫ g.x p) ^ p = homAt x ψ ≫ g.x p ∧
      ∀ q, ψ (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
        ∑ j, algebraMap S A (hw g.B p q.2 j) * χ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) ^ p := by
  obtain ⟨V, hc, hV, hl⟩ := hV
  refine ⟨χ.comp (jetSubstP p fun q : Fin 1 × Fin d => psTrunc p (g.B.A.act (p : 𝓞 E) q.2)), ?_, fun q => ?_⟩
  · rw [pow_eq_act, Category.assoc, g.chart.act, ← Category.assoc, Formalism.L2.Pj.homAt_comp]
  · rw [AlgHom.comp_apply, substP_X, hV, comp1_point_power_expand p hp, psTrunc_expand p hp _ (hc _), ← hl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, MvPolynomial.constantCoeff_X, zero_pow hp, mul_zero,
      Finset.sum_const_zero, map_zero, sub_zero, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact χ.commutes _

end Geo

end PositivityTheory.HtPt.Ce
end
end
