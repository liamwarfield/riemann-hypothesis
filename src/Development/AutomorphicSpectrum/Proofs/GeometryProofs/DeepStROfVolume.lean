module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsIntIffOfNatural
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PrimeLogSum
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllNormHeightBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PartIHolds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianCmCompLawsBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGoodLevel
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitComponentsOfAlgClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPPowerLevelFromPrimesAboveP
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SplitEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁

theorem mem_of_dense_of_isOpen {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    [T0Space X] {U : Set X} (hU : IsOpen U) (hd : Dense U) {x : X} (hx : ∀ z, z ⤳ x → z = x) : x ∈ U := by
  have hfin : (irreducibleComponents X).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hgen : ∀ C ∈ irreducibleComponents X, x ∈ C → C = closure {x} := by
    intro C hC hxC
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have e := hx _ (hg.specializes hxC)
    rw [← e]
    exact hg.def.symm
  let T : Set X := ⋃ C ∈ irreducibleComponents X \ {closure {x}}, C
  have hT : IsClosed T := Set.Finite.isClosed_biUnion (hfin.subset Set.diff_subset)
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hxT : x ∈ Tᶜ := by
    intro h
    obtain ⟨C, ⟨hC, hne⟩, hxC⟩ := Set.mem_iUnion₂.1 h
    exact hne (hgen C hC hxC)
  obtain ⟨w, hwT, hwU⟩ := hd.inter_open_nonempty _ hT.isOpen_compl ⟨x, hxT⟩
  have hwC : w ∈ closure {x} := by
    by_contra hn
    refine hwT (Set.mem_iUnion₂.2 ⟨irreducibleComponent w,
      ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => hn ?_⟩, mem_irreducibleComponent⟩)
    rw [← (show irreducibleComponent w = closure {x} from e)]
    exact mem_irreducibleComponent
  exact (specializes_iff_mem_closure.2 hwC).mem_open hU hwU

theorem injective_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : Function.Injective Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  exact Y.j.isEmbedding.injective

theorem genPt_comp {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (g : X ⟶ X') :
    genPt (ξ ≫ g) = g (genPt ξ) :=
  Scheme.Hom.comp_apply ξ g (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω))

theorem mem_range_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω) (hmax : ∀ y, y ⤳ genPt ξ → y = genPt ξ)
    (hs : ξ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F))) : genPt ξ ∈ Set.range Y.j := by
  have hpr := projProper _ _ _ Y.proj
  have sq : ξ ≫ Y.s = spMap cst ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [hs, spMap_comp']
  let P := pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let ξ₁ : Spec (CommRingCat.of Ω) ⟶ P := pullback.lift ξ (spMap cst) sq
  have hf : ξ₁ ≫ pullback.fst _ _ = ξ := pullback.lift_fst _ _ _
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  let x₁ : P := ξ₁ pt
  have h1 : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) x₁ = genPt ξ := by
    have e := Scheme.Hom.comp_apply ξ₁ (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) pt
    rw [hf] at e
    exact e.symm
  have a₁ := isPreimmersion_fst Y
  have hx₁ : ∀ z : P, z ⤳ x₁ → z = x₁ := by
    intro z hz
    apply (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective
    rw [h1]
    exact hmax _ (h1 ▸ hz.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
  have : LocallyOfFiniteType (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : QuasiCompact (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : IsNoetherian P := {}
  have := Y.jQ_open
  obtain ⟨v', hv'⟩ := mem_of_dense_of_isOpen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hx₁
  exact ⟨v', by rw [Model.j, Scheme.Hom.comp_apply, hv', h1]⟩

theorem splitComps_of_fnAlgClosed (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (hc : Formalism.L2.Pj.FnAlgClosed (Xo := Xo) (c := c)) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have hmax := CptInh.nogen ξ hξ
  obtain ⟨w₀, hw₀⟩ := mem_range_j Y ξ cst hmax hs
  have hwmax : ∀ y, y ⤳ w₀ → y = w₀ := by
    intro y hy
    have h1 : Y.j y ⤳ genPt ξ := hw₀ ▸ hy.map Y.j.continuous
    exact injective_j Y ((hmax _ h1).trans hw₀.symm)
  let Z : Formalism.L2.Pj.Comp Xo c := ⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩
  have hZ : Formalism.L2.Pj.genPt Z = w₀ := by
    have hC := irreducibleComponent_mem_irreducibleComponents w₀
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    exact hwmax _ (hg.specializes mem_irreducibleComponent)
  have e : genPt (Formalism.L2.Pj.genSp Z ≫ Y.j) = genPt ξ := by
    refine (genPt_comp (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z) Y.j).trans ?_
    rw [← hw₀, ← hZ]
    exact congrArg Y.j (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨i, hi⟩ := TowerOfTest.factor ξ hξ (Formalism.L2.Pj.genSp Z ≫ Y.j) e
  have hcomp : i.comp cst = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have hsY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) ≫ spMap (algebraMap (𝓞 c.F) c.F) =
        spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← hs]
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (Formalism.L2.Pj.genSp Z ≫ ·) hsY.symm) ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ Y.s) hi).trans (Category.assoc _ _ _)
    have e0 : (i.comp cst).comp (algebraMap (𝓞 c.F) c.F) =
        (algebraMap c.F (Formalism.L2.Pj.kap Z)).comp (algebraMap (𝓞 c.F) c.F) := by
      apply TowerOfTest.spec_inj
      have : spMap ((i.comp cst).comp (algebraMap (𝓞 c.F) c.F)) =
          spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
        rw [RingHom.comp_assoc, spMap_comp']
      exact this.trans (h2.symm.trans (spMap_comp' _ _).symm)
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i a)) := by
    obtain ⟨p, hp0, hp⟩ := ha
    refine ⟨p.map (Int.castRingHom c.F), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hp0, ?_⟩
    have h3 := Polynomial.hom_eval₂ p (algebraMap ℤ Ω) ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) a
    rw [← Polynomial.aeval_def, hp, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    refine Eq.trans ?_ h3.symm
    exact congrArg (fun φ => Polynomial.eval₂ φ _ p) (Subsingleton.elim _ _)
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i a := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.SplitEx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitComponentsOfAlgClosed
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem splitComps_of_fnAlgClosed_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), FnAlgClosed (Xo := Xo) (c := c) → SplitComps Y :=
  fun _ _ _ _ _ _ _ _ _ Y hc => GlobalTheory.CompanionTheory.Ar.SplitEx.splitComps_of_fnAlgClosed Y hc

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitComponentsOfAlgClosedStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_components_of_alg_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), FnAlgClosed (Xo := Xo) (c := c) → SplitComps Y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.splitComps_of_fnAlgClosed_model | exact GlobalTheory.CompanionTheory.Ar.Plug.splitComps_of_fnAlgClosed_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.splitComps_of_fnAlgClosed_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsGlobal
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem exists_isGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (l : Level H) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∃ Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F), Top.IsGlobal Xo l c Y := by
  intro E _ _ _ H Dw Xo l c hpq hg hA
  obtain ⟨-, hI⟩ := GlobalTheory.CompanionTheory.Ar.Top.partI_holds
  obtain ⟨Yl, hYl, hN6⟩ := hI E H Dw hpq Xo
  obtain ⟨Ygl, hD, hDom⟩ := hN6 l c hg hA
  exact ⟨Ygl, Yl, hg, hYl, hA, hD, hDom⟩

end GlobalTheory.CompanionTheory.Ar.Rec
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem vs_tower : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given →
    Top.GoodTowerExistsX → Top.VolumeTheoremX → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (II : IntersectionSystem), IsFullIntersectionSystem II → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → 1 ≤ Dw.q → 3 * Dw.q + 1 ≤ Dw.p + Dw.q → (2 * discr E * l.M').natAbs.primeFactors.card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 → ∃ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp), o.Extra ∧ CompOf o.toTowerOrigin κ ∧ T.bad = (2 * discr E * l.M').natAbs.primeFactors ∧ T.Proportional ∧ T.T1 II ∧ T.VolEq ∧ T.MeanSlope II C (hostRd E) (hostLval H) := by
  intro hG hTow hVol
  obtain ⟨C, hC, hV⟩ := hVol
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ H Dw l Xo c _ II hII hcl hgood hA hq hpq hcard
  have hN : 1 ≤ Dw.p + Dw.q := by omega
  have hp : 1 ≤ Dw.p := by omega
  obtain ⟨Xf, rfl⟩ : ∃ Xf : ∀ l' : Level H, Moduli Dw l', Xf l = Xo := by
    classical
    refine ⟨Function.update (fun l' => (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l' hN).some) l Xo, ?_⟩
    simp
  obtain ⟨Y, hY⟩ := GlobalTheory.CompanionTheory.Ar.Rec.exists_isGlobal E H Dw Xf l c hN hgood hA
  obtain ⟨T, o, hX⟩ := hTow E H Dw Xf l c Y hY (GlobalTheory.T.split_components_of_alg_closed E H Dw l (Xf l) c Y hcl) hp hq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.tower_components_equiv_of_given E H Dw l (Xf l) c Y T o.toTowerOrigin hG
  have hbad : T.bad = (2 * discr E * l.M').natAbs.primeFactors := by
    have hne : 2 * discr E * l.M' ≠ 0 := by
      intro h0
      obtain ⟨r, hr, hrp⟩ := Nat.exists_infinite_primes (T.bad.sup id + 1)
      have hmem : r ∈ T.bad := (o.bad_iff r).2 ⟨hrp, by rw [h0]; exact dvd_zero _⟩
      have := Finset.le_sup (f := id) hmem
      simp only [id] at this
      omega
    ext r
    rw [o.bad_iff, Nat.mem_primeFactors, Int.natCast_dvd]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, by simpa using hne⟩
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
  have hc : T.bad.card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 := by
    rw [hbad]; exact hcard
  obtain ⟨h1, h2, h3, -, -, h6⟩ := hV E H Dw Xf l c Y T o II hY hX hII hq hpq hc
  exact ⟨Y, T, o, κ, hX, hκ, hbad, h1, h3, h2, h6⟩

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CostTwoLogBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CostTwoLogBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem sum_padicVal_log {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hsub : n.primeFactors ⊆ S) :
    ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p = Real.log n := by
  have h1 : ∑ p ∈ n.primeFactors, (padicValNat p n : ℝ) * Real.log p =
      ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p := by
    refine Finset.sum_subset hsub fun p hpS hp => ?_
    have hpp := hS p hpS
    have hnd : ¬ p ∣ n := fun hd => hp (Nat.mem_primeFactors.2 ⟨hpp, hd, hn⟩)
    simp [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hnd]
  rw [← h1]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp),
      Nat.padicValNat_def]
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity

theorem log_hostRd (E : Type) [Field E] [NumberField E] :
    Real.log (hostRd E) = Real.log ((discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) := by
  have hd : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  have he : |(discr E : ℝ)| = ((discr E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hostRd, Real.log_rpow hd, he]
  ring

theorem costTwo_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H)
    (B : ℝ) (hB : 128 ≤ B)
    (hbad : (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ ⌊B⌋₊) :
    0 ≤ costTwo l B ∧ costTwo l B ≤ 60 * (Real.log B + Real.log (hostRd E)) := by
  classical
  set N : ℕ := ⌊B⌋₊ with hN
  set P : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime with hP
  set Q : Finset ℕ := Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors with hQ
  set n : ℝ := (Module.finrank ℚ E : ℝ) with hn
  set d : ℕ := (discr E).natAbs with hd
  have hd0 : d ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hn0 : 0 < n := by
    rw [hn]; exact_mod_cast Module.finrank_pos
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  have hSp : ∀ p ∈ P ∪ Q, p.Prime := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · exact hPp p h
    · exact hQp p h
  have hcost : costTwo l B = ∑ p ∈ P ∪ Q, exTwo E p * Real.log p := by
    rw [costTwo, GlobalTheory.CompHt.htPrimes_eq, finsum_mem_coe_finset]
  have hterm : ∀ p ∈ P ∪ Q, exTwo E p * Real.log p =
      Real.log p / ((p : ℝ) - 1) + 40 / n * ((padicValNat p d : ℝ) * Real.log p)
        + (if p = 2 then Real.log 2 else 0) := by
    intro p _
    rw [exTwo, GlobalTheory.CovHt.htEx, ← hd, ← hn]
    by_cases h2 : p = 2
    · subst h2; simp only [if_true]; ring_nf
    · simp only [h2, if_false]; ring
  have ha0 : ∀ p : ℕ, p.Prime → 0 ≤ Real.log p / ((p : ℝ) - 1) := fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)

  have hA : ∑ p ∈ P ∪ Q, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 + (Real.log N + 1) := by
    have hN128 : 128 ≤ N := by
      rw [hN]; exact Nat.le_floor (by exact_mod_cast hB)
    have hNr : (128 : ℝ) ≤ N := by exact_mod_cast hN128
    have h3 : ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 := by
      have hPe : P = (Finset.Iic N).filter Nat.Prime := by
        ext p; simp [hP]
      rw [hPe]; exact ReciprocityTheory.ChartRestriction.G.H1.primeLogSum_nat N (by omega)
    have hL1 : 1 ≤ Real.log ((N : ℝ) + 1) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hL2 : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < ((N : ℝ) + 1) / N by positivity)
      rw [Real.log_div (by linarith) (by linarith)] at h
      have : ((N : ℝ) + 1) / N ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have h4 : ∑ p ∈ Q \ P, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 1 := by
      calc ∑ p ∈ Q \ P, Real.log p / ((p : ℝ) - 1) ≤ ∑ _p ∈ Q \ P, Real.log ((N : ℝ) + 1) / N := by
            refine Finset.sum_le_sum fun p hp => ?_
            obtain ⟨hq, hnp⟩ := Finset.mem_sdiff.1 hp
            have hp1 : N + 1 ≤ p := by
              by_contra hc
              exact hnp (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hQp p hq⟩)
            have hp2 : (N : ℝ) + 1 ≤ p := by exact_mod_cast hp1
            have h := Real.log_le_sub_one_of_pos (show 0 < (p : ℝ) / ((N : ℝ) + 1) from div_pos (by linarith) (by linarith))
            rw [Real.log_div (by linarith) (by linarith)] at h
            have h5 : (N : ℝ) * ((p : ℝ) / ((N : ℝ) + 1) - 1) ≤ p - (N + 1) := by
              have e : (p : ℝ) / ((N : ℝ) + 1) - 1 = (p - (N + 1)) / ((N : ℝ) + 1) := by field_simp
              rw [e, ← mul_div_assoc, div_le_iff₀ (by linarith)]
              nlinarith
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            nlinarith [mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ N by linarith),
              mul_le_mul_of_nonneg_left hL1 (show (0 : ℝ) ≤ p - (N + 1) by linarith)]
        _ = (Q \ P).card * (Real.log ((N : ℝ) + 1) / N) := by simp
        _ ≤ N * (Real.log ((N : ℝ) + 1) / N) := by
            have : (((Q \ P).card : ℕ) : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans hbad
            exact mul_le_mul_of_nonneg_right this (div_nonneg (by linarith) (by linarith))
        _ = Real.log ((N : ℝ) + 1) := by field_simp
        _ ≤ Real.log N + 1 := hL2
    rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
    linarith

  have hdsub : d.primeFactors ⊆ P ∪ Q := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdv := Nat.dvd_of_mem_primeFactors hp
    refine Finset.mem_union_right _ (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hpp, ?_, ?_⟩))
    · exact Dvd.dvd.mul_left hdv 2
    · exact mul_ne_zero two_ne_zero hd0
  have hC : ∑ p ∈ P ∪ Q, 40 / n * ((padicValNat p d : ℝ) * Real.log p) = 40 * Real.log (hostRd E) := by
    rw [← Finset.mul_sum, sum_padicVal_log hd0 hSp hdsub, log_hostRd]
    ring

  have hT0 : 0 ≤ ∑ p ∈ P ∪ Q, (if p = 2 then Real.log 2 else 0) :=
    Finset.sum_nonneg fun p _ => by
      split_ifs
      · exact Real.log_nonneg (by norm_num)
      · exact le_rfl
  have hT : ∑ p ∈ P ∪ Q, (if p = 2 then Real.log 2 else 0) ≤ Real.log 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact Real.log_nonneg (by norm_num)
  have hsum : costTwo l B = ∑ p ∈ P ∪ Q, Real.log p / ((p : ℝ) - 1) + 40 * Real.log (hostRd E)
      + ∑ p ∈ P ∪ Q, (if p = 2 then Real.log 2 else 0) := by
    rw [hcost, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib, hC]
  have hL : 0 ≤ Real.log (hostRd E) := by
    rw [log_hostRd]
    exact div_nonneg (Real.log_natCast_nonneg _) hn0.le
  have hA0 : 0 ≤ ∑ p ∈ P ∪ Q, Real.log p / ((p : ℝ) - 1) :=
    Finset.sum_nonneg fun p hp => ha0 p (hSp p hp)
  have hNB : Real.log N ≤ Real.log B := by
    have hN1 : 1 ≤ N := by
      rw [hN]; exact Nat.le_floor (by norm_num; linarith)
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hB7 : 7 * Real.log 2 ≤ Real.log B := by
    have h : Real.log ((2 : ℝ) ^ 7) ≤ Real.log B := Real.log_le_log (by norm_num) (by norm_num; linarith)
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  refine ⟨?_, ?_⟩
  · rw [hsum]; linarith
  · rw [hsum]; linarith

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CostTwoLogBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cost_two_log_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (B : ℝ), 128 ≤ B → (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ ⌊B⌋₊ → 0 ≤ costTwo l B ∧ costTwo l B ≤ 60 * (Real.log B + Real.log (hostRd E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.costTwo_bound | exact GlobalTheory.CompanionTheory.Ar.Plug.costTwo_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.costTwo_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianCmCompLawsBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug.MeanTop

theorem primeFactors_sub (d : ℤ) (M : ℕ) :
    (2 * d * (M : ℤ)).natAbs.primeFactors ⊆ Nat.primeFactors (2 * d.natAbs) ∪ M.primeFactors := by
  have e : (2 * d * (M : ℤ)).natAbs = 2 * d.natAbs * M := by
    simp [Int.natAbs_mul]
  rw [e]
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hp, hd, h0⟩ := hp
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · exact Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hp, h, fun h' => h0 (by rw [h', zero_mul])⟩)
  · exact Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hp, h, fun h' => h0 (by rw [h', mul_zero])⟩)

theorem spread_nonneg {Ψ : Type} [Fintype Ψ] {N : ℕ} (hN : 0 < N) (u : Top.Wt Ψ N) : 0 ≤ Top.spread u := by
  unfold Top.spread
  refine Finset.sum_nonneg fun τ _ => ?_
  have i0 : Fin N := ⟨0, hN⟩
  have h1 := ciInf_le (Set.finite_range (fun i => u τ i)).bddBelow i0
  have h2 := le_ciSup (Set.finite_range (fun i => u τ i)).bddAbove i0
  linarith

theorem errX_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (s : ℝ) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ) :
    GlobalTheory.CovHt.errX s u g = (Real.log (GlobalTheory.CovHt.bndB u g) + s) * GlobalTheory.CovHt.l1 u + (Dw.q : ℝ) * Top.spread (reW u) := by
  unfold GlobalTheory.CovHt.errX Top.spread reW
  congr 2
  convert rfl

end GlobalTheory.CompanionTheory.Ar.Plug.MeanTop

namespace GlobalTheory.CompanionTheory.Ar.Plug


open GlobalTheory.CompanionTheory.Ar.Plug.MeanTop in
set_option maxHeartbeats 1000000 in
theorem top_meanAll : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → GlobalTheory.CompanionTheory.Ar.Top.Given → ArithIntersectionSystemStatement → BirationalPullbackPushforwardFormula → GlobalTheory.CompanionTheory.Ar.Top.GoodTowerExistsX → GlobalTheory.CompanionTheory.Ar.Top.VolumeTheoremX → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → 1 ≤ Dw.q → 3 * Dw.q + 1 ≤ Dw.p + Dw.q → 2 ≤ Fintype.card (CMType H) → (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → GlobalTheory.CovHt.MeanAll U x (Real.log (hostRd E) + |hostLval H|) C := by
  intro hNef hG hII hG6 hGT hVT
  obtain ⟨II, hII⟩ := hII
  obtain ⟨CT, hCT, hT⟩ := vs_tower hG hGT hVT
  refine ⟨CT + 120, by linarith, ?_⟩
  intro E _ _ _ _ H Dw l Xo c r U h e hLaws hUnif hFn hGood hA hq hpq hcardΨ hbad x hx
  classical
  have hqp : Dw.q < Dw.p := by omega
  have hN : 4 ≤ Dw.p + Dw.q := by omega
  have h128 : (128 : ℝ) ≤ 4 * (Fintype.card (CMType H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 := by
    have a : (2 : ℝ) ≤ Fintype.card (CMType H) := by exact_mod_cast hcardΨ
    have b : (4 : ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by exact_mod_cast hN
    nlinarith
  have hbadT : (2 * discr E * (l.M' : ℤ)).natAbs.primeFactors.card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 :=
    (Finset.card_le_card (primeFactors_sub _ _)).trans hbad
  obtain ⟨Y, T, o, κ, -, hCO, hTbad, hProp, hT1, -, hMS⟩ :=
    hT E H Dw l Xo c II hII hFn hGood hA hq hpq hbadT
  have hj : T.j = Dw.p := o.toTowerOrigin.j_eq
  have hW := GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M 0 (Classical.arbitrary T.Comp))
  intro u g hgap
  obtain ⟨-, -, -, -, hl1, -, -, -, hB⟩ := hW u
  obtain ⟨hBeq, hWH⟩ := hB g
  have hWH' : Top.WeightHyp T.j (reW u) g := by rw [hj]; exact hWH hq hqp hgap
  set B := GlobalTheory.CovHt.bndB u g with hBdef
  have hB128 : (128 : ℝ) ≤ B := by
    rw [hBeq]
    unfold Top.bigB0
    have : 0 ≤ ‖reW u‖ / g := div_nonneg (norm_nonneg _) hgap.1.le
    nlinarith
  have hBpos : 0 < B := by linarith
  have hfl128 : 128 ≤ ⌊B⌋₊ := Nat.le_floor (by exact_mod_cast hB128)
  have hflt : Top.bigB0 (reW u) g < (⌊B⌋₊ : ℝ) + 1 := by rw [← hBeq]; exact Nat.lt_floor_add_one B
  have hKB : 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 ≤ ⌊B⌋₊ := by
    refine Nat.le_floor ?_
    rw [hBeq]
    unfold Top.bigB0
    have : 0 ≤ ‖reW u‖ / g := div_nonneg (norm_nonneg _) hgap.1.le
    push_cast at h128 ⊢
    nlinarith
  have hTb : T.bad.card ≤ ⌊B⌋₊ := by rw [hTbad]; exact hbadT.trans hKB
  have hM := hMS (reW u) g hWH' ⌊B⌋₊ hfl128 hflt hTb
  have hsl := fun Z => GlobalTheory.T.uniform_all_norm_height_bound hNef hG hG6 E H Dw l Xo c r U h e hLaws hUnif x hx Y T o κ II hCO hII hProp hT1 Z u g B
    hgap.2.1 hWH' (le_of_eq hBeq.symm)
  obtain ⟨hc0, hc⟩ := GlobalTheory.T.cost_two_log_bound E H l B hB128 (hbad.trans hKB)
  refine ⟨fun Z => T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u, hsl, ?_⟩

  have hfin : (∑ᶠ Z, (T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u)) =
      ∑ c', (T.slope II ⌊B⌋₊ c' (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u) := by
    rw [finsum_comp_equiv κ (f := fun c' => T.slope II ⌊B⌋₊ c' (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u)]
    exact finsum_eq_sum_of_fintype _
  have hcard : (Nat.card (Comp Xo c) : ℝ) = Fintype.card T.Comp := by
    rw [Nat.card_congr κ, Nat.card_eq_fintype_card]
  have hn : (0 : ℝ) < Fintype.card T.Comp := by exact_mod_cast Fintype.card_pos
  rw [hfin, hcard, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sub_div,
    mul_div_cancel_left₀ _ hn.ne']
  set S := (∑ c', T.slope II ⌊B⌋₊ c' (reW u)) / (Fintype.card T.Comp : ℝ) with hS
  have hmin : min T.j (Dw.p + Dw.q - T.j) = Dw.q := by rw [hj]; omega
  unfold Top.RootTower.bracket at hM
  rw [hmin, ← hl1] at hM
  have hrd : 0 < hostRd E := by
    unfold hostRd
    exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero E)) _
  have hfl : (0 : ℝ) < ⌊B⌋₊ := by exact_mod_cast (show 0 < ⌊B⌋₊ by omega)
  have hlog : Top.bigLam ⌊B⌋₊ (hostRd E) (hostLval H) ≤ Real.log B + Real.log (hostRd E) + |hostLval H| := by
    unfold Top.bigLam
    rw [Real.log_mul hfl.ne' hrd.ne']
    have := Real.log_le_log hfl (Nat.floor_le hBpos.le)
    linarith
  have hsp0 := spread_nonneg (by omega) (reW u)
  have hL1 : 0 ≤ GlobalTheory.CovHt.l1 u := by
    unfold GlobalTheory.CovHt.l1
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hq0 : (0 : ℝ) ≤ (Dw.q : ℝ) := Nat.cast_nonneg _
  have a1 := mul_le_mul_of_nonneg_right hlog hL1
  have a2 : 0 ≤ |hostLval H| * GlobalTheory.CovHt.l1 u := mul_nonneg (abs_nonneg _) hL1
  have a3 : 0 ≤ (Dw.q : ℝ) * Top.spread (reW u) := mul_nonneg hq0 hsp0
  have a4 := mul_le_mul_of_nonneg_right hc hL1
  have a5 : CT * (Top.bigLam ⌊B⌋₊ (hostRd E) (hostLval H) * GlobalTheory.CovHt.l1 u + (Dw.q : ℝ) * Top.spread (reW u)) ≤
      CT * ((Real.log B + Real.log (hostRd E) + |hostLval H|) * GlobalTheory.CovHt.l1 u + (Dw.q : ℝ) * Top.spread (reW u)) :=
    mul_le_mul_of_nonneg_left (by linarith) hCT
  have a6 : Real.log B * GlobalTheory.CovHt.l1 u + Real.log (hostRd E) * GlobalTheory.CovHt.l1 u ≤
      (Real.log B + Real.log (hostRd E)) * GlobalTheory.CovHt.l1 u := by ring_nf; rfl
  rw [errX_eq]
  nlinarith

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianCmCompLawsBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_cm_comp_laws_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → GlobalTheory.CompanionTheory.Ar.Top.Given → ArithIntersectionSystemStatement → BirationalPullbackPushforwardFormula → GlobalTheory.CompanionTheory.Ar.Top.GoodTowerExistsX → GlobalTheory.CompanionTheory.Ar.Top.VolumeTheoremX → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → 1 ≤ Dw.q → 3 * Dw.q + 1 ≤ Dw.p + Dw.q → 2 ≤ Fintype.card (CMType H) → (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → GlobalTheory.CovHt.MeanAll U x (Real.log (hostRd E) + |hostLval H|) C := by
  exact GlobalTheory.CompanionTheory.Ar.Plug.top_meanAll
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodDatumParameters
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CardLower
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec

namespace SharpLaws

theorem card_psi (D : D7) (Q : Par D) : Fintype.card (CMType Q.H) = D.R.f := by
  have h := GlobalTheory.PeriodCoord.card_cmType Q.H
  rw [Nat.card_eq_fintype_card, D.host.finrank_cmField] at h
  rw [h]
  show 4 * D.R.ord / 2 = 2 * D.R.ord
  omega

end SharpLaws

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodDatumParameters
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

namespace VsLaws

section Laws

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem idem_val (h : GenFrEx Xo c) (Z : Comp Xo c) :
    evC h Z (GlobalTheory.FlatLine.idem Z) = 1 ∧ ∀ Z', Z' ≠ Z → evC h Z' (GlobalTheory.FlatLine.idem Z) = 0 := by
  obtain ⟨hL, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  exact ⟨GlobalTheory.FlatLine.evR_idem (GlobalTheory.AllWt.liesOn_genFr h Z) (hL.test _ _),
    fun Z' hZ => GlobalTheory.AllWt.evC_eq_zero h hZ (GlobalTheory.FlatLine.idem_mem_suppOn Z)⟩

theorem compLaws_of (hN : N1ab) (hN' : N1c) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hF : FnAlgClosed (Xo := Xo) (c := c))
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hT : ∀ σ, GoodEmb c σ → ∀ k x,
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x))
    (hC : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1) :
    ∃ h e', CompLaws U h e' := by
  obtain ⟨h, hgt⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hTw := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨κ, hb, -⟩ := GlobalTheory.CompBij.exists_bijection (U c.F.val.toRingHom) rfl (hU _ rfl) hF h
  refine ⟨h, GlobalTheory.FlatLine.idem, ?_⟩
  exact
    { comps := by
        rw [Nat.card_congr (Equiv.ofBijective κ hb), Nat.card_eq_fintype_card]
      ne := (GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg E H Dw l Xo c hpq).1
      genT := hgt h
      evalWD := GlobalTheory.TransferCompare.evalWD_framed _ _
      unf := hU
      unTest := hT
      chiTriv := hC
      ptNe := intFrNe_of' (GlobalTheory.T.xoNumPt_of_p_add_q_pos hN' E H Dw l Xo c hpq) GlobalTheory.locFld
        (GlobalTheory.Exist.intFrExt_of_good GlobalTheory.partI_closed hN hB hTw E H Dw l Xo c hpq hg)
      intAll := GlobalTheory.IntegralFrames.intAll GlobalTheory.partI_closed hN hB hTw E H Dw l Xo c hpq hg
      e_sec := GlobalTheory.CompRestr.idem_mem_sec
      e_val := idem_val h }

end Laws

theorem lval_congr {n m : ℕ} (h : n = m) (hn : Fact n.Prime) (hm : Fact m.Prime) (zn : NeZero n) (zm : NeZero m) :
    (deriv (DirichletCharacter.LFunction
        (((quadraticChar (ZMod n)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ n)) 1 /
      DirichletCharacter.LFunction
        (((quadraticChar (ZMod n)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ n) 1).re =
    (deriv (DirichletCharacter.LFunction
        (((quadraticChar (ZMod m)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ m)) 1 /
      DirichletCharacter.LFunction
        (((quadraticChar (ZMod m)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ m) 1).re := by
  subst h
  rfl

theorem hostLval_eq (D : D7) (Q : Par D) (h : Q.H.d = D.host.d) : hostLval Q.H = dlogL D 1 :=
  lval_congr h ⟨Q.H.d_prime⟩ ⟨D.host.hyp.2.1⟩ ⟨Q.H.d_prime.ne_zero⟩ ⟨D.host.hyp.2.1.ne_zero⟩

end VsLaws

theorem vs_laws : Top.Given → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : GlobalTheory.CovTop.Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → (∃ h e', CompLaws Y.U h e') ∧ (∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p) ∧ (T.Q.Dw j).q = D.R.m - j ∧ (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r ∧ Fintype.card (CMType T.Q.H) = D.R.f ∧ hostRd D.host.E = D.host.rdE ∧ hostLval T.Q.H = dlogL D 1 := by
  intro hG D T hT j hj1 hjm Y e o hY
  obtain ⟨⟨-, hN, hN', -⟩, -⟩ := hG
  have hI : InR D j := ⟨hj1, hjm.le⟩
  obtain ⟨hH, hLv, -, hD⟩ := hT.pins
  obtain ⟨hp, hq, -⟩ := hD j hI
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    goodAt_of_two_primes hLv.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.lev.1.2.1 hg0
  have hr1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [hpq]
    simp only [Ranks.r]
    omega
  refine ⟨VsLaws.compLaws_of hN hN' Y.U hr1 hg hY.geo hY.unf hY.unTest hY.chiTriv, hg, hq, hpq, ?_, rfl,
    VsLaws.hostLval_eq D T.Q hH.1⟩
  convert SharpLaws.card_psi D T.Q

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodDatumParametersStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_datum_parameters : Top.Given → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : GlobalTheory.CovTop.Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → (∃ h e', CompLaws Y.U h e') ∧ (∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p) ∧ (T.Q.Dw j).q = D.R.m - j ∧ (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r ∧ Fintype.card (CMType T.Q.H) = D.R.f ∧ hostRd D.host.E = D.host.rdE ∧ hostLval T.Q.H = dlogL D 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.vs_laws | exact GlobalTheory.CompanionTheory.Ar.Plug.vs_laws | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.vs_laws <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FieldOfDatumAbelian
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem field_of_datum_abelian : ∀ D : D7, IsAbelianGalois ℚ D.host.E := by
  intro D
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  haveI : IsMulCommutative (D.host.E ≃ₐ[ℚ] D.host.E) :=
    ⟨⟨fun s t => GlobalTheory.Mem.FieldsLaws.gal_comm D.host s t⟩⟩
  exact {}

end GlobalTheory.CompanionTheory.Ar.Rec
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem deepStR_of_volume : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ArithIntersectionSystemStatement → BirationalPullbackPushforwardFormula → Top.GoodTowerExistsX →
    Top.VolumeTheoremX → DeepStR := by
  intro hN hG hA hG6 hTw hV
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.abelian_cm_comp_laws_bound hN hG hA hG6 hTw hV
  refine ⟨C, hC0, ?_⟩
  intro D T hT hmk j hj1 hjm Y e o hY hcard
  obtain ⟨⟨h, e', hCL⟩, hgood, hq, hpq, hf, hrd, hL⟩ := GlobalTheory.T.good_datum_parameters hG D T hT j hj1 hjm Y e o hY
  haveI := GlobalTheory.CompanionTheory.Ar.Rec.field_of_datum_abelian D
  have hm2 := D.R.two_le_m
  have h2m : 2 * D.R.m ≤ D.R.m ^ 2 := by nlinarith
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hq1 : 1 ≤ (T.Q.Dw j).q := by omega
  have hq3 : 3 * (T.Q.Dw j).q + 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hf2 : 2 ≤ Fintype.card (CMType T.Q.H) := by
    rw [hf]
    show 2 ≤ 2 * D.R.ord
    have := D.R.ord_pos
    omega
  have hcard' : (Nat.primeFactors (2 * (discr D.host.E).natAbs) ∪ Y.d.l₂.M'.primeFactors).card ≤
      4 * Fintype.card (CMType T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) ^ 2 := by
    classical
    have h1 := D.host.card_bad_gt_le Y.d.l₂.M'.primeFactors (B := (D.R.n : ℝ)) le_rfl
    set S := Nat.primeFactors (2 * (discr D.host.E).natAbs) ∪ Y.d.l₂.M'.primeFactors
    have h2 := Finset.card_filter_add_card_filter_not (s := S) (fun p : ℕ => (D.R.n : ℝ) < (p : ℝ))
    have h3 : (S.filter fun p : ℕ => ¬ (D.R.n : ℝ) < (p : ℝ)).card ≤ D.R.n + 1 := by
      refine (Finset.card_le_card (t := Finset.range (D.R.n + 1)) fun p hp => ?_).trans (by simp)
      have : (p : ℝ) ≤ D.R.n := not_lt.1 (Finset.mem_filter.1 hp).2
      have : p ≤ D.R.n := by exact_mod_cast this
      exact Finset.mem_range.2 (by omega)
    have h4 : Fintype.card (CMType T.Q.H) = 2 * D.R.n := hf
    have h5 : 16 ≤ ((T.Q.Dw j).p + (T.Q.Dw j).q) ^ 2 := by nlinarith
    have h6 : 4 * Fintype.card (CMType T.Q.H) * 16 ≤ 4 * Fintype.card (CMType T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) ^ 2 :=
      Nat.mul_le_mul_left _ h5
    omega
  have key := hC D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U h e' hCL
    (GlobalTheory.CompanionTheory.Ar.Ref.unifAll_holds _ _) hY.geo hgood hY.lev.2 hq1 hq3 hf2 hcard' (xiR D) hY.xiAbs
  rw [hrd, hL] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.Plug
