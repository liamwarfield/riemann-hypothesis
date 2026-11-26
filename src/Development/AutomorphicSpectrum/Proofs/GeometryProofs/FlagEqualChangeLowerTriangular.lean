module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri

theorem independent_and_triangular : ∀ (Ω : Type) [Field Ω] (L : Type) [AddCommGroup L] [Module Ω L] (r : ℕ) (b b₀ : Fin r → L) (Tm : Matrix (Fin r) (Fin r) Ω), LinearIndependent Ω b → (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) → (∀ i, b i = ∑ j, Tm i j • b₀ j) → LinearIndependent Ω b₀ ∧ ∀ i j, i < j → Tm i j = 0 := by
  intro Ω _ L _ _ r b b₀ Tm hb hflag hT
  have hspan : Submodule.span Ω (Set.range b₀) = Submodule.span Ω (Set.range b) := by
    have h := hflag r
    unfold flagStep at h
    have e1 : b₀ '' {k : Fin r | (k : ℕ) < r} = Set.range b₀ := by
      rw [← Set.image_univ]
      congr 1
      ext k
      simp [k.isLt]
    have e2 : b '' {k : Fin r | (k : ℕ) < r} = Set.range b := by
      rw [← Set.image_univ]
      congr 1
      ext k
      simp [k.isLt]
    rw [e1, e2] at h
    exact h.symm
  have hb₀ : LinearIndependent Ω b₀ := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range b₀))
    rw [hspan, finrank_span_eq_card hb]
  refine ⟨hb₀, fun i j hij => ?_⟩
  have hmem : b i ∈ Submodule.span Ω (b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
    have h := hflag ((i : ℕ) + 1)
    unfold flagStep at h
    rw [← h]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  obtain ⟨c, hc, hcb⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp hmem
  have hsum : ∑ k, (c k - Tm i k) • b₀ k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hT i, ← hcb, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · simp
    · intro k
      simp
  have h0 : c j - Tm i j = 0 := (Fintype.linearIndependent_iff.mp hb₀) (fun k => c k - Tm i k) hsum j
  have hcj : c j = 0 := by
    by_contra hne
    have hsupp := (Finsupp.mem_supported Ω c).mp hc
    have hj : j ∈ ({k : Fin r | (k : ℕ) < (i : ℕ) + 1} : Set (Fin r)) :=
      hsupp (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
    have hj' : (j : ℕ) < (i : ℕ) + 1 := hj
    have hij' : (i : ℕ) < (j : ℕ) := hij
    omega
  rw [hcj, zero_sub, neg_eq_zero] at h0
  exact h0

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangularStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_equal_change_lower_triangular : ∀ (Ω : Type) [Field Ω] (L : Type) [AddCommGroup L] [Module Ω L] (r : ℕ) (b b₀ : Fin r → L) (Tm : Matrix (Fin r) (Fin r) Ω), LinearIndependent Ω b → (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) → (∀ i, b i = ∑ j, Tm i j • b₀ j) → LinearIndependent Ω b₀ ∧ ∀ i j, i < j → Tm i j = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri.independent_and_triangular | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri.independent_and_triangular | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri.independent_and_triangular <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def tanW (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (w : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left)
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x) :
    Spec (CommRingCat.of (DualNumber S)) ⟶ Y.t.G.left :=
  Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ GlobalTheory.AllWt.ptF y) (by
    rw [hw, Category.assoc, GlobalTheory.AllWt.ptF, Limits.pullback.lift_fst]) ≫ Y.m.φ

theorem isComb_cast {V : Type} [CommRing V] {G : CategoryTheory.Over (Spec (CommRingCat.of V))} [GrpObj G] {r m : ℕ} (h : r = m)
    (v : Fin m → (epsOver V V ⟶ G)) (cf : Fin m → V) (w : epsOver V V ⟶ G) (hc : IsComb v cf w) :
    IsComb (fun i => v (Fin.cast h i)) (fun i => cf (Fin.cast h i)) w := by
  subst h
  exact hc

theorem spec_frac_ext (T : CDVR) {B : Type} [CommRing B]
    {p q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of T.Fr)}
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) : p = q := by
  rw [← Spec.map_preimage p, ← Spec.map_preimage q] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  congr 1
  ext1
  refine IsLocalization.ringHom_ext (nonZeroDivisors T.V) ?_
  exact congrArg CommRingCat.Hom.hom h2

theorem base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (T : CDVR)
    (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr)))
    (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (v : epsOver T.V T.V ⟶ G.G)
    (u' : Spec (CommRingCat.of (DualNumber T.Fr)) ⟶ t'.G.left)
    (h : u' ≫ m2.φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap T.V T.Fr))) ≫ v.left) :
    u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) := by
  apply spec_frac_ext T
  have e1 := m2.cart.1.w
  rw [Category.assoc, ← e1, ← Category.assoc, h, Category.assoc, Over.w v]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameNonarchimedean
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameNonarchimedean
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem inFibre_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → InFibre Or.𝔐.ξ p ⟨centre zV, Or.𝔐.all _⟩ := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev _ _ hGood la T io e y evT zT t hInt zV hR hu
  obtain ⟨-, -, hinv⟩ := hu
  obtain ⟨s, hs⟩ := RingHom.mem_range.1 hinv
  have hgen : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  have hv : ValAt Or.𝔐.ξ zV ((p : RM.Ω)⁻¹) ((Scheme.stalkClosedPointTo zV).hom s) := ⟨Or.𝔐.all _, s, hs, rfl⟩
  have hv' := LieTangent.valAt_base hgen (algebraMap T.V T.Fr) hv
  have hcst : Or.𝔐.cst ((p : c.F)⁻¹) = (p : RM.Ω)⁻¹ := by simp
  have hmem := hGood.1 ((p : c.F)⁻¹)
  have hla : (p : 𝓞 c.F) ∈ la.asIdeal := hInt.1
  have hOver : OverLa la T.V io e := hInt.2.1
  have hev : evT ⟨_, hmem⟩ = io ((p : c.F)⁻¹) := hInt.2.2.2.2.1 _ hmem
  have hr := hR ⟨_, hmem⟩
  rw [hev] at hr
  change ValAt _ _ (Or.𝔐.cst ((p : c.F)⁻¹)) _ at hr
  rw [hcst] at hr
  have heq := LieTangent.valAt_unique hgen hv' hr
  have hp0 : (p : c.F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : la.valuation c.F (p : c.F) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
    exact (la.valuation_lt_one_iff_mem _).2 hla
  have h2 := (WithZero.log_lt_log ((la.valuation c.F).ne_zero_iff.2 hp0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  have h3 : 0 < vLa la (p : c.F) := by unfold vLa; omega
  have h4 : 0 < vV T.V (io (p : c.F)) := by
    rw [hOver.2]
    exact mul_pos (by exact_mod_cast hOver.1) h3
  have h5 : vV T.V (io ((p : c.F)⁻¹)) = - vV T.V (io (p : c.F)) := by
    simp [vV, map_inv₀]
  have h6 := ReciprocityTheory.ChartRestriction.G.PullbackSections.vV_alg_nonneg T ((Scheme.stalkClosedPointTo zV).hom s)
  rw [heq, h5] at h6
  omega

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameNonarchimedeanStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_nonarchimedean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → InFibre Or.𝔐.ξ p ⟨centre zV, Or.𝔐.all _⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteResidueAbsoluteValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteResidueAbsoluteValue
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

theorem mem_range_of_valV_le_one {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {x : K'} (h : valV V x ≤ 1) : x ∈ (algebraMap V K').range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one K' x fun v => ?_
  have hv : v = IsDiscreteValuationRing.maximalIdeal V := by
    apply HeightOneSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal v.isMaximal
  rw [hv]
  exact h

theorem valV_algebraMap_le_one {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] (a : V) : valV V (algebraMap V K' a) ≤ 1 :=
  HeightOneSpectrum.valuation_le_one _ a

theorem vV_nonneg_iff {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {x : K'} (hx : x ≠ 0) : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
  have h := WithZero.log_le_log (valV_ne_zero (V := V) hx) (one_ne_zero : (1 : WithZero (Multiplicative ℤ)) ≠ 0)
  rw [← h, WithZero.log_one, vV]
  omega

theorem absT_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ), 0 < e → 0 < ramOverZ la → (∀ x y : T.Fr, FinRd.absT p la T e (x * y) = FinRd.absT p la T e x * FinRd.absT p la T e y) ∧ FinRd.absT p la T e 1 = 1 ∧ (∀ x : T.Fr, x ≠ 0 → 0 < FinRd.absT p la T e x) ∧ ∀ x : T.Fr, FinRd.absT p la T e x ≤ 1 ↔ x ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H l c p _ la T e he hr
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : (0 : ℝ) < (e : ℝ) * (ramOverZ la : ℝ) := by
    have h1 : (0 : ℝ) < e := by exact_mod_cast he
    have h2 : (0 : ℝ) < (ramOverZ la : ℝ) := by exact_mod_cast hr
    exact mul_pos h1 h2
  have h0 : FinRd.absT p la T e (0 : T.Fr) = 0 := by simp [FinRd.absT]
  have hne : ∀ x : T.Fr, x ≠ 0 → FinRd.absT p la T e x =
      (p : ℝ) ^ (-((vV T.V x : ℝ) / ((e : ℝ) * (ramOverZ la : ℝ)))) := by
    intro x hx
    simp [FinRd.absT, hx]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    by_cases hx : x = 0
    · subst hx; simp [h0]
    by_cases hy : y = 0
    · subst hy; simp [h0]
    rw [hne _ (mul_ne_zero hx hy), hne _ hx, hne _ hy, vV_mul hx hy, ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  · rw [hne _ one_ne_zero]
    have : vV T.V (1 : T.Fr) = 0 := by simp [vV]
    simp [this]
  · intro x hx
    rw [hne _ hx]
    exact Real.rpow_pos_of_pos hp0 _
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp [h0]
    rw [hne _ hx, ← Real.rpow_zero (p : ℝ), Real.rpow_le_rpow_left_iff hp]
    have hiff : -((vV T.V x : ℝ) / ((e : ℝ) * (ramOverZ la : ℝ))) ≤ 0 ↔ 0 ≤ vV T.V x := by
      rw [neg_nonpos, le_div_iff₀ hd, zero_mul]
      exact_mod_cast Iff.rfl
    rw [hiff, vV_nonneg_iff hx]
    constructor
    · exact mem_range_of_valV_le_one
    · rintro ⟨a, rfl⟩
      exact valV_algebraMap_le_one a

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteResidueAbsoluteValueStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_residue_absolute_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ), 0 < e → 0 < ramOverZ la → (∀ x y : T.Fr, FinRd.absT p la T e (x * y) = FinRd.absT p la T e x * FinRd.absT p la T e y) ∧ FinRd.absT p la T e 1 = 1 ∧ (∀ x : T.Fr, x ≠ 0 → 0 < FinRd.absT p la T e x) ∧ ∀ x : T.Fr, FinRd.absT p la T e x ≤ 1 ↔ x ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameLocalBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameLocalBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FrameValue

set_option backward.isDefEq.respectTransparency false

open Limits MonObj

section Grp

variable {S S' T T' : Scheme.{0}}

theorem one_left_pull {G : CategoryTheory.Over S} [GrpObj G] (a : T' ⟶ T) (x : T ⟶ S) (x' : T' ⟶ S) (h : a ≫ x = x') :
    a ≫ (1 : CategoryTheory.Over.mk x ⟶ G).left = (1 : CategoryTheory.Over.mk x' ⟶ G).left := by
  subst h
  exact congrArg (fun q => q.left) (comp_one (M := G) (CategoryTheory.Over.homMk a rfl : CategoryTheory.Over.mk (a ≫ x) ⟶ CategoryTheory.Over.mk x))

theorem one_left_grp {G' : CategoryTheory.Over S'} [GrpObj G'] {G : CategoryTheory.Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (x' : T ⟶ S') (x : T ⟶ S) (e : x' ≫ f = x) :
    (1 : CategoryTheory.Over.mk x' ⟶ G').left ≫ φ = (1 : CategoryTheory.Over.mk x ⟶ G).left := by
  subst e
  have hw : ((1 : CategoryTheory.Over.mk x' ⟶ G').left ≫ φ) ≫ G.hom = (CategoryTheory.Over.mk (x' ≫ f)).hom := by
    have h1 := CategoryTheory.Over.w (1 : CategoryTheory.Over.mk x' ⟶ G')
    rw [Category.assoc, h.1.w, ← Category.assoc, h1]
    rfl
  let x₀ : CategoryTheory.Over.mk (x' ≫ f) ⟶ G := CategoryTheory.Over.homMk _ hw
  have h2 := h.2 (CategoryTheory.Over.mk x') 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h2
  have h3 : x₀ * x₀ = x₀ := CategoryTheory.Over.OverMorphism.ext h2
  have h4 : x₀ = 1 := mul_eq_left.1 h3
  exact congrArg (fun q => q.left) h4

end Grp

section Ring

theorem exists_factor {O' R Ω C : Type} [CommRing O'] [CommRing R] [CommRing Ω] [CommRing C] (g : O' →+* Ω)
    (cl : O' →+* C) (hg : Function.Injective g) (φ : R →+* Ω) (ψ : R →+* C)
    (h : ∀ r, ∃ s, g s = φ r ∧ cl s = ψ r) : ∃ θ : R →+* O', g.comp θ = φ ∧ cl.comp θ = ψ := by
  choose θ h1 h2 using h
  exact ⟨{ toFun := θ
           map_one' := hg (by simp [h1])
           map_mul' := fun a b => hg (by simp [h1])
           map_zero' := hg (by simp [h1])
           map_add' := fun a b => hg (by simp [h1]) }, RingHom.ext h1, RingHom.ext h2⟩

theorem spec_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap b) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap a) = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (b.comp a)) := by
  rw [LieTangent.spec_comp]
  congr 2
  refine RingHom.ext fun t => ?_
  ext <;> simp

theorem spec_fst_alg (R : Type) [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [LieTangent.spec_comp]
  have e1 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext a; simp
  rw [e1, CommRingCat.ofHom_id, Spec.map_id]

theorem pts_eq {O' Ω R₀ : Type} [CommRing O'] [Field Ω] [CommRing R₀] (g : O' →+* Ω) (hg : Function.Injective g)
    {B : Scheme.{0}} (s : B ⟶ Sp R₀) [IsSeparated s] {a b : Sp O' ⟶ B} (h : spMap g ≫ a = spMap g ≫ b) : a = b := by
  haveI : IsDomain O' := hg.isDomain g
  haveI : IsDominant (spMap g) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot g).1 hg]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated s ?_ (spMap g) h
  refine ext_of_isDominant (spMap g) ?_
  rw [← Category.assoc, h, Category.assoc]

end Ring

section Lift

variable {X B : Scheme.{0}} {G : CategoryTheory.Over X} [GrpObj G] {G₀ : CategoryTheory.Over B} [GrpObj G₀] {f : X ⟶ B} {φ : G.left ⟶ G₀.left}

theorem exists_tan_lift (hc : IsGrpPullback G G₀ f φ) {O' R : Type} [CommRing O'] [CommRing R]
    (x : Sp O' ⟶ X) (θ : R →+* O') (P : Sp R ⟶ B) (t : Sp (DualNumber R) ⟶ G₀.left)
    (ht : t ≫ G₀.hom = spMap (algebraMap R (DualNumber R)) ≫ P)
    (h1 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t = (1 : CategoryTheory.Over.mk P ⟶ G₀).left)
    (he : x ≫ f = spMap θ ≫ P) :
    ∃ v : epsAt x ⟶ G, GlobalTheory.CompanionTheory.Ar.IsTanAt G x v ∧ v.left ≫ φ = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ t := by
  have hw : (spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ t) ≫ G₀.hom =
      (spMap (algebraMap O' (DualNumber O')) ≫ x) ≫ f := by
    rw [Category.assoc, ht, ← Category.assoc, LieTangent.spec_dual_alg, Category.assoc, Category.assoc, he]
  have l1 := hc.1.lift_fst _ _ hw
  have l2 := hc.1.lift_snd _ _ hw
  refine ⟨CategoryTheory.Over.homMk (hc.1.lift _ _ hw) l2, ?_, l1⟩
  show spMap (TrivSqZeroExt.fstHom O' O' O').toRingHom ≫ hc.1.lift _ _ hw = (1 : CategoryTheory.Over.mk x ⟶ G).left
  refine hc.1.hom_ext ?_ ?_
  · rw [Category.assoc, l1, ← Category.assoc, LieTangent.spec_fst_dual, Category.assoc, h1,
      one_left_pull _ P _ he.symm, one_left_grp hc x _ rfl]
  · rw [Category.assoc, l2, ← Category.assoc, spec_fst_alg, Category.id_comp]
    exact (CategoryTheory.Over.w (1 : CategoryTheory.Over.mk x ⟶ G)).symm

theorem extends_of (hc : IsGrpPullback G G₀ f φ) {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (M : LieModel G ξ E) (p : Cpt ξ) (e : E)
    (v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G)
    (hv : GlobalTheory.CompanionTheory.Ar.IsTanAt G _ v)
    (h : (M.pt e).left ≫ φ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (genMap ξ p))) ≫ v.left ≫ φ) :
    M.Extends p e v := by
  refine ⟨hv, hc.1.hom_ext (h.trans (Category.assoc _ _ _).symm) ?_⟩
  have h2 : (M.pt e).left ≫ G.hom = spMap (algebraMap Ω (DualNumber Ω)) ≫ ξ := CategoryTheory.Over.w (M.pt e)
  have h3 : v.left ≫ G.hom = spMap (algebraMap (X.presheaf.stalk p.1) (DualNumber (X.presheaf.stalk p.1))) ≫
    X.fromSpecStalk p.1 := CategoryTheory.Over.w v
  have h4 : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (genMap ξ p))) ≫ v.left) ≫ G.hom =
      spMap (algebraMap Ω (DualNumber Ω)) ≫ ξ := by
    rw [Category.assoc, h3, ← Category.assoc, LieTangent.spec_dual_alg, Category.assoc, LieTangent.spec_genMap]
  exact h2.trans h4.symm

end Lift

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
  {S : Type} [CommRing S] [Algebra c.F S]

theorem tanY_one (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ Small.tanY Y y τ i =
      (1 : CategoryTheory.Over.mk (Small.ptY Y y) ⟶ Y.t.G).left := by
  have a : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ Small.tanF Y y τ i =
      (1 : CategoryTheory.Over.mk (Small.ptF y) ⟶ Y.oF.t.G).left := by
    refine Y.m0.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, Small.tanF_φ, (y.tan τ i).2]
      exact (one_left_grp Y.m0.cart (Small.ptF y) y.x (Small.ptF_fst y)).symm
    · rw [Category.assoc, Small.tanF_hom, ← Category.assoc, spec_fst_alg, Category.id_comp]
      exact (CategoryTheory.Over.w (1 : CategoryTheory.Over.mk (Small.ptF y) ⟶ Y.oF.t.G)).symm
  rw [Small.tanY, ← Category.assoc, a]
  exact one_left_grp Y.m.cart (Small.ptF y) (Small.ptY Y y) rfl

end Model

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FrameValue

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots


open FrameValue in
set_option maxHeartbeats 600000 in
theorem frame_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)), ∃ w : EC, FinRd.Roots.IsFrameVec Or io zT MC w s i ∧ Or.𝔐.M.ValAt (FinRd.Roots.gen T zV) (Or.Fl.b s i) (MC.pt w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hv hG la T io e y evT zT t hI zV hR EC _ _ MC s i
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  obtain ⟨-, -, -, -, -, -, ⟨q, φ, ψ, yq, hφ, hψ, hr⟩, -⟩ := hI
  have hgen : genPt Or.𝔐.ξ ⤳ centre (gen T zV) := Or.𝔐.all _
  let P : Cpt Or.𝔐.ξ := ⟨centre (gen T zV), hgen⟩
  have hinj : Function.Injective (genMap Or.𝔐.ξ P) := Or.𝔐.tie.gen.inj P
  have hreg : ∀ r, ∃ s', genMap Or.𝔐.ξ P s' = φ.toRingHom r ∧
      (Scheme.stalkClosedPointTo (gen T zV)).hom s' = ψ.toRingHom r := fun r => by
    obtain ⟨h, e'⟩ := hr r
    obtain ⟨h', s', hs, hs'⟩ := hR ⟨φ r, h⟩
    exact ⟨s', hs, hs'.trans e'.symm⟩
  obtain ⟨θ, hθ1, hθ2⟩ := exists_factor _ _ hinj φ.toRingHom ψ.toRingHom hreg
  have hsep : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have he : Or.𝔐.X.fromSpecStalk P.1 ≫ Or.𝔐.f = spMap θ ≫ Small.ptY Y yq := by
    refine pts_eq (genMap Or.𝔐.ξ P) hinj Y.s ?_
    rw [← Category.assoc, ← Category.assoc]
    have e1 : spMap (genMap Or.𝔐.ξ P) ≫ Or.𝔐.X.fromSpecStalk P.1 = Or.𝔐.ξ := LieTangent.spec_genMap _ _
    rw [e1, ← Fr.pt_eq, Small.ptY_map Y hφ, ← hθ1, LieTangent.spec_comp]
  obtain ⟨v, hvt, hv'⟩ := exists_tan_lift Or.𝔐.m.cart (Or.𝔐.X.fromSpecStalk P.1) θ (Small.ptY Y yq)
    (Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) (Small.tanY_hom Y _ _ _) (tanY_one Y _ _ _) he
  have hext : Or.𝔐.M.Extends P (Or.Fl.b s i) v := by
    refine extends_of Or.𝔐.m.cart _ P _ v hvt ?_
    have e2 := Small.tanY_map Y hφ (Small.labelC s) (Small.labelFin Dw s i)
    have e3 := Fr.tan_eq s i
    have e4 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap (genMap Or.𝔐.ξ P)) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
          Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
      rw [← Category.assoc, spec_dual_comp, hθ1]
    exact e3.symm.trans (e2.trans (e4.trans (congrArg (fun u => _ ≫ u) hv'.symm)))
  have hb := LieTangent.isTanAt_base _ (LieTangent.spec_centre (gen T zV)) hvt
  obtain ⟨w, hw⟩ := MC.onto _ hb
  refine ⟨w, ?_, (Or.𝔐.M.valAt_iff _ _ _).2 ⟨hgen, v, hext, hw⟩⟩
  show (MC.pt w).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Small.labelFin Dw s i)
  have e5 : (MC.pt w).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo (gen T zV)).hom) ≫ v.left :=
    congrArg (fun u => u.left) hw
  have e6 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo (gen T zV)).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
        Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
    have e7 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo (gen T zV)).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) := (spec_dual_comp θ _).trans (by rw [hθ2])
    exact (congrArg (fun u => u ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) e7.symm).trans
      (Category.assoc _ _ _)
  rw [e5, Small.tanY_map Y hψ, e6]
  exact (Category.assoc _ _ _).trans (congrArg (fun u => _ ≫ u) hv')

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameLocalBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_local_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)), ∃ w : EC, FinRd.Roots.IsFrameVec Or io zT MC w s i ∧ Or.𝔐.M.ValAt (FinRd.Roots.gen T zV) (Or.Fl.b s i) (MC.pt w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginRootIndexBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginRootIndexBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit

section Lin

variable {Ω : Type} [Field Ω] {L : Type} [AddCommGroup L] [Module Ω L] {r : ℕ}

theorem exists_coeff_of_mem {c : Fin r → L} {s : Set (Fin r)} {x : L} (h : x ∈ Submodule.span Ω (c '' s)) :
    ∃ f : Fin r → Ω, (∀ j, j ∉ s → f j = 0) ∧ x = ∑ j, f j • c j := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp h
  refine ⟨l, fun j hj => ?_, ?_⟩
  · by_contra hne
    exact hj (hl (Finsupp.mem_support_iff.mpr hne))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    exact zero_smul _ _

theorem coeff_unique {c : Fin r → L} (hc : LinearIndependent Ω c) {f g : Fin r → Ω}
    (h : ∑ j, f j • c j = ∑ j, g j • c j) (j : Fin r) : f j = g j := by
  have h0 : ∑ j, (f - g) j • c j = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have := Fintype.linearIndependent_iff.mp hc (f - g) h0 j
  rwa [Pi.sub_apply, sub_eq_zero] at this

theorem flag_change {b c : Fin r → L} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω c i) (hT : ∀ i, b i = ∑ j, T i j • c j) :
    LinearIndependent Ω c ∧ ∀ i j, i < j → T i j = 0 := by
  have hr : ∀ v : Fin r → L, flagStep Ω v r = Submodule.span Ω (Set.range v) := by
    intro v
    show Submodule.span Ω (v '' {k : Fin r | (k : ℕ) < r}) = _
    rw [← Set.image_univ]
    congr 2
    ext k
    simp [k.isLt]
  have hc : LinearIndependent Ω c := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range c))
    rw [← hr c, ← hf r, hr b, finrank_span_eq_card hb]
  refine ⟨hc, fun i j hij => ?_⟩
  have hmem : b i ∈ Submodule.span Ω (c '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
    have h1 : b i ∈ flagStep Ω b ((i : ℕ) + 1) := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
    rw [hf] at h1
    exact h1
  obtain ⟨f, hf0, hfx⟩ := exists_coeff_of_mem hmem
  rw [coeff_unique hc ((hT i).symm.trans hfx) j]
  refine hf0 j (fun hj => ?_)
  have h2 : (i : ℕ) < j := hij
  have h3 : (j : ℕ) < (i : ℕ) + 1 := hj
  omega

theorem span_gr_eq (A : Subring Ω) {b c : Fin r → L} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω c i) (hT : ∀ i, b i = ∑ j, T i j • c j) (i : Fin r) :
    Submodule.span A {t : Ω | ∃ e ∈ Submodule.span A (Set.range b), e - t • c i ∈ flagStep Ω c i} =
      Submodule.span A {T i i} := by
  obtain ⟨hc, htri⟩ := flag_change hb hf hT
  have hterm : ∀ (v : Fin r → L) (g : Fin r → Ω), (∀ k, i < k → g k = 0) →
      ∑ k ∈ Finset.univ.erase i, g k • v k ∈ flagStep Ω v i := by
    intro v g hg
    refine Submodule.sum_mem _ fun k hk => ?_
    rcases lt_trichotomy k i with hki | hki | hki
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hki, rfl⟩)
    · exact absurd hki (Finset.ne_of_mem_erase hk)
    · rw [hg k hki, zero_smul]
      exact Submodule.zero_mem _
  have hbi : b i - T i i • c i ∈ flagStep Ω c i := by
    have := hterm c (fun j => T i j) (fun k hk => htri i k hk)
    rwa [Finset.sum_erase_eq_sub (Finset.mem_univ i), ← hT i] at this
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨e, he, het⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp he
    set α : Fin r → Ω := fun k => (a k : Ω) with hα
    have hsum : ∑ k, a k • b k = ∑ k, α k • b k := rfl
    rw [hsum] at het
    have hci : c i ∈ flagStep Ω c ((i : ℕ) + 1) := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
    have hmono : flagStep Ω c i ≤ flagStep Ω c ((i : ℕ) + 1) :=
      Submodule.span_mono (Set.image_mono fun k (hk : (k : ℕ) < i) => Nat.lt_succ_of_lt hk)
    have he1 : ∑ k, α k • b k ∈ Submodule.span Ω (b '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
      have h1 : ∑ k, α k • b k ∈ flagStep Ω c ((i : ℕ) + 1) := by
        have := add_mem (hmono het) (Submodule.smul_mem _ t hci)
        rwa [sub_add_cancel] at this
      rw [← hf] at h1
      exact h1
    obtain ⟨f, hf0, hfe⟩ := exists_coeff_of_mem he1
    have hαz : ∀ k, i < k → α k = 0 := by
      intro k hk
      rw [coeff_unique hb hfe k]
      refine hf0 k (fun hk' => ?_)
      have h2 : (i : ℕ) < k := hk
      have h3 : (k : ℕ) < (i : ℕ) + 1 := hk'
      omega
    have hC : ∑ k, α k • b k - α i • b i ∈ flagStep Ω c i := by
      rw [← hf, ← Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      exact hterm b α hαz
    have hE : (α i * T i i - t) • c i ∈ flagStep Ω c i := by
      have heq : (α i * T i i - t) • c i =
          (∑ k, α k • b k - t • c i) - (∑ k, α k • b k - α i • b i) - α i • (b i - T i i • c i) := by
        rw [sub_smul, mul_smul, smul_sub]
        abel
      rw [heq]
      exact sub_mem (sub_mem het hC) (Submodule.smul_mem _ (α i) hbi)
    have ht : t = α i * T i i := by
      by_contra hne
      have hne' : α i * T i i - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hmem : c i ∈ flagStep Ω c i := by
        have := Submodule.smul_mem _ (α i * T i i - t)⁻¹ hE
        rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
      exact hc.notMem_span_image (s := {k : Fin r | (k : ℕ) < i}) (x := i) (fun h => lt_irrefl (i : ℕ) h) hmem
    rw [ht]
    exact Submodule.mem_span_singleton.mpr ⟨a i, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨b i, Submodule.subset_span ⟨i, rfl⟩, hbi⟩

end Lin

section Lines

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem zpow_mem_span {A : Subring Ω} {s σ : Ω} (hs : s ≠ 0) (hσ : σ ≠ 0)
    (h : Submodule.span A {σ} = Submodule.span A {s}) (a : ℤ) : σ ^ a ∈ Submodule.span A {s ^ a} := by
  have h1 : σ ∈ Submodule.span A {s} := by
    rw [← h]
    exact Submodule.mem_span_singleton_self σ
  have h2 : s ∈ Submodule.span A {σ} := by
    rw [h]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.mp h2
  have hu' : (u : Ω) * s = σ := hu
  have hv' : (v : Ω) * σ = s := hv
  have huv : (u : Ω) * v = 1 := by
    have h3 : (u : Ω) * v * σ = 1 * σ := by rw [mul_assoc, hv', hu', one_mul]
    exact mul_right_cancel₀ hσ h3
  have hmem : ∀ n : ℤ, (u : Ω) ^ n ∈ A := by
    intro n
    rcases n with n | n
    · simpa using pow_mem u.2 n
    · have h4 : (u : Ω) ^ (Int.negSucc n) = (v : Ω) ^ (n + 1) := by
        rw [zpow_negSucc, ← inv_pow, inv_eq_of_mul_eq_one_right huv]
      rw [h4]
      exact pow_mem v.2 _
  rw [Submodule.mem_span_singleton]
  refine ⟨⟨(u : Ω) ^ a, hmem a⟩, ?_⟩
  show (u : Ω) ^ a * s ^ a = σ ^ a
  rw [← mul_zpow, hu']

theorem unit_of_tens (Λ : Lat ξ Ω) (q : Cpt ξ) (a : ℤ) {s M : Ω} (hs : Λ.IsGenAt q s) (hM0 : M ≠ 0)
    (hM : Lat.tens (fun _ : Unit => Λ) (fun _ => a) q = Submodule.span (regAt ξ q) {M}) :
    M * s ^ (-a) ∈ regAt ξ q ∧ (M * s ^ (-a))⁻¹ ∈ regAt ξ q := by
  have hs0 : s ≠ 0 := hs.1
  have hsa : s ^ a ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q := by
    apply Submodule.subset_span
    exact ⟨fun _ => s, fun _ => hs, by simp⟩
  have hle : Lat.tens (fun _ : Unit => Λ) (fun _ => a) q ≤ Submodule.span (regAt ξ q) {s ^ a} := by
    apply Submodule.span_le.mpr
    rintro t ⟨σ', hσ', rfl⟩
    have hσ := hσ' ()
    have heq : Submodule.span (regAt ξ q) {σ' ()} = Submodule.span (regAt ξ q) {s} := hσ.2.symm.trans hs.2
    simpa using zpow_mem_span hs0 hσ.1 heq a
  have hMmem : M ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q := by
    rw [hM]
    exact Submodule.mem_span_singleton_self M
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.mp (hle hMmem)
  rw [hM] at hsa
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hsa
  have hr1 : (r' : Ω) * s ^ a = M := hr'
  have hr2 : (r : Ω) * M = s ^ a := hr
  have hsa0 : s ^ a ≠ 0 := zpow_ne_zero a hs0
  constructor
  · have h5 : M * s ^ (-a) = r' := by
      rw [← hr1, zpow_neg, mul_assoc, mul_inv_cancel₀ hsa0, mul_one]
    rw [h5]
    exact r'.2
  · have h6 : (M * s ^ (-a))⁻¹ = r := by
      rw [zpow_neg, mul_inv, inv_inv, ← hr2, mul_comm (r : Ω) M, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
    rw [h6]
    exact r.2

end Lines

theorem root_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (ρ : RootIx Dw) (q : Cpt Or.𝔐.ξ) (ch : (k : RM.K) → RM.ι k), InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) ch q → ∀ (b : Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1) → Or.𝔐.Li) (Tm : Matrix (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) RM.Ω), (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) i) → (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).IsFrameAt b q → (∀ i, b i = ∑ j, Tm i j • Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1 j) → (∀ i, Tm i i ≠ 0) → ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ) ∈ regAt Or.𝔐.ξ q ∧ (((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ))⁻¹ ∈ regAt Or.𝔐.ξ q := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or ρ q ch hch b Tm hfl hfr hT hd
  have hL : (Or.Fl.rootLat ρ).IsDegOn Set.univ RM.y (RM.xdeg ρ) (Or.e ρ) := Or.lines ρ
  obtain ⟨_, hL2⟩ := hL
  have hdeg : Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr
      (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q =
      Submodule.span (regAt Or.𝔐.ξ q) {(∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ} :=
    hL2 q (Set.mem_univ q) ch hch
  have hgr : ((Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1)
      (HodgeCpt.rootIdx Dw ρ).2).IsGenAt q (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) := by
    refine ⟨hd _, ?_⟩
    have h1 := span_gr_eq (regAt Or.𝔐.ξ q) hfr.1 hfl hT (HodgeCpt.rootIdx Dw ρ).2
    rw [← hfr.2] at h1
    exact h1
  have hM0 : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ ≠ 0 := by
    intro h0
    have hmem : Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2 ^ HodgeCpt.rootSgn Dw ρ ∈
        Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr
          (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q := by
      apply Submodule.subset_span
      exact ⟨fun _ => Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2, fun _ => hgr, by simp⟩
    rw [hdeg, h0] at hmem
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hmem
    have hx' : (x : RM.Ω) * 0 = _ := hx
    rw [mul_zero] at hx'
    exact zpow_ne_zero _ (hd _) hx'.symm
  exact unit_of_tens _ q _ hgr hM0 hdeg

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginRootIndexBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_root_index_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (ρ : RootIx Dw) (q : Cpt Or.𝔐.ξ) (ch : (k : RM.K) → RM.ι k), InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) ch q → ∀ (b : Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1) → Or.𝔐.Li) (Tm : Matrix (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) RM.Ω), (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) i) → (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).IsFrameAt b q → (∀ i, b i = ∑ j, Tm i j • Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1 j) → (∀ i, Tm i i ≠ 0) → ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ) ∈ regAt Or.𝔐.ξ q ∧ (((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ))⁻¹ ∈ regAt Or.𝔐.ξ q := by
  exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit.root_unit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameArchimedean
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameArchimedean
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem sigma_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ s : CMType H ⊕ CMType H, ∃ σ : 𝓞 E →+* T.V, (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) ∧ ∀ a, algebraMap T.V T.Fr (σ a) = io (labelEmb c s a) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hev hG la T io e y evT zT t hI zV hR s
  have hgen := Or.𝔐.tie.gen
  have hsp : GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ ⤳ centre zV := Or.𝔐.all _
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom _ _ Or.𝔐.ξ T.V zV hsp hgen
  have hm : ∀ a : 𝓞 E, Or.𝔐.emb s a ∈ regAt Or.𝔐.ξ ⟨centre zV, hsp⟩ := fun a =>
    HodgeBasic.mem_regAt_of_isIntegral hgen Or.𝔐.all Or.𝔐.normal _
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (Or.𝔐.emb s).toIntAlgHom)
  let σ : 𝓞 E →+* T.V := φ.comp ((Or.𝔐.emb s).codRestrict _ hm)
  have hv : ∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a) := fun a => (hφ _ _).2 ⟨hm a, rfl⟩
  refine ⟨σ, hv, fun a => ?_⟩
  have hA : Or.𝔐.cst (labelEmb c s a) ∈ A := hG.1 _
  have h1 := LieTangent.valAt_base hgen (algebraMap T.V T.Fr) (hv a)
  have h2 : GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ (gen T zV) (Or.𝔐.emb s a) (evT ⟨_, hA⟩) := hR ⟨_, hA⟩
  have h5 : evT ⟨_, hA⟩ = io (labelEmb c s a) := hI.2.2.2.2.1 _ hA
  exact (LieTangent.valAt_unique hgen h1 h2).trans h5

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameArchimedeanStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ s : CMType H ⊕ CMType H, ∃ σ : 𝓞 E →+* T.V, (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) ∧ ∀ a, algebraMap T.V T.Fr (σ a) = io (labelEmb c s a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists <;> assumption)
end
end
