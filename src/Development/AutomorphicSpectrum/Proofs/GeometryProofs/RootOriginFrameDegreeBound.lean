module

public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LinearIndependentAndExistsTriInLieEigEqSpan
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TriangularSpanCoeffRatio
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RootOriginFrameComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameTotalBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeightEstimate

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameCombined
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameCombined
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∉ SS → ¬ (p : ℤ) ∣ discr E → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC = FinRd.Roots.lieEig Or MC ρC σ := by
  first | exact @PositivityTheory.UnitarySelfGeneration.root_origin_frame_comparison | exact PositivityTheory.UnitarySelfGeneration.root_origin_frame_comparison
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameCombinedStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_combined : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∉ SS → ¬ (p : ℤ) ∣ discr E → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC = FinRd.Roots.lieEig Or MC ρC σ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined | exact GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined | (intros; apply GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameRelayBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameRelayBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (u : Fin (labelRk Dw s) → EC) (σ : 𝓞 E →+* T.V), (∀ i, FinRd.Roots.IsFrameVec Or io zT MC (u i) s i) → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → LinearIndependent T.Fr u ∧ ∃ yb : Fin (labelRk Dw s) → EC, FinRd.Roots.TriIn u (fun i => (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr)) yb ∧ FinRd.Roots.lieEig Or MC ρC σ = Submodule.span T.V (Set.range yb) := by
  first | exact @PositivityTheory.UnitarySelfGeneration.linearIndependent_and_exists_triIn_lieEig_eq_span | exact PositivityTheory.UnitarySelfGeneration.linearIndependent_and_exists_triIn_lieEig_eq_span
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameRelayBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_relay_bound :
    GlobalTheory.CompanionTheory.Ar.Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (u : Fin (labelRk Dw s) → EC) (σ : 𝓞 E →+* T.V), (∀ i, FinRd.Roots.IsFrameVec Or io zT MC (u i) s i) → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → LinearIndependent T.Fr u ∧ ∃ yb : Fin (labelRk Dw s) → EC, FinRd.Roots.TriIn u (fun i => (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr)) yb ∧ FinRd.Roots.lieEig Or MC ρC σ = Submodule.span T.V (Set.range yb) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound | exact GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializationCoordRatioValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializationCoordRatioValue
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DenValue

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem dh_mem_adjoin (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (f : MRing ι) :
    TiePrimes.dh y c f ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨f, rfl⟩

theorem adjoin_le_subring (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (A : Subring Ω)
    (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩)) : x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hr j.1 j.2
  | algebraMap r =>
    rw [eq_intCast]
    exact intCast_mem A r
  | add x y _ _ hx hy => exact A.add_mem hx hy
  | mul x y _ _ hx hy => exact A.mul_mem hx hy

theorem hasVal_ratio (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜)
    (c : (k : K) → ι k) (hzc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (z ⟨k, i⟩ / z ⟨k, c k⟩) := by
  classical
  unfold Small.HasVal
  refine ⟨Pi.single k 1, Pi.single k 1, MvPolynomial.X ⟨k, i⟩, MvPolynomial.X ⟨k, c k⟩,
    TiePrimes.homog_X _, TiePrimes.homog_X _, fun k' => by simp, ?_, ?_, ?_⟩
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, div_mul_cancel₀ _ (hyc k)]
  · rw [MvPolynomial.aeval_X]
    exact hzc k
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, div_mul_cancel₀ _ (hzc k)]

theorem hasVal_dh (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜)
    (c : (k : K) → ι k) (hzc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {h : MRing ι}
    {d : K → ℕ} (hh : IsMultiHomog h d) :
    Small.HasVal y 0 (TiePrimes.dh y c h) z (aeval z h / aeval z (TiePrimes.cMon c d)) := by
  have hc0 : aeval z (TiePrimes.cMon c d) ≠ 0 := by
    simp only [TiePrimes.cMon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
  unfold Small.HasVal
  refine ⟨d, d, h, TiePrimes.cMon c d, hh, TiePrimes.homog_cMon c d, fun k => by simp, ?_, hc0, ?_⟩
  · rw [TiePrimes.aeval_eq_dh_mul y c hyc hh, TiePrimes.aeval_eq_dh_mul y c hyc (TiePrimes.homog_cMon c d),
      TiePrimes.dh_cMon y c hyc, one_mul]
  · exact (div_mul_cancel₀ _ hc0).symm

private theorem hasVal_eq_of_hasVal_of_le {y : (Σ k, ι k) → Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}
    (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) {s : Ω} {w w' : 𝕜}
    (h1 : Small.HasVal y 0 s z w) (h2 : Small.HasVal y 0 s z w') : w = w' := by
  have hz' : (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ mCoordIdeal y, aeval z f = 0 := hz
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzw⟩ := h1
  obtain ⟨dg', dh', g', h', hg', hh', hd', hy', hz0', hzw'⟩ := h2
  have hdeq : dg = dh := funext fun k => by
    have := hd k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hdeq' : dg' = dh' := funext fun k => by
    have := hd' k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hm1 := TiePrimes.homog_mul hg hh'
  have hm2 := TiePrimes.homog_mul hg' hh
  rw [hdeq', ← hdeq, add_comm] at hm2
  have hneg := TiePrimes.homog_mul (TiePrimes.homog_C (K := K) (J := ι) (-1)) hm2
  rw [zero_add] at hneg
  have hF := TiePrimes.homog_add hm1 hneg
  have hFy : aeval y (g * h' + MvPolynomial.C (-1) * (g' * h)) = 0 := by
    simp only [map_add (f := _), map_mul, hy, hy', MvPolynomial.aeval_C, map_neg, map_one]
    ring
  have hFz := hz'.2 _ ((TiePrimes.mem_coord_iff y hF).2 hFy)
  simp only [map_add (f := _), map_mul, hzw, hzw', MvPolynomial.aeval_C, map_neg, map_one] at hFz
  have hprod : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination hFz
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact sub_eq_zero.1 h0
  · exact absurd h0 (mul_ne_zero hz0 hz0')

theorem value_and_denominator : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (A : Subring Ω) (ev : A →+* 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → (∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x)) → ∀ (c : (k : K) → ι k), (∀ k, z ⟨k, c k⟩ ≠ 0) → (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, ev ⟨_, hr k i⟩ = z ⟨k, i⟩ / z ⟨k, c k⟩) ∧ ∀ a : A, ∃ b : A, ev b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  intro K _ ι _ Ω _ y 𝕜 _ z A ev hz hval c hzc hyc hr
  refine ⟨fun k i => hasVal_eq_of_hasVal_of_le hz (hval ⟨_, hr k i⟩) (hasVal_ratio y z c hzc hyc k i), ?_⟩
  intro a
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzw⟩ := hval a
  have hdeq : dg = dh := funext fun k => by
    have := hd k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hbA : TiePrimes.dh y c h ∈ A := adjoin_le_subring y c A hr (dh_mem_adjoin y c h)
  have hc0 : aeval z (TiePrimes.cMon c dh) ≠ 0 := by
    simp only [TiePrimes.cMon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
  refine ⟨⟨_, hbA⟩, ?_, dh_mem_adjoin y c h, ?_⟩
  · rw [hasVal_eq_of_hasVal_of_le hz (hval ⟨_, hbA⟩) (hasVal_dh y z c hzc hyc hh)]
    exact div_ne_zero hz0 hc0
  · have hab : (a : Ω) * TiePrimes.dh y c h = TiePrimes.dh y c g := by
      have e1 := TiePrimes.aeval_eq_dh_mul y c hyc hg
      have e2 := TiePrimes.aeval_eq_dh_mul y c hyc hh
      rw [hdeq] at e1
      have hP : ∏ k, y ⟨k, c k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
      apply mul_right_cancel₀ hP
      rw [mul_assoc, ← e2, ← e1, hy]
    show (a : Ω) * TiePrimes.dh y c h ∈ _
    rw [hab]
    exact dh_mem_adjoin y c g

end GlobalTheory.CompanionTheory.Ar.DenValue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializationCoordRatioValueStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialization_coord_ratio_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (A : Subring Ω) (ev : A →+* 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → (∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x)) → ∀ (c : (k : K) → ι k), (∀ k, z ⟨k, c k⟩ ≠ 0) → (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, ev ⟨_, hr k i⟩ = z ⟨k, i⟩ / z ⟨k, c k⟩) ∧ ∀ a : A, ∃ b : A, ev b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DenValue.value_and_denominator | exact GlobalTheory.CompanionTheory.Ar.DenValue.value_and_denominator | (intros; apply GlobalTheory.CompanionTheory.Ar.DenValue.value_and_denominator <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrLieModelLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrLieModelLattice
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
private theorem exists_unitary_diagonal_of_isHermitian {X : Scheme.{0}} (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X)
    (c : centre (FinRd.Roots.gen T zV) ⤳ centre zV) :
    X.presheaf.stalkSpecializes c ≫ Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV) =
      Scheme.stalkClosedPointTo zV ≫ CommRingCat.ofHom (algebraMap T.V T.Fr) := by
  have c' := IsLocalRing.specializes_closedPoint
    ((Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) (IsLocalRing.closedPoint T.Fr))
  have e2 := Scheme.stalkClosedPointTo_comp (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) zV
  have e3 := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap T.V T.Fr))
  have e4 := ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of T.V)
  have e4' : (stalkClosedPointIso (CommRingCat.of T.V)).inv =
      (Scheme.ΓSpecIso (CommRingCat.of T.V)).inv ≫
        (Spec (CommRingCat.of T.V)).presheaf.germ ⊤ (IsLocalRing.closedPoint _) trivial := by
    rw [← e4, Iso.inv_hom_id_assoc]
  have e6 := TopCat.Presheaf.germ_stalkSpecializes (Spec (CommRingCat.of T.V)).presheaf
    (U := ⊤) (y := IsLocalRing.closedPoint _) trivial c'
  have e5 : (Spec (CommRingCat.of T.V)).presheaf.stalkSpecializes c' ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) =
      (stalkClosedPointIso (CommRingCat.of T.V)).hom ≫ CommRingCat.ofHom (algebraMap T.V T.Fr) := by
    rw [← Iso.inv_comp_eq, e4', Category.assoc]
    erw [reassoc_of% e6]
    erw [e3]
    rw [Iso.inv_hom_id_assoc]
  change X.presheaf.stalkSpecializes c ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ zV) = _
  rw [e2]
  erw [Scheme.Hom.stalkSpecializes_stalkMap_assoc zV _ _ c']
  rw [e5, Scheme.stalkClosedPointTo, Category.assoc]

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice : ∀ (X : AlgebraicGeometry.Scheme.{0}) (G : CategoryTheory.Over X) [CategoryTheory.GrpObj G] [CategoryTheory.IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (L₀ : Type) [AddCommGroup L₀] [Module Ω L₀] (M : LieModel G ξ L₀) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel G (FinRd.Roots.gen T zV) EC) (A : Subring Ω) (evT : A →+* T.Fr), IsCptGen ξ → AlgebraicGeometry.Smooth G.hom → ∀ (h : genPt ξ ⤳ centre zV), genPt ξ ⤳ centre (FinRd.Roots.gen T zV) → FinRd.Roots.ReadsPt ξ A T evT zV → ∀ (L : Lat ξ L₀) (r : ℕ) (b e : Fin r → L₀) (Tm : Matrix (Fin r) (Fin r) Ω) (w : Fin r → EC) (hT : ∀ i j, Tm i j ∈ A), L.IsFrameAt b ⟨centre zV, h⟩ → (∀ i, b i = ∑ j, Tm i j • e j) → (∀ j, M.ValAt (FinRd.Roots.gen T zV) (e j) (MC.pt (w j))) → M.fibAt L zV MC = Submodule.span T.V (Set.range fun i => ∑ j, evT ⟨Tm i j, hT i j⟩ • w j) := by
  intro X G _ _ Ω _ ξ L₀ _ _ M T zV EC _ _ _ _ MC A evT hX _ h hz hR L r b e Tm w hT hF hb hw
  obtain ⟨-, hF2⟩ := hF
  have c : centre (FinRd.Roots.gen T zV) ⤳ centre zV :=
    zV.base.hom.map_specializes (IsLocalRing.specializes_closedPoint _)
  have hK : ∀ s, (Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV)).hom
      (ConcreteCategory.hom (X.presheaf.stalkSpecializes c) s) =
      algebraMap T.V T.Fr ((Scheme.stalkClosedPointTo zV).hom s) := by
    intro s
    have := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (exists_unitary_diagonal_of_isHermitian T zV c)) s
    first
      | exact this
      | simpa only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] using this
  have hsc : ∀ {x : L₀} {y : EC}, M.ValAt (FinRd.Roots.gen T zV) x (MC.pt y) →
      ∀ s : X.presheaf.stalk (centre (FinRd.Roots.gen T zV)),
        M.ValAt (FinRd.Roots.gen T zV) (genMap ξ ⟨centre (FinRd.Roots.gen T zV), hz⟩ s • x)
          (MC.pt ((Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV)).hom s • y)) := by
    intro x y hxy s
    have := LieModel.ValAt.smul hxy hz s
    rwa [← LieModel.pt_smul] at this
  have hzero : ∀ {x : L₀} {y : EC}, M.ValAt (FinRd.Roots.gen T zV) x (MC.pt y) →
      M.ValAt (FinRd.Roots.gen T zV) 0 (MC.pt 0) := by
    intro x y hxy
    have := hsc hxy 0
    rw [map_zero, zero_smul] at this
    erw [map_zero, zero_smul] at this
    exact this
  have hsum : ∀ (s : Finset (Fin r)) (f : Fin r → L₀) (g : Fin r → EC),
      M.ValAt (FinRd.Roots.gen T zV) 0 (MC.pt 0) →
      (∀ j ∈ s, M.ValAt (FinRd.Roots.gen T zV) (f j) (MC.pt (g j))) →
        M.ValAt (FinRd.Roots.gen T zV) (∑ j ∈ s, f j) (MC.pt (∑ j ∈ s, g j)) := by
    intro s f g h0 hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, MC.add]
      exact LieModel.ValAt.add (hf a (Finset.mem_insert_self a s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hA : ∀ (a : A) (j : Fin r),
      M.ValAt (FinRd.Roots.gen T zV) ((a : Ω) • e j) (MC.pt (evT a • w j)) := by
    intro a j
    obtain ⟨h1, s, hs1, hs2⟩ := hR a
    have := hsc (hw j) s
    rw [hs1, hs2] at this
    exact this
  have hv : ∀ i, M.ValAt (FinRd.Roots.gen T zV) (b i)
      (MC.pt (∑ j, evT ⟨Tm i j, hT i j⟩ • w j)) := by
    intro i
    rw [hb i]
    exact hsum _ _ _ (hzero (hw i)) (fun j _ => hA ⟨Tm i j, hT i j⟩ j)
  unfold LieModel.fibAt
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w' ⟨h', x, hx, hxv⟩
    have hx' : x ∈ Submodule.span (regAt ξ ⟨centre zV, h⟩) (Set.range b) := by
      rw [← hF2]
      exact hx
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx'
    choose s hs using fun i => RingHom.mem_range.mp (cf i).2
    have key : M.ValAt (FinRd.Roots.gen T zV) x
        (MC.pt (∑ i, algebraMap T.V T.Fr ((Scheme.stalkClosedPointTo zV).hom (s i)) •
          ∑ j, evT ⟨Tm i j, hT i j⟩ • w j)) := by
      rw [← hcf]
      refine hsum _ _ _ (hzero hxv) fun i _ => ?_
      have := hsc (hv i) (ConcreteCategory.hom (X.presheaf.stalkSpecializes c) (s i))
      rw [LieTangent.genMap_specializes ⟨centre zV, h⟩ hz c, hK, hs i] at this
      rw [Subring.smul_def]
      exact this
    have hw' := MC.inj (LieModel.ValAt.unique hX hxv key)
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨h, b i, ?_, hv i⟩
    rw [hF2]
    exact Submodule.subset_span ⟨i, rfl⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrLieModelLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_lie_model_lattice : ∀ (X : AlgebraicGeometry.Scheme.{0}) (G : CategoryTheory.Over X) [CategoryTheory.GrpObj G] [CategoryTheory.IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (L₀ : Type) [AddCommGroup L₀] [Module Ω L₀] (M : LieModel G ξ L₀) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel G (FinRd.Roots.gen T zV) EC) (A : Subring Ω) (evT : A →+* T.Fr), IsCptGen ξ → AlgebraicGeometry.Smooth G.hom → ∀ (h : genPt ξ ⤳ centre zV), genPt ξ ⤳ centre (FinRd.Roots.gen T zV) → FinRd.Roots.ReadsPt ξ A T evT zV → ∀ (L : Lat ξ L₀) (r : ℕ) (b e : Fin r → L₀) (Tm : Matrix (Fin r) (Fin r) Ω) (w : Fin r → EC) (hT : ∀ i j, Tm i j ∈ A), L.IsFrameAt b ⟨centre zV, h⟩ → (∀ i, b i = ∑ j, Tm i j • e j) → (∀ j, M.ValAt (FinRd.Roots.gen T zV) (e j) (MC.pt (w j))) → M.fibAt L zV MC = Submodule.span T.V (Set.range fun i => ∑ j, evT ⟨Tm i j, hT i j⟩ • w j) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice | exact GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice | (intros; apply GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompleteDvrBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompleteDvrBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

private theorem exists_isDiffOf_of_isMonHom {S : AlgebraicGeometry.Scheme} {R : Type} [CommRing R] {G : CategoryTheory.Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (f : G ⟶ G) (hf : IsMonHom f) :
    ∃ A : E →ₗ[R] E, M.IsDiffOf f A := by
  have htan : ∀ e : E, IsTanAt G x (M.pt e ≫ f) := by
    intro e
    have h := M.tan e
    unfold IsTanAt at h ⊢
    rw [CategoryTheory.Over.comp_left, ← Category.assoc, h, ← CategoryTheory.Over.comp_left, MonObj.one_comp]
  choose g hg using fun e => M.onto _ (htan e)
  refine ⟨{ toFun := g, map_add' := ?_, map_smul' := ?_ }, fun e => hg e⟩
  · intro e e'
    apply M.inj
    rw [hg, M.add, M.add, hg, hg, MonObj.mul_comp]
  · intro c e
    simp only [RingHom.id_apply]
    apply M.inj
    apply CategoryTheory.Over.OverMorphism.ext
    rw [hg, CategoryTheory.Over.comp_left, M.smul, M.smul, hg, CategoryTheory.Over.comp_left, Category.assoc]

private theorem isDiffOf_unique {S : AlgebraicGeometry.Scheme} {R : Type} [CommRing R] {G : CategoryTheory.Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) {f : G ⟶ G} {A B : E →ₗ[R] E}
    (hA : M.IsDiffOf f A) (hB : M.IsDiffOf f B) : A = B := by
  ext e
  exact M.inj ((hA e).trans (hB e).symm)

theorem exists_lieModel_act_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module T.Fr EC) (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or T zV
  obtain ⟨EC, i1, i2, ⟨MC⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Or.𝔐.t.G T.Fr (FinRd.Roots.gen T zV)
  choose D hD using fun o : 𝓞 E => exists_isDiffOf_of_isMonHom MC (Or.𝔐.t.act.act o) (Or.𝔐.t.act.hom o)
  have hD' : ∀ (o : 𝓞 E) (e : EC), MC.pt (D o e) = MC.pt e ≫ Or.𝔐.t.act.act o := fun o e => hD o e
  refine ⟨EC, i1, i2, MC, RingHom.mk' ⟨⟨D, ?_⟩, ?_⟩ ?_, fun o => hD o⟩
  · show D 1 = 1
    apply isDiffOf_unique MC (hD 1)
    intro e
    rw [Or.𝔐.t.act.one, Module.End.one_apply, Category.comp_id]
  · intro o o'
    show D (o * o') = D o * D o'
    apply isDiffOf_unique MC (hD (o * o'))
    intro e
    rw [Module.End.mul_apply, hD', hD', mul_comm, Or.𝔐.t.act.mul, Category.assoc]
  · intro o o'
    show D (o + o') = D o + D o'
    apply isDiffOf_unique MC (hD (o + o'))
    intro e
    rw [LinearMap.add_apply, MC.add, hD', hD', Or.𝔐.t.act.add, MonObj.comp_mul]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompleteDvrBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_complete_dvr_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module T.Fr EC) (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.exists_lieModel_act_gen | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.exists_lieModel_act_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.exists_lieModel_act_gen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrCoordRatioValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrCoordRatioValue
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem chart_point : ∀ (X : AlgebraicGeometry.Scheme.{0}) (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (A : Subring Ω) (T : CDVR) (evT : A →+* T.Fr) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, evT ⟨_, hr k i⟩ ∈ (algebraMap T.V T.Fr).range) → (∀ a : A, ∃ b : A, evT b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩)) → ∃ (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (h : genPt ξ ⤳ centre zV), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zV, h⟩ ∧ FinRd.Roots.ReadsPt ξ A T evT zV := by
  intro X Ω _ ξ K _ J _ y hall tie A T evT c hc hr hint hfrac
  classical
  have hx : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  obtain ⟨U, hU, hmem⟩ := tie.affine c hx
  have hCeq : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) =
      Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) :=
    (TiePrimes.adjoin_eq hc).trans (Algebra.adjoin_range_eq_range_aeval ℤ _).symm

  have hgU : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, CoordMap.inChart_genPt tie.gen _ c hx specializes_rfl⟩
  let e : Γ(X, U) →+* Ω := (genMap ξ ⟨genPt ξ, specializes_rfl⟩).comp (X.presheaf.germ U _ hgU).hom
  have he : ∀ {p : X} (hp : p ∈ U) (t : Γ(X, U)), genMap ξ ⟨p, hall p⟩ (X.presheaf.germ U p hp t) = e t := by
    intro p hp t
    show _ = genMap ξ ⟨genPt ξ, specializes_rfl⟩ (X.presheaf.germ U _ hgU t)
    rw [RootHt.ArchC.genMap_germ U (hall p) hp t, RootHt.ArchC.genMap_germ U specializes_rfl hgU t]
  have hC : ∀ t, e t ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) := fun t => by
    rw [← hCeq]
    exact (tie.ring c hx (e t)).2 fun p hp =>
      ⟨X.presheaf.germ U p.1 ((hmem p.1).2 ⟨p.2, hp⟩) t, he _ t⟩

  let S : Subring Ω := ((algebraMap T.V T.Fr).range.comap evT).map A.subtype
  have hCS : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩), a ∈ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact ⟨⟨_, hr j.1 j.2⟩, hint j.1 j.2, rfl⟩
    | algebraMap n => simpa using intCast_mem S n
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hAm : ∀ t, e t ∈ A := fun t => by
    obtain ⟨b, -, hb⟩ := hCS _ (hC t)
    rw [← hb]
    exact b.2
  let e' : Γ(X, U) →+* A := e.codRestrict A hAm
  let ev : Γ(X, U) →+* T.Fr := evT.comp e'
  have hev : ∀ t, ev t ∈ (algebraMap T.V T.Fr).range := fun t => by
    obtain ⟨b, hb, hb'⟩ := hCS _ (hC t)
    have : b = e' t := Subtype.ext hb'
    show evT (e' t) ∈ _
    rw [← this]
    exact hb

  obtain ⟨g, hg⟩ : ∃ g : Γ(X, U) →+* T.V, (algebraMap T.V T.Fr).comp g = ev := by
    have hι : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
    let eV : T.V ≃+* (algebraMap T.V T.Fr).range :=
      RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
        ⟨fun a b h => hι (congrArg Subtype.val h), (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
    refine ⟨eV.symm.toRingHom.comp (ev.codRestrict _ hev), RingHom.ext fun t => ?_⟩
    exact congrArg Subtype.val (eV.apply_symm_apply (ev.codRestrict _ hev t))
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have hcV : centre (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Spec (CommRingCat.of T.V) ⟶ X) ∈ U :=
    h0 (Set.mem_univ (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint T.V)))
  obtain ⟨hV, hinV⟩ := (hmem _).1 hcV
  refine ⟨_, hV, hinV, ?_⟩

  have hz : gen T (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) =
      Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec := by
    rw [gen, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
  obtain ⟨hcz, hgerm⟩ := RootHt.ArchC.point_of_ringHom hU ev
  obtain ⟨hgz, hchz⟩ := (hmem _).1 hcz
  have hval : ∀ a : A, (a : Ω) ∈ regAt ξ ⟨_, hgz⟩ →
      ValAt ξ (Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec) (a : Ω) (evT a) := by
    intro a ha
    refine RootHt.ArchC.val_of_fractions hU hcz hgz ev hgerm ha fun t₁ t₂ h => ?_
    rw [he hcz, he hcz] at h
    have h' : a * e' t₂ = e' t₁ := Subtype.ext h
    have h'' := congrArg evT h'
    rwa [map_mul] at h''
  have hreg : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩),
      a ∈ regAt ξ ⟨_, hgz⟩ := fun a ha =>
    (tie.ring c hx a).1 (hCeq ▸ ha) _ hchz
  intro a
  rw [hz]
  refine hval a ?_
  obtain ⟨b, hb0, hbC, habC⟩ := hfrac a
  obtain ⟨h', s, hs1, hs2⟩ := hval b (hreg _ hbC)
  obtain ⟨s₂, hs₂⟩ := hreg _ habC
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' _).map_nonunit s (by
    rw [hs2]
    exact isUnit_iff_ne_zero.2 hb0)
  obtain ⟨u, rfl⟩ := hu
  have hb1 : (b : Ω) * genMap ξ ⟨_, hgz⟩ (↑u⁻¹ : X.presheaf.stalk _) = 1 := by
    rw [← hs1, ← map_mul, Units.mul_inv, map_one]
  refine ⟨s₂ * ↑u⁻¹, ?_⟩
  rw [map_mul, hs₂, _root_.mul_assoc, hb1, _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrCoordRatioValueStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_coord_ratio_value : ∀ (X : AlgebraicGeometry.Scheme.{0}) (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (A : Subring Ω) (T : CDVR) (evT : A →+* T.Fr) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, evT ⟨_, hr k i⟩ ∈ (algebraMap T.V T.Fr).range) → (∀ a : A, ∃ b : A, evT b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩)) → ∃ (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (h : genPt ξ ⤳ centre zV), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zV, h⟩ ∧ FinRd.Roots.ReadsPt ξ A T evT zV := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.chart_point | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.chart_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.chart_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameDegreeBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem reg_val {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {A : Subring Ω} {T : CDVR}
    {evT : A →+* T.Fr} {zV : Spec (CommRingCat.of T.V) ⟶ X} (hξ : IsCptGen ξ) (hR : ReadsPt ξ A T evT zV)
    (h : genPt ξ ⤳ centre zV) (a : A) (ha : (a : Ω) ∈ regAt ξ ⟨centre zV, h⟩) :
    evT a ∈ (algebraMap T.V T.Fr).range := by
  obtain ⟨s, hs⟩ := ha
  have h1 : ValAt ξ zV (a : Ω) ((Scheme.stalkClosedPointTo zV).hom s) := ⟨h, s, hs, rfl⟩
  exact ⟨_, LieTangent.valAt_unique hξ (LieTangent.valAt_base hξ (algebraMap T.V T.Fr) h1) (hR a)⟩

theorem log_bound {S m x y θ : ℝ} (hS : 0 < S) (hx : 0 < x) (hy : 0 < y) {n : ℤ} (hn : n = 1 ∨ n = -1)
    (hm : m = x ^ n) (hb : |Real.log x - Real.log y| ≤ θ) :
    |Real.log S - Real.log (S / m / y⁻¹ ^ n)| ≤ θ := by
  have hm0 : 0 < m := hm ▸ zpow_pos hx n
  have hy' : 0 < y⁻¹ ^ n := zpow_pos (inv_pos.2 hy) n
  rw [Real.log_div (div_pos hS hm0).ne' hy'.ne', Real.log_div hS.ne' hm0.ne', hm, Real.log_zpow, Real.log_zpow,
    Real.log_inv]
  rcases hn with rfl | rfl
  · simp only [Int.cast_one, one_mul]
    rw [show Real.log S - (Real.log S - Real.log x - -Real.log y) = Real.log x - Real.log y by ring]
    exact hb
  · simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    rw [show Real.log S - (Real.log S - -Real.log x - - -Real.log y) = -(Real.log x - Real.log y) by ring, abs_neg]
    exact hb

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem compare : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → Or.𝔐.OmVB → 0 < Dw.p + Dw.q →
    (∀ p' : ℕ, p'.Prime → (p' : ℤ) ∣ discr E → p' ∈ SS) →
    ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC]
      (MC : LieModel Or.𝔐.t.G (gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC →
    ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) →
    ∃ d d' : T.V, (∀ w ∈ lieEig Or MC ρC σ, d • w ∈ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC) ∧
      (∀ w ∈ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC, d' • w ∈ lieEig Or MC ρC σ) ∧
      (p : ℝ) ^ (-Small.latExp E SS p) ≤ absT p la T e (algebraMap T.V T.Fr d) ∧
      (p : ℝ) ^ (-Small.latExp E SS p) ≤ absT p la T e (algebraMap T.V T.Fr d') := by
  intro hG E _ _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hval hA la T io e y evT zT t hI zV hR hOm hpq
    hSS EC _ _ _ _ MC ρC hact s σ hσ
  have hpla : (p : 𝓞 c.F) ∈ la.asIdeal := hI.1
  have he : 0 < e := hI.2.1.1
  obtain ⟨hmul, hone, hpos, hle⟩ := GlobalTheory.T.finite_residue_absolute_value E H l c p la T e he (ram_pos hpla)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hθ := Small.latExp_nonneg E SS (Fact.out : p.Prime)
  have hle1 : (p : ℝ) ^ (-Small.latExp E SS p) ≤ absT p la T e (algebraMap T.V T.Fr 1) := by
    rw [map_one, hone]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  by_cases hpS : p ∈ SS
  · obtain ⟨κz, h1, h2, h3⟩ := GlobalTheory.T.root_origin_frame_total_bound hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT
      zT t hI zV hR hOm hpq hpS EC MC ρC hact s σ hσ
    obtain ⟨h4, D, h5, h6⟩ := GlobalTheory.T.root_origin_frame_height_estimate E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT
      zT t hI zV hR hpS EC MC ρC s
    refine ⟨1, κz * D, fun w hw => ?_, fun w hw => ?_, hle1, ?_⟩
    · rw [one_smul]
      exact h4 (h1 hw)
    · rw [mul_smul]
      exact h2 _ (h6 w hw)
    · rw [map_mul, hmul, h3]
      have e1 : Small.latExp E SS p = Small.htExp p + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E := if_pos hpS
      rw [e1, neg_add, Real.rpow_add hp0]
      exact mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp0.le _)
  · have hd : ¬ (p : ℤ) ∣ discr E := fun h => hpS (hSS p Fact.out h)
    have h1 := GlobalTheory.T.root_origin_frame_combined E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI zV hR hpS hd
      EC MC ρC hact s σ hσ
    refine ⟨1, 1, fun w hw => ?_, fun w hw => ?_, hle1, hle1⟩
    · rw [one_smul, h1]
      exact hw
    · rw [one_smul, ← h1]
      exact hw

theorem diag_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → Or.𝔐.OmVB → 0 < Dw.p + Dw.q →
    (∀ p' : ℕ, p'.Prime → (p' : ℤ) ∣ discr E → p' ∈ SS) →
    ∀ (s : CMType H ⊕ CMType H) (b : Fin (labelRk Dw s) → Or.𝔐.Li)
      (Tm : Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) RM.Ω) (hT : ∀ i j, Tm i j ∈ A),
      (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b s) i) →
      (Or.𝔐.V s).IsFrameAt b ⟨centre zV, Or.𝔐.all _⟩ → (∀ i, b i = ∑ j, Tm i j • Or.Fl.b s j) →
      (∀ i, evT ⟨Tm i i, hT i i⟩ ≠ 0) → ∀ i,
      |Real.log (absT p la T e (evT ⟨Tm i i, hT i i⟩)) - Real.log (absT p la T e (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr))| ≤
        Small.latExp E SS p * Real.log p := by
  intro hG E _ _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hval hA la T io e y evT zT t hI zV hR hOm hpq
    hSS s b Tm hT hfl hfr hb hd i
  have hpla : (p : 𝓞 c.F) ∈ la.asIdeal := hI.1
  have he : 0 < e := hI.2.1.1
  obtain ⟨hmul, hone, hpos, hle⟩ := GlobalTheory.T.finite_residue_absolute_value E H l c p la T e he (ram_pos hpla)
  obtain ⟨EC, _, _, MC, ρC, hact⟩ := GlobalTheory.T.root_origin_complete_dvr_bound E H Dw l Xo c O β Y SS RM Sys Fx Or T zV
  letI : Module T.V EC := Module.compHom EC (algebraMap T.V T.Fr)
  haveI : IsScalarTower T.V T.Fr EC := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.root_origin_frame_archimedean E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI
    zV hR s
  choose u hu huv using GlobalTheory.T.root_origin_frame_local_bound E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI
    zV hR EC MC s
  obtain ⟨hli, yb, htri, hspan⟩ := GlobalTheory.T.root_origin_frame_relay_bound hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y
    evT zT t hI zV hR EC MC ρC hact s u σ hu hσ
  haveI := Or.𝔐.t.semi.smooth
  have hW := GlobalTheory.T.complete_dvr_lie_model_lattice Or.𝔐.X Or.𝔐.t.G RM.Ω Or.𝔐.ξ Or.𝔐.Li Or.𝔐.M T zV EC MC A evT Or.𝔐.tie.gen inferInstance
    (Or.𝔐.all _) (Or.𝔐.all _) hR (Or.𝔐.V s) _ b (Or.Fl.b s) Tm u hT hfr hb huv
  obtain ⟨d, d', hd1, hd2, hμ, hμ'⟩ := compare hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y
    evT zT t hI zV hR hOm hpq hSS EC MC ρC hact s σ hσ
  have hlow := (GlobalTheory.T.flag_equal_change_lower_triangular RM.Ω Or.𝔐.Li _ b (Or.Fl.b s) Tm hfr.1 hfl hb).2
  have htri2 : TriIn u (fun i => evT ⟨Tm i i, hT i i⟩) (fun i => ∑ j, evT ⟨Tm i j, hT i j⟩ • u j) := fun i =>
    ⟨fun j => evT ⟨Tm i j, hT i j⟩, rfl, fun j hij => by
      have : (⟨Tm i j, hT i j⟩ : A) = 0 := Subtype.ext (hlow i j hij)
      show evT ⟨Tm i j, hT i j⟩ = 0
      rw [this, map_zero], rfl⟩
  have c1 := GlobalTheory.T.triangular_span_coeff_ratio T.V T.Fr EC _ u yb _ _ _ d hli htri htri2 hd
    (fun x hx => by
      rw [← hW]
      exact hd1 x (hspan ▸ hx)) i
  have c2 := GlobalTheory.T.triangular_span_coeff_ratio T.V T.Fr EC _ u _ yb _ _ d' hli htri2 htri (fun j => Units.ne_zero _)
    (fun x hx => by
      rw [← hspan]
      exact hd2 x (hW ▸ hx)) i
  obtain ⟨g1, hg1⟩ := c1
  obtain ⟨g2, hg2⟩ := c2
  set a := evT ⟨Tm i i, hT i i⟩ with ha
  set τ : T.Fr := (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr) with hτ
  replace hg1 : algebraMap T.V T.Fr d * τ = algebraMap T.V T.Fr g1 * a := hg1
  replace hg2 : algebraMap T.V T.Fr d' * a = algebraMap T.V T.Fr g2 * τ := hg2
  have hx : 0 < absT p la T e a := hpos _ (hd i)
  have hy : 0 < absT p la T e τ := hpos _ (Units.ne_zero _)
  have hg1' : absT p la T e (algebraMap T.V T.Fr g1) ≤ 1 := (hle _).2 ⟨g1, rfl⟩
  have hg2' : absT p la T e (algebraMap T.V T.Fr g2) ≤ 1 := (hle _).2 ⟨g2, rfl⟩
  have e1 := congrArg (absT p la T e) hg1
  have e2 := congrArg (absT p la T e) hg2
  rw [hmul, hmul] at e1 e2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set P := (p : ℝ) ^ (-Small.latExp E SS p) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hp0 _
  have hlogP : Real.log P = -(Small.latExp E SS p * Real.log p) := by
    rw [hP, Real.log_rpow hp0]
    ring
  have b1 : P * absT p la T e τ ≤ absT p la T e a := by
    calc P * absT p la T e τ ≤ absT p la T e (algebraMap T.V T.Fr d) * absT p la T e τ :=
          mul_le_mul_of_nonneg_right hμ hy.le
      _ = absT p la T e (algebraMap T.V T.Fr g1) * absT p la T e a := e1
      _ ≤ 1 * absT p la T e a := mul_le_mul_of_nonneg_right hg1' hx.le
      _ = _ := one_mul _
  have b2 : P * absT p la T e a ≤ absT p la T e τ := by
    calc P * absT p la T e a ≤ absT p la T e (algebraMap T.V T.Fr d') * absT p la T e a :=
          mul_le_mul_of_nonneg_right hμ' hx.le
      _ = absT p la T e (algebraMap T.V T.Fr g2) * absT p la T e τ := e2
      _ ≤ 1 * absT p la T e τ := mul_le_mul_of_nonneg_right hg2' hy.le
      _ = _ := one_mul _
  have l1 := Real.log_le_log (mul_pos hP0 hy) b1
  have l2 := Real.log_le_log (mul_pos hP0 hx) b2
  rw [Real.log_mul hP0.ne' hy.ne', hlogP] at l1
  rw [Real.log_mul hP0.ne' hx.ne', hlogP] at l2
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem reads_roots : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → (∀ (k : RM.K) (i j : RM.ι k), RM.y ⟨k, j⟩ ≠ 0 → RM.y ⟨k, i⟩ / RM.y ⟨k, j⟩ ∈ A) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → Small.ReadsRootsFin Or z (FinRd.tOf p la T e t) (Small.latExp E SS p) := by
  intro hG E _ _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr hOm hSS A p _ z ev hz hval hA hrat la T io e y evT zT t hI
  have hpla : (p : 𝓞 c.F) ∈ la.asIdeal := hI.1
  have he : 0 < e := hI.2.1.1
  obtain ⟨hmul, hone, hpos, hle⟩ := GlobalTheory.T.finite_residue_absolute_value E H l c p la T e he (ram_pos hpla)
  have habs : ∀ x : A, ‖ev x‖ = absT p la T e (evT x) := hI.2.2.2.2.2.1
  have hzp := hz.1
  have hmax : ∀ k, ∃ ck : RM.ι k, z ⟨k, ck⟩ ≠ 0 ∧ ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, ck⟩‖ := by
    intro k
    obtain ⟨u, hu⟩ := hzp.1 k
    haveI : Nonempty (RM.ι k) := ⟨u⟩
    obtain ⟨m, hm⟩ := Finite.exists_max (fun i => ‖z ⟨k, i⟩‖)
    refine ⟨m, fun h0 => ?_, hm⟩
    have h1 := hm u
    rw [h0, norm_zero] at h1
    exact hu (norm_le_zero_iff.1 h1)
  choose ch hc0 hcm using hmax
  classical
  have hy : ∀ k, RM.y ⟨k, ch k⟩ ≠ 0 := by
    intro k h0
    have hmem : (MvPolynomial.X ⟨k, ch k⟩ : MRing RM.ι) ∈ mCoordIdeal RM.y := by
      show mConeMap RM.y _ = 0
      rw [Small.ReadFinTest.mConeMap_form RM.y (TiePrimes.homog_X _)]
      simp [h0]
    have h1 := hzp.2 _ hmem
    rw [MvPolynomial.aeval_X] at h1
    exact hc0 k h1
  have hr : ∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, ch k⟩ ∈ A := fun k i => hrat k i (ch k) (hy k)
  obtain ⟨hevr, hden⟩ := GlobalTheory.T.specialization_coord_ratio_value RM.K RM.ι RM.Ω RM.y (PadicAlgCl p) z A ev hzp hval ch hc0 hy hr
  have hVr : ∀ k i, evT ⟨_, hr k i⟩ ∈ (algebraMap T.V T.Fr).range := fun k i => (hle _).1 (by
    rw [← habs, hevr, norm_div]
    exact div_le_one_of_le₀ (hcm k i) (norm_nonneg _))
  have hne : ∀ x : A, ev x ≠ 0 → evT x ≠ 0 := fun x hx h0 => by
    have h1 := habs x
    rw [h0, show absT p la T e (0 : T.Fr) = 0 from if_pos rfl] at h1
    exact hx (norm_eq_zero.1 h1)
  obtain ⟨zV, h, hch, hRd⟩ := GlobalTheory.T.complete_dvr_coord_ratio_value Or.𝔐.X RM.Ω Or.𝔐.ξ RM.K RM.ι RM.y Or.𝔐.all Or.𝔐.tie A T evT ch hy hr hVr
    (fun a => by
      obtain ⟨b, h1, h2, h3⟩ := hden a
      exact ⟨b, hne b h1, h2, h3⟩)
  have hunit : ∀ u u' : A, (u : RM.Ω) ∈ regAt Or.𝔐.ξ ⟨centre zV, h⟩ → (u' : RM.Ω) ∈ regAt Or.𝔐.ξ ⟨centre zV, h⟩ →
      u * u' = 1 → ‖ev u‖ = 1 := by
    intro u u' h1 h2 h3
    have a1 : ‖ev u‖ ≤ 1 := by
      rw [habs]
      exact (hle _).2 (reg_val Or.𝔐.tie.gen hRd h u h1)
    have a2 : ‖ev u'‖ ≤ 1 := by
      rw [habs]
      exact (hle _).2 (reg_val Or.𝔐.tie.gen hRd h u' h2)
    have a3 : ‖ev u‖ * ‖ev u'‖ = 1 := by
      rw [← norm_mul, ← map_mul, h3, map_one, norm_one]
    nlinarith [norm_nonneg (ev u), norm_nonneg (ev u')]
  have hsingle : ∀ k, Small.HasVal RM.y (Pi.single k 1) (RM.y ⟨k, ch k⟩) z (z ⟨k, ch k⟩) := fun k =>
    ⟨Pi.single k 1, 0, MvPolynomial.X ⟨k, ch k⟩, 1, TiePrimes.homog_X _, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one,
      fun j => by
        by_cases hj : j = k
        · subst hj
          simp
        · simp [Pi.single_eq_of_ne hj], by simp, by simp, by simp⟩
  intro ρ
  have hpq : 0 < Dw.p + Dw.q := lt_of_le_of_lt (Nat.zero_le _) ρ.2.2
  have hsg : HodgeCpt.rootSgn Dw ρ = 1 ∨ HodgeCpt.rootSgn Dw ρ = -1 := by
    unfold HodgeCpt.rootSgn
    split_ifs <;> simp
  obtain ⟨b, Tm, hfl, hfr, hb, hTA, hTd⟩ := hA.2.2.2 (HodgeCpt.rootIdx Dw ρ).1 ⟨centre zV, h⟩
  obtain ⟨hM, hMi⟩ := hA.2.2.1 ρ ch hy
  have hne' : ∀ j, evT ⟨Tm j j, hTA j j⟩ ≠ 0 := fun j h0 => by
    have h1 : (⟨Tm j j, hTA j j⟩ : A) * ⟨_, (hTd j).2⟩ = 1 := Subtype.ext (mul_inv_cancel₀ (hTd j).1)
    have h2 := congrArg evT h1
    rw [map_mul, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  have hP0 : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have he0 : Or.e ρ ≠ 0 := (Or.lines ρ).1
  have hM0 : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ ≠ 0 := mul_ne_zero hP0 he0
  obtain ⟨hu1, hu2⟩ := GlobalTheory.T.root_origin_root_index_bound E H Dw l Xo c O β Y SS RM Sys Fx Or ρ ⟨centre zV, h⟩ ch hch b Tm hfl hfr hb
    (fun j => (hTd j).1)
  have hT0 := (hTd (HodgeCpt.rootIdx Dw ρ).2).1
  have hTi := (hTd (HodgeCpt.rootIdx Dw ρ).2).2
  let Ma : A := ⟨_, hM⟩
  let Mi : A := ⟨_, hMi⟩
  let Ta : A := ⟨_, hTA (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2⟩
  let Ti : A := ⟨_, hTi⟩
  have hMM : Ma * Mi = 1 := Subtype.ext (mul_inv_cancel₀ hM0)
  have hTT : Ta * Ti = 1 := Subtype.ext (mul_inv_cancel₀ hT0)
  have nMM : ‖ev Ma‖ * ‖ev Mi‖ = 1 := by rw [← norm_mul, ← map_mul, hMM, map_one, norm_one]
  have nTT : ‖ev Ta‖ * ‖ev Ti‖ = 1 := by rw [← norm_mul, ← map_mul, hTT, map_one, norm_one]
  have hx : 0 < ‖ev Ta‖ := by
    by_contra h0
    have h1 : ‖ev Ta‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [h1, zero_mul] at nTT
    exact zero_ne_one nTT
  have hm0 : 0 < ‖ev Ma‖ := by
    by_contra h0
    have h1 : ‖ev Ma‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [h1, zero_mul] at nMM
    exact zero_ne_one nMM
  have hm : ‖ev Ma‖ = ‖ev Ta‖ ^ HodgeCpt.rootSgn Dw ρ := by
    rcases hsg with hs | hs
    · rw [hs] at hu1 hu2 ⊢
      have h1 := hunit (Ma * Ti) (Mi * Ta) (by simpa [Ma, Ti] using hu1) (by
        simpa [Mi, Ta, mul_comm] using hu2) (by
          rw [show Ma * Ti * (Mi * Ta) = (Ma * Mi) * (Ta * Ti) by ring, hMM, hTT, one_mul])
      rw [map_mul, norm_mul] at h1
      rw [zpow_one]
      have hTi0 : ‖ev Ti‖ ≠ 0 := fun h0 => by
        rw [h0, mul_zero] at nTT
        exact zero_ne_one nTT
      exact mul_right_cancel₀ hTi0 (h1.trans nTT.symm)
    · rw [hs] at hu1 hu2 ⊢
      have h1 := hunit (Ma * Ta) (Mi * Ti) (by simpa [Ma, Ta] using hu1) (by
        simpa [Mi, Ti, mul_comm] using hu2) (by
          rw [show Ma * Ta * (Mi * Ti) = (Ma * Mi) * (Ta * Ti) by ring, hMM, hTT, one_mul])
      rw [map_mul, norm_mul] at h1
      rw [zpow_neg_one]
      exact eq_inv_of_mul_eq_one_left h1
  have hseg : Small.HasVal RM.y (RM.xdeg ρ) (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) z
      (∏ k, z ⟨k, ch k⟩ ^ RM.xdeg ρ k) := by
    have h1 := hv_prod (Finset.univ) (fun k _ => hv_zpow hzp (hsingle k) (hy k) (hc0 k) (RM.xdeg ρ k))
    convert h1 using 1
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hS : 0 < Small.supMet (RM.xdeg ρ) z := Finset.prod_pos fun k _ =>
    zpow_pos (norm_pos_iff.2 fun h0 => hc0 k (congrFun h0 (ch k))) _
  have hsup : Small.supMet (RM.xdeg ρ) z = ∏ k, ‖z ⟨k, ch k⟩‖ ^ RM.xdeg ρ k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (hcm k))
      (norm_le_pi_norm (fun i => z ⟨k, i⟩) (ch k))]
  refine ⟨ev Mi * ∏ k, z ⟨k, ch k⟩ ^ RM.xdeg ρ k, ?_, ?_, ?_⟩
  · have h1 := hv_mul (hval Mi) hseg
    rw [zero_add] at h1
    convert h1 using 1
    show (Or.e ρ)⁻¹ = ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ)⁻¹ * _
    field_simp
  · refine mul_ne_zero (fun h0 => ?_) (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc0 k))
    rw [h0, norm_zero, mul_zero] at nMM
    exact zero_ne_one nMM
  · have hw : ‖ev Mi * ∏ k, z ⟨k, ch k⟩ ^ RM.xdeg ρ k‖ = Small.supMet (RM.xdeg ρ) z / ‖ev Ma‖ := by
      rw [norm_mul, norm_prod, hsup]
      simp only [norm_zpow]
      rw [eq_div_iff hm0.ne']
      linear_combination (∏ k, ‖z ⟨k, ch k⟩‖ ^ RM.xdeg ρ k) * nMM
    have hb' := diag_bound hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI zV hRd
      hOm hpq hSS _ b Tm hTA hfl hfr hb (fun j => hne' j) (HodgeCpt.rootIdx Dw ρ).2
    have hyy : 0 < absT p la T e (t (Small.rootFrameIx Dw ρ) : T.Fr) := hpos _ (Units.ne_zero _)
    rw [hw]
    have := log_bound (m := ‖ev Ma‖) (θ := Small.latExp E SS p * Real.log p) hS (x := ‖ev Ta‖) hx hyy hsg hm
      (by rw [habs]; exact hb')
    exact this

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameDegreeBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_degree_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → (∀ (k : RM.K) (i j : RM.ι k), RM.y ⟨k, j⟩ ≠ 0 → RM.y ⟨k, i⟩ / RM.y ⟨k, j⟩ ∈ A) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → Small.ReadsRootsFin Or z (FinRd.tOf p la T e t) (Small.latExp E SS p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.reads_roots | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.reads_roots | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.reads_roots <;> assumption)
end
