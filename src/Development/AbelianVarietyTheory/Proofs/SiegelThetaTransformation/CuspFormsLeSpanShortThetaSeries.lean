module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory

theorem mem_span_of_map_mem_span_image {K : Type*} [Field K] {σ : K →+* ℂ} {C : Type*} [AddCommGroup C]
    [Module K C] {W : Type*} [AddCommGroup W] [Module ℂ W] (j : C →ₛₗ[σ] W) (V : Submodule K C)
    (hj : ∀ (m : ℕ) (b : Fin m → C), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => j (b i)))
    (S : Set C) (hS : S ⊆ V) {f : C} (hf : f ∈ V) (hjf : j f ∈ Submodule.span ℂ (j '' S)) :
    f ∈ Submodule.span K S := by
  let V' : Submodule K C := V ⊓ (Submodule.span ℂ (j '' S)).comap j
  have hSV : S ⊆ V' := fun s hs => ⟨hS hs, Submodule.subset_span ⟨s, hs, rfl⟩⟩
  have hind : ReciprocityTheory.ChartRestriction.G.PullbackSections.IndepToC (j.domRestrict V') := by
    intro m b hb
    exact hj m (fun i => (b i : C)) (fun i => (b i).2.1) (hb.map' V'.subtype (Submodule.ker_subtype V'))
  have himg : (j.domRestrict V') '' (V'.subtype ⁻¹' S) = j '' S := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hSV hx⟩, hx, rfl⟩
  have htop := ReciprocityTheory.ChartRestriction.G.PullbackSections.span_eq_top_of_indepToC (j.domRestrict V') hind (V'.subtype ⁻¹' S)
    (fun g => by rw [himg]; exact g.2.2)
  have h1 : (⟨f, hf, hjf⟩ : V') ∈ Submodule.span K (V'.subtype ⁻¹' S) := by
    rw [htop]; exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := V'.subtype) h1
  rw [Submodule.map_span] at h2
  exact Submodule.span_mono (Set.image_preimage_subset _ _) h2

theorem cusp_le_span_shortGen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ) → 1 ≤ r → l.A = 1 → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → (∀ a n, Dom a n → ∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (dδ : ∀ n, DeltaDat Xo c n), 0 < bad → (∀ n, (dδ n).IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab (dδ n).Xo₂ (dδ n).c₂ (dδ n).nab₂) ∧ UnitC (dδ n) ∧ ¬ 3 ∣ (dδ n).pd ∧ (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, (dδ n).PhiPin ph ψ x₀) ∧ ∀ a, Dom a n → ShortValTot Xo c nab bad nV a n (dδ n)) → SpanningAtDominantWeight Xo c nab bad nV (Formalism.L2.PjFree.cusp Xo c U) dδ := by
  intro hC E _ _ _ H Dw l Xo c r U σ hσ hU hr hA hG hP hχ nab bad nV dδ hbad hd a n hDom _ hn f hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd n
  have hrk : 4 * (Module.finrank ℚ E * r) + 4 ≤ n := by
    have he : Module.finrank ℚ E = 2 * NumberField.InfinitePlace.nrComplexPlaces E :=
      NumberField.IsTotallyComplex.finrank E
    have hr' : r = Dw.p + Dw.q := hU.1
    rw [he, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), ← hr'] at hn
    rw [he]
    calc 4 * (2 * NumberField.InfinitePlace.nrComplexPlaces E * r) + 4
        = 8 * NumberField.InfinitePlace.nrComplexPlaces E * r + 4 := by ring
      _ ≤ n := hn
  have hsp := GlobalTheory.Dict.holSub0_le_span_shortGen hC E H Dw l Xo c n (dδ n) σ r (U σ) hσ hU hr hA hG hP h1 h2 h3 h4 h5 nab bad nV a
    hbad hDom hrk (hχ a n hDom) (h6 a hDom)
  have hf' := (Formalism.L2.PjFree.mem_cusp Xo c U a n f).1 hf
  have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c σ r
    (U σ) hU a n).1
  refine mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (U σ)) (sec Xo c a n) hind (shortGen Xo c nab bad nV a n (dδ n)) (fun g hg => hg.1) hf'.1 (hsp ?_)
  refine ⟨hf'.2 σ hσ, fun k x hx => ?_⟩
  exact dif_neg hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_le_span_shortThetaSeries : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ) → 1 ≤ r → l.A = 1 → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → (∀ a n, Dom a n → ∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (dδ : ∀ n, DeltaDat Xo c n), 0 < bad → (∀ n, (dδ n).IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab (dδ n).Xo₂ (dδ n).c₂ (dδ n).nab₂) ∧ UnitC (dδ n) ∧ ¬ 3 ∣ (dδ n).pd ∧ (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, (dδ n).PhiPin ph ψ x₀) ∧ ∀ a, Dom a n → ShortValTot Xo c nab bad nV a n (dδ n)) → SpanningAtDominantWeight Xo c nab bad nV (Formalism.L2.PjFree.cusp Xo c U) dδ := by
  first | exact @GlobalTheory.cusp_le_span_shortGen | exact GlobalTheory.cusp_le_span_shortGen | (intros; apply GlobalTheory.cusp_le_span_shortGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HolomorphicCuspFormsFramesLeSpanShortThetaReadin
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HolomorphicCuspFormsFramesLeSpanShortThetaReadin
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

theorem sig_add_of_pins {D : D7} (Q : Par D) (h : Q.Pins) {j : ℕ} (hj : InR D j) :
    (Q.Dw j).p + (Q.Dw j).q = D.R.r := by
  obtain ⟨-, -, -, h4⟩ := h
  obtain ⟨hp, hq, -⟩ := h4 j hj
  rw [hp, hq]
  obtain ⟨h1, h2⟩ := hj
  simp only [Formalism.BasicNotions.Ranks.sigW, Formalism.BasicNotions.Ranks.r]
  omega

private theorem dom_wtA_of_wt {D : D7} {j : ℕ} (ka : WeightFamilies.Wt D j) : Dom (wtA ka) ka.n := by
  unfold Dom wtA
  refine ⟨fun τ => ?_, ka.n_even⟩
  intro a b hab
  apply Finset.sum_le_sum
  intro t _
  apply add_le_add
  · split_ifs with h
    · unfold Formalism.L2.Pj.ext0
      split_ifs with h1 h2 <;> first | omega | exact Nat.zero_le _ | exact le_refl _ | exact ka.aPlus_antitone t (Fin.mk_le_mk.2 hab)
    · exact le_refl _
  · split_ifs with h
    · unfold Formalism.L2.Pj.ext0
      split_ifs with h1 h2 <;> first | omega | exact Nat.zero_le _ | exact le_refl _ | exact ka.aM_anti t (Fin.mk_le_mk.2 hab)
    · exact le_refl _

private theorem par_l_A_eq_one_of_pins {D : D7} (Q : Par D) (h : Q.Pins) : Q.l.A = 1 := by
  obtain ⟨-, hL, -⟩ := h
  unfold Par.PinLevel at hL
  exact hL.2

theorem holSub0_le_span_short_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D), LawsM T.toCore → LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j), 8 * D.R.f * D.R.r + 4 ≤ ka.n → GlobalTheory.Dict.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) '' T.sh j ka) := by
  intro hC D T hM hSh hG hb hX j hj ka hn
  obtain ⟨-, dLev, dNab, dPd, dPhi, dRoot, shTot, -, -⟩ := hSh
  have hgood : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := sig_add_of_pins T.Q hM.pins hj
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  have hDom : Dom (wtA ka) ka.n := dom_wtA_of_wt ka
  have hl : T.Q.l.A = 1 := par_l_A_eq_one_of_pins T.Q hM.pins
  have hn' : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ ka.n := by
    rw [hostSize_finrank D]
    calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
      _ ≤ ka.n := hn
  have hP3 : ¬ 3 ∣ (T.dδ j ka.n).pd := by
    obtain ⟨p, hp, hpd⟩ := dPd
    rw [hpd j hj ka.n]
    have h15 := D.host.pde_mod
    rcases hp with rfl | rfl <;> omega
  have hUnit : UnitC (T.dδ j ka.n) := by
    obtain ⟨Cls, x, hF, δ, gdet, hCMP⟩ := dRoot j hj ka.n
    exact unitC_of_finite_character _ _ _ _ _ _ _ _ Cls δ gdet (by rw [hpq]; exact hr1) hCMP
  have hPhi : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ ka.n → ∃ ph ψ x₀, (T.dδ j ka.n).PhiPin ph ψ x₀ := by
    intro h
    obtain ⟨ph, ψ, x₀, -, hph, -⟩ := dPhi j hj ka.n (hpq ▸ h)
    exact ⟨ph, ψ, x₀, hph⟩
  have hPr : ∀ k, HasPrinc ((T.U j T.σ₀).X k) T.Q.l.M := by
    intro k ga hga hcong
    apply hG j hj T.σ₀ hgood k ga hga
    intro x hx
    obtain ⟨u, hu, he⟩ := hcong x hx
    refine ⟨u, hu, ?_⟩
    rw [he, Nat.cast_smul_eq_nsmul]
    abel
  have hChi : ∀ k, ChiOne ((Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)).X k)
      (Formalism.L2.PjFree.laU (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) (wtA ka) ka.n k) := by
    intro k γ hγ
    erw [Formalism.L2.PjFree.laU_ofPj]
    exact hM.chiTriv j hj T.σ₀ hgood _ _ hDom k γ hγ
  have key := GlobalTheory.T.cuspForms_vanishing_off_frames_le_span_shortTheta hC _ _ _ _ (T.Q.Xo j) T.Q.c ka.n (T.dδ j ka.n) T.σ₀ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) ((Formalism.L2.PjFree.goodEmb_iff _).2 hgood)
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hM.unf j hj _ hgood)) hr1 hl (hX j hj) hPr (dLev j hj ka.n)
    (dNab j hj ka.n) hUnit hP3 hPhi (T.nab j) (badN D) D.R.nV (wtA ka) hb hDom hn' hChi (shTot j hj _ _ hDom)
  convert key using 3 <;> rfl

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HolomorphicCuspFormsFramesLeSpanShortThetaReadinStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicCuspForms_frames_le_span_shortThetaReadings : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D), LawsM T.toCore → LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j), 8 * D.R.f * D.R.r + 4 ≤ ka.n → GlobalTheory.Dict.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) '' T.sh j ka) := by
  first | exact @GlobalTheory.Dict.holSub0_le_span_short_rec | exact GlobalTheory.Dict.holSub0_le_span_short_rec | (intros; apply GlobalTheory.Dict.holSub0_le_span_short_rec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InjectiveOfKerCountable
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem injective_of_ker_countable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (h : V →ₗ[ℂ] W) {S : Set V} (hS : S.Countable) (hk : ∀ v, h v = 0 → v ∈ S) : Function.Injective h := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have hi : Function.Injective fun t : ℂ => t • v := smul_left_injective ℂ hne
  have : (Set.univ : Set ℂ).Countable := (hS.preimage hi).mono fun t _ => hk _ (by rw [map_smul, hv, smul_zero])
  exact not_countable_complex this


open MonObj in
theorem exists_isometry [Algebra c.F ℂ] {r g g' : ℕ} {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ}
    (A : AnFib X bas idx e x L y) (hs : IsSympl X bas) (hx : x ∈ X.dom) (hg : g = g') {σ' : KA l →+* ℂ}
    {ty : Fin g' → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g' → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hy : y.x = F.u i P) :
    ∃ gam : L ≃ₗ[𝓞 E] (F.Di i).La, (∀ a b : L, (((F.Di i).EF (gam a) (gam b) : ℤ) : ℚ) = EF X a b) ∧
      ∀ (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (hm : ∀ a, mk a ∈ L), A.Marked mk →
        ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u, gam ⟨mk a, hm a⟩ = F.t i a + l.M • u := by
  obtain ⟨hconj, -, him, -, hsm, hinj, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  obtain ⟨y0, hy0, u, tan, eig, basis, s, gen⟩ := y
  change y0 = _ at hy
  subst hy
  obtain ⟨h, hh, -⟩ := HolHom.existsUnique_linear_ex F i hP (e := A.ex) A.ex_add A.hol
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  have hk : ∀ a : L, ∃ b, P b = h (pv X idx x a) := fun a =>
    (F.ex_ker i P hP _).1 ((hh _).symm.trans ((A.ex_ker _).2 ⟨a, a.2, rfl⟩))
  choose gam hgam using hk
  have hker : ∀ z b, h z = P b → ∃ v ∈ L, z = pv X idx x v := fun z b hz =>
    (A.ex_ker z).1 ((hh z).trans ((F.ex_ker i P hP _).2 ⟨b, hz.symm⟩))
  have hhi : Function.Injective h := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    exact injective_of_ker_countable h (Set.countable_range (pv X idx x)) fun v hv => by
      obtain ⟨w, -, hw⟩ := hker v 0 (hv.trans (map_zero P).symm)
      exact ⟨w, hw.symm⟩
  have hhs : Function.Surjective h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hg])).1 hhi
  let ρ : 𝓞 E → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a =>
    LinearMap.pi fun k => rowType X (idx k) (a : E) • LinearMap.proj k
  have hlin : ∀ (a : 𝓞 E) v k, h (ρ a v) k = ty k (a : E) * h v k := fun a =>
    FibreExp.intertwines F i hP h a (ρ a) fun v => by
      rw [← hh, ← hh]; exact A.ex_lin a v
  let gam₁ : L →ₗ[𝓞 E] (F.Di i).La :=
    { toFun := gam
      map_add' := fun a b => hP.2.1 (by rw [map_add (f := _), hgam, hgam, hgam, ← map_add (f := _), ← hadd]; rfl)
      map_smul' := fun a b => hP.2.1 (funext fun k => by
        rw [RingHom.id_apply, hP.1, hgam, hgam, ← hlin]
        exact congrArg (fun z => h z k) (hsm a b)) }
  have hb : Function.Bijective gam₁ := by
    refine ⟨fun a b hab => Subtype.ext (hinj (hhi ?_)), fun b => ?_⟩
    · rw [← hgam, ← hgam]; exact congrArg P hab
    · obtain ⟨z, hz⟩ := hhs (P b)
      obtain ⟨v, hv, rfl⟩ := hker z b hz
      exact ⟨⟨v, hv⟩, hP.2.1 ((hgam ⟨v, hv⟩).trans hz)⟩
  refine ⟨LinearEquiv.ofBijective gam₁ hb, fun a b => ?_, fun mk hm hmk a ha => ?_⟩
  · let lin : L → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun a =>
      { toFun := fun z => Real.pi * Dict.hx X bas idx x z (pv X idx x a)
        map_add' := fun z w => by simp only [Dict.hx, mulVec_add, add_dotProduct, mul_add]
        map_smul' := fun t z => by
          simp only [Dict.hx, mulVec_smul, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring }
    have hl : ∀ v, (F.ex i P (h v)).left = (A.ex v).left := fun v => by rw [hh]
    have key := FibreExp.alternating_eq F i hP h (fun a : L => pv X idx x a) gam (fun a => (hgam a).symm)
      (fr := A.fr) lin (fun a => Complex.log (A.χ a) +
        Real.pi / 2 * Dict.hx X bas idx x (pv X idx x a) (pv X idx x a))
      (fun j => by simp only [hl]; exact A.fr_hol j) (fun j v => by rw [hl]; exact A.fr_ne j v)
      (fun j j' v => by rw [hl]; exact A.fr_g j j' v) (fun a j v hv => by
        rw [hl] at hv
        have h0 : A.χ a ≠ 0 := by rw [← norm_ne_zero_iff, A.χ_norm a a.2]; exact one_ne_zero
        rw [A.fr_per a a.2 j v hv, add_left_comm, Complex.exp_add (Complex.log _), Complex.exp_log h0]
        rfl) a b
    change (Real.pi : ℂ) * Dict.hx X bas idx x _ _ - Real.pi * Dict.hx X bas idx x _ _ = _ at key
    rw [hconj (pv X idx x a) (pv X idx x b), ← mul_sub, ← neg_sub, Complex.sub_conj, him] at key
    have : ((EF X a b : ℚ) : ℂ) = (((F.Di i).EF (gam a) (gam b) : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (neg_ne_zero.2 Complex.two_pi_I_ne_zero)
      rw [← key]
      push_cast
      ring
    change (((F.Di i).EF (gam a) (gam b) : ℤ) : ℚ) = _
    exact_mod_cast this.symm
  · have hM : (l.M : ℂ) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
    have h1 : F.ex i P ((l.M : ℂ)⁻¹ • P (F.t i a)) = F.ex i P ((l.M : ℂ)⁻¹ • P (gam ⟨mk a, hm a⟩)) := by
      rw [← F.ex_eta i P hP a ha, hgam, ← map_smul, ← hh]
      refine (hmk a ha).trans (congrArg A.ex ?_)
      rw [hsm]
      funext j
      simp
    have h2 := F.ex_add i P hP ((l.M : ℂ)⁻¹ • P (F.t i a))
      ((l.M : ℂ)⁻¹ • P (gam ⟨mk a, hm a⟩) - (l.M : ℂ)⁻¹ • P (F.t i a))
    rw [add_sub_cancel, ← h1, left_eq_mul] at h2
    obtain ⟨w, hw⟩ := (F.ex_ker i P hP _).1 h2
    refine ⟨w, hP.2.1 ?_⟩
    change P (gam _) = _
    rw [map_add (f := _), map_nsmul, hw, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_inv_smul₀ hM, add_sub_cancel]

theorem exists_const {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (W : UW U) {f : Rul Xo c}
    (hf : f ∈ sec Xo c 0 0) (h1 : ∀ y : FrPt Xo c (CAt σ), ‖Formalism.L2.PjFree.toC (evR Xo c f y)‖ = 1) :
    ∃ C : U.Comp → ℂ, ∀ y : FrPt Xo c (CAt σ), ∃ k P, IsPeriod (W.F.Di (W.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P ∧
      y.x = W.F.u (W.ik k) P ∧ Formalism.L2.PjFree.toC (evR Xo c f y) = C k := by
  obtain ⟨-, -, honto, -, hsec, -⟩ := hU
  have hC : ∀ k, ∃ C : ℂ, ∀ x : (U.X k).dom, Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = C := fun k => by
    have hr : ∀ x : (U.X k).dom, Formalism.L2.PjFree.rdU U f k x = Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) := fun x => dif_pos x.2
    obtain ⟨C, -, hC⟩ := const_of_norm_factor (FourierCoefficientDomain.isOpen_dom (U.X k))
      (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected (J := Unit) (fun _ => Formalism.L2.PjFree.rdU U f k) (fun _ _ => 1) 1 one_pos
      (fun _ => (hsec 0 0 ⟨fun _ => antitone_const, Even.zero⟩ f hf k).1) (fun _ => differentiableOn_const _)
      fun x hx => ⟨_, (hr ⟨x, hx⟩).symm ▸ h1 (U.un k ⟨x, hx⟩), fun _ => (mul_one _).symm⟩
    exact ⟨C, fun x => by rw [← hr, hC () x x.2, mul_one]⟩
  choose C hC using hC
  refine ⟨C, fun y => ?_⟩
  obtain ⟨k, x, t, hb⟩ := honto y
  obtain ⟨P, -, hP, hx, -⟩ := W.pt k x
  refine ⟨k, P, hP, hb.1.trans hx, ?_⟩
  have hT : ∀ y : FrPt Xo c (CAt σ), FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y :=
    fun y => by
      by_contra hn
      have h0 : evR Xo c f y = 0 := dif_neg hn
      have := h1 y
      rw [h0] at this
      exact zero_ne_one ((norm_zero (E := ℂ)).symm.trans this)
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hw := (GlobalTheory.borDesc_and_wtField E H Dw l Xo c).2 0 0 f hf ℂ t (U.un k x) y (hT _) (hT _) hb
  have h0 : wchar (S := ℂ) (ex Dw 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
  rw [h0, one_mul] at hw
  exact hw.trans (hC k x)

theorem evR_eq_of_marked (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (hA : l.A = 1) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (h1 : ∀ y : FrPt Xo c (CAt σ), ‖Formalism.L2.PjFree.toC (evR Xo c f y)‖ = 1) {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {L : Lt E r} (hr : 1 ≤ r)
    (hs : IsSympl X bas) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : ∀ a, mk a ∈ L) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ x ∈ X.dom, ∀ x' ∈ X.dom, ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x' L y'),
      A.Marked mk → A'.Marked mk → evR Xo c f y = evR Xo c f y' := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro x hx x' hx' y y' A A' hk hk'
  have hD : 1 ≤ Dw.p + Dw.q := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ'⟩ : Nonempty X.Ψ := by
      by_cases h : τ ∈ X.Ψ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, not_not.1 (mt (X.cmType τ).2 h)⟩⟩
    obtain ⟨ρ, i⟩ := e (idx.symm (τ', ⟨0, hr⟩))
    have := i.pos
    unfold Datum.mult at this
    split_ifs at this <;> omega
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : FD.cc (-ξ₀) = -(-ξ₀) := by
    unfold FD.cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨U, hU, -⟩ := GlobalTheory.FrameUnif.exists_unf_hasPrinc E H Dw l Xo c σ (Dw.p + Dw.q) ξ₀ Gm φ hD hσ hcc him hφ
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨C, hC⟩ := exists_const hU W hf h1
  obtain ⟨k, P, hP, hy, hv⟩ := hC y
  obtain ⟨k', P', hP', hy', hv'⟩ := hC y'
  have hg : g = W.g := Fin.equiv_iff_eq.1 ⟨e.trans W.e.symm⟩
  obtain ⟨ga, hE, hM⟩ := exists_isometry A hs hx hg W.F _ hP hy
  obtain ⟨ga', hE', hM'⟩ := exists_isometry A' hs hx' hg W.F _ hP' hy'
  obtain rfl : k = k' := by
    refine W.ik_injective hσ hU hD (index_eq_of_marked_isometry W.F hD hσ
      ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw W.g W.e) _ _ (ga.symm.trans ga') (fun a b => ?_) (fun a ha => ?_)
      fun a => ⟨ga' (ga.symm (W.F.t _ a)) - W.F.t _ a, by rw [hA, one_smul, add_sub_cancel]; rfl⟩)
    · have h := hE (ga.symm a) (ga.symm b)
      rw [ga.apply_symm_apply, ga.apply_symm_apply, ← hE'] at h
      exact_mod_cast h.symm
    · obtain ⟨u, hu⟩ := hM mk hm hk a ha
      obtain ⟨u', hu'⟩ := hM' mk hm hk' a ha
      refine ⟨u' - ga' (ga.symm u), ?_⟩
      rw [eq_sub_of_add_eq hu.symm, map_sub, map_nsmul, LinearEquiv.trans_apply, ga.symm_apply_apply, hu', smul_sub,
        add_sub_assoc]
      rfl
  exact hv.trans hv'.symm

theorem exists_cvIs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra d.c₂.F ℂ], GoodEmb d.c₂ (algebraMap d.c₂.F ℂ) → d.l₂.A = 1 → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → UnitC d → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (L : Lt E r), 1 ≤ r → IsSympl X bas → SelfD X L → ∃ cv : (Dw.La →ₗ[𝓞 E] (Fin r → E)) → ℂ, (∀ mk, ‖cv mk‖ = 1) ∧ CvIs d X bas idx e L cv := by
  intro E _ _ _ H Dw l Xo c n d inst hσ hA hf hu r g X bas idx e L hr hs _
  obtain ⟨σ, rfl⟩ : ∃ σ : d.c₂.F →+* ℂ, inst = σ.toAlgebra :=
    ⟨algebraMap d.c₂.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra d.c₂.F ℂ := σ.toAlgebra
  have key : ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ x ∈ X.dom, ∀ (y : FrPt d.Xo₂ d.c₂ ℂ)
      (A : AnFib X bas idx e x L y), IsMark d.l₂ L mk → A.Marked mk → evR d.Xo₂ d.c₂ d.cδ y = v := fun mk => by
    by_cases h : ∃ x ∈ X.dom, ∃ (y : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y), A.Marked mk
    · obtain ⟨x', hx', y', A', hk'⟩ := h
      exact ⟨_, hu _ y', fun x hx y A hm hk =>
        evR_eq_of_marked σ hσ hA hf (hu _) hr hs hm.mem x hx x' hx' y y' A A' hk hk'⟩
    · exact ⟨1, norm_one, fun x hx y A _ hk => absurd ⟨x, hx, y, A, hk⟩ h⟩
  choose cv h1 h2 using key
  exact ⟨cv, h1, fun x hx y A mk => h2 mk x hx y A⟩

end GlobalTheory.ClsVal
end
