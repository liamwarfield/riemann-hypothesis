module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Formalism.MonomialMeanResidues.FilteredDegree
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightIdentity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginDegreeCount
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalMultihomogQuotientExists

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginDegreeCountAltBis
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemOpenOfForms
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.FormsVal

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

def valRing (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z) :
    Subring (Ω × ℂ) :=
  ((genMap ξ ⟨centre z, h⟩).prod (Scheme.stalkClosedPointTo z).hom).range

theorem mem_valRing_of_valAt (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : ValAt ξ z a r) :
    (a, r) ∈ valRing ξ z h := by
  obtain ⟨h', s, hs, hr⟩ := hv
  exact ⟨s, Prod.ext hs hr⟩

theorem aeval_mem_valRing (h : genPt ξ ⤳ centre z) {σ : Type} {a : σ → Ω} {r : σ → ℂ}
    (hv : ∀ i, (a i, r i) ∈ valRing ξ z h) (f : MvPolynomial σ ℤ) :
    (aeval a f, aeval r f) ∈ valRing ξ z h := by
  induction f using MvPolynomial.induction_on with
  | C n =>
    have e : (aeval a (C n : MvPolynomial σ ℤ), aeval r (C n : MvPolynomial σ ℤ)) = ((n : Ω × ℂ)) :=
      Prod.ext (by simp) (by simp)
    rw [e]
    exact intCast_mem _ n
  | add f g hf hg =>
    have := add_mem hf hg
    simpa using this
  | mul_X f i hf =>
    have := mul_mem hf (hv i)
    simpa using this

theorem unitAt_of_mem_valRing (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : (a, r) ∈ valRing ξ z h) (hr : r ≠ 0) :
    unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨s, hs⟩ := hv
  have hs1 : genMap ξ ⟨centre z, h⟩ s = a := congrArg Prod.fst hs
  have hs2 : (Scheme.stalkClosedPointTo z).hom s = r := congrArg Prod.snd hs
  have hl : IsLocalHom (Scheme.stalkClosedPointTo z).hom := Scheme.isLocalHom_stalkClosedPointTo z
  have hu : IsUnit s := hl.map_nonunit s ((congrArg IsUnit hs2).mpr hr.isUnit)
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  have h1 : a * genMap ξ ⟨centre z, h⟩ t = 1 := by rw [← hs1, ← map_mul, ht, map_one]
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨ha0, ⟨s, hs1⟩, ⟨t, eq_inv_of_mul_eq_one_right h1⟩⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}
  {w : (Σ k, ι k) → ℂ}

theorem ratio_mem_valRing (h : genPt ξ ⤳ centre z) (hc : CoordsAt ξ y z w) (c : (k : K) → ι k)
    (hu : ∀ k, w ⟨k, c k⟩ ≠ 0) (p : Σ k, ι k) :
    ((y ⟨p.1, c p.1⟩)⁻¹ * y p, (w ⟨p.1, c p.1⟩)⁻¹ * w p) ∈ valRing ξ z h := by
  obtain ⟨k, i⟩ := p
  obtain ⟨-, hr⟩ := hc.2 k (c k) (hu k).isUnit
  obtain ⟨r, hv, hw⟩ := hr i
  have e1 : (w ⟨k, c k⟩)⁻¹ * w ⟨k, i⟩ = r := by rw [hw]; field_simp [hu k]
  have e2 : (y ⟨k, c k⟩)⁻¹ * y ⟨k, i⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by rw [div_eq_mul_inv, mul_comm]
  show ((y ⟨k, c k⟩)⁻¹ * y ⟨k, i⟩, (w ⟨k, c k⟩)⁻¹ * w ⟨k, i⟩) ∈ _
  rw [e1, e2]
  exact mem_valRing_of_valAt h hv

theorem unitAt_form (h : genPt ξ ⤳ centre z) (hc : CoordsAt ξ y z w) (c : (k : K) → ι k)
    (hu : ∀ k, w ⟨k, c k⟩ ≠ 0) {G : MRing ι} {d : K → ℕ} (hG : IsMultiHomog G d) (hw : aeval w G ≠ 0) :
    unitAt ξ ⟨centre z, h⟩ (aeval y G / ∏ k, y ⟨k, c k⟩ ^ d k) := by
  have hm := aeval_mem_valRing h (ratio_mem_valRing h hc c hu) G
  rw [aeval_scale hG (fun k => (y ⟨k, c k⟩)⁻¹) y, aeval_scale hG (fun k => (w ⟨k, c k⟩)⁻¹) w] at hm
  have e : (∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k) * aeval y G = aeval y G / ∏ k, y ⟨k, c k⟩ ^ d k := by
    simp only [inv_pow, Finset.prod_inv_distrib]
    rw [div_eq_mul_inv, mul_comm]
  rw [e] at hm
  refine unitAt_of_mem_valRing h hm (mul_ne_zero ?_ hw)
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hu k))

end Val

section Field

variable {Ω : Type} [Field Ω]

theorem zpow_sum_eq_prod_zpow {R : Type} (Y : Ω) (hY : Y ≠ 0) (s : Finset R) (f : R → ℤ) :
    Y ^ (∑ r ∈ s, f r) = ∏ r ∈ s, Y ^ f r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.prod_insert hr, zpow_add₀ hY, ih]

theorem mono_identity {K R : Type} [Fintype K] [Fintype R] (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) (e : R → Ω)
    (he : ∀ r, e r ≠ 0) (x : R → K → ℤ) (Aa : K → ℤ) (n : R → ℤ) (q : ℕ) (k₀ : K)
    (hA : Aa k₀ = 1 ∧ ∀ k, k ≠ k₀ → Aa k = 0) (a : K → ℤ)
    (ha : ∀ k, a k = -(q : ℤ) * Aa k + ∑ r, -n r * x r k) :
    (∏ k, Y k ^ a k)⁻¹ * ∏ r, e r ^ n r = Y k₀ ^ q / ∏ r, ((∏ k, Y k ^ x r k) • e r) ^ (-n r) := by
  classical
  have h1 : ∏ k, Y k ^ Aa k = Y k₀ := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [hA.2 k hk, zpow_zero]) (by simp), hA.1, zpow_one]
  have h2 : ∏ k, Y k ^ a k = (Y k₀ ^ q)⁻¹ * ∏ r, (∏ k, Y k ^ x r k) ^ (-n r) := by
    have e1 : ∀ k, Y k ^ a k = (Y k ^ Aa k) ^ (-(q : ℤ)) * ∏ r, (Y k ^ x r k) ^ (-n r) := fun k => by
      rw [ha k, zpow_add₀ (hY k), zpow_sum_eq_prod_zpow _ (hY k), ← zpow_mul, mul_comm (Aa k)]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [← zpow_mul, mul_comm (x r k)]
    simp only [e1, Finset.prod_mul_distrib]
    rw [Finset.prod_comm]
    congr 1
    · rw [Finset.prod_zpow, h1, zpow_neg, zpow_natCast]
    · refine Finset.prod_congr rfl fun r _ => ?_
      rw [Finset.prod_zpow]
  have h3 : ∏ r, ((∏ k, Y k ^ x r k) • e r) ^ (-n r) =
      (∏ r, (∏ k, Y k ^ x r k) ^ (-n r)) * (∏ r, e r ^ n r)⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [smul_eq_mul, mul_zpow, zpow_neg (e r)]
  have h4 : ∏ r, (∏ k, Y k ^ x r k) ^ (-n r) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hY k))
  have h5 : ∏ r, e r ^ n r ≠ 0 := Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (he r)
  have h6 : Y k₀ ^ q ≠ 0 := pow_ne_zero _ (hY k₀)
  rw [h2, h3]
  field_simp

end Field

theorem mem_open_of_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 → ∀ (x : Or.Re.R.X) (dg dh : RM.K → ℕ) (G Hf : MRing RM.ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + (combLine (RM.line 1) n₀).a k) → aeval RM.y G = ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * aeval RM.y Hf → aeval (Or.Re.R.lift x x) G ≠ 0 → aeval (Or.Re.R.lift x x) Hf ≠ 0 → Or.Re.π x ∈ Sys.open' := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or n₀ N₀ hn hnone hε x dg dh G Hf hG hH hdeg hy hwG hwH
  classical
  have hmem : Or.Re.R.lift x x ∈ mcPts (mCoordIdeal RM.y) := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  obtain ⟨z, hz, hc⟩ := (mem_mcPts_iff_exists_coordsAt _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie _).1 hmem
  refine (Or.interior x z hc).1 ?_
  by_contra hnab
  choose b hb using hc.1
  have hbw : ∀ k, Or.Re.R.lift x x ⟨k, b k⟩ ≠ 0 := fun k => (hb k).ne_zero
  let p : Cpt Or.𝔐.ξ := ⟨centre z, hz⟩
  have hyc : ∀ k, RM.y ⟨k, b k⟩ ≠ 0 := fun k => (hc.2 k (b k) (hb k)).1
  have hrat : ∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, b k⟩ ∈ regAt Or.𝔐.ξ p := by
    intro k i
    obtain ⟨r, ⟨h', s, hs, -⟩, -⟩ := (hc.2 k (b k) (hb k)).2 i
    exact ⟨s, hs⟩
  have hch : InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) b p := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hyc k, fun c' => ?_⟩
    show (∏ k, RM.y ⟨k, c' k⟩) / ∏ k, RM.y ⟨k, b k⟩ ∈ _
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => hrat k (c' k)
  have he0 : ∀ r, Or.e r ≠ 0 := fun r => (Or.lines r).1
  have hgen : ∀ r, (Or.Fl.rootLat r).IsGenAt p ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) := fun r =>
    ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)) (he0 r),
      (Or.lines r).2 _ trivial b hch⟩
  have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (fun r => -Fx.n r) hgen
  have ya : Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) = RM.y ⟨Or.k₀, b Or.k₀⟩ := by
    rw [← Or.y_eq, Equiv.apply_symm_apply]
  have hch' : InChart Or.𝔐.ξ (fun i' => Or.g (Fx.yf i')) (Or.ix.symm (b Or.k₀)) p := by
    refine ⟨?_, fun j => ?_⟩
    · show Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ≠ 0
      rw [ya]; exact hyc _
    · show Or.g (Fx.yf j) / Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ∈ _
      rw [ya, ← Or.y_eq]
      exact hrat _ _
  have hnat : ∀ m : ℕ, m ≠ 0 → unitAt Or.𝔐.ξ p (m : RM.Ω) := by
    intro m hm
    have e : (((m : RM.Ω), (m : ℂ)) : RM.Ω × ℂ) = ((m : RM.Ω × ℂ)) := Prod.ext (by simp) (by simp)
    have h2 : (((m : RM.Ω), (m : ℂ)) : RM.Ω × ℂ) ∈ valRing Or.𝔐.ξ z hz := by
      rw [e]
      exact natCast_mem _ m
    exact unitAt_of_mem_valRing hz h2 (Nat.cast_ne_zero.2 hm)
  have hp0 : ∀ r : ℕ, r.Prime → ¬ InFibre Or.𝔐.ξ r p := fun r hr hf => hf (hnat r hr.ne_zero)
  obtain ⟨-, hnu⟩ := Or.eff p hp0 _ _ hch' ht
  have hN₀ : N₀ ≠ 0 := by
    rintro rfl
    exact hε (by simp)
  have hA := unitAt_form hz hc b hbw hG hwG
  have hB := unitAt_form hz hc b hbw hH hwH
  have hAB : unitAt Or.𝔐.ξ p ((aeval RM.y G / ∏ k, RM.y ⟨k, b k⟩ ^ dg k) /
      (aeval RM.y Hf / ∏ k, RM.y ⟨k, b k⟩ ^ dh k)) :=
    ⟨div_ne_zero hA.1 hB.1, by rw [div_eq_mul_inv]; exact mul_mem hA.2.1 hB.2.2,
      by rw [inv_div, div_eq_mul_inv]; exact mul_mem hB.2.1 hA.2.2⟩
  have hid := mono_identity (fun k => RM.y ⟨k, b k⟩) hyc Or.e he0 RM.xdeg RM.A.a Fx.n Fx.q' Or.k₀ Or.A_deg
    (combLine (RM.line 1) n₀).a (fun k => by
      simp [combLine, Finset.sum_apply, Fintype.sum_option, RootModel.line, RM.x_deg, hn, hnone])
  have hHf0 : aeval RM.y Hf ≠ 0 := fun h0 => hB.1 (by rw [h0, zero_div])
  have hMh : ∏ k, RM.y ⟨k, b k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
  have hPa : ∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
  have hMg : ∏ k, RM.y ⟨k, b k⟩ ^ dg k =
      (∏ k, RM.y ⟨k, b k⟩ ^ dh k) * ∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, hdeg k, zpow_add₀ (hyc k), zpow_natCast]
  have hfin : (aeval RM.y G / ∏ k, RM.y ⟨k, b k⟩ ^ dg k) / (aeval RM.y Hf / ∏ k, RM.y ⟨k, b k⟩ ^ dh k) =
      (Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ^ Fx.q' /
        ∏ r, ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) * (N₀ : RM.Ω) := by
    have hid' : (∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k)⁻¹ * ∏ r, Or.e r ^ Fx.n r =
        RM.y ⟨Or.k₀, b Or.k₀⟩ ^ Fx.q' / ∏ r, ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r) := hid
    rw [hy, hMg, ya, mul_div_assoc (Or.g Fx.sE), ← hid']
    field_simp
  rw [hfin] at hAB
  exact hnu hnab (GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.unitAt_of_mul hAB (hnat N₀ hN₀))

end GlobalTheory.CompanionTheory.Ar.Small.FormsVal
end
end

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_degree_count_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 → ∀ (x : Or.Re.R.X) (dg dh : RM.K → ℕ) (G Hf : MRing RM.ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + (combLine (RM.line 1) n₀).a k) → aeval RM.y G = ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * aeval RM.y Hf → aeval (Or.Re.R.lift x x) G ≠ 0 → aeval (Or.Re.R.lift x x) Hf ≠ 0 → Or.Re.π x ∈ Sys.open' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.FormsVal.mem_open_of_forms | exact GlobalTheory.CompanionTheory.Ar.Small.FormsVal.mem_open_of_forms | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.FormsVal.mem_open_of_forms <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginMultiplicityBound
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginMultiplicityBound
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

theorem combLine_ref_a_eq_line_a : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)) (n₀ m : Option (RootIx D) → ℤ), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → (∀ r : RootIx D, (m (some r) : ℝ) = (Fx.kA * Fx.q' : ℕ) * fundCo (nu r.1) r.2) → m none = -(Fx.q' : ℤ) → (combLine Or.Re.ref m).a = (combLine (RM.line 1) n₀).a := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or nu n₀ m hn hn₀ hn₀' hm hm'
  funext k₁
  apply Int.cast_injective (α := ℝ)
  have hL : ∀ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) =
      -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (fundCo (nu r.1) r.2 * ∑ k ∈ Finset.Iic r.2, (RM.xdeg (r.1, k) k₁ : ℝ))) := by
    rintro ⟨τ, i⟩
    rw [Or.fund_deg τ i]
    push_cast
    rw [hm (τ, i)]
    simp only [Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum, Nat.cast_mul]
    ring
  have hR : ∀ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ) =
      -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (nu r.1 r.2 * (RM.xdeg r k₁ : ℝ))) := by
    intro r
    have h1 : (RM.line 1 (some r)).a = RM.xdeg r := RM.x_deg 1 r
    rw [h1, hn₀ r]
    push_cast
    have := hn r
    push_cast at this
    rw [this]
    ring
  have hsum : ∑ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) =
      ∑ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ) := by
    simp only [hL, hR, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 2
    exact Finset.sum_congr rfl fun τ _ => sum_fundCo_mul_sum_Iic (nu τ) fun k => (RM.xdeg (τ, k) k₁ : ℝ)
  have hnone : (Or.Re.ref none).a k₁ = (RM.line 1 none).a k₁ := by
    rw [Or.ref_none.1]
    rfl
  simp only [combLine, Fintype.sum_option, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hm', hn₀', hnone]
  push_cast at hsum ⊢
  rw [hsum]

end GlobalTheory.CompanionTheory.Ar.Small.Fund
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginMultiplicityBoundStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_multiplicity_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)) (n₀ m : Option (RootIx D) → ℤ), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → (∀ r : RootIx D, (m (some r) : ℝ) = (Fx.kA * Fx.q' : ℕ) * fundCo (nu r.1) r.2) → m none = -(Fx.q' : ℤ) → (combLine Or.Re.ref m).a = (combLine (RM.line 1) n₀).a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Fund.combLine_ref_a_eq_line_a | exact GlobalTheory.CompanionTheory.Ar.Small.Fund.combLine_ref_a_eq_line_a | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Fund.combLine_ref_a_eq_line_a <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightComparisonShift
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightComparisonShift
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit

theorem log_h_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (ℓ : HermLine ι) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (ℓ.h (fun p => c p.1 * z p)) = Real.log (ℓ.h z) + ∑ k, (ℓ.a k : ℝ) * Real.log ‖c k‖ := by
  have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [ℓ.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hn k)) (ℓ.pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (hn k)), add_comm]
  simp only [Real.log_zpow]

theorem coef_add_smul {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (lam nu : Wt Ψ N) (s : ℝ)
    (j : Option (Ψ × Fin N)) : R.coef (lam - s • nu) s j + s * R.coef nu (-1) j = R.coef lam 0 j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem line_a {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    (R.line t j).a = (R.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp only [RootModel.line, R.x_deg]

theorem torus_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' n₀ : Option (RootIx D) → ℤ) (q₀ : ℕ) (s t : ℝ) (cc : RM.K → ℂ) (z : (Σ k, RM.ι k) → ℂ) (v : ℂ), 0 < q₀ → (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → (∀ j, (n₀ j : ℝ) = q₀ * RM.coef nu (-1) j) → (∀ k, cc k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → v ≠ 0 → s / q₀ * Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ + RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) - Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) = s / q₀ * Real.log ‖v‖ + RM.weight t (lam - s • nu) s z - Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or lam nu n' n₀ q₀ s t cc z v hq hn' hn₀ hc hz hv
  have hq0 : (q₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hn : ∀ k, ‖cc k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  have hzc : ∀ k, ∃ i, (fun p : (Σ k, RM.ι k) => cc p.1 * z p) ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, mul_ne_zero (hc k) hi⟩

  have ha : ∀ k, (((combLine (RM.line 1) n₀).a k : ℤ) : ℝ) = ∑ j, (n₀ j : ℝ) * ((RM.line 1 j).a k : ℝ) := by
    intro k
    simp only [GlobalTheory.CompanionTheory.Ar.Top.combLine, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rfl

  have h1 : Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ =
      Real.log ‖v‖ + ∑ k, ((combLine (RM.line 1) n₀).a k : ℝ) * Real.log ‖cc k‖ := by
    rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.mpr hv)
      (Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hc k))),
      Real.log_prod (fun k _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hc k)))]
    simp only [norm_zpow, Real.log_zpow]

  have h2 : RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) =
      RM.weight t (lam - s • nu) s z +
        ∑ k, (∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ)) * Real.log ‖cc k‖ := by
    simp only [RootModel.weight, log_h_scale _ cc z hc hz, line_a RM t, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hlog : ∀ w : (Σ k, RM.ι k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
      Real.log (∏ r, (Or.sing r).h w ^ n' (some r)) = ∑ r, (n' (some r) : ℝ) * Real.log ((Or.sing r).h w) := by
    intro w hw
    rw [Real.log_prod (fun r _ => (zpow_pos ((Or.sing r).pos w hw) _).ne')]
    simp only [Real.log_zpow]
  have h3 : Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) =
      Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) +
        ∑ k, (∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ)) * Real.log ‖cc k‖ := by
    rw [hlog _ hzc, hlog z hz]
    simp only [log_h_scale _ cc z hc hz, Or.sing_deg, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hn'none : (n' none : ℝ) = 0 := by
    rw [hn' none]
    simp [RootModel.coef]
  have h4 : ∀ k, s / q₀ * ((combLine (RM.line 1) n₀).a k : ℝ) +
      ∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ) =
      ∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ) := by
    intro k
    have e1 : ∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ) = ∑ j, (n' j : ℝ) * ((RM.line 1 j).a k : ℝ) := by
      rw [Fintype.sum_option, hn'none, zero_mul, zero_add]
      exact Finset.sum_congr rfl fun r _ => by simp only [RootModel.line, RM.x_deg]
    rw [e1, ha, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hn₀ j, hn' j, ← coef_add_smul RM lam nu s j]
    field_simp
    ring
  rw [h1, h2, h3]
  have h5 : s / q₀ * ∑ k, ((combLine (RM.line 1) n₀).a k : ℝ) * Real.log ‖cc k‖ +
      ∑ k, (∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ)) * Real.log ‖cc k‖ =
      ∑ k, (∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ)) * Real.log ‖cc k‖ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← h4 k]
    ring
  linear_combination h5

end GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightComparisonShiftStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_weight_comparison_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' n₀ : Option (RootIx D) → ℤ) (q₀ : ℕ) (s t : ℝ) (cc : RM.K → ℂ) (z : (Σ k, RM.ι k) → ℂ) (v : ℂ), 0 < q₀ → (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → (∀ j, (n₀ j : ℝ) = q₀ * RM.coef nu (-1) j) → (∀ k, cc k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → v ≠ 0 → s / q₀ * Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ + RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) - Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) = s / q₀ * Real.log ‖v‖ + RM.weight t (lam - s • nu) s z - Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit.torus_invariant | exact GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit.torus_invariant | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit.torus_invariant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginWeightFree
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Free

theorem rpow_third_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.exp (-(s ^ 2)⁻¹) ^ ((1 : ℝ) / 3) ≤ 3 * s := by
  rw [← Real.exp_mul]
  have hx : 0 < (s ^ 2)⁻¹ / 3 := by positivity
  have h1 : -(s ^ 2)⁻¹ * ((1 : ℝ) / 3) = -((s ^ 2)⁻¹ / 3) := by ring
  rw [h1, Real.exp_neg]
  have h2 : (s ^ 2)⁻¹ / 3 ≤ Real.exp ((s ^ 2)⁻¹ / 3) := by
    linarith [Real.add_one_le_exp ((s ^ 2)⁻¹ / 3)]
  have h3 : (Real.exp ((s ^ 2)⁻¹ / 3))⁻¹ ≤ ((s ^ 2)⁻¹ / 3)⁻¹ := inv_anti₀ hx h2
  have h4 : ((s ^ 2)⁻¹ / 3)⁻¹ = 3 * s ^ 2 := by
    field_simp
  rw [h4] at h3
  nlinarith

theorem epsT_scale (C : ℝ) {s : ℝ} (hs : 0 < s) :
    epsT C (Real.exp (-(s ^ 2)⁻¹)) = C * (-2 * Real.log s) * s ^ 2 := by
  unfold epsT
  have h1 : Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) = (s ^ 2)⁻¹ := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  rw [h1, Real.log_inv, Real.log_pow]
  push_cast
  field_simp

theorem exists_mul_log_le (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ r : ℝ, 0 < r → M * Real.log r ≤ ε / 2 * r + K := by
  set η : ℝ := ε / (2 * (M + 1)) with hη
  have hη0 : 0 < η := by positivity
  refine ⟨M * (-Real.log η), fun r hr => ?_⟩
  have h1 : Real.log (η * r) ≤ η * r - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_mul hη0.ne' hr.ne'] at h1
  have h2 : Real.log r ≤ η * r - Real.log η := by linarith
  have h3 : M * η ≤ ε / 2 := by
    rw [hη]
    have : M * (ε / (2 * (M + 1))) = ε / 2 * (M / (M + 1)) := by
      field_simp
    rw [this]
    have h4 : M / (M + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left h2 hM
  have h6 := mul_le_mul_of_nonneg_right h3 hr.le
  nlinarith

theorem exists_eps_small (A C δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ s, 0 < s → s ≤ s₁ → A * |epsT C (Real.exp (-(s ^ 2)⁻¹))| ≤ δ * s := by
  set B : ℝ := 2 * A * |C| with hB
  have hB0 : 0 ≤ B := by positivity
  have hη : 0 < δ / (B + 1) := by positivity
  obtain ⟨d, hd, hd'⟩ := Metric.continuous_iff.1 Real.continuous_mul_log 0 _ hη
  refine ⟨d / 2, by positivity, fun s hs hsd => ?_⟩
  have h1 := hd' s (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs]
    linarith)
  rw [Real.dist_eq, zero_mul, sub_zero] at h1
  rw [epsT_scale C hs]
  have h2 : |C * (-2 * Real.log s) * s ^ 2| = 2 * |C| * |s * Real.log s| * s := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos hs, abs_of_pos (by positivity : 0 < s ^ 2)]
    ring
  rw [h2]
  have h3 : B * |s * Real.log s| ≤ δ := by
    have h4 : (B + 1) * |s * Real.log s| ≤ δ := by
      have := (lt_div_iff₀' (by positivity : 0 < B + 1)).1 h1
      exact this.le
    nlinarith [abs_nonneg (s * Real.log s)]
  have h5 : A * (2 * |C| * |s * Real.log s| * s) = (B * |s * Real.log s|) * s := by
    rw [hB]; ring
  rw [h5]
  exact mul_le_mul_of_nonneg_right h3 hs.le

theorem scale_le {t₀ s : ℝ} (ht₀ : 0 < t₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hs2 : s ≤ 1 / (|Real.log t₀| + 1)) : Real.exp (-(s ^ 2)⁻¹) ≤ t₀ := by
  have h2 : s ^ 2 ≤ 1 / (|Real.log t₀| + 1) := by nlinarith
  have h3 : 0 < s ^ 2 := by positivity
  have h4 : |Real.log t₀| + 1 ≤ (s ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) h3]
    simpa using h2
  rw [← Real.exp_log ht₀]
  refine Real.exp_le_exp.2 ?_
  linarith [neg_abs_le (Real.log t₀), le_abs_self (Real.log t₀)]

variable {e : ℕ} {σ : Type}

theorem exp_one_le_rW (S : PB.AnSys e σ) (y : S.X) : Real.exp 1 ≤ rW S.L S.s y := by
  have := S.norm_le y
  unfold rW
  linarith

theorem one_le_log_rW (S : PB.AnSys e σ) (y : S.X) : (1 : ℝ) ≤ Real.log (rW S.L S.s y) :=
  (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) (exp_one_le_rW S y))).2 (exp_one_le_rW S y)

theorem abs_ph_le (S : PB.AnSys e σ) (a : σ) {y : S.X} (hy : y ∈ S.open') :
    |S.ph a y| ≤ |S.C₅| * Real.log (rW S.L S.s y) := by
  obtain ⟨h1, h2⟩ := (S.sing a).2.2.2 y hy
  have hl : (1 : ℝ) ≤ Real.log (rW S.L S.s y) := one_le_log_rW S y
  have hc : S.C₅ ≤ |S.C₅| := le_abs_self _
  have hc' : -S.C₅ ≤ |S.C₅| := neg_le_abs _
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg S.C₅]

theorem phT_sub_ph_bound (S : PB.AnSys e σ) (a : σ) {t : ℝ} (ht : 0 < t) (ht' : t ≤ S.t₀)
    {y : S.X} (hy : y ∈ S.open') :
    0 ≤ S.phT a t y - S.ph a y ∧
      S.phT a t y - S.ph a y ≤ t ^ ((1 : ℝ) / 3) + |epsT S.C t| * rW S.L S.s y := by
  obtain ⟨-, -, h3, -, -, -, h7, -⟩ := (S.reg a).2.2 t ht ht'
  have hr : 0 ≤ rW S.L S.s y := (Real.exp_pos 1).le.trans (exp_one_le_rW S y)
  refine ⟨sub_nonneg.2 (h3 y hy), ?_⟩
  have h8 := h7 y hy
  have h9 : epsT S.C t * rW S.L S.s y ≤ |epsT S.C t| * rW S.L S.s y :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hr
  linarith

theorem regular_bound [Fintype σ] (S : PB.AnSys e σ) (n : σ → ℝ) (lE : S.X → ℝ) (ε CE abelian₂ : ℝ) (hε : 0 < ε)
    (ht₀ : 0 < S.t₀) (hE : ∀ y ∈ S.open', lE y ≤ -ε * rW S.L S.s y + CE) :
    ∃ C' s₀ : ℝ, 0 < s₀ ∧ ∀ s, 0 < s → s ≤ s₀ → ∀ c : σ → ℝ, ∑ a, |c a| ≤ abelian₂ → ∀ y ∈ S.open',
      s * lE y + ∑ a, c a * S.phT a (Real.exp (-(s ^ 2)⁻¹)) y - ∑ a, (c a + s * n a) * S.ph a y ≤ C' * s := by
  set M : ℝ := (∑ a, |n a|) * |S.C₅| with hM
  have hM0 : 0 ≤ M := mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)
  obtain ⟨K, hK⟩ := exists_mul_log_le M ε hM0 hε
  obtain ⟨s₁, hs₁, hsm⟩ := exists_eps_small |abelian₂| S.C (ε / 2) (abs_nonneg _) (by positivity)
  refine ⟨CE + K + 3 * |abelian₂|, min s₁ (min 1 (1 / (|Real.log S.t₀| + 1))),
    lt_min hs₁ (lt_min one_pos (by positivity)), ?_⟩
  intro s hs hsle c hc y hy
  have hsA : s ≤ s₁ := hsle.trans (min_le_left _ _)
  have hsB : s ≤ 1 := hsle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsC : s ≤ 1 / (|Real.log S.t₀| + 1) := hsle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht : Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ := scale_le ht₀ hs hsB hsC
  have ht0 : 0 < Real.exp (-(s ^ 2)⁻¹) := Real.exp_pos _
  set t := Real.exp (-(s ^ 2)⁻¹) with htdef
  set r := rW S.L S.s y with hr
  have hr0 : 0 < r := lt_of_lt_of_le (Real.exp_pos 1) (exp_one_le_rW S y)
  set Er : ℝ := t ^ ((1 : ℝ) / 3) + |epsT S.C t| * r with hEr
  have hEr0 : 0 ≤ Er := by positivity

  have h1 : ∑ a, c a * (S.phT a t y - S.ph a y) ≤ |abelian₂| * Er := by
    have h2 : ∑ a, c a * (S.phT a t y - S.ph a y) ≤ ∑ a, |c a| * Er := by
      refine Finset.sum_le_sum fun a _ => ?_
      obtain ⟨h3, h4⟩ := phT_sub_ph_bound S a ht0 ht hy
      calc c a * (S.phT a t y - S.ph a y) ≤ |c a| * (S.phT a t y - S.ph a y) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h3
        _ ≤ |c a| * Er := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
    rw [← Finset.sum_mul] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right (hc.trans (le_abs_self _)) hEr0)

  have h5 : -∑ a, n a * S.ph a y ≤ M * Real.log r := by
    rw [← Finset.sum_neg_distrib, hM, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    have h6 := abs_ph_le S a hy
    calc -(n a * S.ph a y) ≤ |n a * S.ph a y| := neg_le_abs _
      _ = |n a| * |S.ph a y| := abs_mul _ _
      _ ≤ |n a| * (|S.C₅| * Real.log r) := mul_le_mul_of_nonneg_left h6 (abs_nonneg _)
      _ = |n a| * |S.C₅| * Real.log r := by ring
  have h7 := hK r hr0
  have h8 := hE y hy
  have h9 : ∑ a, c a * S.phT a t y - ∑ a, (c a + s * n a) * S.ph a y =
      ∑ a, c a * (S.phT a t y - S.ph a y) - s * ∑ a, n a * S.ph a y := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have h10 := rpow_third_le hs hsB
  have h11 := hsm s hs hsA
  have h12 : |abelian₂| * t ^ ((1 : ℝ) / 3) ≤ |abelian₂| * (3 * s) :=
    mul_le_mul_of_nonneg_left h10 (abs_nonneg _)
  have h13 : |abelian₂| * |epsT S.C t| * r ≤ ε / 2 * s * r := mul_le_mul_of_nonneg_right h11 hr0.le
  have h14 : s * lE y ≤ s * (-ε * r + CE) := mul_le_mul_of_nonneg_left h8 hs.le
  have h15 : s * -∑ a, n a * S.ph a y ≤ s * (ε / 2 * r + K) :=
    mul_le_mul_of_nonneg_left (h5.trans h7) hs.le
  have h16 : |abelian₂| * Er = |abelian₂| * t ^ ((1 : ℝ) / 3) + |abelian₂| * |epsT S.C t| * r := by
    rw [hEr]; ring
  nlinarith

end GlobalTheory.CompanionTheory.Ar.Small.Free

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem root_origin_weight_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' : Option (RootIx D) → ℤ), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → ∃ (q₀ : ℕ) (n₀ : Option (RootIx D) → ℤ) (ε : RM.Ω) (u : MRing RM.ι) (C s₀ : ℝ), 0 < q₀ ∧ (∀ j, (n₀ j : ℝ) = q₀ * RM.coef nu (-1) j) ∧ ε ≠ 0 ∧ ε ∈ chartLatNm RM.y (combLine (RM.line 1) n₀).a 1 ∧ IsFormOff (mCoordIdeal RM.y) u ∧ 0 ≤ C ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z ∈ mcPts (mCoordIdeal RM.y), aeval z u ≠ 0 → ∀ x : ℂ, HasVal RM.y (combLine (RM.line 1) n₀).a ε z x → x ≠ 0 → s / q₀ * Real.log ‖x‖ + RM.weight (scale s) (lam - s • nu) s z ≤ C * s + Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or lam nu n' hn hn'
  obtain ⟨n₀, N₀, hn₀, hN₀, hε0, hεm⟩ := GlobalTheory.T.root_origin_weight_identity E H D l Xo c O β Y S RM Sys Fx Or nu hn
  have hkA : RM.kA = Fx.kA := Or.kA_eq
  have hk0 : 0 < Fx.kA := hkA ▸ RM.kA_pos
  have hq0 : 0 < Fx.kA * Fx.q' := Nat.mul_pos hk0 Fx.q'_pos
  have hq0R : (0 : ℝ) < ((Fx.kA * Fx.q' : ℕ) : ℝ) := by exact_mod_cast hq0
  have hkR : (Fx.kA : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hns : ∀ r, n₀ (some r) = -Fx.n r := by
    intro r
    have h1 := hn₀ (some r)
    have h2 := hn r
    have : (n₀ (some r) : ℝ) = ((-Fx.n r : ℤ) : ℝ) := by
      rw [h1]
      push_cast at h2 ⊢
      rw [h2]
      simp [RootModel.coef]
    exact_mod_cast this
  have hnn : n₀ none = -(Fx.q' : ℤ) := by
    have h1 := hn₀ none
    have : (n₀ none : ℝ) = ((-(Fx.q' : ℤ) : ℤ) : ℝ) := by
      rw [h1]
      simp only [RootModel.coef, hkA]
      push_cast
      field_simp
    exact_mod_cast this
  set ε : RM.Ω := (N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r with hε

  let m : Option (RootIx D) → ℤ := fun o => o.elim (-(Fx.q' : ℤ)) fun r =>
    Fx.n r - if h : (r.2 : ℕ) + 1 < D.p + D.q then Fx.n (r.1, ⟨r.2 + 1, h⟩) else 0
  have hm : ∀ r : RootIx D, (m (some r) : ℝ) = (Fx.kA * Fx.q' : ℕ) * fundCo (nu r.1) r.2 := by
    intro r
    simp only [m, Option.elim, fundCo]
    split_ifs with h
    · push_cast
      have e1 := hn r
      have e2 := hn (r.1, ⟨r.2 + 1, h⟩)
      push_cast at e1 e2
      rw [e1, e2]
      ring
    · have e1 := hn r
      push_cast at e1 ⊢
      rw [e1]
      ring
  have hmn : m none = -(Fx.q' : ℤ) := rfl
  set Eh : HermLine RM.ι := combLine Or.Re.ref m with hEh
  have hEa : Eh.a = (combLine (RM.line 1) n₀).a := GlobalTheory.T.root_origin_multiplicity_bound E H D l Xo c O β Y S RM Sys Fx Or nu n₀ m hn hns hnn hm hmn
  have hEs : IsSmoothHerm Eh := isSmoothHerm_comb Or.Re.ref_smooth m
  have hrep := GlobalTheory.T.root_origin_degree_count E H D l Xo c O β Y S RM Sys Fx Or n₀ N₀ hns hnn hε0
  have hbd := GlobalTheory.T.root_origin_degree_count_alt E H D l Xo c O β Y S RM Sys Fx Or n₀ N₀ hns hnn hε0
  obtain ⟨δ, C₁, hδ, hdec⟩ := GlobalTheory.T.local_multihomog_quotient_exists RM.K RM.ι RM.Ω RM.y Or.Re.J _ Or.Re.R _ Sys Or.Re.π Or.Re.holo Eh hEs ε
    (fun x => by
      obtain ⟨dg, dh, G, Hf, h1, h2, h3, h4, -, h6⟩ := hrep _ (Or.Re.R.mem x x (Or.Re.R.mem_U x))
      exact ⟨dg, dh, G, Hf, h1, h2, by rw [hEa]; exact h3, h4, h6⟩)
    (fun x dg dh G Hf h1 h2 h3 h4 h5 h6 => hbd x dg dh G Hf h1 h2 (by rw [hEa] at h3; exact h3) h4 h5 h6)

  obtain ⟨z₀, hz₀, hz₀J⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts Or.Re.arith Or.Re.R.nondeg
  obtain ⟨dg₁, dh₁, G₁, H₁, hG₁, hH₁, hd₁, hy₁, hy₁', hz₁⟩ := hrep z₀ hz₀
  obtain ⟨T, hT, hJT⟩ := Or.Re.R.homog
  obtain ⟨f, hfT, hfP⟩ : ∃ f ∈ T, f ∉ RM.P := by
    by_contra hc
    push_neg at hc
    exact Or.Re.R.nondeg (hJT ▸ Ideal.span_le.2 hc)
  obtain ⟨df, hf⟩ := hT f hfT
  have hfJ : f ∈ Or.Re.J := hJT ▸ Ideal.subset_span hfT
  have hPprime : (mCoordIdeal RM.y).IsPrime := RingHom.ker_isPrime _
  have hG₁P : G₁ ∉ mCoordIdeal RM.y := fun h => by
    have := aeval_eq_zero_of_mem RM.y h
    rw [hy₁] at this
    exact (mul_ne_zero hε0 hy₁') this
  have hH₁P : H₁ ∉ mCoordIdeal RM.y := fun h => hy₁' (aeval_eq_zero_of_mem RM.y h)
  have hu : IsFormOff (mCoordIdeal RM.y) (f * (G₁ * H₁)) := by
    refine ⟨⟨_, isMultiHomog_mul hf (isMultiHomog_mul hG₁ hH₁)⟩, fun h => ?_⟩
    rcases hPprime.mem_or_mem h with h | h
    · exact hfP h
    · rcases hPprime.mem_or_mem h with h | h
      · exact hG₁P h
      · exact hH₁P h

  let nA : Option (RootIx D) → ℝ := fun o => o.elim 0 fun r => fundCo (nu r.1) r.2
  let lE : Sys.X → ℝ := fun y => -(δ / ((Fx.kA * Fx.q' : ℕ) : ℝ)) * rW Sys.L Sys.s y + C₁ / ((Fx.kA * Fx.q' : ℕ) : ℝ)
  let abelian₂ : ℝ := ∑ r : RootIx D, (|fundCo (lam r.1) r.2| + |fundCo (nu r.1) r.2|)
  have ht₀ : 0 < Sys.t₀ := (Sys.reg none).1
  obtain ⟨C', s₁, hs₁, hA⟩ := Free.regular_bound Sys nA lE (δ / ((Fx.kA * Fx.q' : ℕ) : ℝ)) (C₁ / ((Fx.kA * Fx.q' : ℕ) : ℝ)) abelian₂
    (div_pos hδ hq0R) ht₀ (fun y _ => le_refl _)

  set L₀ := -Real.log Sys.t₀ with hL₀
  refine ⟨Fx.kA * Fx.q', n₀, ε, f * (G₁ * H₁), max C' 0, min s₁ (min 1 (1 / (|L₀| + 1))), hq0, hn₀, hε0, hεm, hu, le_max_right _ _,
    lt_min hs₁ (lt_min one_pos (by positivity)), ?_⟩
  intro s hs hsle z hz huz v hv hv0
  have hsA : s ≤ s₁ := hsle.trans (min_le_left _ _)
  have hsC : s ≤ 1 := hsle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsD : s ≤ 1 / (|L₀| + 1) := hsle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hscale : scale s ≤ Sys.t₀ := by
    have h1 : L₀ ≤ (s ^ 2)⁻¹ := by
      have h2 : s ^ 2 ≤ 1 / (|L₀| + 1) := by nlinarith
      have h3 : 0 < s ^ 2 := by positivity
      have h4 : |L₀| + 1 ≤ (s ^ 2)⁻¹ := by
        rw [le_inv_comm₀ (by positivity) h3]
        simpa using h2
      linarith [le_abs_self L₀]
    unfold scale
    rw [← Real.exp_log ht₀]
    refine Real.exp_le_exp.2 ?_
    linarith

  simp only [map_mul, mul_ne_zero_iff] at huz
  obtain ⟨hfz, hGz, hHz⟩ := huz
  have hzJ : z ∉ mcPts Or.Re.J := fun hh => hfz (by
    have := hh.2 f hfJ
    rw [eval_map] at this
    rw [aeval_def, algebraMap_int_eq]
    exact this)
  obtain ⟨x, cc, hcc, hx⟩ := Or.Re.R.surj z hz hzJ
  have hGx : aeval (Or.Re.R.lift x x) G₁ ≠ (0 : ℂ) := by
    rw [hx, aeval_scale hG₁]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hcc k)) hGz
  have hHx : aeval (Or.Re.R.lift x x) H₁ ≠ (0 : ℂ) := by
    rw [hx, aeval_scale hH₁]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hcc k)) hHz
  have hπ : Or.Re.π x ∈ Sys.open' := hbd x dg₁ dh₁ G₁ H₁ hG₁ hH₁ hd₁ hy₁ hGx hHx
  have hv' : HasVal RM.y Eh.a ε (Or.Re.R.lift x x) (v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k) := by
    rw [hEa, hx]
    exact hasVal_scale cc hcc hv
  have hv'0 : v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k ≠ 0 :=
    mul_ne_zero hv0 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hcc k))
  have hD := hdec x hπ _ hv' hv'0
  have hO := GlobalTheory.T.root_origin_weight_comparison_shift E H D l Xo c O β Y S RM Sys Fx Or lam nu n' n₀ (Fx.kA * Fx.q') s (scale s) cc z v hq0 hn' hn₀ hcc hz.1 hv0
  rw [← hx] at hO
  have hI := GlobalTheory.T.root_origin_weight_comparison E H D l Xo c O β Y S RM Sys Fx Or lam nu n' s x hn' hscale hπ

  let co : Option (RootIx D) → ℝ := fun o => o.elim 0 fun r => fundCo ((lam - s • nu) r.1) r.2
  have hco : ∀ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 = fundCo (lam r.1) r.2 - s * fundCo (nu r.1) r.2 := by
    intro r
    have : (lam - s • nu) r.1 = lam r.1 - s • nu r.1 := rfl
    rw [this, fundCo_sub, fundCo_smul]
  have hLam : ∑ o, |co o| ≤ abelian₂ := by
    rw [Fintype.sum_option]
    simp only [co, Option.elim, abs_zero, zero_add]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [hco]
    have h1 : |s * fundCo (nu r.1) r.2| ≤ |fundCo (nu r.1) r.2| := by
      rw [abs_mul, abs_of_pos hs]
      nlinarith [abs_nonneg (fundCo (nu r.1) r.2)]
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith
  have hAe := hA s hs hsA co hLam _ hπ
  rw [Fintype.sum_option, Fintype.sum_option] at hAe
  simp only [co, nA, Option.elim, zero_mul, mul_zero, add_zero, zero_add] at hAe
  have hlog : Real.log (Eh.h (Or.Re.R.lift x x)) = ∑ r : RootIx D, (m (some r) : ℝ) * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) - Fx.q' * Real.log (RM.A.h (Or.Re.R.lift x x)) := by
    have hwb := (Or.Re.R.mem x x (Or.Re.R.mem_U x)).1
    show Real.log (∏ o, (Or.Re.ref o).h (Or.Re.R.lift x x) ^ m o) = _
    rw [Real.log_prod (fun o _ => zpow_ne_zero _ ((Or.Re.ref o).pos _ hwb).ne'), Fintype.sum_option]
    simp only [Real.log_zpow]
    rw [Or.ref_none.2 _ (Or.Re.R.mem x x (Or.Re.R.mem_U x)), hmn]
    push_cast
    ring
  have hsum : ∑ r : RootIx D, (m (some r) : ℝ) * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) =
      ((Fx.kA * Fx.q' : ℕ) : ℝ) * ∑ r : RootIx D, fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) := by
    simp only [hm, Finset.mul_sum, mul_assoc]
  have hq'R : (Fx.q' : ℝ) ≠ 0 := by exact_mod_cast Fx.q'_pos.ne'
  have hq : s / ((Fx.kA * Fx.q' : ℕ) : ℝ) * Real.log (Eh.h (Or.Re.R.lift x x)) =
      s * ∑ r : RootIx D, fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) -
        s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) := by
    rw [hlog, hsum, hkA]
    push_cast
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ s / ((Fx.kA * Fx.q' : ℕ) : ℝ))
  rw [mul_sub] at hmul
  have hlE : s * lE (Or.Re.π x) = s / ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-δ * rW Sys.L Sys.s (Or.Re.π x) + C₁) := by
    simp only [lE]
    field_simp
  have hsumeq : ∑ r : RootIx D, (fundCo ((lam - s • nu) r.1) r.2 + s * fundCo (nu r.1) r.2) * Sys.ph (some r) (Or.Re.π x) =
      ∑ r : RootIx D, fundCo (lam r.1) r.2 * Sys.ph (some r) (Or.Re.π x) :=
    Finset.sum_congr rfl fun r _ => by rw [hco]; ring
  have hsc : Real.exp (-(s ^ 2)⁻¹) = scale s := rfl
  rw [hsumeq, hsc] at hAe
  have hC : C' * s ≤ max C' 0 * s := mul_le_mul_of_nonneg_right (le_max_left _ _) hs.le
  linarith

end GlobalTheory.CompanionTheory.Ar.Small
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginRootWeightBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem good_origin_root_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b₀ : T.Comp) (lam : Top.Wt (CMType H) (Dw.p + Dw.q)) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = (T.M B b₀).coef lam 0 j) → Top.RegDominant lam → ∃ (q₀ : ℕ) (n₀ : Option (RootIx Dw) → ℤ) (ε : (T.M B b₀).Ω) (u : MRing (T.M B b₀).ι) (C s₀ : ℝ), 0 < q₀ ∧ (∀ j, (n₀ j : ℝ) = q₀ * (T.M B b₀).coef T.nu (-1) j) ∧ ε ≠ 0 ∧ ε ∈ chartLatNm (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a 1 ∧ Small.IsFormOff (mCoordIdeal (T.M B b₀).y) u ∧ 0 ≤ C ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z ∈ mcPts (mCoordIdeal (T.M B b₀).y), MvPolynomial.aeval z u ≠ 0 → ∀ x : ℂ, Small.HasVal (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a ε z x → x ≠ 0 → s / q₀ * Real.log ‖x‖ + (T.M B b₀).weight (Top.scale s) (lam - s • T.nu) s z ≤ C * s + Real.log (∏ r, ((o.toTowerOrigin.Or B b₀).sing r).h z ^ n' (some r)) := by
  intro E _ _ _ H Dw l Xo c _ Y T o B b₀ lam n' hn' _
  exact root_origin_weight_free E H Dw l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y (o.toTowerOrigin.S B) (T.M B b₀)
    (o.toTowerOrigin.Sys b₀) (o.toTowerOrigin.Fx b₀) (o.toTowerOrigin.Or B b₀) lam T.nu n'
    (o.toTowerOrigin.nu_eq b₀) hn'

end GlobalTheory.CompanionTheory.Ar.Small
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginRootWeightBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_root_weight_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b₀ : T.Comp) (lam : Top.Wt (CMType H) (Dw.p + Dw.q)) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = (T.M B b₀).coef lam 0 j) → Top.RegDominant lam → ∃ (q₀ : ℕ) (n₀ : Option (RootIx Dw) → ℤ) (ε : (T.M B b₀).Ω) (u : MRing (T.M B b₀).ι) (C s₀ : ℝ), 0 < q₀ ∧ (∀ j, (n₀ j : ℝ) = q₀ * (T.M B b₀).coef T.nu (-1) j) ∧ ε ≠ 0 ∧ ε ∈ chartLatNm (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a 1 ∧ Small.IsFormOff (mCoordIdeal (T.M B b₀).y) u ∧ 0 ≤ C ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z ∈ mcPts (mCoordIdeal (T.M B b₀).y), MvPolynomial.aeval z u ≠ 0 → ∀ x : ℂ, Small.HasVal (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a ε z x → x ≠ 0 → s / q₀ * Real.log ‖x‖ + (T.M B b₀).weight (Top.scale s) (lam - s • T.nu) s z ≤ C * s + Real.log (∏ r, ((o.toTowerOrigin.Or B b₀).sing r).h z ^ n' (some r)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.good_origin_root_coefficients | exact GlobalTheory.CompanionTheory.Ar.Small.good_origin_root_coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.good_origin_root_coefficients <;> assumption)
end
