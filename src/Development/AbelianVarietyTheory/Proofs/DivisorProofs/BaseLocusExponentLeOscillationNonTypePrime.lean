module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthUnitSizeBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolynomialLocalDepthBetween
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThRuleLower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueGeLocalDepthPrimeToP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueGeLocalDepthPrimeToP
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.TermLoc

theorem harmonic_value_ge_local_depth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA (Dw := Dw) c w n → (∀ k, (ρ : EReal) ≤ nuLocOf C e k (MvPolynomial.map io P)) → ∀ (N : ℕ), Odd N → IsUnit (N : T.V) → ∀ (x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₂ b ^ (N ^ 2) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) 1 (x₂ b) (F b)) → letI := io.toAlgebra; (ρ : EReal) ≤ nval T.V e (hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hC nab hnab e ρ w n he P hP hloc N hN hu x₂ F hF
  letI := io.toAlgebra
  have hst : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hone : ∀ {Z : Over Xo.X} (t : Z ⟶ Xo.univ.t.G), t ≫ Xo.univ.t.act.act 1 = t := fun t => by
    rw [Xo.univ.t.act.one, Category.comp_id]
  have hmix := fun b => (GlobalTheory.T.mixed_translate_pullback_eq_reached_section E H Dw l Xo T.Fr (xOf y) N N 1 1 1 1 hN (by simp) (by simp) (by simp)
    (sOf1 y) 1 (x₂ b) (F b) (one_pow _) (hF b).1 (by rw [_root_.mul_one, hone, one_pow]) (by rw [hone, _root_.mul_one]; exact (hF b).1)
    (hF b).2).2
  choose hh hre hpl using hmix
  have hg := fun b => (GlobalTheory.T.regular_section_integral_germ_unique_scale E H Dw l Xo c hst T io y C hC.1 _ (hh b)).1
    (GlobalTheory.T.reachedSection_regular_on_integralModel E H Dw l Xo c hst T io y C hC _ (hh b) (hre b))
  choose f hf using hg
  obtain ⟨B, hB1, -⟩ := GlobalTheory.T.integralChart_formalBiextension_gauge_bound E H Dw l Xo c hst T io y C
  have hHH : P ∈ HH c w n := hP.1
  have hni := GlobalTheory.T.harmonicValue_integralPoint_eq_value_on_biextensionCopies E H Dw l Xo c hst T io y C nab hnab B hB1 _ n hh f hf w P hHH
  have hch := GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback E H Dw l Xo c hst nab hnab T.Fr y.1 1 1 (N ^ 2 * 1) (N ^ 2) (by simp) (by ring) n hh
    (fun b => sqN Xo N (F b)) hpl w P hHH
  have hn1 : nrm Dw c w (1 : 𝓞 E) = 1 := by simp [nrm]
  rw [hch, hn1, map_one, _root_.one_mul, hni]
  obtain ⟨hF', hA', -, -, -, -, -⟩ := C.gen.1
  obtain ⟨e1, e2, -, -, -, -⟩ := hB1
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [GlobalTheory.ChartBiext.toK_self, hF', e1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [GlobalTheory.ChartBiext.toK_self, hA', e2]
  rw [GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]
  refine (hloc (N ^ 2 * 1)).trans ?_
  unfold nuLocOf
  refine iInf_le_of_le (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (iInf_le_of_le ?_ le_rfl)
  intro m
  exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

end GlobalTheory.RefSum.TermLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueGeLocalDepthPrimeToPStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_value_ge_local_depth_prime_to_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA (Dw := Dw) c w n → (∀ k, (ρ : EReal) ≤ nuLocOf C e k (MvPolynomial.map io P)) → ∀ (N : ℕ), Odd N → IsUnit (N : T.V) → ∀ (x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₂ b ^ (N ^ 2) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) 1 (x₂ b) (F b)) → letI := io.toAlgebra; (ρ : EReal) ≤ nval T.V e (hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  first | exact @GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth | exact GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth | (intros; apply GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.ThetaBound
open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.RefSum.LowP


set_option maxHeartbeats 1000000 in
theorem thRule_lower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (p : ℕ), p.Prime → ¬ p ∣ l.M → ∀ (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P₁ ∈ harmA (Dw := Dw) c a n, ∀ A B : ℝ, PolyBetween Xo la P₁ A B → ∀ (x : Fin n → Dw.La) (f : Rul Xo c), IsThRule Xo c nab x P₁ f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg → (A : EReal) ≤ nval T.V (vV T.V (p : T.Fr)).toNat (evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab p hp hpM la a n P₁ hP₁ A B hPB x f hf T io e ho y hy
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨T', iT, r, y', C', ⟨hr, hiT, φ, hφ, hmap⟩, hfin, hgood, hrat⟩ :=
    Prep.exists_good_chart_allRat E H Dw l Xo c hnab.1 T io y hy (l.M ^ 2) (pow_pos hM0 2)
  have ho' := ho.bc iT hr hiT
  have hvp : 0 < vV T.V (p : T.Fr) := by
    have h1 := ho.2 (p : c.F)
    rw [map_natCast] at h1
    rw [h1]
    exact mul_pos (by exact_mod_cast ho.1) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.vLa_pos la.1 p hp.ne_zero la.2)
  have hvp' : vV T'.V (p : T'.Fr) = (r : ℤ) * vV T.V (p : T.Fr) := by
    rw [← map_natCast iT p, hiT]
  obtain ⟨k₀, hk₀⟩ := Int.eq_ofNat_of_zero_le hvp.le
  have he' : (vV T'.V (p : T'.Fr)).toNat = r * (vV T.V (p : T.Fr)).toNat := by
    rw [hvp', hk₀, ← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  have hk0 : 0 < k₀ := by omega
  have he'pos : 0 < (vV T'.V (p : T'.Fr)).toNat := by
    rw [he', hk₀, Int.toNat_natCast]; exact Nat.mul_pos hr hk0
  have hu : IsUnit (l.M : T'.V) := by
    refine GlobalTheory.PlaceInt.ShortTriv.isUnit_of_coprime T' (ℓ := p)
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)) fun h => ?_
    have h2 := GlobalTheory.PlaceInt.ShortTriv.vV_natCast T' h
    rw [hvp', hk₀] at h2
    have : (0 : ℤ) < (r : ℤ) * (k₀ : ℤ) := by positivity
    omega
  rw [← nval_bc iT hr hiT ((vV T.V (p : T.Fr)).toNat), ← he']
  obtain ⟨n', j, -, -, a3⟩ := (GlobalTheory.TorsFac.factorisation E H Dw l Xo l.M p l.odd dvd_rfl hp).1 hpM
  letI := (iT.comp io).toAlgebra
  choose F hF using fun b : Fin n =>
    (RatData.exists_thetaVal_data E H Dw l Xo c T'.Fr y'.1).1 hrat (x b)
  have hev : iT (evI y f) = thExpr Xo c nab y'.1 P₁ F := by
    letI : Algebra T.Fr T'.Fr := iT.toAlgebra
    exact GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field E H Dw l Xo c nab hnab T io y T'.Fr φ hφ y'.1 hmap a n x P₁ hP₁ F hF f hf
  have ht : ∀ b, ∃ t' : ptO Xo (xOf y') ⟶ Xo.univ.t.G, t' ^ (l.M ^ 2) = 1 ∧
      IsUUOver Xo.univ.t.G Xo.univ.t.PP l.M (sOf1 y') 1 t' (F b) := by
    intro b
    have h1 : levPt Xo y'.1.x (x b) ^ l.M = 1 := by
      obtain ⟨t', -, -, -, -, b1, b2, -⟩ := hF b
      rw [← b1, ← pow_mul, ← pow_two]
      exact (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1
    obtain ⟨t', -, b2, b3⟩ :=
      (uu_through_moves E H Dw l Xo T'.Fr (xOf y') l.M l.odd (sOf1 y')).2 _ _ (F b) h1 (hF b)
    exact ⟨t', (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1, b3⟩
  choose t' ht1 ht2 using ht
  have hρ : ∀ k, (A : EReal) ≤ nuLocOf C' (vV T'.V (p : T'.Fr)).toNat k (MvPolynomial.map (iT.comp io) P₁) :=
    fun k => (hPB T' (iT.comp io) (r * e) ho' y' hfin C' k).1
  have hb := GlobalTheory.T.harmonic_value_ge_local_depth_prime_to_p E H Dw l Xo c T' (iT.comp io) y' C' hgood nab hnab _ A a n he'pos P₁ hP₁ hρ l.M l.odd hu
    t' F (fun b => ⟨ht1 b, ht2 b⟩)
  have hh := (hv_linear E H Dw l Xo c hnab.1 nab hnab T'.Fr y'.1 n P₁).2.2 l.M F
  rw [← hh] at hb
  rw [hev, thExpr, map_inv₀, map_pow, map_natCast, GlobalTheory.PlaceInt.TermBound.nval_inv_pow_mul T' _ _ _ hu]
  exact hb

end GlobalTheory.RefSum.LowP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefAway

theorem vLa_nat_eq_zero {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ}
    (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) : vLa la (N : K) = 0 := by
  rw [vLa, ← map_natCast (algebraMap (𝓞 K) K) N, HeightOneSpectrum.valuation_of_algebraMap,
    (la.intValuation_eq_one_iff_mem_primeCompl _).2 hN]
  simp

theorem vLa_nat_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (h0 : N ≠ 0)
    (hN : ((N : ℕ) : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (N : K) := by
  have h1 : la.valuation K (N : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) N]
    exact (la.valuation_lt_one_iff_mem _).2 hN
  have h2 : la.valuation K (N : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast h0
  have h3 := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at h3
  unfold vLa
  omega

theorem isUnit_nat {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) (N : ℕ) (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) :
    IsUnit ((N : ℕ) : S.V) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simp)
  have h3 := ho.2 (N : K)
  rw [vLa_nat_eq_zero la hN, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)] at h3
  have hx : algebraMap S.V S.Fr (N : S.V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact_mod_cast hN0
  have hne := valV_ne_zero (V := S.V) hx
  have h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1 := by
    unfold vV at h3
    rw [← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]
  unfold valV at h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl] at h4
  by_contra hu
  exact h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)

theorem nat_not_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {p N : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) (h : Nat.Coprime p N) : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal := by
  intro hN
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at huv
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hp) (la.asIdeal.mul_mem_left _ hN)))

theorem vV_nat_eq {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) (p : ℕ) :
    vV S.V (p : S.Fr) = (e : ℤ) * vLa la (p : K) := by
  rw [← ho.2, map_natCast]

theorem le_nval_place {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) {p : ℕ} (hp : 0 < vLa la (p : K)) (A : ℕ) (x : S.Fr)
    (h : ((A : ℝ) : EReal) ≤ nval S.V (vV S.V (p : S.Fr)).toNat x) :
    (((vLa la (p : K) * A : ℤ) : ℝ) : EReal) ≤ nval S.V e x := by
  by_cases hx : x = 0
  · rw [hx, nval_zero]; exact le_top
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  have h1 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℝ) = (e : ℝ) * (vLa la (p : K) : ℝ) := by
    have h2 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℤ) = (e : ℤ) * vLa la (p : K) := by
      rw [Int.toNat_of_nonneg, vV_nat_eq ho]
      rw [vV_nat_eq ho]; positivity
    exact_mod_cast h2
  have he' : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hp' : (0 : ℝ) < (vLa la (p : K) : ℝ) := by exact_mod_cast hp
  rw [nval_of_ne hx, EReal.coe_le_coe_iff] at h ⊢
  rw [h1, le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ he']
  push_cast
  linarith

theorem coprime_type (D : D7) : Nat.Coprime (D.host.g 0 * D.host.g 1) (D.host.QS * D.host.q * D.host.d) := by
  have h (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    have hc := D.ntypes.g_cond k
    have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
    exact h1
  exact Nat.Coprime.mul_left (h 0) (h 1)

theorem err_le (R N ρ u Dg φ c r v g₀ g₁ : ℝ) (hR : 0 ≤ R) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ N) (hu : 0 ≤ u) (hr : 0 < r)
    (hv : 0 < v) (hg₀ : 0 < g₀) (hg₁ : 1 ≤ g₁) (hφ : 0 ≤ φ) (hc : R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ ≤ c) :
    Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v) ≤ c * φ / v := by
  have hN : 0 ≤ N := hρ0.trans hρ
  calc Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v)
      ≤ Dg ^ 2 * (R * N ^ 3 * (r * φ)) / (g₀ * 1) / (r * v) := by gcongr
    _ = R * N ^ 3 * Dg ^ 2 / g₀ * φ / v := by field_simp
    _ ≤ R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ * φ / v := by
      gcongr
      nlinarith [sq_nonneg Dg]
    _ ≤ _ := by gcongr

theorem refExp_le_of_oscLe : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) → ∀ b : ℝ, OscLe (T.Q.Xo j) T.Q.c q (gap (T.Q.Dw j) a) b → refExp_vp (T.U j) cst (wtZ a n) q ≤ (b : EReal) := by
  intro D T hL EX j hj a n cst hD hLP hs hr hJ q hq' hq b hO
  letI := T.Q.H.starRing
  have hqp : q.Prime := hq'.out
  refine (refExp_vp_le_iff _).2 fun la S io e ho y hy φ hφ => ?_
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  obtain rfl := GlobalTheory.PowGerm.starSt _ T.Q.H st hnab.1
  obtain ⟨A, hA⟩ := hO la
  obtain ⟨P₁, hP₁, hPB⟩ := GlobalTheory.T.exists_harmonicPolynomial_localDepth_between D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c q la a hD.1 n hs _ _ hA
  obtain ⟨S', io', y', r, C, P, hy', hr0, hC, hP, hφ', hov, hvm, hsc⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ
  have ho' := hov la.1 e ho
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S'.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T hL EX
  obtain ⟨π, π', hsplit⟩ := GlobalTheory.SplitLevel.level_halfSplit D T hL EX
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hL.pins.2.1.1
  have hcop : Nat.Coprime q T.Q.l.M := by
    rw [hM]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hqp (D.host.g_prime 0)).2 (hq 0))
      ((Nat.coprime_primes hqp (D.host.g_prime 1)).2 (hq 1))
  have hMu : IsUnit ((T.Q.l.M : ℕ) : S'.V) := isUnit_nat la.1 S' _ _ ho' _ (nat_not_mem la.1 la.2 hcop)
  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn1 : 1 ≤ n := by omega
  have hρN : ρ ≤ 2 * D.R.f * D.R.m := by
    refine hρ.trans ?_
    rw [GlobalTheory.DepthLink.finrank_host D, (hL.pins.2.2.2 j hj).2.1]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hρN' : (ρ : ℝ) ≤ 2 * D.R.f * D.R.m := by exact_mod_cast hρN
  have hg0 : 2 ≤ D.host.g 0 := (D.host.g_prime 0).two_le
  have hg1 : 2 ≤ D.host.g 1 := (D.host.g_prime 1).two_le
  have hle : D.host.g 0 ≤ T.Q.l.M := hM ▸ Nat.le_mul_of_pos_right _ (by omega)
  have hg0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
  have hg1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
  have hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ) := by exact_mod_cast hle
  have hDM : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt ρ) < (T.Q.l.M : ℕ) := by
    refine lt_of_le_of_lt ?_ ((hJ 0).2.1.trans_le hle')
    gcongr

  have hε : 0 < vLa la.1 (q : T.Q.c.F) := vLa_nat_pos la.1 hqp.ne_zero la.2
  have hv0 : 0 < vV S.V (q : S.Fr) := by
    rw [vV_nat_eq ho]
    exact mul_pos (by exact_mod_cast ho.1) hε
  obtain ⟨v, hv⟩ : ∃ v : ℕ, vV S.V (q : S.Fr) = v := ⟨_, (Int.toNat_of_nonneg hv0.le).symm⟩
  have hvpos : 0 < v := by omega
  have hv' : (vV S'.V (q : S'.Fr)).toNat = r * v := by
    rw [hvm q hqp.ne_zero, hv, ← Nat.cast_mul, Int.toNat_natCast]
  have hrv : ((r * v : ℕ) : ℤ) = ((r * e : ℕ) : ℤ) * vLa la.1 (q : T.Q.c.F) := by
    rw [← vV_nat_eq ho', hvm q hqp.ne_zero, hv, Nat.cast_mul]
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hvpos' : (0 : ℝ) < v := by exact_mod_cast hvpos

  have hup := GlobalTheory.RefSum.iInf_thRule_le_nuLocOf _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab S' io' y' C hC P hP hy' ϖ hϖ Q hQ ρ _ _ hSB
    α hα1 hα2 hMu a n (r * v) hn1 (Nat.mul_pos hr0 hvpos) ((hJ 0).1.trans hle) hDM P₁ hP₁
  have hloc := (hPB S' io' _ ho' y' hy' C T.Q.l.M).2
  rw [hv'] at hloc
  have hnum : (DF (T.Q.Dw j) a : ℝ) ^ 2 * (rr0 D * (ρ : ℝ) ^ 3 * (r * φ)) / (T.Q.l.M : ℕ) / ((r * v : ℕ) : ℝ) ≤
      cst * φ / v := by
    rw [hM, Nat.cast_mul, Nat.cast_mul]
    refine err_le (rr0 D) _ ρ _ _ φ cst r v _ _ ?_ (Nat.cast_nonneg _) hρN' ?_ hr0' hvpos' (by linarith) (by linarith)
      hφ.nonneg (hJ 0).2.2
    · unfold rr0; positivity
    · positivity
  have hinf := hup.trans (add_le_add hloc (EReal.coe_le_coe_iff.2 hnum))

  obtain ⟨m, hm, hmlow, -⟩ := GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab _ _ π π' hsplit
    (coprime_type D) a n
  have hdep : depthAt_vp (T.U j) (wtZ a n) q y + ((A : ℝ) : EReal) ≤
      ⨅ (f : Rul (T.Q.Xo j) T.Q.c) (_ : ∃ x : Fin n → (T.Q.Dw j).La, IsThRule (T.Q.Xo j) T.Q.c nab x P₁ f),
        nval S'.V (r * v) (evI y' f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen (T.Q.Xo j) T.Q.c nab a n := ⟨x, P₁, hP₁, hx⟩
    have hcusp := (GlobalTheory.thetaRules_exist_and_cusp _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1 (hL.unf j hj) nab hnab).2
      a n hD hLP f hf
    have hlow := GlobalTheory.RefSum.LowP.thRule_lower _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab q hqp
      (hqp.coprime_iff_not_dvd.1 hcop) la a n P₁ hP₁ _ _ hPB x f hx
    obtain ⟨s, hs0, hsv, g, hg, hgs⟩ := GlobalTheory.T.cuspForm_clear_denominators_away_from_place _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (wtZ a n)
      ⟨f, hcusp⟩ m hm (hmlow f hf) la.1 (vLa la.1 (q : T.Q.c.F) * A) (by
        rintro _ ⟨⟨_, S₁, io₁, e₁, ho₁, y₁, hy₁, η, hη, rfl⟩, rfl⟩
        exact le_nval_place ho₁ hε A _ (hlow S₁ io₁ e₁ ho₁ y₁ hy₁))
    have h1 : depthAt_vp (T.U j) (wtZ a n) q y ≤ nval S.V v (io s * evI y f) := by
      refine (iInf₂_le g hg).trans (le_of_eq ?_)
      show nval S.V (vV S.V (q : S.Fr)).toNat (evI y (g : Rul (T.Q.Xo j) T.Q.c)) = _
      rw [hv, Int.toNat_natCast, hgs, evI_smul]
    have h2 : nval S'.V (r * v) (io' s) = ((-(A : ℝ) : ℝ) : EReal) := by
      rw [nval_of_ne ((map_ne_zero io').2 hs0), ho'.2 s, hsv]
      congr 1
      have h3 : ((r * v : ℕ) : ℝ) = ((r * e : ℕ) : ℝ) * (vLa la.1 (q : T.Q.c.F) : ℝ) := by exact_mod_cast hrv
      have h4 : ((r * v : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hr0 hvpos).ne'
      rw [div_eq_iff h4, h3]
      push_cast
      ring
    rw [← hsc nab hnab a n v s f hf, nval_mul, h2] at h1
    refine (add_le_add h1 le_rfl).trans (le_of_eq ?_)
    rw [add_right_comm, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
  have hfin := hdep.trans hinf
  rw [hv, Int.cast_natCast]
  rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_add,
    ← EReal.coe_sub] at hfin
  rw [← EReal.coe_add]
  exact hfin.trans (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.RefAway

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrimeStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLocusExponent_le_oscillation_nonTypePrime : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) → ∀ b : ℝ, OscLe (T.Q.Xo j) T.Q.c q (gap (T.Q.Dw j) a) b → refExp_vp (T.U j) cst (wtZ a n) q ≤ (b : EReal) := by
  first | exact @GlobalTheory.RefAway.refExp_le_of_oscLe | exact GlobalTheory.RefAway.refExp_le_of_oscLe | (intros; apply GlobalTheory.RefAway.refExp_le_of_oscLe <;> assumption)
end
