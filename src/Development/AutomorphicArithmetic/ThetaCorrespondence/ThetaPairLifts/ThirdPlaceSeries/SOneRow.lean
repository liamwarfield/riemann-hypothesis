module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedBundleDegreeLowerBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDegreeParametersBound

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SOneRow
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OfStar
section -- merged from Development.AutomorphicArithmetic.NaturalDivisibility.ExistsContinuousRingEquivPadicOfTotallySplit
open NumberField IsDedekindDomain Formalism.BasicNotions GroundTheory.Global.SemiLocal

private theorem natGen_dvd_iff (x : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator x ∣ n ↔ ((n : ℕ) : 𝓞 ℚ) ∈ x.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

private theorem mem_iff_eq (P : Nat.Primes) (x : HeightOneSpectrum (𝓞 ℚ)) :
    (((P : ℕ) : ℕ) : 𝓞 ℚ) ∈ x.asIdeal ↔ x = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm P := by
  rw [Equiv.eq_symm_apply, ← natGen_dvd_iff]
  constructor
  · intro h
    apply Subtype.ext
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator x) P.2).1 h
  · intro h
    rw [← h]
    exact dvd_refl _

theorem UpperTheory.exists_continuous_ringEquiv_padic_of_totally_split :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) [Fact p.Prime], w ∈ placesOver E p → (placesOver E p).ncard = Module.finrank ℚ E → ∃ i : ℚ_[p] ≃+* w.adicCompletion E, Continuous i := by
  intro E _ _ w p hp hw hcard
  let P : Nat.Primes := ⟨p, hp.out⟩
  let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm P
  have hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (mem_iff_eq P v).2 rfl
  have hlies : ∀ u : HeightOneSpectrum (𝓞 E), u ∈ placesOver E p ↔ u.asIdeal.LiesOver v.asIdeal := by
    intro u
    show ((p : ℕ) : 𝓞 E) ∈ u.asIdeal ↔ _
    rw [Ideal.liesOver_iff]
    constructor
    · intro hu
      have hmem : ((p : ℕ) : 𝓞 ℚ) ∈ u.asIdeal.under (𝓞 ℚ) := by
        rw [Ideal.under, Ideal.mem_comap, map_natCast]
        exact hu
      let q : HeightOneSpectrum (𝓞 ℚ) :=
        { asIdeal := u.asIdeal.under (𝓞 ℚ)
          isPrime := inferInstance
          ne_bot := by
            intro h
            rw [h, Ideal.mem_bot] at hmem
            exact hp.out.ne_zero (by exact_mod_cast hmem) }
      have hq : q = v := (mem_iff_eq P q).1 hmem
      rw [← hq]
    · intro h
      rw [h, Ideal.under, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
  haveI : w.asIdeal.LiesOver v.asIdeal := (hlies w).1 hw
  have hcardS : Fintype.card (PlacesOver E v) = Module.finrank ℚ E := by
    rw [← hcard, ← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => (hlies u).symm)
  have hone : ∀ u : PlacesOver E v,
      (u : HeightOneSpectrum (𝓞 E)).asIdeal.ramificationIdx (𝓞 ℚ) *
        (u : HeightOneSpectrum (𝓞 E)).asIdeal.inertiaDeg (𝓞 ℚ) = 1 := by
    have hsum := sum_ramificationIdx_mul_inertiaDeg (K := ℚ) E v
    intro u
    have hpos : ∀ u' : PlacesOver E v, 1 ≤
        (u' : HeightOneSpectrum (𝓞 E)).asIdeal.ramificationIdx (𝓞 ℚ) *
          (u' : HeightOneSpectrum (𝓞 E)).asIdeal.inertiaDeg (𝓞 ℚ) := fun u' =>
      Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
    by_contra hne
    have hlt := Finset.sum_lt_sum (s := Finset.univ) (f := fun _ : PlacesOver E v => 1)
      (fun u' _ => hpos u') ⟨u, Finset.mem_univ _, lt_of_le_of_ne (hpos u) (Ne.symm hne)⟩
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcardS] at hlt
    exact lt_irrefl _ hlt
  have hrank : Module.finrank (v.adicCompletion ℚ) (w.adicCompletion E) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg]
    exact hone ⟨w, inferInstance⟩
  have hsurj : Function.Surjective (completionMap v w) :=
    Algebra.surjective_algebraMap_iff.2 (Subalgebra.bot_eq_top_of_finrank_eq_one hrank).symm
  letI : Algebra ℚ (HeightOneSpectrum.adicCompletion ℚ (Rat.HeightOneSpectrum.primesEquiv.symm P)) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
  refine ⟨(Padic.adicCompletionEquiv (𝓞 ℚ) P).toRingEquiv.trans
    (RingEquiv.ofBijective (completionMap v w) ⟨(completionMap v w).injective, hsurj⟩), ?_⟩
  exact (continuous_completionMap v w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) P).continuous
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalStar
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem star_guard {y : WD h} (k : NcW y) : (IsQpBig w y.lpDim ∧ TmW y ∧ UpperTheory.GalStar.Sqf y) ∨ Tor y := by
  by_cases hs : ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧
      (y.lpDim = 1 ∨ 16 * y.lpDim ^ 2 < p)
  · have ht : thr w y.lpDim = 2 := if_pos hs
    obtain ⟨p, hp, hw, hc, hb⟩ := hs
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨i, hi⟩ := UpperTheory.exists_continuous_ringEquiv_padic_of_totally_split E w p hw hc
    exact Or.inl ⟨⟨p, inferInstance, i, hi, hb⟩, k.1, fun γ hγ hg z hz => k.2.2 γ hγ hg z (by rwa [ht])⟩
  · exact Or.inr (tor_of_ncW (if_neg hs) k)

theorem tor_of_unr {y : WD h} (u : y.unr) : Tor y := fun s t => by
  have hd : deg ⁅s, t⁆ = 0 := by simp [commutatorElement_def]
  have := inePol_of_unr u (deg_eq_zero_iff.1 hd)
  rwa [WD.inePol_of_mem _ (⁅s, t⁆ : ↥(Weil h)).2] at this

theorem away_nice {x y : WD h} (a : AwayB x y) (k : NcW y) :
    x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g := by
  rcases star_guard k with ⟨q, t, s⟩ | t
  · exact a.tame0 q t s k.2.1
  · rw [a.tor t k.2.1]; exact ⟨k.2.1, fun _ _ => rfl⟩

theorem aw_of_away {x y : WD h} (a : AwayB x y) : Aw x y :=
  ⟨a.dim, fun u => a.tor (tor_of_unr u) (WD.unr_mono0 _ u), fun k => (away_nice a k).2, fun k => (away_nice a k).1⟩
end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]


end UpperTheory.GalS
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SOfStar
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalStar
open scoped commutatorElement
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]
omit [IsCMField E] [Fact l.Prime] in
theorem star_guard'_alt {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (k : NcW (rc (algNorm σ))) :
    (IsQpBig w a ∧ TmW (rc (algNorm σ)) ∧ UpperTheory.GalStar.Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := hrc
  have e : (rc (algNorm σ)).lpDim = a := H.dim _
  have := star_guard k
  rwa [e] at this
theorem isGalU_of_props_alt {π : CuspSub E a} (χ : HChar (maximalRealSubfield E)) {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} (H : PropsB _root_.UpperTheory.One.M.recT π ι r wt HT) :
    _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT :=
  ⟨H.cont, H.ss, fun w hl A h rc hrc σ hσ => aw_of_away (H.away w hl A h rc hrc σ hσ), H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj =>
      have k := H.above P AI T w A h O Bw hj
      ⟨fun ⟨σ, hσ, rc, hrc, n⟩ => (k.nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).1,
        fun ⟨σ, hσ, rc, hrc, n⟩ => (k.nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).2.2.1, fun σ hσ hs => (k.crys σ hσ hs).1⟩⟩
theorem pairU_of_star_alt (H : Row0b _root_.UpperTheory.One.M.recT) : _root_.UpperTheory.GalS.PairUAlt := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, _root_.UpperTheory.GalS.isGalU_of_props_alt χ k⟩
theorem carU_of_star_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (H : Row0b _root_.UpperTheory.One.M.recT) : _root_.UpperTheory.GalS.CarUAlt := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hr
  have hpol := isPolarized_of_isCsd hc
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a (by omega) π _ hr
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E _) (hGK E a _) hpol.dual⟩
  refine ⟨r, wt, HT, _root_.UpperTheory.GalS.isGalU_of_props_alt _ k, fun P AI T w _ A h O _ _ _ Bw hj σ hσ rc hrc n => ?_⟩
  have b := ((k.above P AI T w A h O Bw hj).nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).2.2.2
  exact ⟨b.dim, fun _ => (away_nice b n).1, fun _ _ => (away_nice b n).2⟩
theorem field_of_starFull_alt (_ : _root_.UpperTheory.Zero.LLC.RecTExists) (_ : GlobalTheory.Published.LocalConverseGL)
    (_ : GlobalTheory.Published.LanglandsExhaustionGL) (H : _root_.UpperTheory.One.M.Row) : _root_.UpperTheory.GalS.PairUAlt := _root_.UpperTheory.GalS.pairU_of_star_alt H
theorem ofDual_star_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (H : _root_.UpperTheory.One.M.Row) : _root_.UpperTheory.GalS.CarUAlt := _root_.UpperTheory.GalS.carU_of_star_alt hGK H
end UpperTheory.GalS
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.GalS
theorem bridgeStar_alt : GlobalTheory.Published.GelfandKazhdanDual → (_root_.UpperTheory.One.M.Row → _root_.UpperTheory.GalS.CarUAlt) ∧ (_root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.GalS.CuspUAlt) :=
  fun hGK => ⟨_root_.UpperTheory.GalS.ofDual_star_alt hGK, _root_.UpperTheory.GalS.cusp_of_pair_alt hGK⟩
end UpperTheory.GalS
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HilbertSamuelLowerBoundOfComponents
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.ShortRoad
set_option maxHeartbeats 1000000 in
theorem hilbertSamuel_of_component_estimates_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree →
    _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverHeightSum := by
  intro hX h2 hGD hQd hSi hTo hSA hDG hS hF hDe hSh
  obtain ⟨Cp, hCp, htw⟩ := _root_.GlobalTheory.T.twisted_bundle_degree_lower_bound h2
  have hrk := _root_.GlobalTheory.T.twisted_flat_bundle_ranks h2
  have hgood := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  refine Closed.imp (((((((_root_.GlobalTheory.T.exists_degree_parameters_bound_alt_alt hX h2 hGD hQd hSi hTo hSA hDG hS hF).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS)).and hS).and hF).and
    hDe).and hSh) ?_
  intro eps Fm CH _ H
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _, hR⟩, _, _, hZ⟩, _, _, hQu⟩, CS, _, hSz⟩, _, _, hFl⟩, _, _, hDg⟩, _, _, hSr⟩ := H
  refine ⟨10000 + 2 * Cp, by positivity, ?_⟩
  obtain ⟨x0, H⟩ := ((((((hR.and hZ).and hQu).and hSz).and hFl).and hDg).and hSr)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨hR, hZ⟩, hQu⟩, hSz⟩, hFl⟩, hDg⟩, hSr⟩ := H x hx hle ι p hp
  set PP := (Fm.parT x hx ι).PP
  set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ with hPdef
  obtain ⟨hp1, hq1, hfin, hqe, hanti, ⟨w, hw, huM⟩, -⟩ := hQu i hi
  obtain rfl := hqe u1 hu1
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, hflat, -, hZPP, hTPP, hzb, hz2, -, -⟩ := hZ i hi Y hY
  obtain ⟨hb1, hbU, -, -, -, hbPP, hSq⟩ := hSz i
  obtain ⟨hT, hρ, -, -⟩ := (hSq hi).2 _ hu1
  have hY1 := hY.1
  have hAG := hgood (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (P.wt (lenT p i PP))
    (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P (lenT p i PP) (fun τ => (hanti τ).1) (by omega) hp1 hq1 τ).1)
    (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P (lenT p i PP) (fun τ => (hanti τ).1) (by omega) hp1 hq1 τ).2)
  have hFZ := hFl i hi Y hY
  have hrkZ := (hrk (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 _ hFZ).1
  have htwZ := htw (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (Fm.L x ι).sc.L hL1 hM hfs hfr (le_of_eq (by rw [zBase]))
    _ hFZ (by rw [abs_neg]; exact hflat) (P.wt (lenT p i PP)) w
  have hDf : 1 ≤ CompHt.dimFlag (dat p i) := by
    rw [GlobalTheory.CovTop.WtShape.dim_eq]
    exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hz1 : 1 ≤ zBase (Fm.L x ι) := by
    unfold zBase
    have a : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have b : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hPP1 : 1 ≤ PP := (one_le_pow₀ hz1).trans hZPP
  have hLz : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    unfold zBase
    have a : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have b : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hz12 : zBase (Fm.L x ι) ≤ zBase (Fm.L x ι) ^ 12 := le_self_pow₀ hz1 (by norm_num)
  have hlb : Real.log (Fm.L x ι).sc.b ≤ PP := by
    rw [Formalism.BasicNotions.Scale.b, Real.log_exp]
    linarith
  have hT1 : (1 : ℝ) ≤ (lenT p i PP : ℝ) := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hsq : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ (Fm.L x ι).sc.b by linarith)
    have := Real.one_le_sqrt.2 hb1
    nlinarith
  have hZb : zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.b := by
    have a1 : zBase (Fm.L x ι) ^ 2 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hz1 (by norm_num)
    have a2 : PP ≤ (lenT p i PP : ℝ) * PP := le_mul_of_one_le_left (by linarith) hT1
    exact a1.trans (hZPP.trans (a2.trans (hTPP.trans hsq)))
  have hkap : 0 ≤ kap p i := le_of_lt (pos_of_mul_pos_right (by linarith) (by linarith : (0 : ℝ) ≤ PP))
  have hz0 : 0 ≤ zed p i PP P.u₁ := by
    unfold zed
    exact mul_nonneg (by norm_num) (add_nonneg (by positivity) (mul_nonneg (by positivity) hρ))
  have hDf0 : (0 : ℝ) < CompHt.dimFlag (dat p i) := by exact_mod_cast hDf
  refine ⟨26 * (26 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 + 2 * zed p i PP P.u₁ * lenT p i PP),
    4000 * (Fm.L x ι).sc.b + 2 * (Cp * zBase (Fm.L x ι) ^ 2), by positivity, by positivity, ?_, fun Z => ?_⟩
  · have hA := GlobalTheory.hilbertSamuel_ALogA_le (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (Fm.L x ι).sc.b (zed p i PP P.u₁) hDf (by omega)
      hPP1 hb1 hlb hTPP hz0 hz2
    have e1 := mul_le_mul_of_nonneg_left hZb hCp
    have e2 := mul_le_mul_of_nonneg_left hbU (by positivity : (0 : ℝ) ≤ 10000 + 2 * Cp)
    nlinarith
  obtain ⟨n, Λ, β, ΛD, ΛT, J, hn, hΛ, hβ, hΛD, hΛT, hln, hlβ, hlδ, hlΛ, hlΛD, hlΛT, hJ, hcl⟩ := hR i hi Y hY Z
  obtain ⟨δ0, hδ0, hδ⟩ := hDg i hi Y hY _ hu1
  have hdg : 1 ≤ Y.dg P.u₁ Z := by
    have h0 : (0 : ℝ) < Y.dg P.u₁ Z := hδ0.trans_le (hδ Z).1
    simp only [Deep.dg] at h0 ⊢
    exact Nat.one_le_cast.2 (Nat.cast_pos.1 h0)
  have hsh := hSr i hi Y hY _ hu1 Z
  rw [huM, hrkZ] at hsh
  have hbin : (1 : ℝ) ≤ binT p i PP := by
    unfold binT
    exact Nat.one_le_cast.2 (Nat.choose_pos (by omega))
  have hd : 0 < Y.rkC (P.wt (lenT p i PP)) Z := by nlinarith [hsh.1]
  have htwz := htwZ Z hw (hAG.2 Z)
  rw [← huM] at htwz
  exact GlobalTheory.CovHSNum.deg_bound_of_claim_numbers (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (kap p i) (Fm.L x ι).sc.b (zed p i PP P.u₁)
    (CompHt.rhoB (dat p i) P.u₁) n Λ β ΛD ΛT J (Y.dg P.u₁ Z) (Y.ht P.u₁ Z) (Y.rkC (P.wt (lenT p i PP)) Z)
    (Y.degC (P.wt (lenT p i PP)) Z) (Y.degC (uM p i) Z) (Cp * zBase (Fm.L x ι) ^ 2) hDf hT hPP1 hb1 hlb hTPP rfl hρ hz2 hzb
    hkap hn hΛ hβ hΛD hΛT hdg hd hln hlβ hlδ hlΛ hlΛD hlΛT hJ hsh.2 hcl (by positivity) (by rw [zBase]; exact htwz)
end GlobalTheory.CovTop.ShortRoad
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverHeightSum_of_flatDeg_coverDegree_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverHeightSum := by
  first | exact @_root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates_alt | exact _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates_alt | (intros; apply _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates_alt <;> assumption)
end
end
end
