module

public import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.PhiSetPullSub
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Ev

variable (Xr : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  {K2 : Type} [Field K2] (ev : Rp Xr la N →+* K2) (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0)))

lemma liftEv_alg (r : Rp Xr la N) :
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu (algebraMap (Rp Xr la N) (Lw Xr la w) r) = ev r :=
  IsLocalization.lift_eq _ r

lemma liftEv_w0inv :
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu (w0inv Xr la w) = (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0))⁻¹ := by
  have := congrArg (IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu) (section_mul_inverse_eq_one Xr la w)
  rw [map_mul, liftEv_alg, map_one] at this
  exact eq_inv_of_mul_eq_one_right this

lemma liftEv_frac (k : ℕ) (g : Rp Xr la N) :
    IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0) hu (frac Xr la w k g) = ev g * (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec Xr la w 0))⁻¹ ^ k := by
  rw [frac_apply, map_mul, map_pow, liftEv_alg, liftEv_w0inv]

end Ev

section Std

variable {Xr : PJ D B P j} {la : HeightOneSpectrum (𝓞 B.KO)} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData Xr ka wL wF}

theorem isUnif_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) :
    IsUnif (OsK Xr la G.w) (unifO Xr la G.N) := by
  have : Algebra.IsIntegral (Kp Xr la G.N) (OsK Xr la G.w) := Algebra.IsIntegral.of_finite _ _
  exact isUnif_of_field (Kp Xr la G.N)
    (Op.irreducible_map Xr la G.N (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (Xr.Ol la))))

theorem kp_charZero' : CharZero (Kp Xr la G.N) := by
  have := Kl_charZero Xr la
  exact charZero_of_injective_algebraMap (algebraMap (Xr.Kl la) (Kp Xr la G.N)).injective

theorem isDVRAt_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) (hred : IsReduced (OsK Xr la G.w))
    (ζ : PtsG G la) : IsDVRAt ζ := by
  have := kp_charZero' (la := la) (G := G)
  exact (integralClosure_dvr' (Op Xr la G.N) (Kp Xr la G.N) (OsK Xr la G.w)).2 ζ

theorem loc_charZero (h : IsUnif (OsK Xr la G.w) (unifO Xr la G.N)) (ζ : PtsG G la) [IsDVRAt ζ] :
    CharZero (Loc ζ) := by
  have hK := kp_charZero' (la := la) (G := G)
  have hO : CharZero (Op Xr la G.N) :=
    (RingHom.charZero_iff (IsFractionRing.injective (Op Xr la G.N) (Kp Xr la G.N))).2 hK
  refine charZero_of_injective_algebraMap (R := Op Xr la G.N) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 h.irreducible
  rw [map_mul, map_pow] at ha
  have hb : algebraMap (Op Xr la G.N) (Loc ζ) (unifO Xr la G.N) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (Op Xr la G.N) ↥(As (Op Xr la G.N) (OsK Xr la G.w)) (Loc ζ)]
    intro h0
    exact vL_ne_top ζ (unif_mem_nonZeroDivisors h) ((vL_eq_top_iff ζ _).2 h0)
  exact (mul_ne_zero ((u.isUnit.map (algebraMap (Op Xr la G.N) (Loc ζ))).ne_zero) (pow_ne_zero n hb)) ha

end Std

variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

theorem addVal_map_of_unr {W V : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : W →+* V) (hunr : ∃ ϖ : W, Irreducible ϖ ∧ Irreducible (ι ϖ)) (r : W) :
    IsDiscreteValuationRing.addVal V (ι r) = IsDiscreteValuationRing.addVal W r := by
  obtain ⟨ϖ, hϖ, hιϖ⟩ := hunr
  by_cases hr : r = 0
  · subst hr
    rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, map_mul, map_pow]
  exact IsDiscreteValuationRing.addVal_def' ((u.isUnit.map ι).unit) hιϖ n

theorem fromW_of {ζ : PtsG G la} [IsDVRAt ζ] {y : E.Pt' la}
    (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N))
    (T : CDVR) (ι : Loc ζ →+* T.V) (hloc : IsLocalHom ι) (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ))
    (ev : Rp (xplus X E hM) la G.N →+* T.Fr) (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)))
    (hv : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
      nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F))))
    (hdeg : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        phiAt ζ T.Fr ι h (addVal_map_of_unr ι hunr) (toOsK (xplus X E hM) la G.w x)) :
    Nonempty (FromW ζ y) := by
  have hι : AddValPres ζ ι := addVal_map_of_unr ι hunr
  have honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w i.succ) = 0 := by
    intro i
    have h1 := hdeg (sfr (xplus X E hM) la G.w i.succ)
    rw [(toOsK_eq_zero_iff _ _ _ _).2 (sfr_succ_mem_Jid _ _ _ i), map_zero, coe_sfr, liftEv_frac] at h1
    exact (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hu.ne_zero))
  have hord : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w x)) =
        nval T.V 1 (IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w)) := by
    intro x
    rw [hdeg x]
    exact toE_ord_eq T.Fr h hι _
  let sp : SecPt ζ y :=
    { T := T, ep_pos := ep_pos ζ h, ev := ev, hv := hv, onS := honS, s0 := hu, ord := hord }
  have hevW : ∀ (x : ↥(Frac0 (xplus X E hM) la G.w))
      (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))),
      toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w) →
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        algebraMap T.V T.Fr (ι (algebraMap _ (Loc ζ) a)) := by
    intro x a hxa
    rw [hdeg x, hxa]
    exact phiAt_coe T.Fr h hι a
  exact ⟨{ toSecPt := sp
           ι := ι
           loc := hloc
           unr := hunr
           evW := hevW }⟩

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.HeightF1OfData
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem extVal_unit_zero (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    apply le_antisymm ((IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one _)
    have h2 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (R := T.V) (K := T.Fr) ((u⁻¹ : T.Vˣ) : T.V)
    have h3 : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    by_contra hlt
    rw [not_le] at hlt
    have : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this
    exact lt_irrefl _ this
  simp [vV, h1]

def OrdTieQZ (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v → IsTrivOn c.F v →
    ∃ q : QPt Xo c,
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 → ordQ Xo c q f = ⊤

theorem height_F1_of_data (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU)
    (hreg : regular₂ Xo c U) (htie : OrdTieQZ h δ)
    (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2)
    (hws : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2) (het : etR ∈ cusp Xo c U uet.1 uet.2)
    (hnz : NoCommonZero Xo c wR) (hnzet : NZAt h etR)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2) (hcc : 0 ≤ cc)
    (nuA : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (halg : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v etR ∧
      (v etR ≠ ⊤ → (⨅ k, v (wR k)) ≤ (nuA la : EReal) + ((cc / (2 * i) : ℝ) : EReal) * v etR)) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).TrivialPlaceHyp := by
  classical
  have hc' : (0 : ℝ) ≤ cc / (2 * i) := div_nonneg hcc (by positivity)

  have hR2 := (hreg.1.2 ⟨uL, hdL⟩ ⟨uet, hdE⟩ (N + 1) (fun k => ⟨wR k, hws k⟩) ⟨etR, het⟩ nuA (cc / (2 * i)) hc'
    hnz (fun la y => halg la y.1 y.2)).2
  unfold Data.TrivialPlaceHyp
  intro Z v hAdm hTv
  obtain ⟨q, hq1, hq0⟩ := htie Z v hAdm.1 hTv

  have hqT : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
    refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
    obtain ⟨u, hu⟩ := q.triv a ha
    rw [← hu]
    exact extVal_unit_zero q.T u
  obtain ⟨hE0, hEb⟩ := hR2 ⟨_, hqT⟩
  dsimp only [dataOf, Data.n1] at *
  rw [← huet]
  have hEq : (((ordC (δ Z v) v (wtZ uet.1 uet.2) (valC h uet.1 uet.2 etR Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q etR :=
    hq1 uet.1 uet.2 etR (cusp_le_sec Xo c U _ _ het) (hnzet Z)
  have hEne : ordQ Xo c q etR ≠ ⊤ := by rw [← hEq]; exact EReal.coe_ne_top _
  have hb := hEb hEne
  obtain ⟨k0, hk0⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin (N + 1) => ordQ Xo c q (wR k))
  have hk0le : ordQ Xo c q (wR k0) ≤ ((cc / (2 * i) : ℝ) : EReal) * ordQ Xo c q etR := by
    rw [hk0]; exact hb
  have hev : evC h Z (wR k0) ≠ 0 := by
    intro h0
    rw [hq0 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) h0, ← hEq, ← EReal.coe_mul] at hk0le
    exact EReal.coe_ne_top _ (top_le_iff.1 hk0le)
  have hval : valC h uL.1 uL.2 (wR k0) Z ≠ 0 := valC_ne_zero hev
  have hk0' := hq1 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) hev
  rw [← hk0', ← hEq, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hk0le
  have hle : (⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z)) ≤
      ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) :=
    ciInf_le (Set.finite_range _).bddBelow (⟨k0, hval⟩ : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0})
  have hle' : ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2)
      (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ) ≤ (ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) : ℝ) := by
    exact_mod_cast hle
  exact hle'.trans hk0le

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def RegularityR2 (X : PJ D B P j) (E : PtExt X)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop) : Prop :=
  (∀ (wL wE : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (et : B.Cusp j wE)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (c : ℝ), 0 ≤ c → NoZero gens →
    (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc wE et) ∧ (X.vAt la y (X.inc wE et) ≠ ⊤ →
      (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (X.vAt la y (X.inc wE et)).toReal : ℝ) : EReal))) →
    ∀ la (y' : E.Pt' la), 0 ≤ E.vAt' la y' (X.inc wE et) ∧ (E.vAt' la y' (X.inc wE et) ≠ ⊤ →
      (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (E.vAt' la y' (X.inc wE et)).toReal : ℝ) : EReal))) ∧
  (∀ (wL : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    NoZero gens →
    (∀ la (y : X.Pt la), (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal)) →
    ∀ la (y' : E.Pt' la), (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal))

theorem iInf_span_eq {X : PJ D B P j} {wL : WeightFamilies.Wt D j} {n : ℕ} (g : Fin n → B.Cusp j wL)
    (la : HeightOneSpectrum (𝓞 B.KO)) (v : X.Forms → EReal) (hv0 : v 0 = ⊤)
    (hadd : ∀ F G, min (v F) (v G) ≤ v (F + G))
    (hsmul : ∀ (a : B.KO) F, a ≠ 0 → v (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + v F)
    (hint : ∀ a : 𝓞 B.KO, (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO)) :
    (⨅ F ∈ Submodule.span (𝓞 B.KO) (Set.range g), v (X.inc wL F)) = ⨅ k, v (X.inc wL (g k)) := by
  apply le_antisymm
  · exact le_iInf fun k => iInf₂_le (g k) (Submodule.subset_span (Set.mem_range_self k))
  · refine le_iInf₂ fun F hF => ?_
    induction hF using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact iInf_le _ k
    | zero => simp [hv0]
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]; exact le_trans (le_min hx hy) (hadd _ _)
    | smul a x _ hx =>
      by_cases ha : (a : B.KO) = 0
      · have : a = 0 := by exact_mod_cast ha
        subst this; simp [hv0]
      · have hsm : X.inc wL (a • x) = (a : B.KO) • X.inc wL x := by
          rw [← map_smul]; congr 1; exact (algebraMap_smul B.KO a x).symm
        rw [hsm, hsmul _ _ ha]
        have h0 : (0 : EReal) ≤ (((vAdd la (a : B.KO) : ℤ) : ℝ) : EReal) := by
          exact_mod_cast hint a ha
        calc (⨅ k, v (X.inc wL (g k))) = 0 + ⨅ k, v (X.inc wL (g k)) := (zero_add _).symm
          _ ≤ _ := add_le_add h0 hx

def gd2Xplus {ka wL wF : WeightFamilies.Wt D j} {X : PJ D B P j} (G : GlobalFamilyData X ka wL wF) (E : PtExt X)
    (hM : IntAtExt X E) : GlobalFamilyData (xplus X E hM) ka wL wF :=
  ⟨G.N, G.w, G.del, G.th', G.rz, G.alz, G.th0, G.zc, G.rq, G.th, G.iet, G.et, G.mx⟩

theorem combBound_xplus {ka wL wF : WeightFamilies.Wt D j} (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop)
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (c : ℝ) (hc : 0 ≤ c) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hspan : Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL) (hNZ : NoZero G.w)
    (hint : ∀ (la : HeightOneSpectrum (𝓞 B.KO)) (a : 𝓞 B.KO), (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO))
    (hX : CombBound G S c nus) (hR2 : RegularityR2 X E NoZero) :
    CombBound (gd2Xplus G E hM) S c nus := by
  have dX : ∀ la (y : X.Pt la), X.depth S.sW wL la y = ⨅ k, X.vAt la y (X.inc wL (G.w k)) := by
    intro la y
    unfold PJ.depth
    rw [← hspan]
    exact iInf_span_eq G.w la (X.vAt la y) (X.vAt_zero la y) (X.vAt_add la y) (X.vAt_smul la y) (hint la)
  have dE : ∀ la (y : E.Pt' la), (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y (X.inc wL F)) =
      ⨅ k, E.vAt' la y (X.inc wL (G.w k)) := by
    intro la y
    rw [← hspan]
    exact iInf_span_eq G.w la (E.vAt' la y) (E.vAt'_zero la y) (E.vAt'_add la y) (E.vAt'_smul la y) (hint la)
  intro la y
  cases y with
  | inl y0 => exact hX la y0
  | inr y1 =>
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have hc' : 0 ≤ c / (2 * (G.iet : ℝ)) := by positivity
      have := hR2.1 wL _ G.N G.w G.et nus _ hc' hNZ
        (fun la' y => by have h := (hX la' y).1 hj; rw [dX] at h; exact h) la y1
      show 0 ≤ E.vAt' la y1 (X.inc _ G.et) ∧ (E.vAt' la y1 (X.inc _ G.et) ≠ ⊤ →
        (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _)
      rw [dE]; exact this
    · have := hR2.2 wL G.N G.w nus hNZ (fun la' y => by have h := (hX la' y).2 hj; rw [dX] at h; exact h) la y1
      show (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _
      rw [dE]; exact this

section l2NormAlt

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

end l2NormAlt

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RecConj
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  (c : Coeff l)

private theorem rt0_conj_ne_lemma : (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h2
  have hre := Complex.conj_eq_iff_re.mp h2
  have hsq := H.sqrt_neg_disc_sq
  rw [← hre] at hsq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h3 : ((H.rt0.re ^ 2 : ℝ) : ℂ) = ((-(H.d : ℝ) : ℝ) : ℂ) := by push_cast; exact hsq
  have h4 := Complex.ofReal_injective h3
  nlinarith [sq_nonneg H.rt0.re]

theorem not_good_conj {σ : c.F →+* ℂ} (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  unfold GoodEmb at h h'
  simp only [RingHom.comp_apply] at h h'
  rw [h] at h'
  exact rt0_conj_ne_lemma h'

private theorem imaginary_root_conj_lemma_2 : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
  have h1 : ((starRingEnd ℂ) H.rt0) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exact absurd h rt0_conj_ne_lemma
  · exact h

theorem goodOf_conj (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have key : ∀ τ : c.F →+* ℂ, GoodEmb c τ ∨ GoodEmb c ((starRingEnd ℂ).comp τ) := by
    intro τ
    unfold GoodEmb
    simp only [RingHom.comp_apply]
    generalize hxd : (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ = x
    have hx : (x : ℂ) = H.rt0 := by rw [← hxd]; rfl
    have hx2 : x ^ 2 = -((H.d : ℕ) : c.F) := by
      apply Subtype.ext
      have h0 : (x : ℂ) ^ 2 = -((H.d : ℕ) : ℂ) := by rw [hx, H.sqrt_neg_disc_sq]
      exact_mod_cast h0
    have hsq : (τ x) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, hx2, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Or.inl h
    · right
      rw [h, map_neg, imaginary_root_conj_lemma_2, neg_neg]
  unfold goodOf
  by_cases h1 : GoodEmb c σ
  · have h2 := not_good_conj c h1
    rw [if_neg h2, if_pos h1]
    ext x
    simp
  · rcases key σ with h | h
    · exact absurd h h1
    · rw [if_pos h, if_neg h1]

end

variable {D : D7} {T : Core D} (h : LawsCore T)

theorem recB_supN_conj (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (F : (recB h).Cusp j w) :
    (recB h).supN j w ((starRingEnd ℂ).comp σ) F = (recB h).supN j w σ F := by
  simp [recB, mkB, cutN, Core.Ns, goodOf_conj]

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.NumericalH1Condition
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


variable (Xo c) in
def CombAlg {n : ℕ} (ws : Fin n → Rul Xo c) (et : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (c' : ℝ) :
    Prop :=
  ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
    (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v et)


variable (c) in
def nuOf (nus : HeightOneSpectrum (𝓞 c.F) → ℝ) (la : HeightOneSpectrum (𝓞 c.F)) : ℝ :=
  (ramOverZ la : ℝ) * nus la


variable (c) in
def NumericalH1Condition (nus : HeightOneSpectrum (𝓞 c.F) → ℝ) (P s : ℝ) : Prop :=
  (∀ la, 0 ≤ nus la) ∧ (Function.support nus).Finite ∧
    (∑ᶠ la, (ramOverZ la : ℝ) * nus la * logNorm la) / (Module.finrank ℚ c.F : ℝ) ≤ P * s

def OrdTieOn (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)) (la : HeightOneSpectrum (𝓞 c.F)),
    IsNormDiscrete v → IsOver (K := c.F) v la →
    ∃ y : PtV Xo c cls (PY la) (lies la) la,
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) =
          (((ramIdx (K := c.F) v la : ℤ) : ℝ) : EReal) * vAtV y f) ∧
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 →
        (∃ g ∈ sec Xo c a n, evC h Z g ≠ 0) → vAtV y f = ⊤)

theorem OrdTieOn.ordTie {h : GenFrEx Xo c} {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    {cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop} {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (H : OrdTieOn h δ cls PY lies) : OrdTie h δ cls PY lies := fun Z v la hv ho =>
  let ⟨y, hy, _⟩ := H Z v la hv ho
  ⟨y, hy⟩

theorem one_le_ramIdx {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)} (hv : IsNormDiscrete v)
    (ho : IsOver (K := K) v la) : 1 ≤ ramIdx (K := K) v la := by
  unfold ramIdx
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hK : ((a : K)) ≠ 0 := by exact_mod_cast ha0
  have hne : v (algebraMap K Ω (a : K)) ≠ ⊤ := hv.1 _ ((map_ne_zero _).2 hK)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
  refine le_csInf ⟨n, a, ha, ha0, hn.symm⟩ ?_
  rintro m ⟨b, hb, _, hbm⟩
  have h1 := (ho b).2 hb
  rw [hbm] at h1
  have h0 : (0 : ℤ) < m := by exact_mod_cast h1
  omega

section H1

variable [Fintype (Comp Xo c)] (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nus : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

theorem height_H1_of_data {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (hreg : regular₂ Xo c U)
    (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2) (hw : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2)
    (he : etR ∈ cusp Xo c U uet.1 uet.2) (hnz : NoCommonZero Xo c wR) (hetZ : NZAt h etR)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2) (hcc : 0 ≤ cc)
    (hcomb : CombAlg Xo c wR etR (nuOf c nus) (cc / (2 * (i : ℝ))))
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop)
    (htie : OrdTieOn h δ cls PY lies) (hnu : NumericalH1Condition c nus PN (wsize (wtZ uL.1 uL.2))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R
      (nuOf c nus) ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).FinitePlaceHyp := by
  classical
  refine ⟨fun la => mul_nonneg (Nat.cast_nonneg _) (hnu.1 la), ?_, hnu.2.2, ?_⟩
  · refine hnu.2.1.subset fun la hla => ?_
    rw [Function.mem_support] at hla ⊢
    intro h0
    apply hla
    show (ramOverZ la : ℝ) * nus la = 0
    rw [h0, mul_zero]
  · intro Z v la hadm hover
    show ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0},
        ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ) ≤
      (ramIdx (K := c.F) v la : ℝ) * nuOf c nus la +
        cc / (2 * (i : ℝ)) * (ordC (δ Z v) v ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) : ℝ)
    rw [← huet]
    have hv : IsNormDiscrete v := hadm.1
    obtain ⟨y, hty, hzero⟩ := htie Z v la hv hover
    obtain ⟨T', io, e, ho, z, _, eta, _, hq⟩ := y.2
    let y1 : PtV Xo c (trivialClassCondition Xo c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho z trivial () trivial
    have hyv : vAtV y1 = vAtV y := funext fun g => by
      show y1.1.1 g = y.1.1 g
      rw [hq]
      rfl
    have hc' : (0 : ℝ) ≤ cc / (2 * (i : ℝ)) := div_nonneg hcc (by positivity)
    have hR := (hreg.1.2 ⟨uL, hdL⟩ ⟨uet, hdE⟩ (N + 1) (fun k => ⟨wR k, hw k⟩) ⟨etR, he⟩ (nuOf c nus)
      (cc / (2 * (i : ℝ))) hc' hnz (fun la' y0 => hcomb la' y0.1 y0.2)).1 la ⟨vAtV y1, y1, rfl⟩
    have hR' : 0 ≤ vAtV y etR ∧ (vAtV y etR ≠ ⊤ →
        (⨅ k, vAtV y (wR k)) ≤ ((nuOf c nus la : ℝ) : EReal) + ((cc / (2 * (i : ℝ)) : ℝ) : EReal) * vAtV y etR) := by
      rw [← hyv]
      exact hR
    have he1 : 1 ≤ ramIdx (K := c.F) v la := one_le_ramIdx hv hover
    have hepos : (0 : ℝ) < (ramIdx (K := c.F) v la : ℝ) := by
      exact_mod_cast (show (0 : ℤ) < ramIdx (K := c.F) v la by omega)
    have hE := (hty uet.1 uet.2 etR (cusp_le_sec Xo c U _ _ he) (hetZ Z))
    have htopE : vAtV y etR ≠ ⊤ := by
      intro htop
      rw [htop, EReal.mul_top_of_pos (by exact_mod_cast hepos)] at hE
      exact EReal.coe_ne_top _ hE
    obtain ⟨x, hx⟩ : ∃ x : ℝ, vAtV y etR = (x : EReal) :=
      ⟨_, (EReal.coe_toReal htopE (vAtV_ne_bot y etR)).symm⟩
    have hB := hR'.2 htopE
    rw [hx, ← EReal.coe_mul, ← EReal.coe_add] at hB
    rw [hx, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at hE
    obtain ⟨k0, hk0⟩ : ∃ k0, vAtV y (wR k0) = ⨅ k, vAtV y (wR k) := exists_eq_ciInf_of_finite
    rw [← hk0] at hB
    have hk0Z : evC h Z (wR k0) ≠ 0 := by
      intro h0
      rw [hzero uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hw k0)) h0
        ⟨wR (jc Z), cusp_le_sec Xo c U _ _ (hw (jc Z)), hwb Z⟩] at hB
      exact absurd hB (not_le.2 (EReal.coe_lt_top _))
    have hW := hty uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hw k0)) hk0Z
    have htopW : vAtV y (wR k0) ≠ ⊤ := fun ht => by
      rw [ht] at hB
      exact absurd hB (not_le.2 (EReal.coe_lt_top _))
    obtain ⟨t, ht⟩ : ∃ t : ℝ, vAtV y (wR k0) = (t : EReal) :=
      ⟨_, (EReal.coe_toReal htopW (vAtV_ne_bot y _)).symm⟩
    rw [ht, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at hW
    rw [ht, EReal.coe_le_coe_iff] at hB
    calc ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0},
          ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ)
        ≤ (ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) : ℝ) :=
          Int.cast_le.2 (ciInf_le (f := fun j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0} =>
            ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z)) (Set.finite_range _).bddBelow
            ⟨k0, valC_ne_zero (a := uL.1) (n := uL.2) hk0Z⟩)
      _ = (ramIdx (K := c.F) v la : ℝ) * t := hW
      _ ≤ (ramIdx (K := c.F) v la : ℝ) * (nuOf c nus la + cc / (2 * (i : ℝ)) * x) :=
          mul_le_mul_of_nonneg_left hB hepos.le
      _ = (ramIdx (K := c.F) v la : ℝ) * nuOf c nus la +
            cc / (2 * (i : ℝ)) * ((ramIdx (K := c.F) v la : ℝ) * x) := by ring
      _ = _ := by rw [← hE]

end H1

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.MuValFix
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem MuVal.eq_one_of_fixed {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ}
    (h : MuVal V χ mu) (y : (AE D)ˣ)
    (hy : sigR (AF D.host.F) D.sp.cm.sig (y : AE D) = y) : χ y = 1 := by
  obtain ⟨x, hx⟩ := h.1 1
  have hxy : IsDetRoot V 1 (x * y) := by
    unfold IsDetRoot at hx ⊢
    rw [Units.val_mul, map_mul, hy, ← mul_assoc, ← hx]
  have e2 := h.2 1 (x * y) hxy
  rw [h.2 1 x hx, map_mul] at e2
  have e3 : χ x * 1 = χ x * χ y := by
    apply Subtype.ext
    simpa [Circle.coe_mul] using e2
  exact (mul_left_cancel e3).symm

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RegularityR1ValuedPoints
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CompTieA
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem vAtV_mem_valSet {cls cls' : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop}
    (hc : ∀ T io y, cls T io y → cls' T io y) {PY : Type}
    {lies : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) :
    vAtV y ∈ valSet Xo c cls' la := by
  unfold vAtV valSet
  refine ⟨⟨((y.1).1, ()), ?_⟩, rfl⟩
  obtain ⟨T, io, e, hO, y1, hcl, eta, -, hy⟩ := y.2
  refine ⟨T, io, e, hO, y1, hc T io y1 hcl, (), trivial, ?_⟩
  rw [hy]
  rfl

theorem valC_add (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f g : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (f + g) Z = valC h a n f Z + valC h a n g Z := by
  simp only [valC, evC, evR]
  rw [evalAt_add, AddMonoidAlgebra.single_add]

theorem valC_zero (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Z : Comp Xo c) :
    valC h a n 0 Z = 0 := by
  simp only [valC, evC, evR]
  rw [evalAt_zero, AddMonoidAlgebra.single_zero]

theorem valC_smul_ct (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : c.F) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (t • f) Z = algebraMap c.F (AC Z) t * valC h a n f Z := by
  simp only [valC, evC, evR]
  rw [evalAt_smul, ← Algebra.smul_def, ← Algebra.smul_def, AddMonoidAlgebra.smul_single]

theorem evC_ne_zero_of_valC {h : GenFrEx Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} {Z : Comp Xo c}
    (hf : valC h a n f Z ≠ 0) : evC h Z f ≠ 0 := by
  intro h0
  apply hf
  unfold valC
  rw [h0, AddMonoidAlgebra.single_zero]

end Formalism.L2.Pj
end
end

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IntAlg (f : Rul Xo c) : Prop := ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f

theorem intAlg_zero : IntAlg (0 : Rul Xo c) := by
  intro la v hv
  simp only [valSet, Set.mem_setOf_eq] at hv
  obtain ⟨y, rfl⟩ := hv
  unfold vAtV
  obtain ⟨⟨w, q⟩, T, io, e, ho, z, hz, eta, -, hw⟩ := y
  unfold profI at hw
  obtain ⟨rfl, -⟩ := Prod.mk.inj hw
  simp [evI, evR, evalAt, nval]

theorem intAlg_add {f g : Rul Xo c} (hf : IntAlg f) (hg : IntAlg g) : IntAlg (f + g) := fun la v hv =>
  (le_min (hf la v hv) (hg la v hv)).trans ((isVal_valSet la v hv).add f g)

theorem intAlg_smul (a : 𝓞 c.F) {f : Rul Xo c} (hf : IntAlg f) : IntAlg (a • f) := fun la v hv => by
  have e : (a • f : Rul Xo c) = (a : c.F) • f := rfl
  rw [e]
  by_cases ha : (a : c.F) = 0
  · set_option synthInstance.maxHeartbeats 200000 in
      rw [ha, zero_smul, (isVal_valSet la v hv).zero]
    exact le_top
  · rw [(isVal_valSet la v hv).smul _ _ ha]
    exact add_nonneg (by exact_mod_cast vAdd_int_nonneg la ha) (hf la v hv)

theorem intAlg_span {s : Set (Rul Xo c)} (hs : ∀ f ∈ s, IntAlg f) {f : Rul Xo c}
    (hf : f ∈ Submodule.span (𝓞 c.F) s) : IntAlg f := by
  induction hf using Submodule.span_induction with
  | mem x h => exact hs x h
  | zero => exact intAlg_zero
  | add x y _ _ hx hy => exact intAlg_add hx hy
  | smul a x _ hx => exact intAlg_smul a hx


variable (Xo c) in
def RegularityR1ValuedPoints (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, IntAlg f →
    ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f

theorem ramIdx_nonneg {Ω : Type} [Field Ω] [Algebra c.F Ω] {v : AddValuation Ω (WithTop ℤ)}
    {la : HeightOneSpectrum (𝓞 c.F)} (ho : IsOver (K := c.F) v la) : 0 ≤ ramIdx (K := c.F) v la := by
  unfold ramIdx
  have hpos : ∀ n ∈ {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v ((algebraMap c.F Ω) ↑a) = ↑n}, 0 ≤ n := by
    rintro n ⟨a, ha, -, hv⟩
    have h := (ho a).mpr ha
    rw [hv] at h
    exact_mod_cast h.le
  rcases Set.eq_empty_or_nonempty
      {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v ((algebraMap c.F Ω) ↑a) = ↑n} with he | hne
  · rw [he, Int.csInf_empty]
  · exact hpos _ (Int.csInf_mem hne ⟨0, hpos⟩)

variable (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
  (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
  (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop)

theorem ord_nonneg_of [Nonempty (HeightOneSpectrum (𝓞 c.F))]
    (hT : OrdTie h δ cls PY lies) (hTQ : OrdTieQ h δ) (hR1 : RegularityR1ValuedPoints Xo c C cls PY lies) (hR1Q : RegularityR1Quotient Xo c C)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {F : Rul Xo c} (hFs : F ∈ sec Xo c a n) (hFC : F ∈ C a n) (hF : IntAlg F)
    {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)} (hd : IsNormDiscrete v)
    (hv : (∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) (hne : evC h Z F ≠ 0) :
    0 ≤ ordC (δ Z v) v (wtZ a n) (valC h a n F Z) := by
  have key : (0 : EReal) ≤ (((ordC (δ Z v) v (wtZ a n) (valC h a n F Z) : ℤ) : ℝ) : EReal) := by
    rcases hv with ⟨la, ho⟩ | ht
    · obtain ⟨y, hy⟩ := hT Z v la hd ho
      rw [hy a n F hFs hne]
      exact mul_nonneg (by exact_mod_cast ramIdx_nonneg ho) (hR1 a n F hFC hF la y)
    · obtain ⟨q, hq⟩ := hTQ Z v hd ht
      rw [hq a n F hFs hne]
      obtain ⟨la⟩ := ‹Nonempty (HeightOneSpectrum (𝓞 c.F))›
      exact hR1Q a n F hFC ⟨la, hF la⟩ q
  exact_mod_cast key

theorem mem_of_mem_span_int (S : Submodule c.F (Rul Xo c)) {s : Set (Rul Xo c)} (hs : s ⊆ S) {F : Rul Xo c}
    (hF : F ∈ Submodule.span (𝓞 c.F) s) : F ∈ S := by
  induction hF using Submodule.span_induction with
  | mem x h => exact hs h
  | zero => exact S.zero_mem
  | add x y _ _ hx hy => exact S.add_mem hx hy
  | smul a x _ hx => exact S.smul_mem (a : c.F) hx


omit δ C cls PY lies in
theorem exists_of_mem_span_valG {u : WtR E} {ι : Type} {R : ι → Rul Xo c} {x : ∀ Z : Comp Xo c, AC Z}
    (hx : x ∈ (letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun _ => Algebra.toModule
      Submodule.span (𝓞 c.F) (Set.range fun k => valG h u (R k)))) :
    ∃ F ∈ Submodule.span (𝓞 c.F) (Set.range R), x = valG h u F := by
  try dsimp only at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact ⟨R k, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
  | zero => exact ⟨0, zero_mem _, funext fun Z => (valC_zero h u.1 u.2 Z).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨F, hF, rfl⟩ := hy
    obtain ⟨G, hG, rfl⟩ := hz
    exact ⟨F + G, add_mem hF hG, funext fun Z => (valC_add h u.1 u.2 F G Z).symm⟩
  | smul a y _ hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    refine ⟨a • F, Submodule.smul_mem _ a hF, funext fun Z => ?_⟩
    refine (Algebra.smul_def a (valG h u F Z)).trans ?_
    rw [IsScalarTower.algebraMap_apply (𝓞 c.F) c.F (AC Z)]
    exact (valC_smul_ct h u.1 u.2 (a : c.F) F Z).symm

section LawA2Of

variable [Fintype (Comp Xo c)]
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

end LawA2Of

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.OneCusp
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open scoped ComplexConjugate

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem not_isIso_of_p0_zero (X : Data E r) (h0 : X.p0 = 0) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, hh, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (X.cmType τ).2 h⟩
  obtain ⟨P, hP, hG⟩ := X.signature ⟨τ, hτ⟩
  set v : Fin r → ℂ := fun a => τ (ξ a) with hv
  set w : Fin r → ℂ := P⁻¹.mulVec v with hw
  have hPw : P.mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have h1 : hermC τ X.Gm v v = 0 := by
    have := congrArg τ hh
    rw [map_zero] at this
    rw [← this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermC, herm, map_sum, map_mul, hv, cc, IsCMField.complexEmbedding_complexConj]
  have h2 : hermC τ X.Gm v v = ∑ a, ∑ b, w a * gram τ X.Gm P a b * conj (w b) := by
    have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
        ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := fun f =>
      calc ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ x, ∑ a, ∑ y, ∑ b, f x y a b :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ y, ∑ b, f x y a b := Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ b, ∑ y, f x y a b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have L : ∀ x y, P.mulVec w x * τ (X.Gm x y) * conj (P.mulVec w y) =
        ∑ a, ∑ b, w a * (P x a * τ (X.Gm x y) * conj (P y b)) * conj (w b) := by
      intro x y
      simp only [Matrix.mulVec, dotProduct]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]; ring
    rw [← hPw]
    simp only [hermC, L, gram, col, Matrix.of_apply]
    rw [sw]
    simp only [Finset.mul_sum, Finset.sum_mul]
  have h3 : ∑ a, Complex.normSq (w a) = 0 := by
    rw [h2, hG] at h1
    have : ∑ a, (Complex.normSq (w a) : ℂ) = 0 := by
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ hb.symm]) (by simp)]
      simp [sgn, h0, Complex.mul_conj]
    exact_mod_cast this
  have h4 : w = 0 := funext fun a => Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg _).mp h3 a (Finset.mem_univ a))
  apply hne
  funext a
  have : v a = 0 := by rw [← hPw, h4, Matrix.mulVec_zero]; rfl
  exact (map_eq_zero τ).mp this

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

theorem dom_zero : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩

end

variable {D : D7} {T : Core D}

end Formalism.L2.Pj
end
end
