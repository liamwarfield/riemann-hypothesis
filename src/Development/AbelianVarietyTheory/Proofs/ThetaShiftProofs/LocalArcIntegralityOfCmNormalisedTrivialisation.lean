module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FinLocalAtOfIntModel
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDataDescendsPrincipalIdealSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SplitBaseChange
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.BoxCubicalUnconditional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsKeyIntegral
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcGamma

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (h : IsLieBasis v) : IsLieBasis fun i : Fin m => v (i.cast e) := by
  subst e
  exact h

theorem isLieComb_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    IsLieComb (fun i : Fin m => c (i.cast e)) (fun i : Fin m => v (i.cast e)) w := by
  subst e
  exact h

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (Chart.dualMapR g) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR (g.comp f)) := by
  rw [spMap_comp_spMap]
  refine congrArg spMap (RingHom.ext fun x => ?_)
  ext <;> simp [Chart.dualMapR]

section Pull

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {f : A →+* A'} {D₀ : Out.DegPre A}
  {D₁ : Out.DegPre A'} (p : Out.IsPullDeg f D₀ D₁)
include p

theorem g_eq : D₁.P.g = D₀.P.g :=
  H1.dim_unique _ D₁.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec D₁.P.A (Classical.arbitrary (PrimeSpectrum A')))

theorem keyPB_of_pull {th : D₀.P.L.Sec} {th₁ : D₁.P.L.Sec} (h : ThBC p th th₁) {g₀ n₀ g₁ n₁ v hv v₁ hv₁}
    (hvv : ∀ i, (v₁ i).left ≫ prj p = spMap (Chart.dualMapR f) ≫ (v (i.cast (g_eq p))).left) :
    KeyPB ⟨D₁.P, g₁, D₁.rig, D₁.rig_gen, th₁, n₁, v₁, hv₁⟩ ⟨D₀.P, g₀, D₀.rig, D₀.rig_gen, th, n₀, v, hv⟩ f := by
  refine ⟨prj p, p.he, p.w, g_eq p, Chart.dualMapR f, pull_grp p, p.w_gen, p.w_rig,
    KeyPow.appLE_eq_of_stalk _ th th₁ ((ArcQBC.through_iff _ _).1 h), fun a => ?_, ?_, hvv⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end Pull

section Val

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {V Fr : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field Fr] [Algebra V Fr] [IsFractionRing V Fr] {io : K →+* Fr}

theorem mem_range_iff (h : OverLa w V io 1) (y : K) :
    io y ∈ Set.range (algebraMap V Fr) ↔ w.valuation K y ≤ 1 := by
  have e : io y ∈ Set.range (algebraMap V Fr) ↔ valV V (io y) ≤ 1 :=
    ⟨fun ⟨r, hr⟩ => hr ▸ HeightOneSpectrum.valuation_le_one _ r,
      fun hy => IsDiscreteValuationRing.exists_lift_of_le_one hy⟩
  rw [e]
  by_cases hy : y = 0
  · simp [hy]
  have h1 := h.2 y
  simp only [vV, vLa, Nat.cast_one, _root_.one_mul, neg_inj] at h1
  have a : valV V (io y) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hy)
  have b : w.valuation K y ≠ 0 := ((w.valuation K).ne_zero_iff).2 hy
  rw [← WithZero.log_le_log a one_ne_zero, ← WithZero.log_le_log b one_ne_zero, h1]

theorem vV_eq_neg_count (h : OverLa w V io 1) {gm : Fr} {ca : K} {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
    (hc : IsLocGen w ca I) (u : Vˣ) (e : gm⁻¹ = io ca * algebraMap V Fr u) : vV V gm = -FractionalIdeal.count K w I := by
  have hu : valV V (algebraMap V Fr u) = 1 := by
    refine eq_one_of_one_le_mul_left (HeightOneSpectrum.valuation_le_one _ (u : V))
      (HeightOneSpectrum.valuation_le_one (K := Fr) (IsDiscreteValuationRing.maximalIdeal V) ((u⁻¹ : Vˣ) : V)) ?_
    rw [valV, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h1 := h.2 ca
  have h2 := congrArg (valV V) e
  rw [map_mul, hu, _root_.mul_one, map_inv₀, inv_eq_iff_eq_inv] at h2
  simp only [vV, vLa, Nat.cast_one, _root_.one_mul, neg_inj] at h1
  rw [vV, h2, WithZero.log_inv, h1, valuation_eq_exp_count w hc.1, hc.2]
  simp

end Val

theorem exists_ringHom {K R V Fr : Type} [Field K] [CommRing R] [Algebra R K] [CommRing V] [Field Fr] [Algebra V Fr]
    (hi : Function.Injective (algebraMap V Fr)) (io : K →+* Fr)
    (h : ∀ r : R, io (algebraMap R K r) ∈ Set.range (algebraMap V Fr)) :
    ∃ j : R →+* V, (algebraMap V Fr).comp j = io.comp (algebraMap R K) := by
  choose j hj using h
  exact ⟨⟨⟨⟨j, hi (by simp [hj])⟩, fun a b => hi (by simp [hj])⟩, hi (by simp [hj]), fun a b => hi (by simp [hj])⟩,
    RingHom.ext hj⟩

theorem exists_keyIntegral {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {V Fr : Type} [CommRing V]
    [IsDomain V] [Field Fr] [Algebra V Fr] (hi : Function.Injective (algebraMap V Fr)) {io : K →+* Fr}
    (hval : ∀ y : K, io y ∈ Set.range (algebraMap V Fr) ↔ w.valuation K y ≤ 1)
    {D : Out.DegPre K} {DV : Out.DegPre V} {DF : Out.DegPre Fr} (pw : Out.IsPullDeg (algebraMap V Fr) DV DF)
    (pK : Out.IsPullDeg io D DF) {th : D.P.L.Sec} {thw : DV.P.L.Sec} {th₁ th₂ : DF.P.L.Sec} {gm : Fr} (hgm : gm ≠ 0)
    (nw : ThNZ thw) (h₁ : ThBC pw thw th₁) (h₂ : ThBC pK th th₂) (hm : ThMul gm th₁ th₂) {g₀ n₀ v hv}
    {B : Out.PolAV (Sp (𝓞 K))} {φ : D.P.A.left ⟶ B.A.left}
    (hφ : IsGrpPullback D.P.A B.A (spMap (algebraMap (𝓞 K) K)) φ) {ρ : 𝓞 K →+* V} {ψ : DV.P.A.left ⟶ B.A.left}
    (hρ : ∀ x, algebraMap V Fr (ρ x) = io (x : K)) (hψ : IsGrpPullback DV.P.A B.A (spMap ρ) ψ)
    (hc : prj pw ≫ ψ = prj pK ≫ φ) {M : Matrix (Fin D.P.g) (Fin D.P.g) K}
    (hM : IsModelAt B ⟨D.P, g₀, D.rig, D.rig_gen, th, n₀, v, hv⟩ φ w M) :
    ∃ x' : KeyIn Fr, KeyPB x' ⟨D.P, g₀, D.rig, D.rig_gen, th, n₀, v, hv⟩ io ∧ KeyIntegral V x' gm⁻¹ (io M.det) := by
  obtain ⟨R, _, _, _, _, _, ρR, xR, φR, hg, hρR, hvalR, hfib, -, hw⟩ := hM
  obtain ⟨j, hj⟩ := exists_ringHom hi io fun r : R => (hval _).2 ((hvalR _).1 ⟨r, rfl⟩)
  have hjρ : j.comp ρR = ρ := RingHom.ext fun x => hi (by
    rw [hρ, RingHom.comp_apply, ← RingHom.comp_apply (algebraMap V Fr), hj, RingHom.comp_apply,
      ← RingHom.comp_apply (algebraMap R K), hρR])
  have hG : IsGrpPullback xR.P.A B.A (spMap ρR) φR := hfib.1
  have n : IsGrpPullback DV.P.A B.A (spMap j ≫ spMap ρR) ψ :=
    hψ.congr (by rw [spMap_comp_spMap]; exact congrArg spMap hjρ.symm) rfl
  have sq : ψ ≫ B.A.hom = (DV.P.A.hom ≫ spMap j) ≫ spMap ρR := n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := hG.1.lift_fst _ _ sq
  have e₂ := hG.1.lift_snd _ _ sq
  generalize hG.1.lift _ _ sq = ψ' at e₁ e₂
  have hψ' : IsGrpPullback DV.P.A xR.P.A (spMap j) ψ' := hG.cancel (e₁ ▸ n) e₂
  have eK : DF.P.g = D.P.g := g_eq pK
  have eV : DF.P.g = DV.P.g := g_eq pw
  have eR : DV.P.g = xR.P.g := eV.symm.trans (eK.trans hg.symm)
  have := D.P.isAb.comm
  have := DV.P.isAb.comm
  have := DF.P.isAb.comm
  have := xR.P.isAb.comm
  obtain ⟨vV, hvV, eVv⟩ := exists_isLieBasis_baseChange R V j _ _ ψ' hψ' xR.P.isAb.smooth _ _ (isLieBasis_cast eR xR.basis)
  obtain ⟨v₁, hv₁, ev₁⟩ := exists_isLieBasis_baseChange V Fr _ _ _ (prj pw) (pull_grp pw) DV.P.isAb.smooth _ _
    (isLieBasis_cast eV hvV)
  obtain ⟨v₂, hv₂, ev₂⟩ := exists_isLieBasis_baseChange K Fr _ _ _ (prj pK) (pull_grp pK) D.P.isAb.smooth _ _
    (isLieBasis_cast eK hv)
  have gF : 1 ≤ DF.P.g := eK ▸ g₀
  refine ⟨⟨DF.P, gF, DF.rig, DF.rig_gen, th₂, ArcQBC.thNZ_of_thBC pK h₂ n₀, v₂, hv₂⟩, keyPB_of_pull pK h₂ ev₂,
    th₁, ArcQBC.thNZ_of_thBC pw h₁ nw, v₁, hv₁, (M.submatrix (Fin.cast eK) (Fin.cast eK)).map io,
    ⟨DV.P, eV ▸ gF, DV.rig, DV.rig_gen, thw, nw, vV, hvV⟩, fun i => ?_, fun i => ?_, ?_, keyPB_of_pull pw h₁ ev₁⟩
  · show th₁.f i = constFn DF.P.A.hom _ gm⁻¹ * th₂.f i
    rw [hm i, ← _root_.mul_assoc, ← KeyPow.constFn_mul, inv_mul_cancel₀ hgm, KeyPow.constFn_one, _root_.one_mul]
  · obtain ⟨wK, hwK, hwK'⟩ := hw (i.cast eK)
    refine (lieComb_baseChange K Fr io _ _ (prj pK) (pull_grp pK) _ _ wK _ v₂ (v₁ i) ev₂ (isLieComb_cast eK hwK)).1
      (hφ.1.hom_ext ?_ ?_)
    · have hd : Formalism.L2.Pj.dualMap (algebraMap R K) = Chart.dualMapR (algebraMap R K) := rfl
      rw [Category.assoc, ← hc, ← Category.assoc, ev₁, ← e₁, Category.assoc, ← Category.assoc (vV _).left, eVv,
        Category.assoc, Category.assoc, hwK', hd, ← Category.assoc, ← Category.assoc (spMap (Chart.dualMapR io)),
        dual_comp, dual_comp, hj]
      rfl
    · rw [Category.assoc, (pull_grp pK).1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (LieCombBaseChange.dualMap_over io).symm
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact congrArg io (Matrix.det_submatrix_equiv_self (finCongr eK) M)

theorem vV_gamma : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → M.γ ≠ 0 → vV Tv.V M.γ = -FractionalIdeal.count K₁ w s.Tl.I := by
  intro _ E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ hO hρ hψ hc _ hgm
  obtain ⟨-, -, -, hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloc, -, hmod⟩ := s.good
  obtain ⟨N, hN, hL⟩ := hmod w
  obtain ⟨th₁, th₂, h₁, h₂, hm⟩ := M.th_tie
  have hval := mem_range_iff hO
  obtain ⟨x', hPB, hInt⟩ := exists_keyIntegral (IsFractionRing.injective Tv.V Tv.Fr) hval M.pw M.pK hgm M.thw_nz h₁ h₂ hm
    hB.1 hρ hψ.2.1 hc hN
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ca, _, _, _, -, -, -, -, -, hca, -⟩ := hloc w
  obtain ⟨u, hu⟩ := KeyVal.integral_section_unit K₁ _ _ _ w (hloc w) Tv.V Tv.Fr io x' _ _ ca N.det 1 hval hPB hInt hL
    (by simp) hca
  exact vV_eq_neg_count hO hca u hu

end GlobalTheory.ArcGamma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInOverValuationRing
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem isPolFibre_prj {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'}
    {D₀ : Out.DegPre R} {D₁ : Out.DegPre R'} (p : Out.IsPullDeg f D₀ D₁) : IsPolFibre f D₀.P D₁.P (prj p) :=
  ⟨H1.dim_unique _ D₁.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec D₁.P.A (Classical.arbitrary (PrimeSpectrum R'))), pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem exists_arcIn_over_valuationRing : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (ρ : 𝓞 K₁ →+* Tv.V) (O : Type) [CommRing O] (β : O →+* c.F) (b : O →+* Tv.V), (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → (∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (β x))) → ∃ (aw : ArcIn Dw l β Tv.V b) (aK : ArcIn Dw l (RingHom.id c.F) Tv.Fr (io.comp (algebraMap c.F K₁))) (pw : Out.IsPullDeg (algebraMap Tv.V Tv.Fr) aw.D₀ aK.D₀) (pK : Out.IsPullDeg io a.D₀ aK.D₀) (ψ : aw.D₀.P.A.left ⟶ s.B.A.left), InBC (algebraMap Tv.V Tv.Fr) aw (aK.restrict β) pw ∧ InBC io a aK pK ∧ IsPolFibre ρ s.B aw.D₀.P ψ ∧ prj pw ≫ ψ = prj pK ≫ s.φB ∧ TauCan aw.D₀ n' := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s Tv io ρ O _ β b hρ hb
  letI := H.starRing
  obtain ⟨aK, pK, hBC, -⟩ := GlobalTheory.ArcPull.exists_isBC hK.laws.polBaseChange hK.laws.globalFns a io io.injective
  have hB : IsPolFibre (algebraMap (𝓞 K₁) K₁) s.B a.D₀.P s.φB :=
    (isFibreOf_iff_isPolFibre _ _ _ s.B s.toCMPart.xB s.φB).1 s.good.2.2.2.1
  obtain ⟨Pv, ψ, hψ⟩ := exists_isPolFibre hK.laws.polBaseChange ρ s.B
  have hcomp : io.comp (algebraMap (𝓞 K₁) K₁) = (algebraMap Tv.V Tv.Fr).comp ρ :=
    RingHom.ext fun x => (hρ x).symm
  have hχ : IsPolFibre ((algebraMap Tv.V Tv.Fr).comp ρ) s.B aK.D₀.P (prj pK ≫ s.φB) :=
    hcomp ▸ GlobalTheory.CM.EllComp.isPolFibre_comp hB (isPolFibre_prj pK)
  obtain ⟨φ, hφψ, hφ⟩ := GlobalTheory.CM.EllComp.exists_isPolFibre_lift hψ hχ
  obtain ⟨DV, p, rfl, hp, hq⟩ := GlobalTheory.T.exists_degenerationData_extension_over_dvr hK Tv.V Tv.Fr Pv aK.D₀ φ hφ
  obtain rfl : prj p = φ := eq_of_heq hp
  obtain ⟨oB, hoB⟩ := polOActPull _ _ _ s.B DV.P ψ hψ.2.1 hψ.2.2 (𝓞 E) s.oa
  have htau : TauCan aK.D₀ n' :=
    (GlobalTheory.T.isTauCanonical_iff_of_isPullDeg_tauBimult hK K₁ Tv.Fr io a.D₀ aK.D₀ pK n' io.injective a.bimult aK.bimult).1 s.tau
  have hact : ∀ x, (aK.oa.onB.act x).left ≫ prj p = prj p ≫ (oB.act x).left := fun x => by
    have h₁ : (aK.oa.onB.act x).left ≫ prj pK = prj pK ≫ (a.oa.onB.act x).left := hBC.act x
    have w := hφ.2.1.1.w
    generalize prj p = u at hφψ w ⊢
    generalize prj pK = u' at hφψ h₁
    refine hψ.2.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hoB, reassoc_of% hφψ, hφψ, reassoc_of% h₁, s.act]
    · rw [Category.assoc, Category.assoc, Over.w, w, ← Category.assoc, Over.w]
  obtain ⟨aw, pw, rfl, hpw, hin, ht⟩ := GlobalTheory.T.arcData_descends_principalIdealSubring hK E H Dw l c O β Tv.V Tv.Fr (algebraMap Tv.V Tv.Fr) b
    ((io.comp (algebraMap c.F K₁)).comp β) (aK.restrict β) DV p n' oB (IsFractionRing.injective _ _)
    (RingHom.ext fun x => (hb x).symm) s.n_pos htau hact (fun v => hq _ _ aK.bimult) (fun v => hq _ _ aK.bimult)
  obtain rfl : pw = p := eq_of_heq hpw
  exact ⟨aw, aK, pw, pK, ψ, hin, (inBC_iff_isBC io a aK pK).2 hBC, hψ, hφψ, ht⟩

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbelianLetterIntegral
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.EtaInt

open GlobalTheory.CM.IntCoord (sc)

theorem sc_mul {S : Type} [CommRing S] (s t : S) : sc s ≫ sc t = sc (s * t) := by
  refine Over.OverMorphism.ext ((spMap_comp_spMap _ _).trans ?_)
  show spMap _ = spMap _
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR, _root_.mul_assoc]

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  refine (spMap_comp_spMap _ _).trans ?_
  change spMap ((dualMap g).comp (dualMap f)) = spMap (dualMap (g.comp f))
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem sc_over {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} {G : Over (Sp A)} {G' : Over (Sp B)}
    {φ : G'.left ⟶ G.left} {v : epsR A ⟶ G} {v' : epsR B ⟶ G'} (h : v'.left ≫ φ = spMap (dualMap f) ≫ v.left) (a : A) :
    (sc (f a) ≫ v').left ≫ φ = spMap (dualMap f) ≫ (sc a ≫ v).left := by
  show (spMap (epsScaleR (f a)) ≫ v'.left) ≫ φ = spMap (dualMap f) ≫ spMap (epsScaleR a) ≫ v.left
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ v.left) (LieCombBaseChange.dualMap_epsScale f a).symm

theorem eq_sc_of_isLieComb {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G] {n : ℕ} {v : Fin n → (epsR S ⟶ G)}
    {c : Fin n → S} {a : S} {u w : epsR S ⟶ G} (hu : IsLieComb c v u) (hw : IsLieComb (a • c) v w) : w = sc a ≫ u := by
  rw [CM.IntCoord.isLieComb_iff] at hu hw
  have e := map_list_prod (Geo.Tor.preHom (G := G) (sc a)) (List.ofFn fun i => sc (c i) ≫ v i)
  rw [List.map_ofFn, ← hu] at e
  refine hw.trans (Eq.trans ?_ e.symm)
  congr 2
  funext i
  show sc (a * c i) ≫ v i = sc a ≫ sc (c i) ≫ v i
  rw [← Category.assoc, sc_mul]

theorem isTangent_sc {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G] {v : epsR S ⟶ G} (h : IsTangent v) (a : S) :
    IsTangent (sc a ≫ v) := by
  show _ ≫ spMap (epsScaleR a) ≫ v.left = _
  rw [← Category.assoc, spMap_comp_spMap]
  refine Eq.trans (congrArg (fun q => spMap q ≫ v.left) (RingHom.ext fun x => ?_)) h
  simp [epsScaleR]

theorem c_pow_of_pull {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] {f : A →+* B}
    {D : Out.DegPre A} {D' : Out.DegPre B} (p : Out.IsPullDeg f D D') {n : ℕ} (h : ∀ y, D.c y ^ n = 1) (y : D'.X) :
    D'.c y ^ n = 1 := by
  have gp := pull_grp p
  let U : Over.mk ((𝟙_ (Over (Sp B))).hom ≫ spMap f) ⟶ 𝟙_ (Over (Sp A)) := toUnit _
  have hU : U.left = spMap f := ((Category.comp_id _).symm.trans (Over.w U)).trans (Category.id_comp _)
  have e : pushHom gp _ (D'.c y) = Geo.Tor.preHom U (D.c (p.xe y)) :=
    Over.OverMorphism.ext ((p.c_pr y).trans (congrArg (· ≫ (D.c (p.xe y)).left) hU.symm))
  have e' : pushHom gp _ (D'.c y ^ n) = pushHom gp _ 1 := by
    rw [map_pow, e, ← map_pow, h, map_one, map_one]
  exact Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) e') ((Over.w _).trans (Over.w _).symm))

theorem lift_through_split (hK : Known) {K V F : Type} [CommRing K] [IsDomain K] [IsNoetherianRing K] [CommRing V]
    [IsDomain V] [IsNoetherianRing V] [CommRing F] [IsDomain F] [IsNoetherianRing F] {io : K →+* F} {j : V →+* F}
    (hio : Function.Injective io) (hj : Function.Injective j) {DK : Out.DegPre K} {DV : Out.DegPre V} {DF : Out.DegPre F}
    (pK : Out.IsPullDeg io DK DF) (pw : Out.IsPullDeg j DV DF) {n : ℕ} (hn : 0 < n) (hc : ∀ y, DV.c y ^ n = 1)
    {sB : ∀ T : Over (Sp K), (T ⟶ DK.P.A) → Out.GtPt DK T} (hs : IsSplit DK n sB) {u : epsR K ⟶ DK.P.A} {a : K}
    {e : Out.GtPt DK (epsR K)} (he : Out.GtPt.IsPull (spMap (epsScaleR a)) (sB _ u) e) {v : epsR V ⟶ DV.P.A}
    (hv : IsTangent v) {u₁ : epsR F ⟶ DF.P.A} (hu₁ : u₁.left ≫ prj pK = spMap (dualMap io) ≫ u.left) (x : F)
    (h : (sc (x * io a) ≫ u₁).left ≫ prj pw = spMap (dualMap j) ≫ v.left) :
    ∃ (ν : Out.GtPt DV (epsR V)) (ν₁ e₂ : Out.GtPt DF (epsR F)),
      GtTanR ν ∧ LetBC pw ν ν₁ ∧ LetBC pK e e₂ ∧ GtComb ![x] ![e₂] ν₁ := by
  obtain ⟨sV, hV⟩ := GlobalTheory.ArcCM.exists_isSplit hK V DV n hn hc
  obtain ⟨sF, hF⟩ := GlobalTheory.ArcCM.exists_isSplit hK F DF n hn (c_pow_of_pull pw hc)
  obtain rfl : e = sB _ (sc a ≫ u) := TorsionPairTest.isPull_unique he (hs.2.2 _ _ (sc a) u)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.SplitBC.split_baseChange hK V F j DV DF pw n sV sF hj hV hF v _ h
  refine ⟨_, _, _, h₁ hv, h₂,
    (GlobalTheory.SplitBC.split_baseChange hK K F io DK DF pK n sB sF hio hs hF _ _ (sc_over hu₁ a)).2,
    ![sF _ (sc (x * io a) ≫ u₁)], ![sF _ 1, sF _ (sc (x * io a) ≫ u₁)], fun i => ?_, ?_, fun i => ?_, rfl⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hF.2.2 _ _ (sc x) (sc (io a) ≫ u₁)
    rw [← Category.assoc, sc_mul] at this
    exact this
  · have := hF.2.1 (epsR F) 1 1
    rw [_root_.mul_one] at this
    exact TanPart.isZero_of_isAdd this
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hF.2.1 (epsR F) 1 (sc (x * io a) ≫ u₁)
    rw [_root_.one_mul] at this
    exact this

theorem isUnit_of_notMem {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {Tv : CDVR}
    {io : K →+* Tv.Fr} {ρ : 𝓞 K →+* Tv.V} (ho : OverLa w Tv.V io 1)
    (hρ : ∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : IsUnit (ρ s) := by
  have h1 : w.valuation K (s : K) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).2 hs
  have h0 : (s : K) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  have h2 := ho.2 (s : K)
  rw [vLa, h1, vV] at h2
  have h3 : valV Tv.V (io (s : K)) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 h0)
  have h4 : valV Tv.V (io (s : K)) = 1 := by
    rw [← WithZero.exp_log h3]
    simp only [WithZero.log_one, neg_zero, mul_zero, neg_eq_zero] at h2
    rw [h2, WithZero.exp_zero]
  rw [← hρ] at h4
  have h5 := ((IsDiscreteValuationRing.maximalIdeal Tv.V).valuation_eq_one_iff_notMem (K := Tv.Fr)).1 h4
  by_contra hu
  exact h5 hu

theorem letter_unique {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c : Coeff l} {nΨ n' : ℕ} {o : LamObj c nΨ n'} (L : LamLetters o)
    (hB : IsFibreOf o.B o.xB (gmap o.K₁) o.φB) {k : Fin o.xB.P.g} {u u' : epsR o.K₁ ⟶ o.xB.P.A} (h : L.IsLetter k u)
    (h' : L.IsLetter k u') : u = u' := by
  refine Over.OverMorphism.ext (hB.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  unfold LamLetters.IsLetter at h h'
  rcases hs : L.src k with q | q <;> rw [hs] at h h' <;> exact h.trans h'.symm

theorem letter_integral {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c : Coeff l} {nΨ n' f : ℕ} {o : LamObj c nΨ n'} {La : ℝ}
    (ho : LamObjGood o f La) {L : LamLetters o} (hL : L.IsGood) (p : HeightOneSpectrum (𝓞 o.K₁)) {k : Fin o.xB.P.g}
    {cl : o.K₁} (hcl : IsLocGen p cl (L.ℓ k).I) {u : epsR o.K₁ ⟶ o.xB.P.A} (hu : L.IsLetter k u) :
    ∃ (s : 𝓞 o.K₁) (t : epsR (𝓞 o.K₁) ⟶ o.B.A), s ∉ p.asIdeal ∧ IsTangent t ∧
      (sc ((s : o.K₁) * cl) ≫ u).left ≫ o.φB = spMap (dualMap (algebraMap (𝓞 o.K₁) o.K₁)) ≫ t.left := by
  have hB := ho.2.2.2.1
  obtain ⟨M, hM, -⟩ := ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  have hf := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB o.φB).1 hB
  obtain ⟨s, hs, hm⟩ := (isModelAt_integral_iff_mem_lieLat _ o.B o.xB o.φB hf p M hM _).1
    (letter_integral_of_isLocGen E H l c nΨ n' f o La ho L hL p M hM k cl hcl)
  obtain ⟨t, ht, w, hw, hc⟩ := ((CM.integral_tangent_coordinates _ o.B _).2.2.2.2.1 _).1 hm
  obtain ⟨u', hu', hU⟩ := hL.2.2.1 k
  obtain rfl := letter_unique L hB hu hu'
  have e : s • cl • L.U k = ((s : o.K₁) * cl) • L.U k := by
    rw [mul_smul]; exact (algebraMap_smul o.K₁ s _).symm
  have hc' : IsLieComb (((s : o.K₁) * cl) • L.U k) o.xB.v w := e ▸ hc
  exact ⟨s, t, hs, ht, eq_sc_of_isLieComb hU hc' ▸ hw⟩

end GlobalTheory.ArcCM.EtaInt

namespace GlobalTheory.ArcCM

open EtaInt
open GlobalTheory.CM.IntCoord (sc)

theorem abelian_letter_integral : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (m : Fin d.a.D₀.P.g) (cl : K₁), s.kind τ k = some m → IsLocGen w cl (s.line τ k).I → ∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![io ((n' : K₁) * cl)] ![e₂] ν₁ := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ ho hρ hψ hsq hτ τ k m cl hk hcl
  letI := H.starRing
  obtain ⟨u, hu, he⟩ := s.eta τ k m hk
  have hcl' : IsLocGen w cl (s.L.ℓ m).I := by
    have : s.line τ k = s.L.ℓ m := by unfold CMIn.line; rw [hk]; rfl
    exact this ▸ hcl
  obtain ⟨r, t, hr, ht, hrt⟩ := letter_integral s.good s.L_good w hcl' hu
  obtain ⟨r', hr'⟩ := (isUnit_of_notMem ho hρ hr).exists_left_inv
  obtain ⟨v, hv, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
  obtain ⟨u₁, hu₁, -⟩ := existsUnique_isVecOver (pull_grp M.pK).1 u
  obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver (pull_grp M.pw).1 v
  have hu₁' : u₁.left ≫ prj M.pK = spMap (dualMap io) ≫ u.left := hu₁
  have hv₁' : v₁.left ≫ prj M.pw = spMap (dualMap (algebraMap Tv.V Tv.Fr)) ≫ v.left := hv₁
  have hv' : v.left ≫ ψ = spMap (dualMap ρ) ≫ t.left := hv
  have hrt' : (sc ((r : K₁) * cl) ≫ u).left ≫ s.φB = spMap (dualMap (algebraMap (𝓞 K₁) K₁)) ≫ t.left := hrt
  have hring : (algebraMap Tv.V Tv.Fr).comp ρ = io.comp (algebraMap (𝓞 K₁) K₁) := RingHom.ext hρ
  have e₁ : v₁ = sc (io ((r : K₁) * cl)) ≫ u₁ := by
    refine Over.OverMorphism.ext (((pull_grp M.pw).1.paste_horiz hψ.2.1.1).hom_ext ?_
      ((Over.w _).trans (Over.w _).symm))
    show v₁.left ≫ prj M.pw ≫ ψ = (sc (io ((r : K₁) * cl)) ≫ u₁).left ≫ prj M.pw ≫ ψ
    have a₁ : v₁.left ≫ prj M.pw ≫ ψ = spMap (dualMap ((algebraMap Tv.V Tv.Fr).comp ρ)) ≫ t.left := by
      rw [← Category.assoc, hv₁', Category.assoc, hv', ← Category.assoc, dual_comp]
    have a₂ : (sc (io ((r : K₁) * cl)) ≫ u₁).left ≫ prj M.pK ≫ s.φB =
        spMap (dualMap (io.comp (algebraMap (𝓞 K₁) K₁))) ≫ t.left := by
      rw [← Category.assoc, sc_over hu₁', Category.assoc, hrt', ← Category.assoc, dual_comp]
    rw [a₁, hsq, a₂, hring]
  have hn : (n' : K₁) ≠ 0 := Nat.cast_ne_zero.2 s.n_pos.ne'
  refine lift_through_split hK io.injective (IsFractionRing.injective Tv.V Tv.Fr) M.pK M.pw s.n_pos hτ.1 s.split he
    (isTangent_sc (hv.isTangent hψ.2.1 ht) r') hu₁' _ ?_
  have e₂ : io ((n' : K₁) * cl) * io (n' : K₁)⁻¹ = algebraMap Tv.V Tv.Fr r' * io ((r : K₁) * cl) := by
    rw [← map_mul, mul_right_comm, mul_inv_cancel₀ hn, _root_.one_mul, map_mul, ← hρ, ← _root_.mul_assoc, ← map_mul, hr',
      map_one, _root_.one_mul]
  rw [e₂, ← sc_mul, Category.assoc, ← e₁]
  exact sc_over hv₁' r'

end GlobalTheory.ArcCM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemRangeOfLetBC
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.IntLetterCoord

open Matrix GlobalTheory.BasisUniv

theorem mem_range_of_comb {A K : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] {I : Type} {g m : ℕ} (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A) (U : Fin m → Fin g → A)
    (hU : ∀ k i, U k ᵥ* M i = ρ i • U k)
    (h : ∀ w : Fin g → PowerSeries A, (∀ i, w ᵥ* (M i).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (ρ i) • w) →
      ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j))
    (z : Fin g → A) (y : Fin m → K) (hz : (fun j => algebraMap A K (z j)) = ∑ k, y k • fun j => algebraMap A K (U k j))
    (k : Fin m) : y k ∈ Set.range (algebraMap A K) := by
  have hK : ∀ i, (fun j => algebraMap A K (z j)) ᵥ* (M i).map (algebraMap A K) =
      algebraMap A K (ρ i) • fun j => algebraMap A K (z j) := fun i => by
    have e : ∀ k, (fun j => algebraMap A K (U k j)) ᵥ* (M i).map (algebraMap A K) =
        algebraMap A K (ρ i) • fun j => algebraMap A K (U k j) := fun k => by
      funext j
      have := congrArg (algebraMap A K) (congrFun (hU k i) j)
      simpa [Matrix.vecMul, dotProduct] using this
    rw [hz, Matrix.sum_vecMul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_vecMul, e, smul_comm]
  have hA : ∀ i, z ᵥ* (M i).map (RingHom.id A) = RingHom.id A (ρ i) • z := fun i => by
    funext j
    apply IsFractionRing.injective A K
    have := congrFun (hK i) j
    simpa [Matrix.vecMul, dotProduct] using this
  have hfl : (algebraMap A K).Flat :=
    RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors A))
  obtain ⟨cf, hcf, -⟩ := eig_powerSeries M ρ U hU h (RingHom.id A) (RingHom.Flat.id A) z hA
  have := (eig_powerSeries M ρ U hU h (algebraMap A K) hfl _ hK).unique (y₂ := fun k => algebraMap A K (cf k)) hz (by
    funext j
    have := congrArg (algebraMap A K) (congrFun hcf j)
    simpa [Finset.sum_apply, Algebra.smul_def] using this)
  exact ⟨cf k, (congrFun this k).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem mem_range_of_letBC (hL : Out.Laws) (hL₂ : Out.Laws2) (hU : Out.UnifBaseChangeSt) (hL₅ : Out.Laws5)
    {A K : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {b : O →+* A} {b' : O →+* K}
    {a : ArcIn Dw l β A b} {a' : ArcIn Dw l β K b'}
    {p : Out.IsPullDeg (algebraMap A K) a.D₀ a'.D₀} (hp : InBC (algebraMap A K) a a' p)
    {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (hB : ArcBasis W ρ e) (τ : E →+* ℂ) {e₁ : Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR K)}
    (he : ∀ k, LetBC p (e τ k) (e₁ k)) {ν : Out.GtPt a.D₀ (epsR A)} {ν₁ e₂ : Out.GtPt a'.D₀ (epsR K)}
    (hν : GtTanR ν) (hν₁ : LetBC p ν ν₁) {y : Fin (Dw.mult τ) → K} (h₂ : GtComb y e₁ e₂) {x : K}
    (hx : GtComb ![x] ![e₂] ν₁) (k : Fin (Dw.mult τ)) : x * y k ∈ Set.range (algebraMap A K) := by
  have hG := hL.globalFns
  have hf : Function.Injective (algebraMap A K) := IsFractionRing.injective _ _
  obtain ⟨hW, -⟩ := (GlobalTheory.ArcQBC.baseChanges hL hL₂ hU hL₅ E H Dw l Xo c O β Y A K b a _ hf b' hp.1).2 a' p hp
  obtain ⟨W', hW'⟩ := hW χ W
  obtain ⟨m, -, hm, -⟩ := GlobalTheory.ArcBaseChange.main hL hL₂ E H Dw l Xo c O β Y A b a χ W K b' a' _ p W' hp hW'
  obtain ⟨v₀, hv₀, hB⟩ := hB
  obtain ⟨g, s, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.ConstLie.exists_const_basis hG E H Dw l Xo c O β Y A b a χ W
  have ex := GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y A b a χ W
  have ex' := GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y K b' a' _ W'
  have lin := GlobalTheory.ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y A b a χ W
  have lin' := GlobalTheory.ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y K b' a' _ W'
  have hsm : Smooth W.t.G.hom := W.t.semi.smooth
  have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
  obtain ⟨n, j, hy⟩ := Chart.univChartLoc W.t.G
  obtain ⟨n', j', hy'⟩ := exists_chart_of_pullback _ m.cart
  choose v' hv' using fun j => exists_lift _ m.cart (v j)
  have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange _ m.cart hv hv'
  have coord : ∀ ξ ξ' w, GtTanR ξ → LieImg W ξ w → LetBC p ξ ξ' → ∃ (z : Fin g → A) (w' : epsR (PowerSeries K) ⟶ W'.t.G),
      IsLieComb (fun j => PowerSeries.C (R := A) (z j)) v w ∧ LieImg W' ξ' w' ∧
      IsLieComb (fun j => PowerSeries.C (R := K) (algebraMap A K (z j))) v' w' := fun ξ ξ' w ht hw hξ => by
    obtain ⟨z, hz, -⟩ := hcomb _ ht
    have h1 := (lin g z s ξ v w (fun i => (hev i).2) hz).1 hw
    obtain ⟨w', hw'⟩ := exists_lift _ m.cart w
    refine ⟨z, w', h1, hm _ _ w w' hξ hw hw', ?_⟩
    simpa only [PowerSeries.map_C] using Chart.comb_baseChange _ m.cart h1 hv' hw'
  choose U u hU₀ hu hU' using fun k => coord _ _ _ (((ex (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1) (hv₀ τ k) (he k)
  obtain ⟨w, hw⟩ := (ex ν).1.exists
  obtain ⟨z, w', -, hw', hz'⟩ := coord _ _ _ hν hw hν₁
  obtain ⟨w₂, hw₂⟩ := (ex' e₂).1.exists
  have c₂ := (lin' _ y e₁ e₂ u w₂ hu h₂).1 hw₂
  have c₁ := (lin' _ ![x] ![e₂] ν₁ (fun _ => w₂) w' (fun i => by fin_cases i; exact hw₂) hx).1 hw'
  have d₂ : IsLieComb (∑ k, PowerSeries.C (R := K) (y k) • fun j => PowerSeries.C (R := K) (algebraMap A K (U k j)))
      v' w₂ := by
    have hc := (Chart.isLieComb_iff (∑ k, PowerSeries.C (R := K) (y k) •
      fun j => PowerSeries.C (R := K) (algebraMap A K (U k j))) v' _).2 rfl
    have := (comb_iff hy' hb' hU' hc _).2 rfl
    rwa [((Chart.isLieComb_iff _ _ _).1 this).trans ((Chart.isLieComb_iff _ _ _).1 c₂).symm] at hc
  have d₁ := (comb_iff hy' hb' (u := fun _ : Fin 1 => w₂) (fun _ => d₂) hz' _).1 c₁
  have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
  have hUe : ∀ k x, U k ᵥ* M x = ρ τ x • U k := fun k x => by
    have := (eig_iff hy hv _ (hMR x) (hU₀ k) _).1 (((hB τ).1 k).2 x)
    funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  refine mem_range_of_comb M (fun x => ρ τ x) U hUe (fun s hs => ?_) z (fun k => x * y k) ?_ k
  · have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
    have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
    simpa only [comb_iff hy hv hU₀ hc] using this
  · funext i
    have := congrArg (PowerSeries.constantCoeff (R := K)) (congrFun d₁ i)
    simpa [Finset.sum_apply, Finset.mul_sum, _root_.mul_assoc] using this

theorem main : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (Yw : Model Xo c (c.V Wl).subtype), Yw.N4 → (∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew) → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (x : Tv.Fr), (∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![x] ![e₂] ν₁) → ∀ m, x * M.g τ k m ∈ Set.range (algebraMap Tv.V Tv.Fr) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d Tv io Wl M Yw hN hB τ k x ⟨ν, ν₁, e₂, hν, hν₁, he₂, hx⟩ m
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨χ₀, hχ₀, -⟩ := hN Tv.V M.b ϖ M.aw (Or.inr ⟨inferInstance, hϖ, by
    rw [← hϖ.maximalIdeal_eq]; infer_instance⟩)
  obtain ⟨W₀⟩ := (Yw.hasArcData_iff _ _ _ _ _).1 ((hχ₀ χ₀).1 rfl).2.2.2
  obtain ⟨e₁, e₂', l₁, l₂, -, hg⟩ := M.e_tie
  have hK' : InBC io (d.a.restrict (c.V d.Wp).subtype) (M.aK.restrict (c.V d.Wp).subtype) M.pK := ⟨rfl, M.bcK.2⟩
  obtain ⟨-, x₂, -⟩ :=
    (GlobalTheory.ArcQBC.baseChanges hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c _ _ d.Y K₁ Tv.Fr _
      (d.a.restrict (c.V d.Wp).subtype) io io.injective _ hK'.1).2 (M.aK.restrict (c.V d.Wp).subtype) M.pK hK'
  obtain rfl : e₂ = e₂' τ k := (x₂ (d.e τ k)).unique he₂ (l₂ τ k)
  exact mem_range_of_letBC hK.laws hK.laws2 hK.ubc hK.laws5 M.bcw W₀ (hB χ₀ W₀) τ (l₁ τ) hν hν₁ (hg τ k) hx m

end GlobalTheory.IntLetterCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DiscrMulXiIntegral
noncomputable section

namespace GlobalTheory.XiIntegral

section Tangent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

def origin (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem gtTanR_iff (ν : GtPt D (epsR R)) : GtTanR ν ↔ origin R ≫ ν.b = 1 ∧
    ∀ χ y J, Good D.P.L y J → val (ν.s χ) (origin R).left y J = 1 := by
  constructor
  · rintro ⟨g₀, h₀, h⟩
    obtain ⟨h₁, h₂⟩ := (ConstLie.isZero_iff_zeroAlong (ρ := origin R) h).1 h₀
    refine ⟨h₁, fun χ y J hJ => ?_⟩
    have := h₂ χ _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · rintro ⟨h₁, h₂⟩
    obtain ⟨g₀, h⟩ := ConstLie.exists_isPullGt (origin R) ν
    obtain ⟨b, v⟩ := (TorusModel.isPull_iff _ _ _).1 h
    exact ⟨g₀, ⟨b.trans h₁, fun χ => corr_of_val D.P.isLB fun y J hJ =>
      (v χ y J hJ).trans ((h₂ χ y J hJ).trans (val_one _).symm)⟩, h⟩

theorem gtTanR_of_isZero {ν : GtPt D (epsR R)} (h : ν.IsZero) : GtTanR ν := by
  have hb : ν.b = 1 := h.1
  exact (gtTanR_iff ν).2 ⟨by rw [hb, MonObj.comp_one], fun χ y J hJ => (val_corr hJ (h.2 χ) _).trans (val_one _)⟩

theorem gtTanR_of_scale {a : R} {ν ν' : GtPt D (epsR R)} (h : GtPt.IsPull (spMap (epsScaleR a)) ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  have s : (origin R).left ≫ spMap (epsScaleR a) = (origin R).left :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by simp [epsScaleR]))
  refine (gtTanR_iff ν').2 ⟨Over.OverMorphism.ext ?_, fun χ y J hJ => ?_⟩
  · rw [← h₁, Over.comp_left, Over.comp_left, h.1, ← Category.assoc, s]
  · refine (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_)
    rw [s]
    exact h₂ χ y J hJ

theorem gtTanR_of_isAdd {ν ν' ν'' : GtPt D (epsR R)} (h : ν.IsAdd ν' ν'') (ht : GtTanR ν) (ht' : GtTanR ν') :
    GtTanR ν'' := _root_.GlobalTheory.FinLocalTan.gtTanR_of_isAdd (ν := ν) (ν' := ν') (ν'' := ν'') h ht ht'

theorem gtTanR_of_gtComb {m : ℕ} {cf : Fin m → R} {e : Fin m → GtPt D (epsR R)} {ν : GtPt D (epsR R)}
    (h : GtComb cf e ν) (he : ∀ i, GtTanR (e i)) : GtTanR ν := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  have : ∀ i, GtTanR (p i) := fun i => Fin.induction (gtTanR_of_isZero h₀)
    (fun j ih => gtTanR_of_isAdd (ha j) ih (gtTanR_of_scale (hu j) (he j))) i
  exact this _

end

end Tangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem exists_intHom {E : Type} [Field E] [NumberField E] [IsCMField E] {K₁ : Type} [Field K₁] [NumberField K₁]
    (τK : E →+* K₁) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X) :
    ∃ φ : X →+ 𝓞 K₁, ∀ x, (φ x : K₁) = ((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x)) := by
  obtain ⟨-, hadd, -, hint, -⟩ := GlobalTheory.ArcQ.pairE_properties E X ξ
  have hi : ∀ x, IsIntegral ℤ (((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x))) := fun x => by
    have h := (hint x).map (τK.comp (IsCMField.complexConj E).toRingEquiv.toRingHom).toIntAlgHom
    simpa [cc] using h
  refine ⟨AddMonoidHom.mk' (fun x => ⟨_, hi x⟩) fun x y => ?_, fun x => rfl⟩
  apply RingOfIntegers.ext
  show _ * τK (cc (pairE ξ (x + y))) = _ * τK (cc (pairE ξ x)) + _ * τK (cc (pairE ξ y))
  rw [hadd]
  simp [cc, mul_add]

theorem discr_mul_xi_integral : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)), s.kind τ k = none → ∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂] ν₁ := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ _ hρ _ _ _ τ k hk
  have hG : Out.GlobalFnsSt := hK.laws.globalFns
  obtain ⟨φ, hφ⟩ := exists_intHom (labK c K₁ τ) s.ξ
  obtain ⟨hb, hd⟩ := s.xi τ k hk
  obtain ⟨hw1, -, hw3⟩ := GlobalTheory.TorusTangent.main hG Tv.V M.aw.D₀
  obtain ⟨-, -, hK3⟩ := GlobalTheory.TorusTangent.main hG K₁ d.a.D₀
  obtain ⟨hF1, hF2, -⟩ := GlobalTheory.TorusTangent.main hG Tv.Fr M.aK.D₀
  obtain ⟨-, hadd, -⟩ := GlobalTheory.ArcQ.pairE_properties E d.a.D₀.X s.ξ
  let φw : M.aw.D₀.X →+ Tv.V :=
    ρ.toAddMonoidHom.comp (φ.comp (M.pK.xe.toAddMonoidHom.comp M.pw.xe.symm.toAddMonoidHom))
  let φ₀ : d.a.D₀.X →+ K₁ := AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE s.ξ x))) fun x y => by
    rw [hadd]; simp [cc]
  let φ₂ : M.aK.D₀.X →+ Tv.Fr := io.toAddMonoidHom.comp (φ₀.comp M.pK.xe.toAddMonoidHom)
  obtain ⟨ν, ⟨hν, hνb, hνd⟩, -⟩ := hw1 φw
  obtain ⟨ν₁, h₁, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pw hG ν
  obtain ⟨e₂, h₂, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pK hG (d.e τ k)
  have t₁ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pw hG h₁ hν
  have t₂ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pK hG h₂ (s.tan τ k)
  obtain ⟨b₁, d₁⟩ := hw3 Tv.Fr M.aK.D₀ _ M.pw φw ν ν₁ hνb hνd h₁
  obtain ⟨b₂, d₂⟩ := hK3 Tv.Fr M.aK.D₀ _ M.pK φ₀ (d.e τ k) e₂ hb hd h₂
  obtain ⟨ν', hν'⟩ := GlobalTheory.ConstLie.exists_gtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂]
  have t₃ : GtTanR ν' := gtTanR_of_gtComb hν' fun i => by fin_cases i; exact t₂
  obtain ⟨b₃, d₃⟩ := hF2 φ₂ _ e₂ ν' t₂ b₂ d₂ hν'
  have key : ∀ x, algebraMap Tv.V Tv.Fr (φw (M.pw.xe x)) = (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂) x := fun x => by
    show algebraMap Tv.V Tv.Fr (ρ (φ (M.pK.xe (M.pw.xe.symm (M.pw.xe x))))) =
      ((NumberField.discr E : ℤ) : Tv.Fr) * io (labK c K₁ τ (cc (pairE s.ξ (M.pK.xe x))))
    rw [AddEquiv.symm_apply_apply, hρ, hφ, map_mul, map_intCast]
  have e : ν₁ = ν' := (hF1 (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂)).unique
    ⟨t₁, b₁, fun x j hj => (d₁ x j hj).trans (congrArg _ (key x))⟩ ⟨t₃, b₃, d₃⟩
  exact ⟨ν, ν₁, e₂, hν, h₁, h₂, e ▸ hν'⟩

end GlobalTheory.XiIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LocalArcIntegralityOfCmNormalisedTrivialisation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.FinLoc


open GlobalTheory.IntModelExists GlobalTheory.Frames in
theorem exists_intModel_heq : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (Yw : Model Xo c (c.V Wl).subtype) (b : c.V Wl →+* Tv.V) (aw : ArcIn Dw l (c.V Wl).subtype Tv.V b) (aK : ArcIn Dw l (RingHom.id c.F) Tv.Fr (io.comp (algebraMap c.F K₁))) (pw : Out.IsPullDeg (algebraMap Tv.V Tv.Fr) aw.D₀ aK.D₀) (pK : Out.IsPullDeg io d.a.D₀ aK.D₀), Yw.N4 → ArcLieBasis d.W d.e → InBC (algebraMap Tv.V Tv.Fr) aw (aK.restrict (c.V Wl).subtype) pw → InBC io d.a aK pK → ∃ M : IntModel d Tv io Wl, M.b = b ∧ HEq M.aw aw ∧ M.aK = aK ∧ HEq M.pw pw ∧ HEq M.pK pK ∧ M.γ ≠ 0 ∧ (∀ τ, (M.g τ).det ≠ 0) ∧ ∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew := by
  intro hL hL₂ hU hL₅ E _ _ _ H Dw l Xo c K₁ _ _ _ d Tv io Wl Yw b aw aK pw pK hN hd hw hK
  have hG := hL.globalFns
  have hinj : Function.Injective (algebraMap Tv.V Tv.Fr) := IsFractionRing.injective _ _
  have hb : ∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (x : c.F)) := fun x =>
    (RingHom.congr_fun hw.1 x).symm
  let ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V) := fun τ => b.comp (embV c Wl τ)
  have hρ : ∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = io (algebraMap c.F K₁ (embK c τ x)) := fun τ x => hb _

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨χ₀, hχ₀, -⟩ := hN Tv.V b ϖ aw (Or.inr ⟨inferInstance, hϖ, by
    rw [← hϖ.maximalIdeal_eq]; infer_instance⟩)
  obtain ⟨W₀⟩ := (Yw.hasArcData_iff _ _ _ _ _).1 ((hχ₀ χ₀).1 rfl).2.2.2
  obtain ⟨ew, -, hew⟩ := GlobalTheory.T.exists_constant_eigenbasis_tangent_arc hL hL₂ E H Dw l Xo c _ _ Yw Tv.V b aw χ₀ W₀ ρ (io.comp (algebraMap c.F K₁))
    hw.1 hρ (exists_values c Wl)

  obtain ⟨W₁, e₁, l₁, b₁⟩ := exists_arcBasis_baseChange hL hL₂ hU hL₅ hinj hw W₀ hew
  have hK' : InBC io (d.a.restrict (c.V d.Wp).subtype) (aK.restrict (c.V d.Wp).subtype) pK := ⟨rfl, hK.2⟩
  have hd' : ArcBasis (Y := d.Y) d.W (fun τ => (algebraMap c.F K₁).comp (embK c τ)) d.e := hd
  obtain ⟨W₂, e₂, l₂, b₂⟩ := exists_arcBasis_baseChange hL hL₂ hU hL₅ io.injective hK' d.W hd'
  have hρ' : (fun τ => io.comp ((algebraMap c.F K₁).comp (embK c τ))) = fun τ => (algebraMap Tv.V Tv.Fr).comp (ρ τ) :=
    funext fun τ => RingHom.ext fun x => (hρ τ x).symm
  rw [hρ'] at b₂
  obtain ⟨p, p₁, p₂, p₃⟩ := exists_self aK.D₀ aK.gen
  have b₂' := (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c _ _ d.Y Tv.Fr _ _ _ W₂ _ e₂ b₂).1 _ _ Yw _ _ _ W₁ p e₂
    (fun x y => (p₂ _).trans (congrArg (x • ·) (p₂ y).symm)) (fun x => p₁ _) (fun τ k => p₃ _)
  obtain ⟨g, hg, hge⟩ := exists_matrix hG W₁ b₁ b₂'
  have t₁ : ∀ τ k, GtTanR (e₁ τ k) := fun τ k => by
    obtain ⟨v, i, hv⟩ := b₁
    exact ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c _ _ Yw Tv.Fr _ _ _ W₁ (e₁ τ k)).2 _ (i τ k)).2 ((hv τ).1 k).1

  obtain ⟨thw, hthw, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange aw.D₀.P
  obtain ⟨-, -, -, x₁, z₁⟩ := (GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c _ _ Yw Tv.V Tv.Fr b aw _ hinj _ hw.1).2
    (aK.restrict (c.V Wl).subtype) pw hw
  obtain ⟨-, -, -, x₂, z₂⟩ :=
    (GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c _ _ d.Y K₁ Tv.Fr _ (d.a.restrict (c.V d.Wp).subtype) io
      io.injective _ hK'.1).2
      (aK.restrict (c.V d.Wp).subtype) pK hK'
  obtain ⟨th₁, hth₁⟩ := (x₁ thw).exists
  obtain ⟨th₂, hth₂⟩ := (x₂ d.th).exists
  have nz : ThNZ d.th := by
    obtain ⟨_, _, _, _, h, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.exists_ne_zero_iff _ _).1 h
  obtain ⟨gm, hγ⟩ :=
    ((GlobalTheory.ThetaOverField.nonzero_generates hL hL₂ Tv.Fr aK.D₀ th₁).2.1 (z₁ _ _ hth₁ hthw) th₂).exists
  have hγ₀ : gm ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := (GlobalTheory.ThetaOverField.exists_ne_zero_iff aK.D₀ th₂).2 (z₂ _ _ hth₂ nz)
    refine hj ((hγ j).trans ?_)
    rw [constFn, map_zero, map_zero, zero_mul]
  exact ⟨⟨b, hb, ρ, hρ, aw, aK, pw, pK, hw, hK, thw, hthw, ew, gm, g, ⟨th₁, th₂, hth₁, hth₂, hγ⟩,
    ⟨e₁, e₂, l₁, l₂, t₁, hge⟩⟩, rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, hγ₀, hg,
    (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c _ _ Yw Tv.V b aw χ₀ W₀ ρ ew hew).2.1⟩

section Val

variable {K : Type} [Field K] [NumberField K]

theorem mem_range_of_le_one {w : HeightOneSpectrum (𝓞 K)} {T : CDVR} {io : K →+* T.Fr} {e : ℕ}
    (ho : OverLa w T.V io e) {x : K} (hx : w.valuation K x ≤ 1) : io x ∈ Set.range (algebraMap T.V T.Fr) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  have h1 : valV T.V (io x) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 h0)
  have h2 : WithZero.log (w.valuation K x) ≤ 0 := by
    simpa using (WithZero.log_le_log ((w.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 hx
  have h3 : 0 ≤ vV T.V (io x) := by
    rw [ho.2 x]
    exact mul_nonneg (Int.natCast_nonneg e) (by unfold vLa; omega)
  refine IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) ?_
  refine (WithZero.log_le_log h1 one_ne_zero).1 ?_
  rw [WithZero.log_one]
  unfold vV at h3
  omega

theorem exists_lift {T : CDVR} {R : Type} [CommRing R] (f : R →+* T.Fr)
    (h : ∀ x, f x ∈ Set.range (algebraMap T.V T.Fr)) : ∃ g : R →+* T.V, ∀ x, algebraMap T.V T.Fr (g x) = f x := by
  choose g hg using h
  have hi : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  exact ⟨{ toFun := g
           map_one' := hi (by simp [hg])
           map_mul' := fun x y => hi (by simp [hg])
           map_zero' := hi (by simp [hg])
           map_add' := fun x y => hi (by simp [hg]) }, hg⟩

theorem vLa_natCast (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (hN : N ≠ 0) :
    vLa la (N : K) = vla la (Ideal.span {(N : 𝓞 K)}) := by
  classical
  have h : (N : K) = algebraMap (𝓞 K) K (N : 𝓞 K) := by simp
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ (by exact_mod_cast hN), WithZero.log_exp, neg_neg, vla]

theorem bound_of_mul_mem {T : CDVR} {N x : T.Fr} (hN : N ≠ 0) (h : N * x ∈ Set.range (algebraMap T.V T.Fr))
    {m : ℤ} (hm : vV T.V N ≤ m) : x = 0 ∨ -m ≤ vV T.V x := by
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  obtain ⟨v, hv⟩ := h
  have h0 : algebraMap T.V T.Fr v ≠ 0 := hv ▸ mul_ne_zero hN hx
  have h1 : valV T.V (algebraMap T.V T.Fr v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v
  have h2 := (WithZero.log_le_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  have h3 : 0 ≤ vV T.V (N * x) := by
    rw [← hv]
    unfold vV
    omega
  rw [vV_mul hN hx] at h3
  omega

theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  have := la.isMaximal
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ la.ne_bot
  letI := Ideal.Quotient.field la.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 K ⧸ la.asIdeal) (ringChar _))

theorem exists_locGen (p : HeightOneSpectrum (𝓞 K)) (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    ∃ x : K, IsLocGen p x I ∧ vLa p x = FractionalIdeal.count K p I := by
  obtain ⟨x, hx⟩ := p.valuation_surjective K (WithZero.exp (-FractionalIdeal.count K p I))
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  have h1 : ordAt p x = FractionalIdeal.count K p I := by
    rw [ordAt, hx, WithZero.log_exp, neg_neg]
  exact ⟨x, ⟨h0, by rw [← ordAt_eq_count p h0, h1]⟩, h1⟩

end Val

end GlobalTheory.ArcCM.FinLoc

namespace GlobalTheory.ArcCM


open FinLoc in
theorem finLocalAt_of_cmIn : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.ArcQ.FinLocalAt d w n (-FractionalIdeal.count K₁ w s.Tl.I) (fun τ k => -FractionalIdeal.count K₁ w (s.line τ k).I) (w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la) (intAt Xo c a' n la) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s hM hS la w hw a' n
  obtain ⟨Tv, io, hfin, how⟩ := (exists_finSite_norm_eq_zpow_siteAlg K₁ w).1
  have hvw : ∀ x : K₁, vV Tv.V (io x) = vLa w x := fun x => by rw [how.2 x]; simp
  have hlo : w.asIdeal.LiesOver la.asIdeal := ⟨hw.symm⟩
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 c.F) := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx la.asIdeal w.asIdeal la.ne_bot]
    exact Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot)
  have hola : OverLa la Tv.V (io.comp (algebraMap c.F K₁)) (w.asIdeal.ramificationIdx (𝓞 c.F)) :=
    ⟨he, fun x => (hvw _).trans (ordAt_algebraMap_of_liesOver hw x)⟩

  obtain ⟨p, hp, hpl⟩ := exists_prime_mem la
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]
    have := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl
    simpa using this
  obtain ⟨Wl, hpW, hWl⟩ := exists_valuationSubring_complex_comap_val_eq c.F _ p hpU
  obtain ⟨Yw, h4, hpush⟩ := hM p Wl hp hpW
  obtain ⟨b, hb⟩ := exists_lift (T := Tv) ((io.comp (algebraMap c.F K₁)).comp (c.V Wl).subtype) fun x =>
    mem_range_of_le_one hola (by
      have hx : (x : c.F) ∈ Wl.comap c.F.val.toRingHom := x.2
      rw [hWl] at hx
      exact hx)
  obtain ⟨ρ, hρ⟩ := exists_lift (T := Tv) (io.comp (algebraMap (𝓞 K₁) K₁)) fun x =>
    mem_range_of_le_one how (w.valuation_le_one x)
  have hρ' : ∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁) := hρ

  obtain ⟨aw, aK, pw, pK, ψ, bw, bK, hψ, hsq, htau⟩ :=
    GlobalTheory.ArcCM.exists_arcIn_over_valuationRing hK E H Dw l c K₁ d.a d.e d.th d.jj n' La c₁ s Tv io ρ _ (c.V Wl).subtype b hρ' hb
  obtain ⟨M, m₁, m₂, m₃, m₄, m₅, hγ, hg, hbas⟩ := exists_intModel_heq hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c K₁ d
    Tv io Wl Yw b aw aK pw pK h4 (arcDatum_arcLieBasis hK.laws hK.laws2 E H Dw l Xo c K₁ d s.tan) bw bK
  subst m₁
  obtain rfl := eq_of_heq m₂
  subst m₃
  obtain rfl := eq_of_heq m₄
  obtain rfl := eq_of_heq m₅

  have hn' : n' ≠ 0 := s.n_pos.ne'
  have hm : ∀ N : ℕ, N ≠ 0 → vla la (Ideal.span {(N : 𝓞 c.F)}) ≤ mOf E n' la →
      vV Tv.V (N : Tv.Fr) ≤ ((w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la : ℕ) : ℤ) := fun N hN h => by
    have e := hola.2 (N : c.F)
    rw [map_natCast, vLa_natCast la hN] at e
    rw [e]
    exact_mod_cast Nat.mul_le_mul_left _ h
  have key : ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)), ∃ cl : K₁, cl ≠ 0 ∧
      vLa w cl = FractionalIdeal.count K₁ w (s.line τ k).I ∧ ∀ j, io cl * M.g τ k j = 0 ∨
        -((w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la : ℕ) : ℤ) ≤ vV Tv.V (io cl * M.g τ k j) := by
    intro τ k
    cases hk : s.kind τ k with
    | none =>
      have hd : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
      refine ⟨1, one_ne_zero, ?_, fun j => ?_⟩
      · simp [CMIn.line, hk, MLine.one, vLa, FractionalIdeal.count_one]
      · have h := GlobalTheory.IntLetterCoord.main hK E H Dw l Xo c K₁ d Tv io Wl M Yw h4 hbas τ k _
          (GlobalTheory.XiIntegral.discr_mul_xi_integral hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau τ k hk) j
        refine bound_of_mul_mem (N := ((NumberField.discr E).natAbs : Tv.Fr)) (by exact_mod_cast hd) ?_
          (hm _ hd (le_max_left _ _))
        rw [map_one, _root_.one_mul]
        obtain ⟨v, hv⟩ := h
        rcases Int.natAbs_eq (NumberField.discr E) with h' | h'
        · exact ⟨v, by rw [hv, congrArg (Int.cast : ℤ → Tv.Fr) h', Int.cast_natCast]⟩
        · exact ⟨-v, by rw [map_neg, hv, congrArg (Int.cast : ℤ → Tv.Fr) h', Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]⟩
    | some m =>
      obtain ⟨cl, hcl, hv⟩ := exists_locGen w (s.line τ k).I
      refine ⟨cl, hcl.1, hv, fun j => ?_⟩
      have h := GlobalTheory.IntLetterCoord.main hK E H Dw l Xo c K₁ d Tv io Wl M Yw h4 hbas τ k _
        (GlobalTheory.ArcCM.abelian_letter_integral hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau τ k m cl hk hcl) j
      refine bound_of_mul_mem (N := (n' : Tv.Fr)) (by exact_mod_cast hn') ?_ (hm _ hn' (le_max_right _ _))
      rwa [map_mul, map_natCast, _root_.mul_assoc] at h
  choose cl hcl₀ hcl₁ hcl₂ using key
  have hio : ∀ τ k, io (cl τ k) ≠ 0 := fun τ k => (map_ne_zero io).2 (hcl₀ τ k)
  refine GlobalTheory.ArcQ.finLocalAt_of_intModel hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d w Tv io Wl Yw M la _
    (fun τ k => (io (cl τ k))⁻¹) (fun τ => Matrix.diagonal (fun k => io (cl τ k)) * M.g τ) _ _ _ hS.1 hfin how hola h4
    hpush hbas ⟨hγ, GlobalTheory.ArcGamma.vV_gamma hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau hγ⟩
    (fun τ k => ⟨inv_ne_zero (hio τ k), ?_⟩) (fun τ => ?_) (fun τ k j => ?_) (fun τ k j => ?_) a' n
  · rw [← hcl₁, ← hvw]
    simp [vV]
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => hio τ k) (hg τ)
  · rw [Matrix.diagonal_mul, inv_mul_cancel_left₀ (hio τ k)]
  · rw [Matrix.diagonal_mul]
    exact hcl₂ τ k j

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LocalArcIntegralityOfCmNormalisedTrivialisationStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localArcIntegrality_of_cmNormalisedTrivialisation : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.ArcQ.FinLocalAt d w n (-FractionalIdeal.count K₁ w s.Tl.I) (fun τ k => -FractionalIdeal.count K₁ w (s.line τ k).I) (w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la) (intAt Xo c a' n la) := by
  first | exact @GlobalTheory.ArcCM.finLocalAt_of_cmIn | exact GlobalTheory.ArcCM.finLocalAt_of_cmIn | (intros; apply GlobalTheory.ArcCM.finLocalAt_of_cmIn <;> assumption)
end
