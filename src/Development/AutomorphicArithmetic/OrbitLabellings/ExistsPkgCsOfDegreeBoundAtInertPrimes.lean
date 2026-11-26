module

public import Development.AutomorphicArithmetic.OrbitLabellings.ExistsOrbitLabellingAtInertPrimeOfOddOrder
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralC
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitsInLevelPrime
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrFin
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtPelUnif
public import Development.AutomorphicArithmetic.OrbitLabellings.BlkMemSSelfConjugatePlacesOfCMDatum
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestBis
open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralChartCover

theorem cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y), ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ φ.Finite ∧ UpFBr.GeoJ T'.V t'.G (𝓞 E) (fun a => t'.act.act a) (chD C3.ch) (fun i => MvPowerSeries.map φ (C3.FT i)) (fun a i => MvPowerSeries.map φ (C3.actT a i)) := by
  intro E _ _ _ H Dw lv Xo c inst hstar T io y C3
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨T', φ, t', m, hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T C3.I.G C3.I.t' C3.I.m2 _ C3.I.m1
  obtain ⟨F', x', act', hF, hA, hx, ha⟩ := GlobalTheory.integralChart_baseChange E H Dw lv Xo c T io y C3 T' φ t' m
  exact ⟨T', φ, t', hi, hf, P.D, P.A, P.U.toUnifPre, F', x', _, t'.act.toRingAct, P.oD, P.oA, act', hF, funext hA, fun _ => rfl, hx, P.lin, ha⟩

end GlobalTheory.IntegralChartCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestTer
open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.UpperBoundDescent

theorem desc : ∀ (p : ℕ) [Fact p.Prime] (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ¬ IsUnit (p : T.V) → ∀ (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ) (FT : Fin dd → PS T.V 2 dd) (actT : OE → Fin dd → PS T.V 1 dd), UpFBr.UpFLaw p T'.V OE dd (fun i => MvPowerSeries.map φ (FT i)) (fun a i => MvPowerSeries.map φ (actT a i)) → UpFBr.UpFLaw p T.V OE dd FT actT := by
  intro p _ T T' φ hφ hfin hp OE _ _ dd FT actT h C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hb hf r W hW j
  have hinj : Function.Injective ((algebraMap O C).comp iota) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have hp0 : (p : T.V) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    obtain ⟨m, u', hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
    have h1 : ((algebraMap O C).comp iota) ϖ = 0 := by
      rw [map_mul, map_pow, mul_eq_zero] at ha
      rcases ha with ha | ha
      · exact absurd ha (u.isUnit.map _).ne_zero
      · exact pow_eq_zero_iff'.1 ha |>.1
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hp (by rw [hm]; simp)
    have h2 := congrArg ((algebraMap O C).comp iota) hm
    rw [map_natCast, map_mul, map_pow, h1, zero_pow hm0, mul_zero] at h2
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h2)
  obtain ⟨ι', hl, hc⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ hφ hfin.to_isIntegral iota hinj
  have key : ∀ {σ : Type} (f : MvPowerSeries σ T.V),
      MvPowerSeries.map ι' (MvPowerSeries.map φ f) = MvPowerSeries.map iota f := by
    intro σ f
    ext n
    simp only [MvPowerSeries.coeff_map, ← hc, RingHom.comp_apply]
  have := h C v O hv ι' hl w t hb hf r W (by simpa only [key] using hW) j
  simpa only [key] using this

end GlobalTheory.UpperBoundDescent
end

section -- merged from Development.AutomorphicArithmetic.OrbitLabellings.LabelSetGeoOfEvenOfRankOKOfNotDvdDiscr
section -- merged from Development.AutomorphicArithmetic.OrbitLabellings.LabelSetEvOfGeoOfNotDvdDiscr
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.labelSet_ev_of_geo_of_not_dvd_discr :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    y.IsAlg →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    ∀ (hg : LabSGeo C3 ι Y lab), ¬ (V.l : ℤ) ∣ NumberField.discr E → Even d → lab.RankOK Dw → (∀ o s, lab.big o 0 s ↔ Even s.val) →
    ∀ (o : Orb) (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hup E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ie hie k Y hY _ Orb _ d _ lab ha hg hdisc _ hr _ o Hc
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  have hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) := by
    rwa [NumberField.discr_eq_discr E (Module.Free.chooseBasis ℤ (𝓞 E))]
  obtain ⟨T', φ, t', hi, hf, hG⟩ := GlobalTheory.IntegralChartCover.cover E H Dw lv Xo c hstar T io y C3
  have hp : ¬ IsUnit ((V.l : ℕ) : T.V) :=
    UpFBr.not_isUnit_l (ie.comp (algebraMap T.V T.Fr)) fun t => embIntSt_holds T C V ie hie t
  have hp' : ¬ IsUnit ((V.l : ℕ) : T'.V) := fun h => by
    letI := φ.toAlgebra
    haveI : Algebra.IsIntegral T.V T'.V := ⟨hf.to_isIntegral⟩
    haveI : FaithfulSMul T.V T'.V := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
    exact hp (isUnit_of_map_unit (algebraMap T.V T'.V) _ (by rwa [map_natCast]))
  have hL := GlobalTheory.UpperBoundDescent.desc V.l T T' φ hi hf hp _ _ _ _
    (UpFBr.upFLaw_of_geoJ (hup V.l) Y.l_odd T'.V hp' t'.G _ _ _ hG hd)
  exact UpFBr.chStSelf_of_upChar Y (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) Hc
    (UpFBr.upCharS_chartL hL hie hd hY ha hg hr o Hc)
end

section -- merged from Development.AutomorphicArithmetic.OrbitLabellings.LabelSetGeoOfLabelSetArith
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

private theorem UpperTheory.extend_sigma_coefficients_by_zero {A C W : Type} [Fintype A] [Field C] [AddCommGroup W] [Module C W] (m : A → ℕ)
    (e : (Σ s : A, Fin (m s)) → W) (a : A) (b : Fin (m a) → C) :
    ∃ b' : (Σ s : A, Fin (m s)) → C, (∀ q, q.1 ≠ a → b' q = 0) ∧ ∑ x, b x • e ⟨a, x⟩ = ∑ q, b' q • e q := by
  refine ⟨fun q => if h : q.1 = a then b (h ▸ q.2) else 0, fun q hq => dif_neg hq, ?_⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

theorem UpperTheory.labelSetGeo_of_labelSetArith :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    LabSGeo C3 ι Y lab := by
  intro E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY Orb _ d _ lab ha
  have hsep1 : ∀ o (s s' : ZMod d), s ≠ s' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau o s) a - emA3 io ι (lab.tau o s') a) = 0 :=
    fun o s s' h => ha.sep (o, s) (o, s') fun e => h (Prod.mk.inj e).2
  have hgeo := fun o => GlobalTheory.T.separatedEmbeddings_directions_typedBasis E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY (ZMod d) (lab.tau o) (hsep1 o)
  refine { em_int := fun _ _ x => embedding_integral ι _ x
           em_conj := ?_
           e_int := fun _ _ i => a3uvec_int C3 hι _ i
           e_eig := fun o x a => (hgeo o).2.1 x.1 x.2 a
           e_sat := ?_
           e_full := ?_ }
  · intro o a x
    rw [← ha.conj o a]
    exact (embedding_conjugate hstar ι _ x).symm
  · intro o
    obtain ⟨w, h1, h2⟩ := (hgeo o).2.2.1
    exact ⟨w, h1, fun q q' => (h2 q q').trans (by congr)⟩
  · intro o a v hv
    obtain ⟨b, hb⟩ := (hgeo o).2.2.2 a v hv
    obtain ⟨b', h1, h2⟩ := UpperTheory.extend_sigma_coefficients_by_zero (fun s => Dw.mult (lab.tau o s)) (selfLieBasisVector C3 ι lab o) a b
    exact ⟨b', h1, hb.trans h2⟩
end

section -- merged from Development.AutomorphicArithmetic.OrbitLabellings.ValBlocksSOfBlkMemS
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.valBlocksS_of_blkMemS :
    ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (hd : ZMod d), hd + hd = 0 →
    ∀ (Orb : Type) [Fintype Orb] (I J : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (ν : ℝ),
    ValO X n FFimg ν → ∀ (F : ∀ o, RF.Flag (X o)) (nW : ℕ), nW ≤ 2 * n + 1 → ∀ ga : Orb → ZMod d → ℕ → ℕ,
    PlaneBlockProductsMemFamily hd X n F FFimg ga → (∀ o, (X o).Alt) → (∀ o, (X o).j' < (X o).n) →
    (∀ o s, (X o).rkF 1 (s + hd) = (X o).rkF 0 s) → (∀ o s k, ga o s k ≠ 0 → k ≤ (X o).rkF 0 s) →
    ValBlocksS hd X F nW ga ν := by
  intro C _ _ V d _ hd hhd Orb _ I J _ _ X n FFimg ν hV F nW hnW ga hMem hAlt hj hrk hga
  intro L hAtt hOne hRows hWt
  have hwt : ∀ o, ∀ q ∈ L o, ∀ (g : Fin 2) (a : ZMod d) (k : ℕ),
      GlobalTheory.wt (X o) q.1 g a k ≠ 0 → k ≤ (X o).rkF g a := by
    intro o q hq g a k hne
    fin_cases g
    · have hle : GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k ≤ ga o a k := by
        rw [← hWt o a k]
        exact le_sum_map (L o) (fun q => GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k) hq
      apply hga o a k
      have : GlobalTheory.wt (X o) q.1 0 a k ≠ 0 := hne
      omega
    · have hs : a + hd + hd = a := by rw [add_assoc, hhd, add_zero]
      have hle : GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k ≤ ga o (a + hd) k := by
        rw [← hWt o (a + hd) k]
        exact le_sum_map (L o)
          (fun q => GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k) hq
      rw [hs] at hle
      have hne' : GlobalTheory.wt (X o) q.1 1 a k ≠ 0 := hne
      have h0 : ga o (a + hd) k ≠ 0 := by omega
      have := hga o (a + hd) k h0
      rw [← hrk o (a + hd), hs] at this
      exact this
  have hOK : ∀ o, ∀ q ∈ L o, GlobalTheory.AttainsOK (X o) (F o) q.1 q.2 := fun o q hq =>
    attainsOK_of (X o) (F o) (Or.inl (hAlt o)) (hj o) q.1 q.2 (hwt o q hq) (hAtt o q hq)
  have hsum : ∑ o, (List.map (fun q => RF.GlobalTheory.what₂ (X o).n q.1) (L o)).sum ≤ n := by omega
  exact val_lists hV jetProd F L hOK hsum (hMem L hOne hWt)
end

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

private def pairColsS (n : ℕ) : Fin (n / 2) × Fin 2 ↪ Fin n where
  toFun x := ⟨2 * x.1.val + x.2.val, by have := x.1.2; have := x.2.2; omega⟩
  inj' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : 2 * a.val + b.val = 2 * a'.val + b'.val := congrArg Fin.val h
    have := b.2
    have := b'.2
    exact Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

theorem UpperTheory.labelSetGeo_of_even_of_rankOK_of_not_dvd_discr :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    y.IsAlg →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    ¬ (V.l : ℤ) ∣ NumberField.discr E → Even d → lab.RankOK Dw → (∀ o s, lab.big o 0 s ↔ Even s.val) → lab.j' < lab.n →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (ga : Orb → ZMod d → ℕ → ℕ),
    (∀ o s k', ga o s k' ≠ 0 → 1 ≤ k' ∧ k' ≤ Dw.mult (lab.tau o s)) → WtTieS Dw.mult lab.tau ga (fun τ i => a (τ, i)) →
    ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW →
    ∃ (X : ∀ o, RowData C V d (fun _ => lab.II Dw o) (JJ fun _ => lab.II Dw o)) (F : ∀ o, RF.Flag (X o)),
      (∀ o, (X o).n = lab.n ∧ (X o).m = lab.j + lab.j' ∧ (X o).Alt ∧ ∀ s, (X o).rkF 0 s = Dw.mult (lab.tau o s)) ∧
      ValBlocksS lab.hd X F nW ga ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY halg Orb _ d _ lab ha hdisc hev hr hbig hj
    a ga hsupp htie nW ν hν
  have hg : LabSGeo C3 ι Y lab := UpperTheory.labelSetGeo_of_labelSetArith E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha
  have hR2 : RankMaximalSelfCharts Xo c := rank_maximal_self_charts_of_nondegenerate Xo c rank_maximal_self_unconditional (GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c)
  have hCart : CartSelfSt := cartesian_self_conj_of_stability ptSelf_holds hStabSelf_holds
  have Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V := fun o =>
    { charZero := inferInstance
      algClosed := Y.algClosed
      l_odd := Y.l_odd
      k_unit := Y.k_unit
      cartH := hCart C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
      rank := rankHyp_ofLabS ha hg hr o
      axes := axesSelf_holds C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
      G0 := SelfConjugateGermZero.germ_zero_self_conjugate C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) _
      CEq := cEqSelf_holds C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
      R1 := independence_bound_self_conjugate C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
        (hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _)
      R2 := hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _
      CH := UpperTheory.labelSet_ev_of_geo_of_not_dvd_discr hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY halg Orb d lab ha hg hdisc hev hr hbig o _ }
  have hty : ∀ o (g : Fin 2) (x : lab.II Dw o),
      ((rdS Y (selfOfLab ha hg) Hy o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + lab.hd := fun _ _ _ => rfl
  have hrk : ∀ o g t, (rdS Y (selfOfLab ha hg) Hy o).rkF g t = Dw.mult (lab.tau o (idxS lab.hd g t)) :=
    fun o g t => rkF_sigmaS (m := fun s => Dw.mult (lab.tau o s)) lab.hd _ (hty o) g t
  have hrk0 : ∀ o s, (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s = Dw.mult (lab.tau o s) := fun o s => hrk o 0 s
  have hrk1 : ∀ o s, (rdS Y (selfOfLab ha hg) Hy o).rkF 1 (s + lab.hd) = (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s := by
    intro o s
    rw [hrk0, hrk]
    have e : idxS lab.hd 1 (s + lab.hd) = s := by
      unfold idxS
      rw [if_neg (by decide), add_sub_cancel_right]
    rw [e]
  have hA : ∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt := fun o => ⟨hev, hbig o⟩
  have hsupp' : ∀ o s k', ga o s k' ≠ 0 → 1 ≤ k' ∧ k' ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s := by
    intro o s k' h
    rw [hrk0]
    exact hsupp o s k' h
  refine ⟨fun o => rdS Y (selfOfLab ha hg) Hy o,
    fun o => let F := stdFlagS (m := fun s => Dw.mult (lab.tau o s)) lab.hd _ (hty o); ⟨F.en, F.en_inj, F.en_ty⟩,
    fun o => ⟨rfl, rfl, hA o, hrk0 o⟩, ?_⟩
  exact UpperTheory.valBlocksS_of_blkMemS C V d lab.hd ha.hd_two Orb _ _ _ (nW / 2) _ ν
    (RF.valO_self Y (selfOfLab ha hg) Hy (chartLetterSystem C3 V ι a) nW ν
      (hν.trans (descent_holds Xo c T io y C3 C V ι hι k Y hY a nW)) (selfSep_ofLab ha hg)
      (valuation_eq_self_of_unit_germ Y _ _ _ nW (unitSelf_holds Y _) (germLiftSelf_holds Y _ _)) (pairColsS nW))
    _ nW (by omega) ga
    (UpperTheory.blkMemS_selfConjugate_places_of_CMDatum E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg Hy a (nW / 2) nW (pairColsS nW) _ ga
      (fun _ _ _ _ => rfl) hA hj hsupp' htie)
    hA (fun _ => hj) hrk1 (fun o s k' h => (hsupp' o s k' h).2)
end

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth UpperTheory.G2 NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace UpperTheory.OrbitFamilyRestriction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private noncomputable def gaT (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) : ℕ → ℕ :=
  GlobalTheory.RowAt.gap (Dw.mult τ) fun i => a (τ, i)

private theorem card_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) : Z.card * P.d = Fintype.card P.Pl := by
  haveI := P.nz
  have hbij : Function.Bijective (fun x : {z // z ∈ Z} × ZMod P.d => P.pos x.1.1 x.2.val) := by
    constructor
    · rintro ⟨⟨z1, hz1⟩, s1⟩ ⟨⟨z2, hz2⟩, s2⟩ heq
      obtain ⟨q, -, hq⟩ := h (P.pos z1 s1.val)
      have e1 := hq (z1, s1) ⟨hz1, rfl⟩
      have e2 := hq (z2, s2) ⟨hz2, by simpa using heq.symm⟩
      have e := e1.trans e2.symm
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rfl
    · intro w
      obtain ⟨q, ⟨hq1, hq2⟩, -⟩ := h w
      exact ⟨(⟨q.1, hq1⟩, q.2), hq2⟩
  have hc := Fintype.card_of_bijective hbij
  rw [Fintype.card_prod, Fintype.card_coe, ZMod.card] at hc
  exact hc

private theorem exists_rowFamS (hUp : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {Dw : Datum H} {lv : Level H} (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] :
    AllPts Xo c fun N j l pl a nW ν => N.cls l = PrimeClass.inertClass → Odd (N.ordP l) →
      ∃ (Z : Finset (parOf N j l).Pl) (tau : {z // z ∈ Z} → ZMod (2 * (parOf N j l).d) → (E →+* ℂ))
        (R : RowFamS (parOf N j l) l Z), RF.IsReps (parOf N j l) Z ∧
        Function.Bijective (fun x : {z // z ∈ Z} × ZMod (2 * (parOf N j l).d) => tau x.1 x.2) ∧
        (∀ o s, InPsi H (tau o s) ↔ Even s.val) ∧
        (∀ o s, Even s.val → tau o s = pl (N.pos l o.1 (s.val % N.ordP l))) ∧
        (∀ o s, (R.X o).rkF 0 s = Dw.mult (tau o s)) ∧
        ValBlocksS ((parOf N j l).d : ZMod (2 * (parOf N j l).d)) R.X R.F nW (fun o s => gaT Dw a (tau o s)) ν := by
  intro hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 T io e hover y halg C3 nW ν hν hcls hodd
  obtain ⟨C, hF, hCZ, V, ι, hVl, hemb, halgc, hcpl, hMM, hvm, hnu⟩ :=
    GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hover
  have hl2 : V.l ≠ 2 := hVl ▸ ne_two_of_not_small hsmall
  have hνC := hnu y C3 lv.M a nW ν hν
  have hvM : V.v (lv.M : C) = 0 := hvm _ hM
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hemb halgc hcpl hl2
    (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M hvM
  rw [← hVl] at hcls hodd ⊢
  haveI : NeZero (N.ordP V.l) := ⟨hodd.pos.ne'⟩
  haveI : NeZero (2 * N.ordP V.l) := ⟨by have := hodd.pos; omega⟩
  obtain ⟨Z, hZ⟩ := GlobalTheory.InertLabelling.exists_reps N V.l
  have hZ' : RF.IsReps (parOf N j V.l) Z := hZ
  obtain ⟨lab, hari, hhd, hn, hj, hj', hbig, htau, hsurj, hdisc⟩ :=
    UpperTheory.exists_orbit_labelling_at_inert_prime_of_odd_order E H lv c N pl htie la T io C V ι hemb hcpl hVl hl2 hMM hcls hodd j Z hZ' (N.R.k - 1) j (N.R.m - j)
  have hinP : ∀ o s, lab.tau o s ↑H.rt = H.rt0 ↔ Even s.val := by
    intro o s
    rw [htau o s]
    split_ifs with he
    · simp only [he, iff_true]
      exact (htie.psi _).2 ⟨_, rfl⟩
    · simp only [he, iff_false]
      exact fun h => (RowLab.inPsi_conj_iff (H := H) _).1 h ((htie.psi _).2 ⟨_, rfl⟩)
  have hmult : ∀ o s, Dw.mult (lab.tau o s) = if Even s.val then Dw.p else Dw.q := by
    intro o s
    simp only [Datum.mult, hinP]
  have h2 : ((N.ordP V.l : ℕ) : ZMod (2 * N.ordP V.l)) + (N.ordP V.l : ℕ) = 0 := by
    rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
  have hpar : ∀ s : ZMod (2 * N.ordP V.l), Even (s - ((N.ordP V.l : ℕ) : ZMod (2 * N.ordP V.l))).val ↔ ¬Even s.val := by
    intro s
    have e1 : s - ((N.ordP V.l : ℕ) : ZMod (2 * N.ordP V.l)) = s + (N.ordP V.l : ℕ) := by
      rw [sub_eq_iff_eq_add, add_assoc, h2, add_zero]
    have hlt : N.ordP V.l < 2 * N.ordP V.l := by have := hodd.pos; omega
    rw [e1, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.even_iff, Nat.even_iff,
      Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _)]
    obtain ⟨t, ht⟩ := hodd
    omega
  have hk3 := N.R.m_add_three_le_k
  have hrank : lab.RankOK Dw := by
    intro o
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g s
      rw [hbig, hbig]
      fin_cases g <;> simp
    · intro s hs
      rw [hbig] at hs
      simp only [iff_true] at hs
      rw [hmult, if_pos hs, hn, hj, hp]
      simp only [Ranks.sigW]
      omega
    · intro s hs
      rw [hbig] at hs
      simp only [iff_true] at hs
      rw [hmult, if_neg hs, hj', hq]
      simp only [Ranks.sigW]
    · intro s hs
      rw [hbig] at hs
      simp at hs
      rw [hhd, hmult, if_pos ((hpar s).2 (Nat.not_even_iff_odd.2 hs)), hn, hj, hp]
      simp only [Ranks.sigW]
      omega
    · intro s hs
      rw [hbig] at hs
      simp at hs
      rw [hhd, hmult, if_neg (fun h => (hpar s).1 h hs), hj', hq]
      simp only [Ranks.sigW]
  have hbig0 : ∀ o s, lab.big o 0 s ↔ Even s.val := fun o s => by rw [hbig]; simp
  have hlt : lab.j' < lab.n := by rw [hj', hn]; omega
  have hmono : ∀ τ, ∀ i k, i ≤ k → k < Dw.mult τ → a (τ, k) ≤ a (τ, i) :=
    fun τ i k hik hk => hdom τ ⟨i, by omega⟩ ⟨k, hk⟩ (Fin.mk_le_mk.2 hik)
  have hsupp : ∀ o s k', gaT Dw a (lab.tau o s) k' ≠ 0 → 1 ≤ k' ∧ k' ≤ Dw.mult (lab.tau o s) :=
    fun o s k' h => (GlobalTheory.RowAt.gap_sums _ _ (hmono _)).1 k' h
  have hwt : WtTieS Dw.mult lab.tau (fun o s => gaT Dw a (lab.tau o s)) fun τ i => a (τ, i) := by
    refine ⟨fun o s i hi => ?_, fun σ hσ => ?_⟩
    · exact (((GlobalTheory.RowAt.gap_sums _ _ (hmono _)).2 _ le_rfl).1 i hi).symm
    · obtain ⟨x, hx⟩ := hsurj σ
      exact absurd hx (hσ x.1 x.2)
  obtain ⟨X, F, hX, hval⟩ := UpperTheory.labelSetGeo_of_even_of_rankOK_of_not_dvd_discr hUp E H Dw lv Xo c hstar T io y C3 C V ι hemb lv.M Y hY halg
    {z // z ∈ Z} (2 * N.ordP V.l) lab hari hdisc ⟨N.ordP V.l, by ring⟩ hrank hbig0 hlt a
    (fun o s => gaT Dw a (lab.tau o s)) hsupp hwt nW ν hνC
  have key : ∀ v w : ℕ, v < 2 * N.ordP V.l → w < 2 * N.ordP V.l → (Even v ↔ Even w) →
      v % N.ordP V.l = w % N.ordP V.l → v = w := by
    intro v w hv hw hpw hvw
    have hm := hodd.pos
    have h1 := Nat.div_add_mod v (N.ordP V.l)
    have h2 := Nat.div_add_mod w (N.ordP V.l)
    have h3 : v / N.ordP V.l < 2 := (Nat.div_lt_iff_lt_mul hm).2 hv
    have h4 : w / N.ordP V.l < 2 := (Nat.div_lt_iff_lt_mul hm).2 hw
    rw [Nat.even_iff, Nat.even_iff] at hpw
    obtain ⟨t, ht⟩ := hodd
    generalize v / N.ordP V.l = p1 at *
    generalize w / N.ordP V.l = p2 at *
    generalize v % N.ordP V.l = r1 at *
    generalize w % N.ordP V.l = r2 at *
    interval_cases p1 <;> interval_cases p2 <;> omega
  have hinj : Function.Injective (fun x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l) => lab.tau x.1 x.2) := by
    rintro ⟨o, s⟩ ⟨o', s'⟩ heq
    simp only at heq
    have hps : Even s.val ↔ Even s'.val := by rw [← hinP o s, ← hinP o' s', heq]
    have hpos : N.pos V.l o.1 s.val = N.pos V.l o'.1 s'.val := by
      rw [htau, htau] at heq
      by_cases he : Even s.val
      · rw [if_pos he, if_pos (hps.1 he)] at heq
        exact htie.inj heq
      · rw [if_neg he, if_neg (fun h => he (hps.2 h))] at heq
        exact htie.inj ((ComplexEmbedding.involutive_conjugate E).injective heq)
    obtain ⟨q, -, hq'⟩ := hZ (N.pos V.l o.1 s.val)
    have e1 := hq' (o.1, (s.val : ZMod (N.ordP V.l))) ⟨o.2, by simp only [ZMod.val_natCast, RowLab.pos_mod]⟩
    have e2 := hq' (o'.1, (s'.val : ZMod (N.ordP V.l))) ⟨o'.2, by simp only [ZMod.val_natCast, RowLab.pos_mod, hpos]⟩
    have e3 := e1.trans e2.symm
    simp only [Prod.mk.injEq] at e3
    obtain ⟨ho, hs⟩ := e3
    have hmod : s.val % N.ordP V.l = s'.val % N.ordP V.l := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hs
    have hv := key _ _ (ZMod.val_lt s) (ZMod.val_lt s') hps hmod
    exact Prod.ext (Subtype.ext ho) (ZMod.val_injective _ hv)
  have hnm : lab.j + lab.j' = N.R.m := by rw [hj, hj']; omega
  refine ⟨Z, lab.tau,
    { C := C, V := V, hVl := rfl, I := fun o x ↦ lab.II Dw o, J := fun o ↦ JJ fun x ↦ lab.II Dw o, X := X, F := F,
      hn := fun o => ⟨(hX o).1.trans hn, (hX o).2.1.trans hnm⟩,
      alt := fun o => (hX o).2.2.1 },
    hZ', ⟨hinj, hsurj⟩, fun o s => hinP o s, fun o s he => ?_, fun o s => (hX o).2.2.2 s, ?_⟩
  · exact (htau o s).trans ((if_pos he).trans (congrArg pl (RowLab.pos_mod N V.l o.1 s.val).symm))
  · rw [hhd] at hval
    exact hval

private theorem rest_add (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K) (p : Prop) [Decidable p] (g : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (if p ∧ k = n then (0 : ℝ) else (k : ℝ) * g k) =
      ((∑ k ∈ Finset.Icc 1 K, k * g k : ℕ) : ℝ) - (n : ℝ) * if p then (g n : ℝ) else 0 := by
  push_cast
  by_cases hp : p
  · have hn : n ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨h1, hK⟩
    simp only [hp, true_and, if_true]
    rw [← Finset.add_sum_erase _ _ hn, ← Finset.add_sum_erase (Finset.Icc 1 K) (fun k => (k : ℝ) * (g k : ℝ)) hn]
    rw [if_pos rfl, Finset.sum_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]
    ring
  · simp [hp]

end UpperTheory.OrbitFamilyRestriction

open UpperTheory.OrbitFamilyRestriction in
theorem UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)],
    (AllPts Xo c fun N j l pl a nW ν => N.cls l = PrimeClass.inertClass → Odd (N.ordP l) → ∀ T θ0 C1 : ℝ,
      RF.DegHyp2 (parOf N j l) (gapW N pl a) T θ0 (restOf N Dw pl a) C1 →
      N.R.f * ((RF.i0 N.R.k l + 1) * (N.R.k - 1) + 4 * N.R.r) ≤ nW →
      ∃ Pk : PkgCs (parOf N j l) l C1, Pk.T = T ∧ Pk.ν = ν) ∧
    (AllPts Xo c fun N j l _ a nW ν => N.cls l = PrimeClass.inertClass → Odd (N.ordP l) → (∀ z, 0 ≤ N.w j z) →
      ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) → 4 * N.R.r * s * N.R.f ≤ nW →
      ∃ Pk : PkgZeroCs (parOf N j l) l, Pk.ν = ν) := by
  intro hUp E _ _ _ H Dw lv Xo c _
  have hR := exists_rowFamS hUp Xo c
  refine ⟨?_, ?_⟩
  · intro hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 Tc io e hover y halg C3 nW ν hν hcls hodd
      T θ0 C1 hdeg hrows
    obtain ⟨Z, tau, R, hZ, hbij, hpsi, hev, hrk, hval⟩ :=
      hR hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 Tc io e hover y halg C3 nW ν hν hcls hodd
    have hk3 := N.R.m_add_three_le_k
    have hmono : ∀ τ, ∀ i k, i ≤ k → k < Dw.mult τ → a (τ, k) ≤ a (τ, i) :=
      fun τ i k hik hk => hdom τ ⟨i, by omega⟩ ⟨k, hk⟩ (Fin.mk_le_mk.2 hik)
    have hmr : ∀ τ, Dw.mult τ ≤ N.R.r := by
      intro τ
      unfold Datum.mult
      rw [hp, hq]
      simp only [Ranks.sigW, Ranks.r]
      split_ifs <;> omega
    have hmain : ∀ (o : {z // z ∈ Z}) (s : ZMod (2 * (parOf N j (resCharOf la)).d)), Even s.val →
        gaT Dw a (tau o s) (N.R.k - 1) = gapW N pl a (N.pos (resCharOf la) o.1 (s.val % N.ordP (resCharOf la))) := by
      intro o s he
      rw [hev o s he]
      have hin : pl (N.pos (resCharOf la) o.1 (s.val % N.ordP (resCharOf la))) ↑H.rt = H.rt0 :=
        (htie.psi _).2 ⟨_, rfl⟩
      simp only [gaT, GlobalTheory.RowAt.gap, Datum.mult, hin, if_true, hp, Ranks.sigW, gapW]
      split_ifs with hc1 hc2
      · rw [show N.R.k - 1 - 1 = N.R.k - 2 by omega]
      · omega
      · omega
    have hstep : ∀ (o : {z // z ∈ Z}) (s : ZMod (2 * (parOf N j (resCharOf la)).d)),
        (∑ k ∈ Finset.Icc 1 N.R.r, if Even s.val ∧ k = N.R.k - 1 then (0 : ℝ) else (k : ℝ) * (gaT Dw a (tau o s) k : ℝ)) =
          (∑ i : Fin (Dw.mult (tau o s)), (a (tau o s, i) : ℝ)) - ((N.R.k - 1 : ℕ) : ℝ) *
            (if Even s.val then (gapW N pl a (N.pos (resCharOf la) o.1 (s.val % N.ordP (resCharOf la))) : ℝ) else 0) := by
      intro o s
      rw [rest_add (N.R.k - 1) N.R.r (by omega) (by simp only [Ranks.r]; omega) (Even s.val) (gaT Dw a (tau o s))]
      have hg : (∑ k ∈ Finset.Icc 1 N.R.r, k * gaT Dw a (tau o s) k) = ∑ i : Fin (Dw.mult (tau o s)), a (tau o s, i) :=
        ((GlobalTheory.RowAt.gap_sums _ _ (hmono (tau o s))).2 _ (hmr _)).2
      congr 1
      · rw [hg]
        push_cast
        rfl
      · by_cases he : Even s.val
        · rw [if_pos he, if_pos he, hmain o s he]
        · rw [if_neg he, if_neg he]
    have hsumW : ∑ z, (gapW N pl a z : ℝ) = ∑ o : {z // z ∈ Z}, ∑ s : ZMod (2 * (parOf N j (resCharOf la)).d),
        (if Even s.val then (gapW N pl a (N.pos (resCharOf la) o.1 (s.val % N.ordP (resCharOf la))) : ℝ) else 0) := by
      let G : (E →+* ℂ) → ℝ := fun τ => ∑ z, if pl z = τ then (gapW N pl a z : ℝ) else 0
      calc ∑ z, (gapW N pl a z : ℝ) = ∑ τ, G τ := by
            simp only [G]
            rw [Finset.sum_comm]
            simp
        _ = ∑ x : {z // z ∈ Z} × ZMod (2 * (parOf N j (resCharOf la)).d), G (tau x.1 x.2) := (hbij.sum_comp G).symm
        _ = ∑ o, ∑ s, G (tau o s) := Fintype.sum_prod_type' (fun o s => G (tau o s))
        _ = _ := by
            refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun s _ => ?_
            by_cases he : Even s.val
            · rw [if_pos he, hev o s he]
              simp [G, htie.inj.eq_iff]
            · rw [if_neg he]
              refine Finset.sum_eq_zero fun z _ => if_neg ?_
              intro hz
              have h1 : InPsi H (pl z) := (htie.psi _).2 ⟨z, rfl⟩
              rw [hz] at h1
              exact he ((hpsi o s).1 h1)
    have hDF : ((DF Dw a : ℕ) : ℝ) = ∑ o : {z // z ∈ Z}, ∑ s : ZMod (2 * (parOf N j (resCharOf la)).d),
        ∑ i : Fin (Dw.mult (tau o s)), (a (tau o s, i) : ℝ) := by
      let g : (E →+* ℂ) → ℝ := fun τ => ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)
      calc ((DF Dw a : ℕ) : ℝ) = ∑ τ, g τ := by simp only [DF, Nat.cast_sum, g]
        _ = ∑ x : {z // z ∈ Z} × ZMod (2 * (parOf N j (resCharOf la)).d), g (tau x.1 x.2) := (hbij.sum_comp g).symm
        _ = ∑ o, ∑ s, g (tau o s) := Fintype.sum_prod_type' (fun o s => g (tau o s))
    have hrest : restOf N Dw pl a = ∑ o : {z // z ∈ Z}, ∑ s : ZMod (2 * (parOf N j (resCharOf la)).d),
        ∑ k ∈ Finset.Icc 1 N.R.r, if Even s.val ∧ k = N.R.k - 1 then (0 : ℝ) else (k : ℝ) * (gaT Dw a (tau o s) k : ℝ) := by
      rw [Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun s _ => hstep o s]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← hsumW, ← hDF]
      unfold restOf
      rw [Nat.cast_sub (by omega : 1 ≤ N.R.k), Nat.cast_one]
    exact ⟨⟨hodd, Z, hZ, R, fun o s => gaT Dw a (tau o s), gapW N pl a, nW, T, θ0, restOf N Dw pl a, ν,
      fun o s k hk => by rw [hrk]; exact (GlobalTheory.RowAt.gap_sums _ _ (hmono _)).1 k hk,
      fun o s he => hmain o s he, hrest, hrows, hdeg, hval⟩, rfl, rfl⟩
  · intro hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 Tc io e hover y halg C3 nW ν hν hcls hodd
      hw s ha hrows
    obtain ⟨Z, tau, R, hZ, hbij, hpsi, hev, hrk, hval⟩ :=
      hR hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 Tc io e hover y halg C3 nW ν hν hcls hodd
    have hk3 := N.R.m_add_three_le_k
    have hmono : ∀ τ, ∀ i k, i ≤ k → k < Dw.mult τ → a (τ, k) ≤ a (τ, i) :=
      fun τ i k hik hk => hdom τ ⟨i, by omega⟩ ⟨k, hk⟩ (Fin.mk_le_mk.2 hik)
    have hmr : ∀ τ, Dw.mult τ ≤ N.R.r := by
      intro τ
      unfold Datum.mult
      rw [hp, hq]
      simp only [Ranks.sigW, Ranks.r]
      split_ifs <;> omega
    have hc := card_reps _ Z hZ
    have hf : Fintype.card (parOf N j (resCharOf la)).Pl = N.R.f := by
      show Fintype.card (Bool × N.R.A) = N.R.f
      simp [Fintype.card_prod, Formalism.HC.Frame.card_A, Ranks.f, Ranks.n]
    refine ⟨⟨Z, R, fun o σ => gaT Dw a (tau o σ), N.R.r, s, nW, 1, ν, le_rfl, hw, ?_, ?_, ?_, hval⟩, rfl⟩
    · intro o σ k hk
      have h := (GlobalTheory.RowAt.gap_sums _ _ (hmono (tau o σ))).1 k hk
      rw [hrk]
      exact ⟨h.1, h.2, h.2.trans (hmr _)⟩
    · intro o σ
      by_cases h0 : 0 < Dw.mult (tau o σ)
      · have h := ((GlobalTheory.RowAt.gap_sums _ _ (hmono (tau o σ))).2 _ (hmr _)).1 0 h0
        exact le_of_eq_of_le h (ha _ h0)
      · have hz : ∀ k, gaT Dw a (tau o σ) k = 0 := by
          intro k
          simp only [gaT, GlobalTheory.RowAt.gap]
          split_ifs <;> omega
        simp [hz]
    · show 4 * N.R.r * s * (Z.card * (parOf N j (resCharOf la)).d) ≤ nW
      rw [hc, hf]
      exact hrows
