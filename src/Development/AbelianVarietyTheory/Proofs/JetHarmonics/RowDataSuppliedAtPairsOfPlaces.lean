module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NuLocCLeNuPlEBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralC
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfIntegralGaugedFormalGroupLaw
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLaw
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubstOneVariableUncurryEqSubst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorEigenspace
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvExpLinearPartIntegralCharMemIntegralGerm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsPairData
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsPairData
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem hasProj_pairData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), HasProj (Y.raw p) V := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  obtain ⟨M, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_adjoint_projectors_placePairs C V O dd Y d Unit (fun _ => I) (fun _ => p) (by
    rintro ⟨⟨⟩, x⟩ ⟨⟨⟩, x'⟩ hne
    exact p.em_sep x x' (fun h => hne (by rw [h])))
  refine ⟨M (), (h1 ()).1, (h1 ()).2, fun g c => h2 () g c, fun g c => h3 () g () (1 - g) c ?_,
    fun g v => h4 () g v⟩
  intro h
  have h' : g = 1 - g := (Prod.ext_iff.mp h).2
  revert h'
  fin_cases g <;> decide

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsPairDataStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaugeAdjointLieProjectors_pairData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), HasProj (Y.raw p) V := by
  first | exact @GlobalTheory.hasProj_pairData | exact GlobalTheory.hasProj_pairData | (intros; apply GlobalTheory.hasProj_pairData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfFormalBiextension
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndPairPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndPairPlaces
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.TeichPair

theorem hasTeich : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ g, HasTeich (Y.raw p) V g := by
  intro C _ _ V O _ _ dd Y d _ I _ p g
  obtain ⟨s, N, ζ, hs, hN, h1, h2, h3, hζ⟩ := exists_seq V Y.cpl (p.em g) (p.em_int g) (p.em_frob g)
    (fun a a' h => p.em_sep (g, a) (g, a') fun h' => h (congrArg Prod.snd h')) (p.em_unr g)
  obtain ⟨M, M', hM, -, hl, hl'⟩ := GlobalTheory.T.exists_adjointIntegralEnd_of_ladicLimit C V O dd Y d I p s hs
  have key : ∀ (a : ZMod d) (z w : C), V.Ge 0 w →
      (∀ N : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge N (z - p.em g a (s n) * w)) → z = ζ a * w := fun a z w hw h => by
    rw [← sub_eq_zero]
    refine eq_zero_of_ge (V := V) fun n => ?_
    obtain ⟨n0, hn⟩ := h n
    have e1 := hn (max n0 n) (le_max_left _ _)
    have e2 := (hw.mul_int (hζ a (max n0 n))).mono (w' := n) (by exact_mod_cast le_max_right _ _)
    have := e1.sub e2
    convert this using 1
    ring
  have hconj : ∀ a x, p.em (1 - g) a (star x) = p.em g a x := fun a x => by
    fin_cases g
    · show p.em 1 a (star x) = p.em 0 a x
      rw [p.em_conj, star_star]
    · show p.em 0 a (star x) = p.em 1 a x
      rw [p.em_conj]
  refine ⟨N, ζ, M, M', hN, h1, h2, h3, hM, fun c => funext fun i => ?_, fun q => funext fun i => ?_⟩
  · refine key _ _ _ (p.u_int g c i) fun n => ?_
    have := hl n (p.u g c) i
    simp only [p.u_eig] at this
    exact this
  · refine key _ _ _ (p.u_int (1 - g) q i) fun n => ?_
    have := hl' n (p.u (1 - g) q) i
    simp only [p.u_eig, hconj] at this
    exact this

end GlobalTheory.TeichPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndPairPlacesStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_pair_places : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ g, HasTeich (Y.raw p) V g := by
  first | exact @GlobalTheory.TeichPair.hasTeich | exact GlobalTheory.TeichPair.hasTeich | (intros; apply GlobalTheory.TeichPair.hasTeich <;> assumption)
end
end

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem cartHyp_of_formalBiextension : CartFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  exact GlobalTheory.T.cartHyp_of_integralGaugedFormalGroupLaw C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p)
    (GlobalTheory.T.hasGaugeAdjointLieProjectors_pairData C V O dd Y d I p) (GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_pair_places C V O dd Y d I p)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GermsDerivKernelOfFormal
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem germs_deriv_kernel_of_formal : IntegralGermIndependentAllCharts ∧ CEqFBSt ∧ IndependenceBoundAllCharts :=
  ⟨fun C _ _ V O _ _ dd Y d _ I _ p H =>
      GlobalTheory.T.integralGerms_independent_of_curveSystem C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p _ H =>
      GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p hr H h2 =>
      GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p) hr H h2⟩

end GlobalTheory.RowLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterBoundPairsOfPlacesIntegralChart
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterBoundPairsOfPlacesIntegralChart
set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CharPair

theorem sum_sigma_type {M : Type} [AddCommMonoid M] {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d)
    (f : (Σ b : ZMod d, Fin (m b)) → M) (hf : ∀ x, x.1 ≠ a → f x = 0) : ∑ x, f x = ∑ i : Fin (m a), f ⟨a, i⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    exact Finset.sum_eq_zero fun i _ => hf _ hb
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem isSat_type {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) {n : ℕ}
    {w : Fin n → (Σ b : ZMod d, Fin (m b)) → C} (hw : IsSat V w) (h0 : ∀ q x, x.1 ≠ a → w q x = 0) :
    IsSat V fun q (i : Fin (m a)) => w q ⟨a, i⟩ := by
  obtain ⟨h1, w', h2, h3⟩ := hw
  refine ⟨fun q i => h1 q _, fun i q => w' ⟨a, i⟩ q, fun i q => h2 _ q, fun q q' => ?_⟩
  rw [← h3 q q', sum_sigma_type m a (fun x => w q x * w' x q') fun x hx => by rw [h0 q x hx, zero_mul]]

theorem coeff_single_one_uncurry_eq_partialDerivative {C : Type} [Field C] {dd : ℕ} (f : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.coeff (Finsupp.single i 1) (un1 f) = ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl f i := by
  show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem integralSeries_uncurry_one {C : Type} [Field C] {V : VF C} {dd : ℕ} {f : PS C 1 dd} (hf : IntS V f) : IntS V (un1 f) :=
  fun _ => hf _

theorem isCharacter_uncurry_logarithm_law {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I) {f : PS C 1 dd}
    (hf : ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh Y.B.G.F f) :
    MvPowerSeries.subst (addP (Y.raw p) (gp C (Fin dd) (0 : Fin 2)) (gp C (Fin dd) 1)) (un1 f) =
      MvPowerSeries.subst (gp C (Fin dd) (0 : Fin 2)) (un1 f) * MvPowerSeries.subst (gp C (Fin dd) (1 : Fin 2)) (un1 f) := by
  rw [RowLawPair.formalAdd_eq_law Y p (RowLawPair.zc_gp 0) (RowLawPair.zc_gp 1),
    RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawSquare.zc_law Y (RowLawPair.zc_gp 0) (RowLawPair.zc_gp 1)),
    RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawPair.zc_gp 0), RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawPair.zc_gp 1)]
  exact hf.2

theorem orbitSum_eq {d l : ℕ} (hl : 0 < l) (p : ZMod d → ℕ) (s : ZMod d) :
    (∑' i : ℕ, ((l : ℝ) ^ (-((i : ℝ) + 1))) * (p (s + ((i + 1 : ℕ) : ZMod d)) : ℝ)) = S4.frobSum l p s := by
  unfold S4.frobSum
  exact tsum_congr fun i => by rw [ValuationFitting.rpow_neg_succ hl]

theorem chSt_pair : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab), lab.RankOK Dw → ∀ (o : Orb) (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY hy hl Orb d _ lab ha hg hr o Hc g a hb w hw h0
  have hinj : Function.Injective (lab.tau o g) := fun s s' h =>
    (Prod.mk.inj (Prod.mk.inj (ha.inj (a₁ := (o, g, s)) (a₂ := (o, g, s')) h)).2).2
  obtain ⟨χ, hχ, hdet⟩ := GlobalTheory.T.exists_characters_bounded_minor_eigenspace hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hl d (lab.tau o g) hinj
    (ha.frob o g) a lab.n (fun q i => w q ⟨a, i⟩) (isSat_type (fun b => Dw.mult (lab.tau o g b)) a hw h0)
  have hconj : ∀ s, ComplexEmbedding.conjugate (lab.tau o g s) = lab.tau o (1 - g) s := by
    intro s
    fin_cases g
    · exact (ha.conj o s).symm
    · show ComplexEmbedding.conjugate (lab.tau o 1 s) = lab.tau o 0 s
      rw [ha.conj]
      exact star_star _
  simp only [hconj] at hdet
  have hl1 : 1 < V.l := V.l_prime.one_lt
  rw [orbitSum_eq V.l_prime.pos (fun s => Dw.mult (lab.tau o (1 - g) s)) a] at hdet
  have hL : (1 : ℝ) < V.l := by exact_mod_cast hl1
  have h1 := S4.one_div_eq_gam_add_rho hl1
  have hdiv : ∀ x : ℝ, x / ((V.l : ℝ) - 1) = x * (S4.gam V.l + S4.rho V.l) := fun x => by
    rw [← h1]; ring
  have hrho : 0 ≤ S4.rho V.l := div_nonneg zero_le_one (by nlinarith)
  have hgam : 0 ≤ S4.gam V.l := div_nonneg (by linarith) (by nlinarith)
  have hj : (0 : ℝ) ≤ lab.j := Nat.cast_nonneg _
  have hj' : (0 : ℝ) ≤ lab.j' := Nat.cast_nonneg _
  obtain ⟨hc, hbig, hsm⟩ := hr o
  have hpb : ∀ b, lab.big o g b → Dw.mult (lab.tau o (1 - g) b) = 0 + lab.j' := fun b h => by
    rw [hsm (1 - g) b fun hh => (hc g b).1 hh h, zero_add]
  have hps : ∀ b, ¬ lab.big o g b → Dw.mult (lab.tau o (1 - g) b) = lab.n + lab.j := fun b h =>
    hbig (1 - g) b ((hc g b).2 h)
  have hmat : (Matrix.of fun ρ q : Fin lab.n => ∑ x : lab.II Dw o g,
      (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (un1 (χ ρ)) * lieBasisVector C3 ι lab o g x i) * w q x) =
      Matrix.of fun ρ q : Fin lab.n => ∑ x, (∑ i, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ ρ) i *
        ι (chartUnitVectors C3 ⟨lab.tau o g a, x⟩ i)) * w q ⟨a, x⟩ := by
    ext ρ q
    simp only [Matrix.of_apply, coeff_single_one_uncurry_eq_partialDerivative]
    exact sum_sigma_type (fun b => Dw.mult (lab.tau o g b)) a _ fun x hx => by rw [h0 q x hx, mul_zero]
  rw [← hmat] at hdet
  refine ⟨fun ρ x => ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (un1 (χ ρ)) * lieBasisVector C3 ι lab o g x i,
    fun ρ x => VF.Ge.sum fun i _ => (integralSeries_uncurry_one (hχ ρ).1 _).mul_int (hg.u_int o g x i), fun S t ht ρ => ?_,
    fun hA => hdet.trans (WithTop.coe_le_coe.mpr ?_), fun hB => hdet.trans (WithTop.coe_le_coe.mpr ?_)⟩
  · exact GlobalTheory.T.mvExp_linearPart_integralChar_mem_integralGerm C V d (lab.II Dw o) (Fin (chD C3.ch)) (Y.raw (pairOfLab ha hg o))
      (RowLawPair.rLaw_raw Y _) Hc (un1 (χ ρ)) (integralSeries_uncurry_one (hχ ρ).1) ((constantCoeff_uncurry _).trans (hχ ρ).2.1)
      (isCharacter_uncurry_logarithm_law Y _ (hχ ρ).2) g S t ht
  · rw [S4.frobSum_alt hl1 0 lab.j' (lab.n + lab.j) (lab.big o g) (CharacteristicFromRanks.alt_step (lab.big o) hc hA g) _ hpb hps a hb]
    show _ ≤ (lab.n : ℝ) * S4.gam V.l + ((lab.j : ℝ) + lab.j') / ((V.l : ℝ) - 1)
    rw [hdiv]
    push_cast
    nlinarith [mul_nonneg hj hrho, mul_nonneg hj' hgam]
  · rw [S4.frobSum_const hl1 (0 + lab.j') _ (fun b => hpb b (hB b)) a]
    show _ ≤ ((lab.j : ℝ) + lab.j') / ((V.l : ℝ) - 1)
    rw [hdiv, hdiv]
    push_cast
    nlinarith [mul_nonneg hj hrho, mul_nonneg hj hgam]

end GlobalTheory.CharPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterBoundPairsOfPlacesIntegralChartStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterBound_pairs_of_places_integralChart : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab), lab.RankOK Dw → ∀ (o : Orb) (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc := by
  first | exact @GlobalTheory.CharPair.chSt_pair | exact GlobalTheory.CharPair.chSt_pair | (intros; apply GlobalTheory.CharPair.chSt_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateAndRowConditionTwoPairsOfPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateAndRowConditionTwoPairsOfPlaces
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NonDegPair

section

open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.RowLawSquare GlobalTheory.RowLawPair
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] {dd : ℕ}

theorem coeff_mvExp_of_van {τ : Type} {T : Set τ} {H : MvPowerSeries τ C} [CharZero C] (hH : Van T H)
    (ν : τ →₀ ℕ) (hν : ∀ w ∈ ν.support, w ∉ T) (t : τ) :
    coeff (ν + Finsupp.single t 1) (mvExp H) = coeff (ν + Finsupp.single t 1) H := by
  have h := GlobalTheory.RowLaw.AddCurve.van_pderiv_mvExp hH t ν hν
  rw [map_sub, coeff_pderiv, coeff_pderiv, ← sub_mul, mul_eq_zero] at h
  rcases h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (Nat.cast_add_one_ne_zero _)

theorem van_add {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f + g) :=
  fun ν hν => by rw [map_add (f := _), hf ν hν, hg ν hν, add_zero]

theorem van_sub {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f - g) :=
  fun ν hν => by rw [map_sub, hf ν hν, hg ν hν, sub_zero]

theorem zc_cvAt {V : VF C} {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) (s : Fin 2) :
    Zc fun j => cvAt (X s : MvPowerSeries (Fin 2) C) (γ j) := fun j =>
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (hγ j).1

def toOne (b : MvPowerSeries (Fin dd) C) : PS C 1 dd := subst (pt C dd (0 : Fin 1)) b

theorem sb_toOne {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (b : MvPowerSeries (Fin dd) C) :
    sb ![a] (toOne b) = subst a b := by
  unfold toOne sb
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (zc_pt 0)) (hasSubst_sb (zc1 ha))]
  congr 1
  funext i
  exact sb_pt (zc1 ha) 0 i

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

theorem van_h {n : ℕ} (j : Fin n) {b : Fin dd → PS C n dd} (hb : Zc b) :
    Van {s : Fin n × Fin dd | s.1 = j} (sb ![gp C (Fin dd) j, b] Y.h) := by
  classical
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = 0} (fun s => zc2 (GlobalTheory.RowLawPair.zc_gp j) hb s.1 s.2) ?_ (h_axes Y 0)
  rintro ⟨s, x⟩ hs ν hν
  obtain rfl : s = 0 := hs
  show coeff ν (X (j, x) : PS C n dd) = 0
  rw [coeff_X, if_neg]
  rintro rfl
  exact hν (j, x) (by simp) rfl

theorem sb_gp_three (f : PS C 3 dd) : sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1, gp C (Fin dd) 2] f = f := by
  have e : (fun q : Fin 3 × Fin dd => ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1, gp C (Fin dd) 2] q.1 q.2) = X := by
    funext ⟨s, x⟩
    fin_cases s <;> rfl
  unfold sb
  rw [e, subst_self]
  rfl

theorem formalGroupCocycleLinearTerm_eq_chartLinear (u : Fin dd → C) : c2 (Y.raw p) u = Y.chartLinearTerm u := by
  have z := fun j : Fin 3 => GlobalTheory.RowLawPair.zc_gp (C := C) (dd := dd) j
  have hv : Van {s : Fin 3 × Fin dd | s.1 = 0}
      (sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1] Y.h + sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 2] Y.h -
        sb ![gp C (Fin dd) (0 : Fin 3), law Y (gp C (Fin dd) 1) (gp C (Fin dd) 2)] Y.h) :=
    van_sub (van_add (van_h Y 0 (z 1)) (van_h Y 0 (z 2))) (van_h Y 0 (zc_law Y (z 1) (z 2)))
  have e := exp_gauge_cocycle_second_variable Y (z 0) (z 1) (z 2)
  rw [sb_gp_three, ← mvExp_eq hv.const] at e
  funext μ
  unfold c2 FBChart.chartLinearTerm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [formalAdd_eq_law Y p (z 1) (z 2), hAt_eq_sb, hAt_eq_sb, hAt_eq_sb, ← e, coeff_mvExp_of_van hv]
  intro w hw
  classical
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hw)
  exact Fin.succ_ne_zero _

theorem cob_eq (b : MvPowerSeries (Fin dd) C) : cob (Y.raw p) b =
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (toOne b) - ev (n := 2) ![pt C dd 0] (toOne b) -
      ev (n := 2) ![pt C dd 1] (toOne b) := by
  unfold cob
  rw [formalAdd_eq_law Y p (GlobalTheory.RowLawPair.zc_gp 0) (GlobalTheory.RowLawPair.zc_gp 1),
    ← sb_toOne (zc_law Y (GlobalTheory.RowLawPair.zc_gp 0) (GlobalTheory.RowLawPair.zc_gp 1)),
    ← sb_toOne (GlobalTheory.RowLawPair.zc_gp 0), ← sb_toOne (GlobalTheory.RowLawPair.zc_gp 1)]
  rfl

theorem nonDeg_raw (h : NDG Y) : NonDeg (Y.raw p) V := by
  rintro γ hγ hu hadd ⟨b, hb, hcob⟩
  refine h γ hγ hu (fun i μ h0 h1 => ?_) ⟨toOne b, intS_subst V (zc_pt 0) (fun _ => intS_X V _) hb, fun μ => ?_⟩
  · have e := hadd i μ h0 h1
    rw [formalAdd_eq_law Y p (zc_cvAt hγ 0) (zc_cvAt hγ 1)] at e
    have e2 : (fun q : Fin 2 × Fin dd => cvAt (X q.1 : MvPowerSeries (Fin 2) C) (γ q.2)) =
        fun q : Fin 2 × Fin dd => ![fun j => cvAt (X 0 : MvPowerSeries (Fin 2) C) (γ j),
          fun j => cvAt (X 1 : MvPowerSeries (Fin 2) C) (γ j)] q.1 q.2 := by
      funext ⟨s, x⟩
      fin_cases s <;> rfl
    rw [e2]
    exact e
  · have e := hcob μ
    rwa [formalGroupCocycleLinearTerm_eq_chartLinear, cob_eq] at e

end

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem nonDegenerate_and_rowConditionTwo_pairsOfPlaces : (∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), NDG Y → NonDeg (Y.raw p) V) ∧ RankMaximalOfNondegenerate :=
  ⟨fun _ _ _ _ _ _ _ _ Y _ _ _ _ p h => nonDeg_raw Y p h,
    fun C _ _ V O _ _ dd Y d _ I _ p h _ Hc =>
      GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate C V d I (Fin dd) (Y.raw p) (GlobalTheory.RowLawPair.rLaw_pairData C V O dd Y d I p) (GlobalTheory.T.hasGaugeAdjointLieProjectors_pairData C V O dd Y d I p)
        (nonDeg_raw Y p h) Hc⟩

end GlobalTheory.NonDegPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateAndRowConditionTwoPairsOfPlacesStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonDeg_raw_pairData_and_rankMaximal : (∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), NDG Y → NonDeg (Y.raw p) V) ∧ RankMaximalOfNondegenerate := by
  first | exact @GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces | exact GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces | (intros; apply GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemChartFamilyAtPlacePairs
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemChartFamilyAtPlacePairs
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MemPair

section Blocks

open scoped BigOperators
open Classical Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj GlobalTheory.RowAt

theorem prod_pow_single {R : Type} [CommMonoid R] {d : ℕ} [NeZero d] (f : Fin 2 → ZMod d → ℕ → R)
    (M : Fin 2 → ZMod d → ℕ) (g : Fin 2) (a : ZMod d) (n e : ℕ) (h : e ≠ 0 → n ≤ M g a) :
    ∏ g', ∏ a', ∏ k ∈ Finset.range (M g' a' + 1), f g' a' k ^ (if g' = g ∧ a' = a ∧ k = n then e else 0)
      = f g a n ^ e := by
  rw [Finset.prod_eq_single g, Finset.prod_eq_single a, Finset.prod_eq_single n]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hn
    have : e = 0 := by
      by_contra he
      exact hn (Finset.mem_range.2 (Nat.lt_succ_of_le (h he)))
    simp [this]
  · intro a' _ ha
    simp [ha]
  · simp
  · intro g' _ hg
    simp [hg]
  · simp

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : RF.Flag X)

theorem poly_eq (b : RF.GlobalTheory d) (M : Fin 2 → ZMod d → ℕ) (h : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ M g a) :
    b.poly X F = ∏ g, ∏ a, ∏ k ∈ Finset.range (M g a + 1),
      MvPolynomial.rename (F.letter g a) (minorK C (b.what₂ X.n) (X.rkF g a) k) ^ b.wt X g a k := by
  cases b with
  | bi g a i y =>
    simp only [RF.GlobalTheory.wt, pow_add, Finset.prod_mul_distrib]
    rw [prod_pow_single (fun g' a' k => MvPolynomial.rename (F.letter g' a')
        (minorK C ((RF.GlobalTheory.bi g a i y).what₂ X.n) (X.rkF g' a') k)) M g a X.n,
      prod_pow_single (fun g' a' k => MvPolynomial.rename (F.letter g' a')
        (minorK C ((RF.GlobalTheory.bi g a i y).what₂ X.n) (X.rkF g' a') k)) M (1 - g) (a + (i : ZMod d)) X.n]
    · rfl
    · intro he
      refine h _ _ _ ?_
      simp [RF.GlobalTheory.wt, he]
    · intro he
      refine h _ _ _ ?_
      simp only [RF.GlobalTheory.wt, and_self, if_true]
      omega
  | ch g a u =>
    simp only [RF.GlobalTheory.wt]
    rw [prod_pow_single (fun g' a' k => MvPolynomial.rename (F.letter g' a')
        (minorK C ((RF.GlobalTheory.ch g a u).what₂ X.n) (X.rkF g' a') k)) M g a X.n]
    · rfl
    · intro he
      refine h _ _ _ ?_
      simp [RF.GlobalTheory.wt, he]
  | mon g e N =>
    rw [Finset.prod_eq_single g]
    · show (∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rkF g a) (e a))) =
        ∏ a : ZMod d, ∏ k ∈ Finset.range (M g a + 1),
          MvPolynomial.rename (F.letter g a) (minorK C N (X.rkF g a) k) ^ (RF.GlobalTheory.mon g e N).wt X g a k
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [monP, map_prod]
      have h1 : ∀ k ∈ Finset.Icc 1 (min N (X.rkF g a)), (RF.GlobalTheory.mon g e N).wt X g a k = e a k := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        simp only [RF.GlobalTheory.wt]
        rw [if_pos ⟨trivial, hk⟩]
      refine Finset.prod_congr_of_eq_on_inter ?_ ?_ ?_
      · intro k hk hk'
        have : e a k = 0 := by
          by_contra he
          exact hk' (Finset.mem_range.2 (Nat.lt_succ_of_le (h g a k (by rwa [h1 k hk]))))
        rw [this, pow_zero, map_one]
      · intro k _ hk
        rw [Finset.mem_Icc] at hk
        simp only [RF.GlobalTheory.wt]
        rw [if_neg (fun h => hk h.2), pow_zero]
      · intro k hk _
        rw [h1 k hk, map_pow]
    · intro g' _ hg
      simp [RF.GlobalTheory.wt, hg]
    · simp

theorem le_rows (b : RF.GlobalTheory d) (g : Fin 2) (a : ZMod d) (k : ℕ) (h : b.wt X g a k ≠ 0) : k ≤ b.what₂ X.n := by
  cases b with
  | bi g' a' i y =>
    simp only [RF.GlobalTheory.wt] at h
    by_contra hk
    have : k ≠ X.n := fun e => hk (le_of_eq e)
    simp [this] at h
  | ch g' a' u =>
    simp only [RF.GlobalTheory.wt] at h
    by_contra hk
    have : k ≠ X.n := fun e => hk (le_of_eq e)
    simp [this] at h
  | mon g' e N =>
    simp only [RF.GlobalTheory.wt] at h
    by_contra hk
    rw [if_neg] at h
    · exact h rfl
    · rintro ⟨-, -, h3⟩
      exact hk (h3.trans (min_le_left _ _))

theorem both_groups (b : RF.GlobalTheory d) (g : Fin 2) (a a' : ZMod d) (k k' : ℕ) (h : b.wt X g a k ≠ 0)
    (h' : b.wt X (1 - g) a' k' ≠ 0) : k = X.n ∧ k' = X.n := by
  have hg : ∀ g : Fin 2, 1 - g ≠ g := by decide
  cases b with
  | bi g' a'' i y =>
    simp only [RF.GlobalTheory.wt] at h h'
    constructor
    · by_contra hk
      simp [hk] at h
    · by_contra hk
      simp [hk] at h'
  | ch g' a'' u =>
    simp only [RF.GlobalTheory.wt] at h h'
    constructor
    · by_contra hk
      simp [hk] at h
    · by_contra hk
      simp [hk] at h'
  | mon g' e N =>
    simp only [RF.GlobalTheory.wt] at h h'
    have h1 : g = g' := by
      by_contra hk
      simp [hk] at h
    have h2 : 1 - g = g' := by
      by_contra hk
      simp [hk] at h'
    exact absurd (h2.trans h1.symm) (hg g)

end Blocks

section Letters

open scoped BigOperators
open Classical Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj GlobalTheory.RowAt

variable {Ty : Type} (r : Ty → ℕ) {Orb : Type} {d : ℕ} (tau : Orb → Fin 2 → ZMod d → Ty)

abbrev Ix (o : Orb) (g : Fin 2) : Type := Σ a : ZMod d, Fin (r (tau o g a))

def toRow (w : WVO (Ix r tau)) : Σ τ : Ty, Fin (r τ) := ⟨tau w.1 w.2.1 w.2.2.1, w.2.2.2⟩

def toLet {n : ℕ} (x : Fin n × WVO (Ix r tau)) : Formalism.L2.Pj.Letter Ty r n :=
  ⟨tau x.2.1 x.2.2.1 x.2.2.2.1, x.2.2.2.2, x.1⟩

theorem toRow_inj (inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2) :
    Function.Injective (toRow r tau) := by
  rintro ⟨o, g, a, i⟩ ⟨o', g', a', i'⟩ h
  have h1 : ((o, g, a) : Orb × Fin 2 × ZMod d) = (o', g', a') := inj (congrArg Sigma.fst h)
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  have h2 : i = i' := eq_of_heq (Sigma.mk.inj h).2
  rw [h2]

theorem sigma_eq {A : Type} {m : A → ℕ} (x : Σ s, Fin (m s)) (a : A) (c : Fin (m a)) (h1 : x.1 = a)
    (h2 : (x.2 : ℕ) = c) : x = ⟨a, c⟩ := by
  obtain ⟨s, i⟩ := x
  subst h1
  exact congrArg _ (Fin.ext h2)

variable {C : Type} [Field C] {V : VF C} [NeZero d] [Fintype Orb]

theorem isImgO {dd n : ℕ} (inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2)
    (X : ∀ o, RawChart C d (Ix r tau o) (Fin dd)) (U : (Σ τ : Ty, Fin (r τ)) → Fin dd → C)
    (hU : ∀ w : WVO (Ix r tau), (X w.1).u w.2.1 w.2.2 = U (toRow r tau w))
    (Q : MvPolynomial (Fin n × WVO (Ix r tau)) C) :
    IsImgO X (fun ℓ : Formalism.L2.Pj.Letter Ty r n => ℓ.2.2) (fun ℓ => U ⟨ℓ.1, ℓ.2.1⟩)
      (MvPolynomial.rename (toLet r tau) Q) Q := by
  have hi := toRow_inj r tau inj
  have hx : ∀ x : Fin n × WVO (Ix r tau),
      (⟨(toLet r tau x).1, (toLet r tau x).2.1⟩ : Σ τ : Ty, Fin (r τ)) = toRow r tau x.2 := fun _ => rfl
  refine ⟨fun ℓ w => if toRow r tau w = ⟨ℓ.1, ℓ.2.1⟩ then 1 else 0, ?_, ?_⟩
  · intro ℓ hℓ
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ hℓ)
    beta_reduce
    rw [hx, Finset.sum_eq_single x.2]
    · rw [hU, if_pos rfl, one_smul]
    · intro w _ hw
      rw [if_neg (fun h => hw (hi h)), zero_smul]
    · simp
  · rw [MvPolynomial.aeval_rename]
    have : ((fun ℓ : Formalism.L2.Pj.Letter Ty r n => ∑ w : WVO (Ix r tau),
        MvPolynomial.C (if toRow r tau w = ⟨ℓ.1, ℓ.2.1⟩ then (1 : C) else 0) * MvPolynomial.X (ℓ.2.2, w)) ∘
          toLet r tau) = (MvPolynomial.X : _ → MvPolynomial (Fin n × WVO (Ix r tau)) C) := by
      funext x
      simp only [Function.comp]
      rw [hx, Finset.sum_eq_single x.2]
      · rw [if_pos rfl, map_one, one_mul]
        rfl
      · intro w _ hw
        rw [if_neg (fun h => hw (hi h)), map_zero, zero_mul]
      · simp
    rw [this, MvPolynomial.aeval_X_left_apply]

def ind (C : Type) [Field C] {N n : ℕ} (col : Fin N → Fin n) (k : ℕ) (ρ : Fin k) (b : Fin n) : C :=
  if h : ρ.val < N then (if b = col ⟨ρ.val, h⟩ then 1 else 0) else 0

theorem rename_minor {J : Fin 2 → Type} [∀ g, Fintype (J g)] (o : Orb) (X : RowData C V d (Ix r tau o) J)
    (F : RF.Flag X) (h1 : ∀ g a c, (F.en g a c).1 = a) (h2 : ∀ g a c, ((F.en g a c).2 : ℕ) = c)
    {N n : ℕ} (col : Fin N → Fin n) (g : Fin 2) (a : ZMod d) (k : ℕ) (hk : k ≤ r (tau o g a)) (hN : k ≤ N)
    (hr : k ≤ X.rkF g a) :
    MvPolynomial.rename (toLet r tau) (toAll o (MvPolynomial.rename
      (fun x : Fin N × WV (Ix r tau o) => (col x.1, x.2))
        (MvPolynomial.rename (F.letter g a) (minorK C N (X.rkF g a) k)))) =
      (GlobalTheory.CombMinor.cMat (tau o g a) k hk (ind C col k)).det := by
  rw [minorK, dite_eq_left ⟨hN, hr⟩, toAll, MvPolynomial.rename_rename, MvPolynomial.rename_rename,
    MvPolynomial.rename_rename, AlgHom.map_det]
  congr 1
  ext ρ i : 2
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.rename_X,
    GlobalTheory.CombMinor.cMat]
  have hρ : ρ.val < N := lt_of_lt_of_le ρ.2 hN
  rw [Finset.sum_eq_single (col ⟨ρ.val, hρ⟩)]
  · rw [ind, dite_eq_left hρ, if_pos rfl, map_one, one_mul]
    congr 1
    simp only [Function.comp, RF.Flag.letter]
    rw [sigma_eq _ a (Fin.castLE hk i) (h1 g a (Fin.castLE hr i)) (h2 g a (Fin.castLE hr i))]
    rfl
  · intro b _ hb
    rw [ind, dite_eq_left hρ, if_neg hb, map_zero, zero_mul]
  · simp

theorem sum_fin_gap (m i : ℕ) (f : ℕ → ℕ) :
    ∑ k : Fin (m + 1), (if i < k.val then f k.val else 0) = ∑ k ∈ Finset.Icc (i + 1) m, f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if i < k then f k else 0) (m + 1), ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

theorem prod_mem [Fintype Ty] (O : Subring C) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2)
    (surj : Function.Surjective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2)
    (hcc : ∀ o g s, cc (tau o g s) = tau o (1 - g) s)
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V d (Ix r tau o) (J o))
    (F : ∀ o, RF.Flag (X o)) (h1 : ∀ o g a c, ((F o).en g a c).1 = a)
    (h2 : ∀ o g a c, (((F o).en g a c).2 : ℕ) = c) (hrk : ∀ o g s, (X o).rkF g s = r (tau o g s))
    (hsm : ∀ o g s, r (tau o g s) < (X o).n ∨ r (tau o (1 - g) s) < (X o).n)
    (hdom : ∀ τ i j, i ≤ j → j < r τ → a τ j ≤ a τ i) {n : ℕ} (L : Orb → List (RF.GlobalTheory d × ℝ))
    (hL : ∀ o g s k, ((L o).map fun q => q.1.wt (X o) g s k).sum = gap (r (tau o g s)) (a (tau o g s)) k)
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (RF.rowsAt X L o i)) → Fin n) (hpl : Function.Injective pl) :
    MvPolynomial.rename (toLet r tau)
      (∏ o, toAll o (prodAll (RF.plAt n pl o) fun i => (RF.blkAt L o i).poly (X o) (F o))) ∈
        HaO r n C O cc isX a := by
  have hg1 : ∀ g : Fin 2, 1 - g ≠ g := by decide
  have hL' : ∀ o g s k, ∑ i : Fin (L o).length, (RF.blkAt L o i).wt (X o) g s k =
      gap (r (tau o g s)) (a (tau o g s)) k := by
    intro o g s k
    rw [← hL]
    exact RF.sum_get (L o) fun q => q.1.wt (X o) g s k
  have hle : ∀ o i g s k, (RF.blkAt L o i).wt (X o) g s k ≠ 0 → k ≤ r (tau o g s) := by
    intro o i g s k h
    refine ((gap_sums _ _ (hdom (tau o g s))).1 k ?_).2
    rw [← hL']
    intro h0
    exact h ((Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ _))
  have key := GlobalTheory.CombMinor.prod_det_mem_HaO Ty r n C O cc isX a
    (Σ o, Σ _i : Fin (L o).length, Σ g : Fin 2, Σ s : ZMod d, Fin (r (tau o g s) + 1))
    (fun α => tau α.1 α.2.2.1 α.2.2.2.1) (fun α => α.2.2.2.2.val) (fun α => Nat.le_of_lt_succ α.2.2.2.2.2)
    (fun α => ind C (fun ρ => pl ⟨α.1, α.2.1, ρ⟩) α.2.2.2.2.val)
    (fun α => (RF.blkAt L α.1 α.2.1).wt (X α.1) α.2.2.1 α.2.2.2.1 α.2.2.2.2.val) ?_ ?_ ?_ ?_
  · convert key using 1
    rw [map_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun o _ => ?_
    have ht : ∀ (P : Fin (L o).length → MvPolynomial (Fin n × WV (Ix r tau o)) C),
        toAll o (∏ i, P i) = ∏ i, toAll (I := Ix r tau) o (P i) := fun P => by unfold toAll; rw [map_prod]
    rw [prodAll, ht, map_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [poly_eq (X o) (F o) _ (fun g s => r (tau o g s)) (hle o i), toAll, Fintype.prod_sigma]
    simp only [map_prod, map_pow]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases he : (RF.blkAt L o i).wt (X o) g s k.val = 0
    · simp only [he, pow_zero]
    · congr 1
      exact rename_minor r tau o (X o) (F o) (h1 o) (h2 o) (fun ρ => pl ⟨o, i, ρ⟩) g s k.val
        (Nat.le_of_lt_succ k.2) (le_rows _ _ _ _ _ he) (by rw [hrk]; exact Nat.le_of_lt_succ k.2)
  · intro α ρ b
    unfold ind
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
    · exact O.zero_mem
  · intro τ h
    obtain ⟨⟨o, g, s⟩, rfl⟩ := surj τ
    have h3 : ((o, 1 - g, s) : Orb × Fin 2 × ZMod d) = (o, g, s) := inj ((hcc o g s).symm.trans h)
    simp only [Prod.mk.injEq] at h3
    exact hg1 g h3.2.1
  · rintro ⟨o, i, g, s, k⟩ ⟨o', i', g', s', k'⟩ he he' hσ ρ ρ' b
    have h3 : ((o', g', s') : Orb × Fin 2 × ZMod d) = (o, 1 - g, s) := inj (hσ.trans (hcc o g s))
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl, rfl⟩ := h3
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hc, hc'⟩ := hc
    simp only [ind] at hc hc'
    split_ifs at hc hc' with a1 a2 a3 a4 <;> try contradiction
    have h4 := hpl (a2.symm.trans a4)
    have h5 : i = i' := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj h4).2)
    subst h5
    obtain ⟨e1, e2⟩ := both_groups _ _ _ _ _ _ _ he he'
    have b1 := k.2
    have b2 := k'.2
    rcases hsm o' g s' with h | h <;> simp only at e1 e2 <;> omega
  · intro τ i
    obtain ⟨⟨o, g, s⟩, rfl⟩ := surj τ
    simp only at i ⊢
    rw [← (((gap_sums _ _ (hdom (tau o g s))).2 _ le_rfl).1 i.val i.2), ← sum_fin_gap, Finset.sum_filter,
      Fintype.sum_sigma, Finset.sum_eq_single o]
    · rw [Fintype.sum_sigma]
      simp only [← hL']
      have : ∀ k : Fin (r (tau o g s) + 1), (if i.val < k.val then
          ∑ j : Fin (L o).length, (RF.blkAt L o j).wt (X o) g s k.val else 0) =
          ∑ j : Fin (L o).length, if i.val < k.val then (RF.blkAt L o j).wt (X o) g s k.val else 0 := by
        intro k
        split_ifs <;> simp
      rw [Finset.sum_congr rfl fun k _ => this k]
      refine Eq.trans ?_ Finset.sum_comm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fintype.sum_sigma, Finset.sum_eq_single g]
      · rw [Fintype.sum_sigma, Finset.sum_eq_single s]
        · simp
        · intro s' _ hs
          refine Finset.sum_eq_zero fun k _ => if_neg fun h => hs ?_
          have h3 : ((o, g, s') : Orb × Fin 2 × ZMod d) = (o, g, s) := inj h.1
          simpa using h3
        · simp
      · intro g' _ hs
        refine Finset.sum_eq_zero fun k _ => if_neg fun h => hs ?_
        have h3 : ((o, g', k.1) : Orb × Fin 2 × ZMod d) = (o, g, s) := inj h.1
        simp only [Prod.mk.injEq] at h3
        exact h3.2.1
      · simp
    · intro o' _ hs
      refine Finset.sum_eq_zero fun k _ => if_neg fun h => hs ?_
      have h3 : ((o', k.2.1, k.2.2.1) : Orb × Fin 2 × ZMod d) = (o, g, s) := inj h.1
      simp only [Prod.mk.injEq] at h3
      exact h3.1
    · simp

end Letters

section Main

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem blkMemSt_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab), Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ (Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V) (F : ∀ o, RF.Flag (RF.rd Y (pairOfLab ha hg) Hy o)), (∀ o g s q, (((F o).en g s q).2 : ℕ) = q) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ n : ℕ, RF.BlockMembershipChart Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) n F Finset.univ (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) := by
  intro E _ _ _ H Dw lv Xo c _ _ T io y C3 C _ _ V ι _ k Y _ Orb _ d _ lab ha hg surj hrk hj Hy F hF a hdom n L _ hL pl hpl
  refine ⟨_, ?_, isImgO Dw.mult lab.tau ha.inj (fun o => Y.raw (pairOfLab ha hg o))
    (fun w i => ι (chartUnitVectors C3 w i)) (fun w => rfl) _⟩
  refine prod_mem Dw.mult lab.tau V.RR _ _ (fun τ i => a (τ, i)) ha.inj surj ?_
    (fun o => RF.rd Y (pairOfLab ha hg) Hy o) F (fun o g s q => (F o).en_ty g s q) hF ?_ ?_ ?_ L
    (fun o => hL o (Finset.mem_univ o)) pl hpl
  · intro o g s
    fin_cases g
    · exact (ha.conj o s).symm
    · show ComplexEmbedding.conjugate (lab.tau o 1 s) = lab.tau o 0 s
      rw [ha.conj]
      exact star_star _
  · intro o g s
    exact (GlobalTheory.flag_of_numbering C V d (fun _ => ZMod d) (fun g s => Dw.mult (lab.tau o g s))
      (fun _ => Equiv.refl _) _ (RF.rd Y (pairOfLab ha hg) Hy o) (fun _ _ => rfl)).1 g s
  · intro o g s
    show _ < lab.n ∨ _ < lab.n
    by_cases hb : lab.big o g s
    · right
      rw [(hrk o).2.2 (1 - g) s (fun h => ((hrk o).1 g s).1 h hb)]
      exact hj
    · left
      rw [(hrk o).2.2 g s hb]
      exact hj
  · intro τ i j hij hj'
    exact hdom τ ⟨i, lt_of_le_of_lt hij hj'⟩ ⟨j, hj'⟩ hij

end Main

end GlobalTheory.MemPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemChartFamilyAtPlacePairsStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockProd_mem_chartFamily_at_place_pairs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab), Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ (Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V) (F : ∀ o, RF.Flag (RF.rd Y (pairOfLab ha hg) Hy o)), (∀ o g s q, (((F o).en g s q).2 : ℕ) = q) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ n : ℕ, RF.BlockMembershipChart Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) n F Finset.univ (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) := by
  first | exact @GlobalTheory.MemPair.blkMemSt_pair | exact GlobalTheory.MemPair.blkMemSt_pair | (intros; apply GlobalTheory.MemPair.blkMemSt_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtPairsOfPlaces
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem supply_pairs : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → (∀ o, (Even d ∧ ∀ s : ZMod d, (lab.big o 0 s ↔ Even s.val)) ∨ ∀ s, lab.big o 0 s) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → Supply V d Orb Finset.univ lab.n (lab.j + lab.j') lab.big (fun o g s => Dw.mult (lab.tau o g s)) (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) nW ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY hy hl Orb _ d _ lab ha hsurj hr hj hdich a hdom nW ν hν
  have hg : LabGeo C3 ι Y lab :=
    GlobalTheory.LabelledDirections.labGeoSt E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha
  have hnd : NDG Y := GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY
  have Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V := fun o =>
    FBChart.hyps GlobalTheory.cartHyp_of_formalBiextension axesFB GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.2 Y (pairOfLab ha hg o)
      (rankHyp_ofLab ha hg hr o)
      (GlobalTheory.T.nonDeg_raw_pairData_and_rankMaximal.2 C V (𝓞 E) _ Y d _ (pairOfLab ha hg o) hnd (rankHyp_ofLab ha hg hr o) _)
      (GlobalTheory.T.characterBound_pairs_of_places_integralChart hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hl Orb d lab ha hg hr o _)
  have hfl := fun o => GlobalTheory.flag_of_numbering C V d (fun _ => ZMod d) (fun g s => Dw.mult (lab.tau o g s))
    (fun _ => Equiv.refl _) (JJ (lab.II Dw o)) (RF.rd Y (pairOfLab ha hg) Hy o) (fun _ _ => rfl)
  have hrk : ∀ o g s, (RF.rd Y (pairOfLab ha hg) Hy o).rkF g s = Dw.mult (lab.tau o g s) := fun o => (hfl o).1
  choose F hF using fun o => (hfl o).2
  refine ⟨fun o => lab.II Dw o, fun o => JJ (lab.II Dw o), inferInstance, inferInstance,
    fun o => RF.rd Y (pairOfLab ha hg) Hy o, F, fun o => ⟨rfl, rfl⟩, fun o _ g s => ⟨Iff.rfl, hrk o g s⟩, ?_⟩
  refine RF.valBlocks_of_nuPlE Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) nW F Finset.univ _ ν
    (hν.trans (GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw lv Xo c T io y C3 C V ι hι k Y hY a nW))
    (pairsSep_ofLab ha hg) (GlobalTheory.RowVal.value_eq_prod C V (𝓞 E) _ Y d Orb _ (pairOfLab ha hg) Hy _ nW) GlobalTheory.JetProd.jetProd
    (GlobalTheory.T.blockProd_mem_chartFamily_at_place_pairs E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hsurj hr hj Hy F
      (fun o g s q => (hF o g s q).2) a hdom nW) ?_
  refine RF.blkAdm _ F Finset.univ _ (fun o _ => hdich o) (fun _ _ => hj) fun o _ g s q hq => ?_
  rw [hrk]
  by_contra hc
  exact hq (by unfold gap; rw [if_neg fun h => hc h.2])

end GlobalTheory.RowAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtPairsOfPlacesStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowData_supplied_at_pairs_of_places : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → (∀ o, (Even d ∧ ∀ s : ZMod d, (lab.big o 0 s ↔ Even s.val)) ∨ ∀ s, lab.big o 0 s) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → Supply V d Orb Finset.univ lab.n (lab.j + lab.j') lab.big (fun o g s => Dw.mult (lab.tau o g s)) (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) nW ν := by
  first | exact @GlobalTheory.RowAt.supply_pairs | exact GlobalTheory.RowAt.supply_pairs | (intros; apply GlobalTheory.RowAt.supply_pairs <;> assumption)
end
