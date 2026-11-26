module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenOfTop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivativeCongruenceGermIntegralTranslate
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DofIterSmulDir
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValColumnsCongr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEigenColumn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdConstantCoeffDmonOfCols
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.SymbolCols

theorem colM_apply {ι : Type} [Finite ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) (b : Fin n) (l : ι) :
    colM m b l = m (l, b) := by
  simp [colM]

theorem sum_degree_colM {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    ∑ b, (colM m b).degree = m.degree := by
  simp only [Finsupp.degree_eq_sum, colM_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem coeff_mul_congr {k σ : Type} [CommRing k] (N : ℕ) (f g E : MvPowerSeries σ k)
    (h : ∀ mo : σ →₀ ℕ, mo.degree ≤ N → coeff mo f = coeff mo g)
    (mo : σ →₀ ℕ) (hmo : mo.degree ≤ N) : coeff mo (f * E) = coeff mo (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add (f := _)]
  rw [h p.1 (by omega)]

theorem exists_col {ι : Type} [Fintype ι] {n : ℕ} (m a : ι × Fin n →₀ ℕ)
    (hdeg : m.degree = a.degree) (hne : m ≠ a) :
    ∃ b, (colM m b).degree ≤ (colM a b).degree ∧ colM m b ≠ colM a b := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ b, (colM a b).degree ≤ (colM m b).degree := fun b => by
    by_contra h
    have := hcon b (by omega)
    rw [this] at h
    exact h le_rfl
  have hs : ∑ b, (colM a b).degree = ∑ b, (colM m b).degree := by
    rw [sum_degree_colM, sum_degree_colM, hdeg]
  have heq := (Finset.sum_eq_sum_iff_of_le fun b _ => hle b).1 hs
  refine hne (Finsupp.ext fun ⟨l, b⟩ => ?_)
  rw [← colM_apply, ← colM_apply, hcon b (heq b (Finset.mem_univ b)).ge]

end GlobalTheory.SymbolCols

namespace GlobalTheory


end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdNabValLeadingMinors
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.CrudeValue

variable {k : Type} [CommRing k] {d : ℕ}

theorem constantCoeff_expS [Algebra ℚ k] {n : ℕ} (g : PS k n d) (hg : constantCoeff g = 0) :
    constantCoeff (FB.expS k g) = 1 := by
  unfold FB.expS
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [map_pow, hg, zero_pow hj, smul_zero]

theorem constantCoeff_ev_eq_zero {m n : ℕ} (a : Fin m → Pt k n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS k m d) (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have ha' : ∀ q : Fin m × Fin d, constantCoeff ((fun q : Fin m × Fin d => a q.1 q.2) q) = 0 :=
    fun q => ha q.1 q.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
    (hasSubst_of_constantCoeff_zero ha') ha' hf

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] [Algebra ℚ k] [Algebra R k]


omit [Algebra ℚ k] in
theorem constantCoeff_hL (B : FB R d O) (h : PS k 2 d) (hh : constantCoeff h = 0) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by
  have hp : ∀ i, constantCoeff (pt k (n := 1) d 0 i) = 0 := fun i => constantCoeff_X _
  refine constantCoeff_ev_eq_zero _ (fun j i => ?_) h hh
  fin_cases j
  · exact hp i
  · refine constantCoeff_ev_eq_zero ![pt k d 0] (fun j i' => ?_) (B.actK k w0 i) ?_
    · fin_cases j
      exact hp i'
    · unfold FB.actK
      rw [constantCoeff_map, B.A.const, map_zero]

theorem nabVal_monomial (B : FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (e : ι →₀ ℕ) :
    B.nabVal k h w0 q f u (MvPolynomial.monomial e 1) =
      constantCoeff (DmonOf (B.G.mapF (algebraMap R k)) u e
        (f * FB.expS k ((q : k) • B.hL k h w0))) := by
  classical
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  · simp only [FB.nabVal, FB.FK, DpolyOf, MvPolynomial.support_monomial,
      if_neg (one_ne_zero : (1 : k) ≠ 0), Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_true, map_one, one_mul]

end GlobalTheory.CrudeValue

namespace GlobalTheory


end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValLeOfMemSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdNabValLeadingMinorsOfColumnJets
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory


open CrudeValue SymbolCols in
theorem sum_prod_nabVal_leading_minors_of_column_jets : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), constantCoeff h = 0 → ∀ (w0 : O) (q : ℕ) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → ∀ (u : (Σ τ : T, Fin (r τ)) → Fin d → k) (lam : Fin n → (Σ τ : T, Fin (r τ)) → Fin d → k), (∀ b l l', (∃ i, col l.1 i = b) → (∃ i, col l'.1 i = b) → ∑ i, lam b l i * u l' i = if l = l' then 1 else 0) → ∀ (c : Fin n → k) (f : Fin n → PS k 1 d), (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ (colM al b).degree → coeff mo (f b) = c b * coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) = (∏ b, c b) * ∏ p, ((al p).factorial : k) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 q T _ _ r n col m hcol P al hP hal u lam hpair c f hf
  obtain ⟨h1, hhom, -, hsupp⟩ :=
    LeadingMinors.coeff_prod_leading_minors k T r n col m hcol P al hP hal
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  have halP : al ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, h1]
    exact one_ne_zero
  set E : PS k 1 d := FB.expS k ((q : k) • B.hL k h w0) with hE
  have hE1 : constantCoeff E = 1 := constantCoeff_expS _ (by
    rw [smul_eq_C_mul, map_mul, constantCoeff_hL B h hh w0, mul_zero])
  have hdeg : ∀ mo ∈ P.support, mo.degree = al.degree := fun mo hmo => by
    have := hhom (MvPolynomial.mem_support_iff.1 hmo)
    rw [← this, Finsupp.degree_eq_weight_one]
    rfl
  have hval : ∀ mo ∈ P.support, ∀ b, (colM mo b).degree ≤ (colM al b).degree →
      B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) =
        if colM mo b = colM al b then (∏ l, ((al (l, b)).factorial : k)) * c b else 0 := by
    intro mo hmo b hb
    have hsym := constantCoeff_dmonOf_prod_linear R k (algebraMap R k) d B.G _ u (lam b)
      (fun _ => 1) (colM al b) (colM mo b) (C (c b) * E)
      (fun l l' hl hl' => hpair b l l' (hsupp al halP l b (by rwa [colM_apply] at hl))
        (hsupp mo hmo l' b (by rwa [colM_apply] at hl'))) hb
    simp only [colM_apply, one_pow, mul_one, map_mul, constantCoeff_C, hE1] at hsym
    rw [nabVal_monomial, ← hE, ← hsym, ← mul_assoc, mul_comm _ (C (c b))]
    refine constantCoeff_DmonOf_congr_jet k d _ _ u (colM mo b) _ _ fun mo' hm => ?_
    refine coeff_mul_congr (colM al b).degree _ _ E (fun mo'' hm' => ?_) mo' (hm.trans hb)
    rw [coeff_C_mul]
    exact hf b mo'' hm'
  rw [Finset.sum_eq_single al]
  · rw [h1, one_mul, Finset.prod_congr rfl fun b _ => (hval al halP b le_rfl).trans (if_pos rfl),
      Finset.prod_mul_distrib, mul_comm, Fintype.prod_prod_type_right]
  · intro mo hmo hne
    obtain ⟨b, hb, hb'⟩ := exists_col mo al (hdeg mo hmo) hne
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hval mo hmo b hb, if_neg hb']), mul_zero]
  · intro hal'
    exact absurd halP hal'

end GlobalTheory
end

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FamGerm

namespace GlobalTheory.DepthBound

theorem minorMonomial_support {k : Type} [CommRing k] {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} {n : ℕ}
    (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) (Z : T → Prop) (hm : ∀ t, ¬ Z t → ∀ s, m t s = 0)
    {mo : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ} (hmo : mo ∈ (minorsP k col m).support) (l : Σ τ : T, Fin (r τ))
    (b : Fin n) (h : mo (l, b) ≠ 0) : Z l.1 ∧ ∃ i, col l.1 i = b := by
  have hS : minorsP k col m ∈ MvPolynomial.supported k
      {x : (Σ τ : T, Fin (r τ)) × Fin n | Z x.1.1 ∧ ∃ i, col x.1.1 i = x.2} := by
    refine Subalgebra.prod_mem _ fun τ _ => Subalgebra.prod_mem _ fun s _ => ?_
    by_cases hz : Z τ
    · exact Subalgebra.pow_mem _ (LeadingMinors.det_X_mem_supported _ _ fun a i => by exact ⟨hz, _, rfl⟩) _
    · rw [hm τ hz, pow_zero]; exact Subalgebra.one_mem _
  rw [MvPolynomial.mem_supported] at hS
  exact hS (Finset.mem_coe.2 ((MvPolynomial.mem_vars_iff_mem_support (l, b)).2
    ⟨mo, hmo, Finsupp.mem_support_iff.2 h⟩))

theorem map_minorsP {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {T : Type} [Fintype T] [DecidableEq T]
    {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) :
    MvPolynomial.map φ (minorsP k col m) = minorsP k' col m := by
  simp only [minorsP, map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 a i
  simp

theorem eval_minorsP {k : Type} [CommRing k] {T : Type} [Fintype T] [DecidableEq T]
    {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ)
    (y : (Σ τ : T, Fin (r τ)) × Fin n → k) :
    MvPolynomial.eval y (minorsP k col m) = ∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) =>
      y (⟨τ, Fin.castLE s.isLt a⟩, col τ (Fin.castLE s.isLt i))).det ^ m τ s := by
  simp only [minorsP, map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 a i
  simp

theorem minorMonomial_add (k : Type) [CommRing k] {T : Type} [Fintype T] [DecidableEq T]
    {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n) (m m' : ∀ τ, Fin (r τ) → ℕ) :
    minorsP k col (fun t s => m t s + m' t s) = minorsP k col m * minorsP k col m' := by
  simp only [minorsP, pow_add, Finset.prod_mul_distrib]

theorem sum_prod_restrict {k ι : Type} [CommRing k] [Fintype ι] {n : ℕ} (S : Finset (Fin n))
    (P : MvPolynomial (ι × Fin n) k) (hP : ∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → b ∈ S)
    (mu mu' : Fin n → (ι →₀ ℕ) → k) (h1 : ∀ mo ∈ P.support, ∀ b ∈ S, mu b (colM mo b) = mu' b (colM mo b))
    (h0 : ∀ b, b ∉ S → mu' b 0 = 1) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b ∈ S, mu b (colM mo b) =
      ∑ mo ∈ P.support, P.coeff mo * ∏ b, mu' b (colM mo b) := by
  refine Finset.sum_congr rfl fun mo hmo => ?_
  rw [Finset.prod_congr rfl (h1 mo hmo), Finset.prod_subset (Finset.subset_univ S)]
  intro b _ hb
  have : colM mo b = 0 := Finsupp.ext fun l => by
    by_contra h
    exact hb (hP mo hmo l b h)
  rw [this, h0 b hb]

section Nab

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k] [Algebra ℚ k]
  [Algebra R k] (B : FB R d O) (h : PS k 2 d)

theorem nabVal_smul_dir (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (c : ι → k) (u : ι → Fin d → k)
    (mo : ι →₀ ℕ) : B.nabVal k h w0 q f (fun l => c l • u l) (MvPolynomial.monomial mo 1) =
      (∏ l, c l ^ mo l) * B.nabVal k h w0 q f u (MvPolynomial.monomial mo 1) := by
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, PullbackColumn.dpolyOf_monomial_one, DirScale.dmonOf_smul_dir, map_mul,
    constantCoeff_C]

theorem nabVal_C_mul (w0 : O) (q : ℕ) (c : k) (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) : B.nabVal k h w0 q (C c * f) u P = c * B.nabVal k h w0 q f u P := by
  unfold FB.nabVal
  rw [mul_assoc, GE.dpolyOf_Cmul_f, map_mul, constantCoeff_C]

theorem const_of_canon (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have := congrArg constantCoeff hh.ax0
  rwa [WickVanishing.gt_const_ev_eq _ (WickVanishing.pair_points_zero_constant WickVanishing.gp_zero₂ (WickVanishing.gp_pt 0)), map_zero] at this

theorem nabVal_zero (hh : B.IsCanonGauge k h) (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) : B.nabVal k h w0 q f u (MvPolynomial.monomial 0 1) = constantCoeff f := by
  have hA : ∀ b : O, WickVanishing.GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    WickVanishing.gt_const_ev _ (WickVanishing.pair_points_zero_constant (WickVanishing.gp_pt 0) (WickVanishing.gp_comp1 _ _ (hA w0) (WickVanishing.gp_pt 0))) h
      (const_of_canon B h hh)
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, ColumnValue.dmonOf_zero_index, map_mul,
    CrudeValue.constantCoeff_expS _ (by rw [WickVanishing.nt_const_smul, cL, mul_zero]), mul_one]

variable {R' : Type} [CommRing R'] [Algebra R' k] (φ : R →+* R') (hφ : (algebraMap R' k).comp φ = algebraMap R k)
include hφ

omit [Algebra ℚ k] in
theorem toK_map {n : ℕ} (f : PS R n d) : FB.toK k (MvPowerSeries.map φ f) = FB.toK k f := by
  ext mo
  simp only [coeff_map, ← hφ, RingHom.comp_apply]

omit [Algebra ℚ k] in
theorem FK_map : (FBMap.mapFB φ B).FK k = B.FK k := funext fun _ => toK_map φ hφ _

omit [Algebra ℚ k] in
theorem actK_map : (FBMap.mapFB φ B).actK k = B.actK k := funext fun _ => funext fun _ => toK_map φ hφ _

theorem isCanonGauge_map (hh : B.IsCanonGauge k h) : (FBMap.mapFB φ B).IsCanonGauge k h := by
  refine ⟨hh.ax0, hh.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [FK_map B φ hφ]; exact (toK_map φ hφ _).trans hh.ph1
  · rw [FK_map B φ hφ]; exact (toK_map φ hφ _).trans hh.ph2
  · exact (toK_map φ hφ _).trans hh.sy
  · rw [actK_map B φ hφ]; exact (toK_map φ hφ _).trans (hh.ad a)

omit [Algebra ℚ k] in
theorem hL_map : (FBMap.mapFB φ B).hL k h = B.hL k h := by
  funext w0; unfold FB.hL; rw [actK_map B φ hφ]

omit [Algebra ℚ k] in
theorem dAct_map : dAct k (FBMap.mapFB φ B) = dAct k B := by
  funext a; unfold dAct; rw [actK_map B φ hφ]

theorem nabVal_map (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) : (FBMap.mapFB φ B).nabVal k h w0 q f u P = B.nabVal k h w0 q f u P := by
  unfold FB.nabVal; rw [FK_map B φ hφ, hL_map B h φ hφ]

end Nab

section Val

variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem mem_span_of_val_le (x y : TWO.Ov v) (hx : (x : F) ≠ 0) (h : v (x : F) ≤ v (y : F)) : y ∈ Ideal.span {x} := by
  have h0 : 0 ≤ v ((y : F) / x) := by
    by_contra hlt
    have e : v (y : F) = v ((y : F) / x) + v (x : F) := by rw [← v.map_mul, div_mul_cancel₀ _ hx]
    have hne : v (x : F) ≠ ⊤ := fun e' => hx (v.top_iff.1 e')
    have := WithTop.add_lt_add_right hne (not_le.1 hlt)
    rw [← e, zero_add] at this
    exact absurd h (not_le.2 this)
  refine Ideal.mem_span_singleton'.2 ⟨⟨(y : F) / x, h0⟩, Subtype.ext ?_⟩
  exact div_mul_cancel₀ _ hx

theorem val_le_of_mem_span {x y : TWO.Ov v} (h : y ∈ Ideal.span {x}) : v (x : F) ≤ v (y : F) := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
  rw [Subring.coe_mul, v.map_mul]
  exact le_add_of_nonneg_left (TWO.v_nonneg v c)

theorem val_prod_le {κ : Type} (S : Finset κ) (x : κ → F) (r : κ → ℚ) (h : ∀ k ∈ S, v (x k) ≤ (r k : ℚ)) :
    v (∏ k ∈ S, x k) ≤ ((∑ k ∈ S, r k : ℚ) : WithTop ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, v.map_mul, WithTop.coe_add]
    exact add_le_add (h k (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Val

theorem val_eigen_columns {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {F : Type} [Field F]
    [CharZero F] [Algebra R F] (v : AddValuation F (WithTop ℚ)) (φ : R →+* TWO.Ov v)
    (hφ : (algebraMap (TWO.Ov v) F).comp φ = algebraMap R F) (B : FB R d O) (h : PS F 2 d) (hh : B.IsCanonGauge F h)
    (w0 a : O) (p k : ℕ) (hp0 : p ≠ 0) (hp : ¬ IsUnit (p : TWO.Ov v)) (hcop : ∃ u u' : O, u * a + u' * star a = 1)
    (ω : PS R 1 d) (hω1 : constantCoeff ω = 1)
    (hω : FB.toK F ω = FB.expS F (ev (n := 1) ![B.actK F a] (B.hL F h w0) - (p : F) • B.hL F h w0))
    {T : Type} [Fintype T] [DecidableEq T] {rk : T → ℕ} (τ : T → O →+* TWO.Ov v)
    (e : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v)
    (he : ∀ (c : O) l, (dAct F B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F))
    (Z : T → Prop) (hZ : ∀ t, Z t → τ t a ∈ Ideal.span {(p : TWO.Ov v)})
    {n : ℕ} (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ)
    (hS : ∀ t i, Z t → col t i ∈ S) (hm : ∀ t, ¬ Z t → ∀ s, m t s = 0)
    (yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov v) (f : Fin n → PS (TWO.Ov v) 1 d)
    (hf0 : ∀ b ∈ S, v (constantCoeff (FB.toK F (f b))) = 0)
    (hf : ∀ b ∈ S, ∀ l, Z l.1 → ∀ mo, v (p : F) ≤ v (coeff mo (Dof (B.FK F) (fun i => (e l i : F)) (FB.toK F (f b)) -
      C (yy (l, b) : F) * FB.toK F (f b))))
    (γ ep : ℚ) (hep : v (p : F) = (ep : ℚ))
    (hy : ∀ t, Z t → ∀ s : Fin (rk t), v (((Matrix.of fun a i : Fin (s.val + 1) =>
      yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov v) : F) ≤ ((s.val + 1) * γ : ℚ))
    (hD : (∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) : ℕ) * γ < ep) :
    v (∑ mo ∈ (minorsP F col m).support, (minorsP F col m).coeff mo * ∏ b ∈ S,
      B.nabVal F h w0 (k * p) (FB.toK F (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
        (MvPolynomial.monomial (colM mo b) 1)) ≤ ((∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) : ℕ) * γ : ℚ) := by
  classical
  have hpF : ((p : TWO.Ov v) : F) = p := map_natCast (TWO.Ov v).subtype p
  have hmax : ∀ x ∈ Ideal.span {(p : TWO.Ov v)}, x ∈ IsLocalRing.maximalIdeal (TWO.Ov v) :=
    fun x hx => (Ideal.span_singleton_le_iff_mem _).2 hp hx
  let e₁ : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v := fun l => if Z l.1 then e l else 0
  let α : (Σ t, Fin (rk t)) → TWO.Ov v := fun l => if Z l.1 then τ l.1 a else 0
  let y₁ : (Σ t, Fin (rk t)) × Fin n → TWO.Ov v := fun x => if Z x.1.1 ∧ x.2 ∈ S then yy x else 0
  let f₁ : Fin n → PS (TWO.Ov v) 1 d := fun b => if b ∈ S then f b else 1
  have hB' := isCanonGauge_map B h φ hφ hh
  obtain ⟨ρ, hρ, hval⟩ := nabVal_columns_congr (TWO.Ov v) d O F (FBMap.mapFB φ B) h hB' w0 a p k
    (MvPowerSeries.map φ ω) (by rw [toK_map φ hφ, actK_map B φ hφ, hL_map B h φ hφ, hω])
    (Ideal.span {(p : TWO.Ov v)}) _ e₁ α
    (fun l => by
      by_cases hl : Z l.1
      · simpa only [α, if_pos hl] using hZ _ hl
      · simp only [α, if_neg hl]; exact Ideal.zero_mem _)
    (fun l => by
      rw [dAct_map B φ hφ]
      by_cases hl : Z l.1
      · simp only [e₁, α, if_pos hl]; exact he a l
      · simp only [e₁, α, if_neg hl, Pi.zero_apply, map_zero, zero_smul]
        exact Matrix.mulVec_zero _)
    (fun l l' => by
      rw [dAct_map B φ hφ]
      by_cases hl : Z l.1
      · by_cases hl' : Z l'.1
        · simp only [e₁, if_pos hl, if_pos hl']
          obtain ⟨u, u', huu⟩ := hcop
          have h1 : τ l'.1 (star a) ∉ IsLocalRing.maximalIdeal (TWO.Ov v) := fun hx => by
            have := congrArg (τ l'.1) huu
            rw [map_add (f := _), map_mul, map_mul, map_one] at this
            exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 (this ▸
              Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hmax _ (hZ _ hl'))) (Ideal.mul_mem_left _ _ hx)))
          have h2 : IsUnit (τ l.1 a - τ l'.1 (star a)) := by
            by_contra hx
            have := Ideal.sub_mem _ (hmax _ (hZ _ hl)) ((IsLocalRing.mem_maximalIdeal _).2 hx)
            rw [sub_sub_cancel] at this
            exact h1 this
          have h3 := bilinPart_eigen_mem_range (TWO.Ov v) d O F _ h hB' a (e l) (e l') _ _
            (by rw [dAct_map B φ hφ]; exact he a l) (by rw [dAct_map B φ hφ]; exact he (star a) l') h2
          have h4 := he w0 l'
          change (dAct F B w0).mulVec (fun i => algebraMap (TWO.Ov v) F (e l' i)) =
            algebraMap (TWO.Ov v) F (τ l'.1 w0) • fun i => algebraMap (TWO.Ov v) F (e l' i) at h4
          rw [h4, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
          exact Subring.mul_mem _ ⟨_, rfl⟩ h3
        · simp only [e₁, if_neg hl', Pi.zero_apply, map_zero]
          rw [show (fun _ : Fin d => (0 : F)) = 0 from rfl, Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero]
          exact Subring.zero_mem _
      · simp only [e₁, if_neg hl, Pi.zero_apply, map_zero]
        rw [show (fun _ : Fin d => (0 : F)) = 0 from rfl, zero_dotProduct]
        exact Subring.zero_mem _)
    n f₁ y₁
    (fun l b mo => by
      by_cases hl : Z l.1
      · by_cases hb : b ∈ S
        · refine mem_span_of_val_le v _ _ (by rw [hpF]; exact_mod_cast hp0) ?_
          rw [hpF]
          refine (hf b hb l hl mo).trans_eq (congrArg v ?_)
          simp only [e₁, f₁, y₁, if_pos hl, if_pos hb, if_pos (And.intro hl hb)]
          change _ = algebraMap (TWO.Ov v) F (coeff mo (Dof (FBMap.mapFB φ B).G.F (e l) (f b) - C (yy (l, b)) * f b))
          rw [← coeff_map]
          refine congrArg (coeff mo) (Eq.symm ?_)
          rw [map_sub, map_mul, map_C, InvDerMap.map_Dof, ← FK_map B φ hφ]
          rfl
        · simp [f₁, y₁, hb, Dof]
      · simp [e₁, y₁, hl, Dof])
    (minorsP (TWO.Ov v) col m)
  have hinj : Function.Injective (algebraMap (TWO.Ov v) F) := Subtype.val_injective
  rw [sum_prod_restrict S (minorsP F col m) (fun mo hmo l b hb => by
      obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m Z hm hmo l b hb
      exact hS _ i hz)
    (fun b mo => B.nabVal F h w0 (k * p) (FB.toK F (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
        (MvPolynomial.monomial mo 1))
    (fun b mo => (FBMap.mapFB φ B).nabVal F h w0 (p * k) (FB.toK F (f₁ b * MvPowerSeries.map φ ω ^ k))
      (fun l i => algebraMap (TWO.Ov v) F (e₁ l i)) (MvPolynomial.monomial mo 1))
    (fun mo hmo b hb => by
      have e1 : (fun l i => algebraMap (TWO.Ov v) F (e₁ l i)) =
          fun l => (if Z l.1 then (1 : F) else 0) • fun i => (e l i : F) := by
        funext l i
        by_cases hl : Z l.1 <;> simp [e₁, hl]
      have e2 : ∏ l, (if Z l.1 then (1 : F) else 0) ^ colM mo b l = 1 := Finset.prod_eq_one fun l _ => by
        by_cases hl : Z l.1
        · rw [if_pos hl, one_pow]
        · have : colM mo b l = 0 := by
            by_contra hx
            exact hl (minorMonomial_support col m Z hm hmo l b hx).1
          rw [this, pow_zero]
      beta_reduce
      rw [nabVal_map B h φ hφ, e1, nabVal_smul_dir, e2, one_mul, mul_comm p k, FB.toK, FB.toK, FB.toK, map_mul, map_pow,
        ← FB.toK, ← FB.toK, ← FB.toK, ← FB.toK, toK_map φ hφ]
      simp only [f₁, if_pos hb])
    (fun b hb => by
      beta_reduce
      rw [nabVal_zero _ h hB']
      simp [f₁, hb, hω1])]
  rw [← map_minorsP (algebraMap (TWO.Ov v) F), MvPolynomial.support_map_of_injective _ hinj]
  simp only [MvPolynomial.coeff_map]
  rw [hval, map_add (f := _)]
  have hmain : v (algebraMap (TWO.Ov v) F (MvPolynomial.eval y₁ (minorsP (TWO.Ov v) col m) *
      ∏ b, constantCoeff (f₁ b))) ≤ ((∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) : ℕ) * γ : ℚ) := by
    rw [map_mul, v.map_mul, map_prod, eval_minorsP, map_prod]
    refine (add_le_add (val_prod_le v _ _ (fun t => ∑ s : Fin (rk t), (m t s * (s.val + 1) : ℕ) * γ) fun t _ => ?_)
      (val_prod_le v _ _ (fun _ => 0) fun b _ => ?_)).trans (le_of_eq ?_)
    · rw [map_prod]
      refine val_prod_le v _ _ _ fun s _ => ?_
      rw [map_pow, v.map_pow]
      by_cases ht : Z t
      · have e3 : (Matrix.of fun a i : Fin (s.val + 1) =>
            y₁ (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))) = Matrix.of fun a i : Fin (s.val + 1) =>
            yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i)) := by
          ext1 a i
          exact if_pos ⟨ht, hS _ _ ht⟩
        rw [e3]
        refine (nsmul_le_nsmul_right (hy t ht s) _).trans (le_of_eq ?_)
        rw [← WithTop.coe_nsmul]
        congr 1
        push_cast
        ring
      · simp [hm t ht]
    · by_cases hb : b ∈ S
      · have := hf0 b hb
        rw [constantCoeff_map] at this
        simp only [f₁, if_pos hb, this]
        rfl
      · simp [f₁, hb]
    · rw [← WithTop.coe_add]
      congr 1
      simp [Finset.sum_mul]
  have hρ' : ((ep : ℚ) : WithTop ℚ) ≤ v (algebraMap (TWO.Ov v) F ρ) := by
    rw [← hep, ← hpF]; exact val_le_of_mem_span v hρ
  rw [v.map_add_eq_of_lt_left (lt_of_le_of_lt hmain (lt_of_lt_of_le (by exact_mod_cast hD) hρ'))]
  exact hmain

theorem val_factorial {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {p n : ℕ} (hp : p.Prime)
    (hpu : ¬ IsUnit (p : TWO.Ov v)) (hn : n < p) : v (n.factorial : F) = 0 := by
  have h1 : IsCoprime ((n.factorial : ℤ) : TWO.Ov v) ((p : ℤ) : TWO.Ov v) :=
    (Nat.isCoprime_iff_coprime.2 (hp.coprime_factorial_of_lt hn).symm).intCast
  obtain ⟨a, b, hab⟩ := h1
  have h2 : IsUnit ((n.factorial : ℕ) : TWO.Ov v) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact_mod_cast isUnit_of_mul_isUnit_right h
    · exact absurd (by exact_mod_cast isUnit_of_mul_isUnit_right h) hpu
  have h3 := TWO.v_unit v h2.unit
  rwa [IsUnit.unit_spec, show (((n.factorial : ℕ) : TWO.Ov v) : F) = n.factorial from
    map_natCast (TWO.Ov v).subtype _] at h3

theorem val_unit_columns {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {F : Type} [Field F]
    [CharZero F] [Algebra R F] (v : AddValuation F (WithTop ℚ)) (B : FB R d O) (h : PS F 2 d)
    (hh : B.IsCanonGauge F h) (w0 a : O) (p k : ℕ) (hp' : p.Prime) (hp : ¬ IsUnit (p : TWO.Ov v)) (ω : PS R 1 d)
    (hω : FB.toK F ω = FB.expS F (ev (n := 1) ![B.actK F a] (B.hL F h w0) - (p : F) • B.hL F h w0))
    {T : Type} [Fintype T] [DecidableEq T] {rk : T → ℕ} (τ : T → O →+* TWO.Ov v)
    (e : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v)
    (he : ∀ l, (dAct F B a).mulVec (fun i => (e l i : F)) = (τ l.1 a : F) • fun i => (e l i : F))
    (Z : T → Prop) (hZ : ∀ t, Z t → IsUnit (τ t a)) (lam : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v)
    (hlam : ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0)
    {n : ℕ} (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ)
    (hcol : ∀ t, Function.Injective (col t))
    (hS : ∀ t i, Z t → col t i ∈ S) (hm : ∀ t, ¬ Z t → ∀ s, m t s = 0)
    (hD : ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) < p) :
    ∃ (g : Fin n → PS F 1 d) (nb : Fin n → ℕ), (∀ b mo, 0 ≤ v (coeff mo (g b))) ∧
      ∑ b, nb b = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) ∧ ∀ f : Fin n → PS F 1 d,
      (∀ b ∈ S, ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ nb b → coeff mo (f b) = coeff mo (g b)) →
      v (∑ mo ∈ (minorsP F col m).support, (minorsP F col m).coeff mo * ∏ b ∈ S,
        B.nabVal F h w0 (k * p) (ev (n := 1) ![B.actK F a] (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
          (MvPolynomial.monomial (colM mo b) 1)) = 0 := by
  classical
  let sc : (Σ t, Fin (rk t)) → (TWO.Ov v)ˣ := fun l => if hl : Z l.1 then (hZ _ hl).unit else 1
  let lam' : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v := fun l i => ((sc l)⁻¹ : (TWO.Ov v)ˣ) * lam l i
  let u' : (Σ t, Fin (rk t)) → Fin d → F := fun l => ((sc l : TWO.Ov v) : F) • fun i => (e l i : F)
  obtain ⟨al, hal⟩ : ∃ al : (Σ t, Fin (rk t)) × Fin n →₀ ℕ, al = ∑ τ, ∑ s : Fin (rk τ), m τ s •
    ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (rk τ)),
      col τ (Fin.castLE s.isLt a)) 1 := ⟨_, rfl⟩
  obtain ⟨hc1, -, hdeg, -⟩ := LeadingMinors.coeff_prod_leading_minors F T rk n col m hcol (minorsP F col m) al rfl hal
  have hsup : al ∈ (minorsP F col m).support := MvPolynomial.mem_support_iff.2 (by rw [hc1]; exact one_ne_zero)
  have hcols : ∀ mo ∈ (minorsP F col m).support, ∀ l b, mo (l, b) ≠ 0 → b ∈ S := fun mo hmo l b hb => by
    obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m Z hm hmo l b hb
    exact hS _ i hz
  let g : Fin n → PS F 1 d := fun b =>
    ∏ l, (∑ i, C (lam' l i : F) * (X ((0 : Fin 1), i) : PS F 1 d)) ^ al (l, b)
  refine ⟨g, fun b => (colM al b).degree, fun b mo => ?_, (SymbolCols.sum_degree_colM al).trans hdeg, fun f hf => ?_⟩
  · have : g b = MvPowerSeries.map (algebraMap (TWO.Ov v) F)
        (∏ l, (∑ i, C (lam' l i) * (X ((0 : Fin 1), i) : PS (TWO.Ov v) 1 d)) ^ al (l, b)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_prod, map_pow, map_sum, map_mul, map_C, map_X]
      rfl
    rw [this, coeff_map]
    exact TWO.v_nonneg v _
  let f₂ : Fin n → PS F 1 d := fun b => if b ∈ S then f b else g b
  have key := sum_prod_nabVal_leading_minors_of_column_jets R d O F B h (const_of_canon B h hh) w0 k T rk n col m hcol
    (minorsP F col m) al rfl hal u' (fun _ l i => (lam' l i : F)) (fun b l l' _ _ => by
      have h1 : ∑ i, lam' l i * ((sc l' : TWO.Ov v) * e l' i) = if l = l' then 1 else 0 := by
        have : ∀ i, lam' l i * ((sc l' : TWO.Ov v) * e l' i) =
            (((sc l)⁻¹ : (TWO.Ov v)ˣ) * (sc l' : TWO.Ov v)) * (lam l i * e l' i) := fun i => by
          simp only [lam']; ring
        simp only [this]
        rw [← Finset.mul_sum, hlam]
        split_ifs with hl
        · rw [hl, Units.inv_mul, mul_one]
        · rw [mul_zero]
      have h2 := congrArg (algebraMap (TWO.Ov v) F) h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, apply_ite (algebraMap (TWO.Ov v) F), map_one, map_zero] at h2
      exact h2)
    (fun _ => 1) f₂ (fun b mo hmo => by
      rw [one_mul]
      by_cases hb : b ∈ S
      · simp only [f₂, if_pos hb]; exact hf b hb mo hmo
      · simp only [f₂, if_neg hb]; rfl)
  rw [sum_prod_restrict S (minorsP F col m) hcols
    (fun b mo => B.nabVal F h w0 (k * p) (ev (n := 1) ![B.actK F a] (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
      (MvPolynomial.monomial mo 1))
    (fun b mo => B.nabVal F h w0 k (f₂ b) u' (MvPolynomial.monomial mo 1))
    (fun mo hmo b hb => by
      beta_reduce
      rw [mul_comm k p, nabVal_pullback_monomial R d O F B h hh w0 a p k ω hω _ _ (fun l => (τ l.1 a : F)) he,
        nabVal_smul_dir]
      simp only [f₂, if_pos hb]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : Z l.1
      · simp only [sc, dif_pos hl, IsUnit.unit_spec]
      · have : colM mo b l = 0 := by
          by_contra hx
          exact hl (minorMonomial_support col m Z hm hmo l b hx).1
        rw [this, pow_zero, pow_zero])
    (fun b hb => by
      beta_reduce
      have h0 : ∀ l, al (l, b) = 0 := fun l => by
        by_contra hx
        exact hb (hcols al hsup l b hx)
      rw [nabVal_zero _ h hh]
      simp only [f₂, if_neg hb, g, h0, pow_zero, Finset.prod_const_one, map_one]), key, Finset.prod_const_one, one_mul]
  refine Finset.prod_induction _ (fun x => v x = 0) (fun x x' hx hx' => by rw [v.map_mul, hx, hx', add_zero])
    v.map_one fun x _ => val_factorial v hp' hp (lt_of_le_of_lt (Finsupp.le_degree x al) (hdeg ▸ hD))

end GlobalTheory.DepthBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ColValueMulOfDisjointColumns
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem sum_coeff_mul_weight {k σ : Type} [CommRing k] (w : (σ →₀ ℕ) → k) (P₁ P₂ : MvPolynomial σ k) :
    ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * w mo =
      ∑ m₁ ∈ P₁.support, ∑ m₂ ∈ P₂.support, P₁.coeff m₁ * P₂.coeff m₂ * w (m₁ + m₂) := by
  let L : MvPolynomial σ k →ₗ[k] k := (MvPolynomial.basisMonomials σ k).constr k w
  have hL : ∀ (m : σ →₀ ℕ) (a : k), L (MvPolynomial.monomial m a) = a * w m := by
    intro m a
    have h1 : (MvPolynomial.monomial m a : MvPolynomial σ k) =
        a • MvPolynomial.basisMonomials σ k m := by
      rw [MvPolynomial.coe_basisMonomials]
      simp [MvPolynomial.smul_monomial]
    rw [h1, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hP : ∀ P : MvPolynomial σ k, L P = ∑ mo ∈ P.support, P.coeff mo * w mo := by
    intro P
    conv_lhs => rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hL m _
  rw [← hP]
  conv_lhs => rw [P₁.as_sum, P₂.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [MvPolynomial.monomial_mul, hL]

theorem colValue_mul_of_disjoint_columns :
    ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (n : ℕ) (mu : Fin n → (ι →₀ ℕ) → k) (T : Finset (Fin n)) (P₁ P₂ : MvPolynomial (ι × Fin n) k), (∀ mo ∈ P₁.support, ∀ l b, mo (l, b) ≠ 0 → b ∈ T) → (∀ mo ∈ P₂.support, ∀ l b, mo (l, b) ≠ 0 → b ∉ T) → ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * ∏ b, mu b (colM mo b) = (∑ mo ∈ P₁.support, P₁.coeff mo * ∏ b ∈ T, mu b (colM mo b)) * ∑ mo ∈ P₂.support, P₂.coeff mo * ∏ b ∈ Tᶜ, mu b (colM mo b) := by
  intro k _ ι _ n mu T P₁ P₂ h₁ h₂
  rw [sum_coeff_mul_weight (fun mo => ∏ b, mu b (colM mo b)) P₁ P₂, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_
  have e₁ : ∏ b ∈ T, mu b (colM (m₁ + m₂) b) = ∏ b ∈ T, mu b (colM m₁ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₂ (l, b) = 0 := by
      by_contra h
      exact h₂ m₂ hm₂ l b h hb
    simp [colM, this]
  have e₂ : ∏ b ∈ Tᶜ, mu b (colM (m₁ + m₂) b) = ∏ b ∈ Tᶜ, mu b (colM m₂ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₁ (l, b) = 0 := by
      by_contra h
      exact (Finset.mem_compl.1 hb) (h₁ m₁ hm₁ l b h)
    simp [colM, this]
  rw [← Finset.prod_mul_prod_compl T, e₁, e₂]
  ring

end GlobalTheory
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthBound

theorem sum_prod_const_mul {k Λ : Type} [CommRing k] [Fintype Λ] {n : ℕ} (S : Finset (Fin n))
    (P : MvPolynomial (Λ × Fin n) k) (mu mu' : Fin n → (Λ →₀ ℕ) → k) (c : Fin n → k)
    (h : ∀ b ∈ S, ∀ mo, mu b mo = c b * mu' b mo) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b ∈ S, mu b (colM mo b) =
      (∏ b ∈ S, c b) * ∑ mo ∈ P.support, P.coeff mo * ∏ b ∈ S, mu' b (colM mo b) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [Finset.prod_congr rfl fun b hb => h b hb _, Finset.prod_mul_distrib]
  ring

end GlobalTheory.DepthBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundFromCharactersPointDatum
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.FamGerm GlobalTheory.DepthBound
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthFromChars

theorem depth_bound_of_chars : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (FamGerm.minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k := by
  intro hL _ hL4 hTB hC p hp E _ _ _ H V _ _ _ F _ _ _ _ _ _ y hcomp hpu Dw I r bs Cc M₀ hred a k
    haa hcop hpk T _ _ rk τ e he isV _ hV hU ⟨lam, hlam⟩ ⟨ε, hε⟩ n S col m hcol hS D hD hDp hk hM h hh ep hep
  have hTW : TwistBCSpanStatement := twistBCSpan_of hTB
  have hVR : TWM.VRatioGtStatement := GlobalTheory.RatioVal.main
  have hUU : UUStatement := GlobalTheory.UnitBallFree.main hL.globalFns hTB
  obtain ⟨jA, jR, -, -, -, -, -, jS, jX, -, -, -, -, jB⟩ := GlobalTheory.JetRoad.jetRoad
  have hG : FamGerm.GermExSt := GlobalTheory.FamGermExist.germ_exists_unique_linear hL hL4 hTW jA jR jS jX
  have hGV : GermValSt := GlobalTheory.GermValuation.main hL hL4 hTW jA jR jS jX hG
  have hJ : JetsSt := GlobalTheory.GermJets.jets hL hL4 hTW jA jR jS jX hG
  have hP : PullGermSt := GlobalTheory.PullGerm.germ_pullback hL hL4 hTW jA jR jS jX GlobalTheory.JetRoad.rosIdSt hG
  have hE : EigGermSt := GlobalTheory.T.derivative_congruence_germ_integral_translate hL hL4 hTW jA jR jS jX GlobalTheory.JetRoad.rosIdSt jB hG
  classical
  let _ := H.starRing
  have hp' : p.Prime := hp.out
  have hp2 : 2 ≤ p := hp'.two_le
  have hpF : ((p : TWO.Ov y.v) : F) = p := map_natCast (TWO.Ov y.v).subtype p
  have hep0 : 0 < ep := by
    by_contra hle
    refine hpu (Ideal.span_singleton_eq_top.1 ((Ideal.eq_top_iff_one _).2 (mem_span_of_val_le y.v _ 1 ?_ ?_)))
    · rw [hpF]; exact_mod_cast hp'.ne_zero
    · rw [hpF, hep, OneMemClass.coe_one, y.v.map_one]
      exact_mod_cast not_lt.1 hle
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp2
    linarith
  set θ : ℚ := ep / ((p : ℚ) - 1) with hθ
  have hθ0 : 0 < θ := div_pos hep0 hp1
  obtain ⟨c, hc⟩ := ExactTerm.exists_val_eq_of_nonneg y.hv hθ0.le
  obtain ⟨ω, hω1, hω⟩ := FramePull.exists_integral_frame_pullback V y.d (𝓞 E) F y.B h hh H.w0 a p haa

  let m₁ : ∀ t, Fin (rk t) → ℕ := fun t s => if isV t then m t s else 0
  let m₂ : ∀ t, Fin (rk t) → ℕ := fun t s => if isV t then 0 else m t s
  have hm : m = fun t s => m₁ t s + m₂ t s := by
    funext t s
    by_cases ht : isV t <;> simp [m₁, m₂, ht]
  have hm₁ : ∀ t, ¬ isV t → ∀ s, m₁ t s = 0 := fun t ht s => if_neg ht
  have hm₂ : ∀ t, ¬ ¬ isV t → ∀ s, m₂ t s = 0 := fun t ht s => if_pos (not_not.1 ht)
  have hDD : ∑ t, ∑ s : Fin (rk t), m₁ t s * (s.val + 1) + ∑ t, ∑ s : Fin (rk t), m₂ t s * (s.val + 1) = D := by
    rw [hD, hm]
    simp only [add_mul, Finset.sum_add_distrib]

  obtain ⟨y₁, hy₁, hy₂⟩ := hC p E H V F y hcomp hpu a haa hcop {t // isV t} (fun t => rk t.1) (fun t => τ t.1)
    (fun l => e ⟨l.1.1, l.2⟩) (fun c l => he c ⟨l.1.1, l.2⟩) (fun t => hV t.1 t.2)
    (fun t => ⟨fun i => lam ⟨t.1, i⟩, fun i i' => by simpa using hlam ⟨t.1, i⟩ ⟨t.1, i'⟩⟩)
    ⟨fun t => ε t.1, fun t t' => by simpa only [Subtype.ext_iff] using hε t.1 t'.1⟩
    ⟨c, by rw [TWO.mem_Ov, hc]; exact_mod_cast hθ0.le⟩
    (by
      change (p - 1) • y.v c = _
      rw [hc, hep, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one, hθ,
        mul_div_cancel₀ _ hp1.ne'])
    n (fun t => col t.1) (fun t => hcol t.1)
  let yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v := fun x =>
    if hx : isV x.1.1 then y₁ (⟨⟨x.1.1, hx⟩, x.1.2⟩, x.2) else 0
  choose s₁ s₁' t₁ c₁ f₁ r₁ h₁ hc₁ hr₁ hf₁ hf₁' using fun b => exists_eigen_column y hL hTW hVR hUU hG hGV hE Dw I r bs
    Cc M₀ hred a p k hp' (by omega) haa hcop hpk (Σ t : {t // isV t}, Fin (rk t.1)) (fun l => e ⟨l.1.1, l.2⟩)
    (fun l => y₁ (l, b)) (fun l => τ l.1.1 a) (fun l => hV _ l.1.2) (fun l => he a ⟨l.1.1, l.2⟩) (hy₁ b) h hh ω hω1 hω
  have hD₁ : ((∑ t, ∑ s : Fin (rk t), m₁ t s * (s.val + 1) : ℕ) : ℚ) * θ ≤ D * θ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hθ0.le
  have hF₁ := val_eigen_columns y.v _ (fO_comp_eq y) y.B h hh H.w0 a p k hp'.ne_zero hpu hcop ω hω1 hω τ e he isV hV
    S col m₁ (fun t i ht => (hS t i).2 ht) hm₁ yy f₁ (fun b _ => hf₁ b)
    (fun b _ l hl mo => by
      simp only [yy, dif_pos hl]
      exact hf₁' b ⟨⟨l.1, hl⟩, l.2⟩ mo)
    θ ep hep
    (fun t ht s => by
      simp only [yy, dif_pos ht]
      refine (hy₂ ⟨t, ht⟩ s).trans (le_of_eq ?_)
      change (s.val + 1) • y.v c = _
      rw [hc, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_succ])
    (hD₁.trans_lt (by
      have : (D : ℚ) < (p : ℚ) - 1 := by
        have h1 : D + 1 < p := by omega
        have h2 : (D : ℚ) + 1 < p := by exact_mod_cast h1
        linarith
      calc (D : ℚ) * θ < ((p : ℚ) - 1) * θ := mul_lt_mul_of_pos_right this hθ0
        _ = ep := by rw [hθ, mul_div_cancel₀ _ hp1.ne']))

  obtain ⟨g, nb, hg, hnb, hF₂⟩ := val_unit_columns y.v y.B h hh H.w0 a p k hp' hpu ω hω τ e (he a) (fun t => ¬ isV t)
    hU lam hlam Sᶜ col m₂ hcol (fun t i ht => Finset.mem_compl.2 fun h' => ht ((hS t i).1 h')) hm₂ (by omega)
  have hnbD : ∑ b, nb b ≤ D := by omega
  have hnbD' : ∀ b, nb b ≤ D := fun b =>
    (Finset.single_le_sum (f := nb) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)).trans hnbD
  choose s₂ s₂' t₂ c₂ f₂ r₂ h₂ hc₂ hr₂ hf₂ using fun b => exists_jet_column y hL hG hJ hP r bs Cc M₀ hred a p k (nb b)
    (by omega) haa (by have := hnbD' b; omega)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hnbD' b) hred.2.1) hM) h hh ω hω (g b) (hg b)
  have hF₂' := hF₂ f₂ fun b _ => hf₂ b
  let f : Fin n → PS F 1 y.d := fun b =>
    if b ∈ S then MvPowerSeries.C (c₁ b) * (FB.toK F (f₁ b) * FB.toK F ω ^ k)
    else MvPowerSeries.C (c₂ b) * (ev (n := 1) ![y.B.actK F a] (f₂ b) * FB.toK F ω ^ k)
  have hval : y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (minorsP F col m) f) ≤
      ((∑ b ∈ S, r₁ b + D * θ + ∑ b ∈ Sᶜ, r₂ b : ℚ) : WithTop ℚ) := by
    have e₁ := colValue_mul_of_disjoint_columns F _ n (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
      (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) S (minorsP F col m₁) (minorsP F col m₂)
      (fun mo hmo l b hb => by
        obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m₁ isV hm₁ hmo l b hb
        exact (hS _ i).2 hz)
      (fun mo hmo l b hb => by
        obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m₂ (fun t => ¬ isV t) hm₂ hmo l b hb
        exact fun h' => hz ((hS _ i).1 h'))
    rw [← minorMonomial_add, ← hm, sum_prod_const_mul S _ (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
        (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) (fun b mo => y.B.nabVal F h H.w0 (k * p)
        (FB.toK F (f₁ b) * FB.toK F ω ^ k) (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) c₁
        (fun b hb mo => by simp only [f, if_pos hb]; exact nabVal_C_mul _ _ _ _ _ _ _ _),
      sum_prod_const_mul Sᶜ _ (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
        (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) (fun b mo => y.B.nabVal F h H.w0 (k * p)
        (ev (n := 1) ![y.B.actK F a] (f₂ b) * FB.toK F ω ^ k) (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) c₂
        (fun b hb mo => by simp only [f, if_neg (Finset.mem_compl.1 hb)]; exact nabVal_C_mul _ _ _ _ _ _ _ _)] at e₁
    refine (congrArg y.v e₁).trans_le ?_
    rw [y.v.map_mul, y.v.map_mul, y.v.map_mul, hF₂', add_zero, WithTop.coe_add, WithTop.coe_add]
    exact add_le_add (add_le_add (val_prod_le y.v _ _ _ fun b _ => (hc₁ b).le)
      (hF₁.trans (WithTop.coe_le_coe.2 hD₁))) (val_prod_le y.v _ _ _ fun b _ => (hc₂ b).le)
  obtain ⟨gm, hgm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hval)
  refine ⟨fun b => if b ∈ S then s₁ b else s₂ b, fun b => if b ∈ S then s₁' b else s₂' b,
    fun b => if b ∈ S then t₁ b else t₂ b, f, gm, fun b => ?_, hgm.symm, ?_⟩
  · by_cases hb : b ∈ S
    · simp only [f, if_pos hb]; exact h₁ b
    · simp only [f, if_neg hb]; exact h₂ b
  · rw [← hgm, WithTop.coe_le_coe] at hval
    have h1 : (gm : ℝ) ≤ ∑ b ∈ S, (r₁ b : ℝ) + D * (ep / (p - 1)) + ∑ b ∈ Sᶜ, (r₂ b : ℝ) := by
      rw [hθ] at hval
      exact_mod_cast hval
    have h2 : ∑ b ∈ S, (r₁ b : ℝ) ≤ S.card * r * Cc / (4 * k) := by
      refine (Finset.sum_le_card_nsmul _ _ _ fun b _ => hr₁ b).trans (le_of_eq ?_)
      rw [nsmul_eq_mul]; ring
    have hCk : 0 ≤ Cc / k := div_nonneg hred.1 (Nat.cast_nonneg _)
    have h3 : ∑ b ∈ Sᶜ, (r₂ b : ℝ) ≤ (D : ℝ) ^ 2 * Cc / k := by
      have h4 : ∑ b ∈ Sᶜ, nb b ^ 2 ≤ D ^ 2 :=
        calc ∑ b ∈ Sᶜ, nb b ^ 2 ≤ ∑ b, nb b ^ 2 := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          _ ≤ ∑ b, nb b * D := Finset.sum_le_sum fun b _ => by
            rw [sq]; exact Nat.mul_le_mul_left _ (hnbD' b)
          _ ≤ D ^ 2 := by rw [← Finset.sum_mul, sq]; exact Nat.mul_le_mul_right _ hnbD
      refine (Finset.sum_le_sum fun b _ => hr₂ b).trans ?_
      simp only [mul_div_assoc]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h4) hCk
    rw [mul_div_assoc (D : ℝ) (ep : ℝ)]
    linarith

end GlobalTheory.DepthFromChars
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundFromCharactersPointDatumStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_bound_from_characters_pointDatum : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (FamGerm.minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k := by
  first | exact @GlobalTheory.DepthFromChars.depth_bound_of_chars | exact GlobalTheory.DepthFromChars.depth_bound_of_chars | (intros; apply GlobalTheory.DepthFromChars.depth_bound_of_chars <;> assumption)
end
