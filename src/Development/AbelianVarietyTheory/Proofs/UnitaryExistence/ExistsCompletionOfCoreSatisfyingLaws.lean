module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentWeight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodFormAdditiveBalancedPosDefBoundedRank
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocalDataAtConcretePointsExist
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTower
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor
  Formalism.L2.Pj GlobalTheory.Models

namespace GlobalTheory.LocalData.Towers

theorem isIntegral_rat_zeta_of_coeff (n : ℕ) : IsIntegral ℚ (zeta n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : zeta 0 = 1 := by simp [zeta]
    rw [this]; exact isIntegral_one
  · have h := Complex.isPrimitiveRoot_exp n hn.ne'
    exact (h.isIntegral hn).tower_top

theorem exists_coeff_containing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (s : Finset ℂ), (∀ z ∈ s, IsAlgebraic ℚ z) → ∃ c : Coeff l, ∀ z ∈ s, z ∈ c.F := _root_.GlobalTheory.exists_coeff_containing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_valuationSubring {l : Level H} (c : Coeff l) (p : ℕ) (v : HeightOneSpectrum (𝓞 c.F))
    (hv : (p : 𝓞 c.F) ∈ v.asIdeal) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ c.V W = (v.valuation c.F).valuationSubring := by
  obtain ⟨W, hWe, hWn⟩ := GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom
    (v.valuation c.F).valuationSubring
  have hpU : (p : c.F) ∈ (v.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (v.valuation c.F)).lt_one_iff_lt_one]
    have := (v.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hv
    simpa using this
  exact ⟨W, by simpa using hWn _ hpU, hWe⟩

theorem baseAt_of_eq {l : Level H} {c : Coeff l} {v : HeightOneSpectrum (𝓞 c.F)} {V : ValuationSubring c.F}
    (h : V = (v.valuation c.F).valuationSubring) : PointsOfFlagModel.BaseAt v V.subtype := by
  subst h
  refine ⟨Subtype.val_injective, fun x => ⟨?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩⟩
  rintro ⟨y, rfl⟩
  exact y.2

theorem exists_coeff_ge {l : Level H} (c : Coeff l) (l₂ : Level H) : ∃ c₂ : Coeff l₂, c.F ≤ c₂.F := by
  classical
  haveI := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c₂, h⟩ := exists_coeff_containing E H l₂ (Finset.univ.image fun i => ((b i : c.F) : ℂ)) (by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom c.F.val)
  refine ⟨c₂, fun x hx => ?_⟩
  have key : ∀ y : c.F, (y : ℂ) ∈ c₂.F := by
    intro y
    have hy : y ∈ Submodule.span ℚ (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      have e : ((a • y : c.F) : ℂ) = (a : ℂ) * (y : ℂ) := by simp [Rat.smul_def]
      rw [e]
      exact mul_mem (SubfieldClass.ratCast_mem _ a) hy
  exact key ⟨x, hx⟩

def deeper (l : Level H) (k : ℕ) (hk : 0 < k) : Level H :=
  { l with A := k * l.A, A_pos := Nat.mul_pos hk l.A_pos }

theorem dvd_deeper (l : Level H) (k : ℕ) (hk : 0 < k) : l.Dvd (deeper l k hk) :=
  ⟨dvd_rfl, le_rfl, Dvd.intro_left k rfl⟩

variable {D : Datum H}

theorem exists_transition {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) (hN : ToroidalLevelCompatibility (H := H) (D := D)) {p : ℕ}
    (hp : p.Prime) {W W' : ValuationSubring ℂ} (hW : (p : ℂ) ∈ W.nonunits) (hW' : (p : ℂ) ∈ W'.nonunits)
    (i i' : Idx H p) (hl : i.l.Dvd i'.l) (hc : i.c.F ≤ i'.c.F) (he : i.c.V W = i.c.V W') :
    ∃ (b : i.c.V W →+* i'.c.V W') (π : (S.Y p W' hp hW' i').X ⟶ (S.Y p W hp hW i).X),
      IsTransition (S.Y p W hp hW i) (S.Y p W' hp hW' i') b π := by
  obtain ⟨L1, L2, L3, -⟩ := GlobalTheory.T.all_uniformization_laws_hold
  obtain ⟨l₀, h₀, r₀⟩ := S.raises p W hp hW i
  obtain ⟨l₀', h₀', r₀'⟩ := S.raises p W' hp hW' i'
  obtain ⟨-, hsp, hmono⟩ := GlobalTheory.Models.primeToPart_spec E H p hp
  let b : i.c.V W →+* i'.c.V W' :=
    ((IntermediateField.inclusion hc).toRingHom.comp (i.c.V W).subtype).codRestrict (i'.c.V W') fun x => by
      have hx : (x : i.c.F) ∈ i.c.V W' := he ▸ x.2
      exact hx
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_transition_map_raised_models GlobalTheory.T.semiAbelian_hom_extends_uniquely_over_dvr L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN l₀ l₀' _ _ i.l i.c _ _
    (S.Y p W hp hW i) i'.l i'.c _ _ (S.Y p W' hp hW' i') b (S.aux _).1.pos ⟨_, dvd_rfl⟩
    (hmono _ _ _ _ h₀ h₀' hl) (hsp _ _ h₀).1 (hsp _ _ h₀').1 hl hc
    ((GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW).1
    ((GlobalTheory.CoeffRings.coeff_isDedFrac E H i'.l i'.c).2.2.2 p W' hp hW').1 (fun _ => rfl) r₀ r₀'
  exact ⟨b, π, hπ⟩

theorem exists_towerAt {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) (hD : 1 ≤ D.p + D.q) (l : Level H)
    (c : Coeff l) {p : ℕ} (hp : p.Prime) (hg : l.GoodAt p) : ∃ Tw : PointsOfFlagModel.Tower p (Xo l) c, PointsOfFlagModel.TowerAt Tw := by
  have hN := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H D hD).1
  have hne : ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β),
      Nonempty Y.X := fun l c O _ β Y =>
    ((GlobalTheory.T.typeFn_period_exist_moduli_nonempty E H D).2.2 GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws hD l (Xo l) c).map fun x => Y.j x
  let lv : ℕ → Level H := fun n => deeper l (p ^ n) (pow_pos hp.pos n)
  choose cN hcN using fun n => exists_coeff_ge c (lv n)
  choose W hW hWe using fun v : PointsOfFlagModel.abelian₂ p c => exists_valuationSubring c p v.1 v.2
  choose WN hWN hWNe using fun n (w : PointsOfFlagModel.abelian₂ p (cN n)) => exists_valuationSubring (cN n) p w.1 w.2
  refine ⟨{ O := fun v => c.V (W v)
            β := fun v => (c.V (W v)).subtype
            Y := fun v => S.Y p (W v) hp (hW v) ⟨l, c, hg⟩
            lvN := lv
            XoN := fun n => Xo (lv n)
            cN := cN
            ON := fun n w => (cN n).V (WN n w)
            βN := fun n w => ((cN n).V (WN n w)).subtype
            YN := fun n w => S.Y p (WN n w) hp (hWN n w) ⟨lv n, cN n, hg⟩ },
    fun v => ⟨baseAt_of_eq (hWe v), hne _ _ _ _ _⟩,
    fun n => ⟨dvd_deeper l _ (pow_pos hp.pos n), dvd_rfl, fun w => ⟨⟨baseAt_of_eq (hWNe n w), hne _ _ _ _ _⟩, ?_⟩⟩⟩
  obtain ⟨v, hv, hve⟩ := GlobalTheory.GlobalModelGuards.exists_prime_eq c (WN n w) p hp (hWN n w)
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hve
  exact ⟨⟨v, hv⟩, exists_transition S hN hp (hW ⟨v, hv⟩) (hWN n w) ⟨l, c, hg⟩ ⟨lv n, cN n, hg⟩ (dvd_deeper l _ (pow_pos hp.pos n))
    (hcN n) ((hWe ⟨v, hv⟩).trans hve)⟩

theorem nonempty_tower {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) (l : Level H) (c : Coeff l)
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (p : ℕ) : Nonempty (PointsOfFlagModel.Tower p (Xo l) c) := by
  choose q hq hqv using fun v : PointsOfFlagModel.abelian₂ p c => GlobalTheory.Reg.exists_prime_natCast_mem v.1
  choose W hW _ using fun v : PointsOfFlagModel.abelian₂ p c => exists_valuationSubring c (q v) v.1 (hqv v)
  exact ⟨{ O := fun v => c.V (W v)
           β := fun v => (c.V (W v)).subtype
           Y := fun v => S.Y (q v) (W v) (hq v) (hW v) ⟨l, c, hg _ (hq v)⟩
           lvN := fun _ => l
           XoN := fun _ => Xo l
           cN := fun _ => c
           ON := fun _ v => c.V (W v)
           βN := fun _ v => (c.V (W v)).subtype
           YN := fun _ v => S.Y (q v) (W v) (hq v) (hW v) ⟨l, c, hg _ (hq v)⟩ }⟩

theorem exists_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ p : ℕ, ∃ Tw : PointsOfFlagModel.Tower p Xo c, p.Prime → PointsOfFlagModel.TowerAt Tw := by
  intro E _ _ _ H D l Xo c hD hg p
  classical
  obtain ⟨Xf, rfl⟩ : ∃ Xf : ∀ l : Level H, Moduli D l, Xf l = Xo :=
    ⟨Function.update (fun l => (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 E H D l hD).some) l Xo, Function.update_self ..⟩
  obtain ⟨L1, L2, L3, -⟩ := GlobalTheory.T.all_uniformization_laws_hold
  obtain ⟨S, -⟩ := GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing L1 L2 L3 (GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField) E H D Xf hD (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H D hD).1
  by_cases hp : p.Prime
  · obtain ⟨Tw, h⟩ := exists_towerAt S hD l c hp (hg p hp)
    exact ⟨Tw, fun _ => h⟩
  · obtain ⟨Tw⟩ := nonempty_tower S l c hg p
    exact ⟨Tw, fun h => absurd h hp⟩

end GlobalTheory.LocalData.Towers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalDataPrescribedPointsFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalDataPrescribedPointsFlag
noncomputable section

namespace GlobalTheory.PrescribedPoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.DIV.Inh Formalism.MainNotions.DIV.Inh.LocalProvisionModel Formalism.L2.Pj NumberField

def formOf {E : Type} [Field E] [NumberField E] (L : LatB E) (hs : ∀ a b, L.beta a b = L.beta b a)
    (ha : ∀ a a' b, L.beta (a + a') b = L.beta a b + L.beta a' b) : L.Y →ₗ[ℤ] L.Y →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => L.beta a b)
      (fun b b' => by rw [hs a, ha, hs b, hs b'])).toIntLinearMap)
    (fun a a' => by
      ext b
      simp [ha a a' b])).toIntLinearMap

def LatticeLaws (D : D7) (r j : ℕ) (L : LatB D.host.E) : Prop :=
  (∀ a b, L.beta a b = L.beta b a) ∧ (∀ a a' b, L.beta (a + a') b = L.beta a b + L.beta a' b) ∧
  (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) →
    ∀ a b, L.beta (x • a) b = L.beta a (x' • b)) ∧
  (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ L.Y),
    ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * L.beta (b i) (b k)) ∧
  ∃ ρ : ℕ, Module.finrank ℤ L.Y = 2 * D.R.f * ρ ∧ ρ ≤ j ∧ ρ + j ≤ r

def zeroLattice (D : D7) : LatB D.host.E := ⟨Fin 0 → 𝓞 D.host.E, fun a b => beK D 0 a b⟩

theorem zeroLattice_subsingleton (D : D7) : Subsingleton (zeroLattice D).Y :=
  inferInstanceAs (Subsingleton (Fin 0 → 𝓞 D.host.E))

theorem zeroLattice_laws (D : D7) (r j : ℕ) (h : j ≤ r) : LatticeLaws D r j (zeroLattice D) := by
  refine ⟨fun a b => ?_, fun a a' b => ?_, fun x x' _ a b => ?_, ⟨_, inferInstance, bK D 0, beK_posDef D 0⟩,
    0, finrank_copies D 0, Nat.zero_le _, by omega⟩
  · exact (beK_apply D 0 _ _).trans ((beK_apply D 0 _ _).trans (by simp)).symm
  · exact (congrArg (fun f => f b) (map_add (beK D 0) a a'))
  · exact (beK_apply D 0 _ _).trans ((beK_apply D 0 _ _).trans (by simp)).symm

section

variable (D : D7) (r j p : ℕ) (M : MP D p) (Q : Type) (fl : Q → CF p) (Lt : Q → LatB D.host.E)
  (hL : ∀ y, LatticeLaws D r j (Lt y))

@[reducible] def locWithPoints : Loc D r j p where
  Mdl := Unit
  Xm := ()
  YY := ()
  Xn := fun _ => ()
  Pt := fun _ => Q
  fld := fun y => fl y
  Ylat := fun y => (Lt y).Y
  ylAdd := fun _ => inferInstance
  ylMod := fun _ => inferInstance
  ylFree := fun _ => inferInstance
  ylFin := fun _ => inferInstance
  be := fun y => formOf (Lt y) (hL y).1 (hL y).2.1
  be_symm := fun y => (hL y).1
  be_bal := fun y => (hL y).2.2.1
  be_posDef := fun y => (hL y).2.2.2.1
  yl_rank := fun y => by
    obtain ⟨ρ, h1, h2⟩ := (hL y).2.2.2.2
    exact ⟨ρ, h1, fun _ _ => h2⟩
  Gen := fun _ => M.Gn
  abAt := fun _ => True
  Sh := fun _ => Unit
  IsInv := fun _ => True
  IsLocFree := fun _ => True
  Sec := fun _ => PUnit
  secAdd := fun _ => inferInstance
  H0 := fun _ => ⊤
  nrm := fun _ _ _ => 0
  nrm_nonneg := fun _ _ _ => le_rfl
  norm_le_one_of_mem_sections := fun _ _ _ _ => zero_le_one
  GIso := fun _ _ => Empty
  vrat := fun _ _ => 0
  Lb := fun _ => ()
  Lb_inv := fun _ => trivial
  nrmRef := fun _ _ _ => 0
  DVP := M.Gn
  dvRho := fun _ => 0
  Ext := fun _ => Unit
  Chart := fun _ _ _ => Empty
  chAt := fun _ => True
  chOpen := fun _ => True
  chAbExact := fun _ => True
  chModU := fun _ => True
  chConst := fun _ => True

  PL := Unit
  phiAt := fun _ _ _ => 0
  phiAt_zero := fun _ {_} _ _ => rfl
  divGe := fun _ _ _ _ => True
  FJd := Unit
  Chr := fun _ => Unit
  fjN := fun _ _ _ _ => 0
  Unim := ℕ
  LBG := fun _ => Unit
  LBGq := fun _ => Unit
  resQ := fun _ => ()
  PPq := fun _ => ()
  symmG := fun _ => True
  rigG := fun _ => True
  LBGt := fun _ _ => Unit
  LBB := fun _ _ => Unit
  resGt := fun _ _ => ()
  prPull := fun _ => ()
  principal := fun _ => True
  psiV := fun _ _ => 0
  piPP := ()
  keySh := fun _ => ()
  latStd := fun n => n
  At := fun _ La n => AtM (2 * (D.R.f * r * La)) n
  atAdd := fun _ _ _ => inferInstance
  atFin := fun _ _ _ => inferInstance
  at_tors := fun _ _ _ x => atM_tors _ _ x
  at_card := fun _ _ _ h => atM_card _ _ h
  Th := fun y La n => ((fl y).C)ˣ × Multiplicative (AtM (2 * (D.R.f * r * La)) n)
  thGrp := fun _ _ _ => inferInstance
  ovr := fun _ _ _ => MonoidHom.snd _ _
  ovr_surj := fun _ _ _ x => ⟨(1, x), rfl⟩
  scal := fun _ _ _ => MonoidHom.inl _ _
  scal_inj := fun _ _ _ a b h => congrArg Prod.fst h
  scal_central := fun _ _ _ a g => by
    ext <;> simp [mul_comm]
  ker_ovr := fun _ _ _ g => ⟨fun h => ⟨g.1, Prod.ext rfl h.symm⟩, fun ⟨a, h⟩ => by rw [← h]; rfl⟩
  dl := fun _ _ _ => MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.inv _)
  dl_ovr := fun _ _ _ _ => rfl
  dl_scal := fun _ La n a => Prod.ext rfl (inv_one : (1 : Multiplicative (AtM (2 * (D.R.f * r * La)) n))⁻¹ = 1)
  dl_dl := fun _ _ _ g => by
    show (g.1, (g.2⁻¹)⁻¹) = g
    rw [inv_inv]
  Sn := fun _ _ _ => PUnit
  snAdd := fun _ _ _ => inferInstance
  snMod := fun _ _ _ => inferInstance
  act := fun _ _ _ => 1
  act_scal := fun _ _ _ _ _ => Subsingleton.elim _ _
  vth := fun _ _ _ => 0
  Jet := fun _ _ _ _ => PUnit
  jAdd := fun _ _ _ _ => inferInstance
  jMod := fun _ _ _ _ => inferInstance
  intJet := fun _ _ _ _ => ⊤
  jet := fun _ _ _ _ => 0
  LieGt := fun _ _ => PUnit
  LieB := fun _ _ => PUnit
  LieT := fun _ _ => PUnit
  lgAdd := fun _ _ => inferInstance
  lbAdd := fun _ _ => inferInstance
  ltAdd := fun _ _ => inferInstance
  resB := fun _ _ => 0
  incT := fun _ _ => 0
  kapGt := fun _ _ _ _ => 0
  kapB := fun _ _ _ _ => 0
  Harm := fun _ => Unit
  SecP := fun _ => Unit
  evA := fun _ _ _ => 0
  evGt := fun _ _ _ => 0
  Tp := fun _ => PUnit
  tpAdd := fun _ => inferInstance
  OmV := fun _ => PUnit
  omAdd := fun _ => inferInstance
  omMod := fun _ => inferInstance
  om := fun _ => ⊤
  ht := fun _ => 0
  IsHTBlowup := fun _ _ => False
  eOmP := fun _ _ _ => ()
  SES := fun _ => Unit
  ExactMod := fun _ _ => True
  htSES := fun _ _ => ()
  nefHT := fun _ _ => True
  nefQ := fun _ => True
  descK := fun _ _ => True
  bdryLoci := fun _ => True
  BT := fun _ => Unit
  extA := fun _ => True
  compat := fun _ _ => True
  Crv := M.Cv
  eDeg := fun c => -∑ᶠ τ, ((∑ i ∈ Finset.Icc 1 j, M.dg c τ i) + -∑ i ∈ Finset.Icc (j + 1) r, M.dg c τ i)
  Pm := fun c => pmM D (M.dg c) (r + j)
  Pm_nonneg := fun c => pmM_nonneg D _ _
  degLie := fun c τ b => if b then -∑ i ∈ Finset.Icc (j + 1) r, M.dg c τ i else ∑ i ∈ Finset.Icc 1 j, M.dg c τ i
  degLdR := fun c μ => -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 r, μ τ i * (M.dg c τ i : ℝ)

@[reducible] def extWithPoints (q₀ : Q) (h₀ : Subsingleton (Lt q₀).Y) :
    ExtA D (locWithPoints D r j p M Q fl Lt hL) where
  FlagData := fun _ => Unit
  flagCl := fun _ _ => ()
  allFlags := ()
  YY_eq := rfl
  Idl := fun _ => Unit
  blowUp := fun _ _ => ()
  powP := fun _ => True
  pbPrinc := fun _ _ => True
  Corr := fun _ _ => Unit
  diagCl := fun _ _ _ => ()
  IvD := fun _ => Unit
  jIdl := fun _ _ => ()
  ZP := fun _ => M.Gn
  spz := fun _ _ => True
  abP := fun _ => True
  inQ := fun _ => False
  isGenP := fun _ => False
  isGenP_ab := fun _ h => h.elim
  gpt := fun η => η
  abAt_iff := fun _ => Iff.rfl
  gpt_notQ := fun _ h => h
  genFin := fun _ => M.fin
  genNe := fun _ => M.ne
  redK := fun _ y => y
  dvRho_pos_iff := fun _ _ => by
    show 0 < (0 : ℕ) ↔ ¬ True
    simp
  genK := fun η => η
  redK_genK := fun _ => rfl
  imgM := fun χ => Empty.elim χ
  imgU := fun χ => Empty.elim χ
  img_spz := fun χ => Empty.elim χ
  imgU_inQ := fun χ => Empty.elim χ
  chAt_imgM := fun χ => Empty.elim χ
  chAbExact_imgU := fun χ => Empty.elim χ
  RFam := fun _ _ => Unit
  chFam := fun _ => ()
  ptK := fun _ _ => q₀
  ptK_good := fun _ _ => ⟨fun _ => rfl, fun _ => h₀⟩
  vpi := fun _ => 1
  vpi_pos := fun _ => zero_lt_one
  ordGe := fun _ _ _ _ => True
  yEta := fun _ => q₀
  yEta_good := fun _ => ⟨fun _ => trivial, fun _ => h₀⟩
  homSh := fun _ _ => ()
  homSh_inv := fun _ _ _ _ => trivial
  isoSec := fun _ => 0
  nrm_isoSec := fun φ => Empty.elim φ
  isoSymm := fun φ => Empty.elim φ
  vrat_symm := fun φ => Empty.elim φ
  LieV := fun _ => PUnit
  lvAdd := fun _ => inferInstance
  lvMod := fun _ => inferInstance
  lieL := fun _ => ⊤
  eig := fun _ _ => ⊤
  Wst := fun _ _ _ => ⊤
  Wst_le := fun _ _ _ => le_rfl
  taut := fun _ _ _ => ⊤
  taut_eq := fun _ _ _ => by simp
  nrmIn := fun _ _ _ _ => 0
  nrmRef_def := fun _ _ _ => rfl
  nrm_Lb_def := fun _ _ _ => rfl
  om_smul := fun _ _ _ _ _ => AddSubgroup.mem_top _
  TC := fun _ => PUnit
  tcAdd := fun _ => inferInstance
  tcMod := fun _ => inferInstance
  iT := fun _ => 0
  iT_span := fun _ => Subsingleton.elim _ _
  htC := fun _ => 0
  htC_iT := fun _ _ => rfl
  psiC := fun _ => 0
  lieGt1 := fun _ => ⊤
  eT := fun _ _ => 0
  HTn := fun _ => Empty
  htEval := fun h => Empty.elim h
  htIdl := fun _ => ()
  IsHTBlowup_def := fun n Z' _ => ⟨fun h => h.elim, fun ⟨h, _⟩ => Empty.elim h⟩
  wFib := fun _ _ _ => ⊤
  htFlags := fun _ => ()
  omSh := fun _ => ()
  omPat := fun _ => ⊤
  omPat_def := fun _ _ _ h => h.elim
  BPt := fun _ => Empty
  bfld := fun _ => M.K
  OmB := fun _ => PUnit
  obAdd := fun _ => inferInstance
  obMod := fun _ => inferInstance
  omB := fun _ => ⊤
  omPB := fun _ => ⊤
  eOmB := fun _ _ => ⊤
  eB := fun _ _ => 0
  YsP := fun _ => Empty
  ysBd := fun _ => True
  FlP := Unit
  hFl := fun _ => ()
  FlCl := Unit
  flMem := fun _ _ => True
  flDim := fun _ => 0
  Sum1 := Unit
  locus := fun _ => ()
  bdryLoci_def := fun _ => ⟨fun _ => ⟨∅, Set.finite_empty, fun x => Empty.elim x, by simp⟩, fun _ => trivial⟩
  CrvS := fun _ => Empty
  degGr := fun _ _ _ => 0
  nefHT_def := fun _ _ => ⟨fun _ C => Empty.elim C, fun _ => trivial⟩
  CrvQ := Empty
  degGrQ := fun _ _ _ => 0
  nefQ_def := fun _ => ⟨fun _ C => Empty.elim C, fun _ => trivial⟩
  degGrD := fun c => M.dg c
  degLdR_def := fun _ _ => rfl
  degLie_f := fun _ _ => rfl
  degLie_alt := fun _ _ => rfl
  eDeg_def := fun _ _ => rfl
  Pm_head := fun c τ i _ h2 => le_trans (le_abs_self _)
    (abs_le_pmM D (M.dg c) (r + j) τ _ (Finset.Icc_subset_Icc le_rfl (by omega)))
  Pm_tail := fun c τ i _ _ => le_trans (neg_le_abs _)
    (abs_le_pmM D (M.dg c) (r + j) τ _ (Finset.Icc_subset_Icc (by omega) (by omega)))

end

@[reducible] def provWithPoints (D : D7) (Dat : Type) (rk jj : Dat → ℕ) (h : ∀ w, 1 ≤ jj w ∧ jj w + 1 ≤ rk w)
    (M : ∀ (_ : Dat) (p : ℕ), MP D p) (Q : Dat → ℕ → Type) (fl : ∀ w p, Q w p → CF p)
    (Lt : ∀ w p, Q w p → LatB D.host.E) (hL : ∀ w p y, LatticeLaws D (rk w) (jj w) (Lt w p y))
    (q₀ : ∀ w p, Q w p) (h₀ : ∀ w p, Subsingleton (Lt w p (q₀ w p)).Y) : ModuliIntegralCharts.Prov D where
  Dat := Dat
  rk := rk
  jj := jj
  jj_range := h
  loc := fun w p => locWithPoints D (rk w) (jj w) p (M w p) (Q w p) (fl w p) (Lt w p) (hL w p)
  ex := fun w p => extWithPoints D (rk w) (jj w) p (M w p) (Q w p) (fl w p) (Lt w p) (hL w p) (q₀ w p) (h₀ w p)
  NgC := fun _ => Unit
  NgC_ne := fun _ => ⟨()⟩
  KF := fun _ _ => Unit
  kfNorm := fun _ _ => 1
  pbKF := fun _ _ _ _ => 0
  levIn := fun _ _ => True
  Xg := fun _ => Unit
  bc := fun _ _ => ()
  DivX := fun _ => Unit
  effD := fun _ => True
  noVertD := fun _ => True
  posBdD := fun _ => True
  ampleOnAbelianBase := fun _ _ _ => True
  Met := fun _ => Unit
  nefFib := fun _ => True
  ampleGen := fun _ => True
  limRA := fun _ => True

end GlobalTheory.PrescribedPoints

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PrescribedPoints Formalism.MainNotions.DIV.Inh Formalism.MainNotions.DIV.Inh.LocalProvisionModel in
theorem exists_prov_prescribed_points :
    ∀ (D : D7) (Pt : ℕ → ℕ → Type) (fld : ∀ j p, Pt j p → ModuliIntegralCharts.CF p) (L : ∀ j p, Pt j p → LatB D.host.E), (∀ j p y, (∀ a b, (L j p y).beta a b = (L j p y).beta b a) ∧ (∀ a a' b, (L j p y).beta (a + a') b = (L j p y).beta a b + (L j p y).beta a' b) ∧ (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) → ∀ a b, (L j p y).beta (x • a) b = (L j p y).beta a (x' • b)) ∧ (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (L j p y).Y), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * (L j p y).beta (b i) (b k)) ∧ ∃ ρ : ℕ, Module.finrank ℤ (L j p y).Y = 2 * D.R.f * ρ ∧ ρ ≤ (D.R.sigW j).1 ∧ ρ + (D.R.sigW j).1 ≤ D.R.r) → ∃ (P : ModuliIntegralCharts.Prov D) (dat : ℕ → P.Dat), ∀ j, 1 ≤ j → j < D.R.m → (P.rk (dat j) = D.R.r ∧ P.jj (dat j) = (D.R.sigW j).1) ∧ ∀ p y, ∃ η : (P.loc (dat j) p).Pt (P.loc (dat j) p).YY, (P.loc (dat j) p).fld η = fld j p y ∧ ∃ e : (P.loc (dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] (L j p y).Y, ∀ a b, (L j p y).beta (e a) (e b) = (P.loc (dat j) p).be η a b := by
  intro D Pt fld L hL
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : ∀ w : {j : ℕ // 1 ≤ j ∧ j < D.R.m}, 1 ≤ (D.R.sigW w.1).1 ∧ (D.R.sigW w.1).1 + 1 ≤ D.R.r := by
    rintro ⟨w, h1, h2⟩
    simp only [Formalism.BasicNotions.Ranks.sigW, Formalism.BasicNotions.Ranks.r]
    omega
  refine ⟨provWithPoints D {j : ℕ // 1 ≤ j ∧ j < D.R.m} (fun _ => D.R.r) (fun w => (D.R.sigW w.1).1) hr
    (fun _ p => mpTrivialAb D p (nonempty_coefficient_field p).some) (fun w p => Option (Pt w.1 p))
    (fun w p y => y.elim (nonempty_coefficient_field p).some (fld w.1 p))
    (fun w p y => y.elim (zeroLattice D) (L w.1 p))
    (fun w p y => match y with
      | none => zeroLattice_laws D _ _ (by have := hr w; omega)
      | some y => hL w.1 p y)
    (fun _ _ => none) (fun _ _ => zeroLattice_subsingleton D),
    fun j => if h : 1 ≤ j ∧ j < D.R.m then ⟨j, h⟩ else ⟨1, le_rfl, hm⟩, fun j h1 h2 => ?_⟩
  beta_reduce
  rw [dite_eq_left (And.intro h1 h2)]
  exact ⟨⟨rfl, rfl⟩, fun p y => ⟨some y, rfl, LinearEquiv.refl _ _, fun a b => rfl⟩⟩

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalDataPrescribedPointsFlagStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localData_prescribed_points_flag : ∀ (D : D7) (Pt : ℕ → ℕ → Type) (fld : ∀ j p, Pt j p → ModuliIntegralCharts.CF p) (L : ∀ j p, Pt j p → LatB D.host.E), (∀ j p y, (∀ a b, (L j p y).beta a b = (L j p y).beta b a) ∧ (∀ a a' b, (L j p y).beta (a + a') b = (L j p y).beta a b + (L j p y).beta a' b) ∧ (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) → ∀ a b, (L j p y).beta (x • a) b = (L j p y).beta a (x' • b)) ∧ (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (L j p y).Y), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * (L j p y).beta (b i) (b k)) ∧ ∃ ρ : ℕ, Module.finrank ℤ (L j p y).Y = 2 * D.R.f * ρ ∧ ρ ≤ (D.R.sigW j).1 ∧ ρ + (D.R.sigW j).1 ≤ D.R.r) → ∃ (P : ModuliIntegralCharts.Prov D) (dat : ℕ → P.Dat), ∀ j, 1 ≤ j → j < D.R.m → (P.rk (dat j) = D.R.r ∧ P.jj (dat j) = (D.R.sigW j).1) ∧ ∀ p y, ∃ η : (P.loc (dat j) p).Pt (P.loc (dat j) p).YY, (P.loc (dat j) p).fld η = fld j p y ∧ ∃ e : (P.loc (dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] (L j p y).Y, ∀ a b, (L j p y).beta (e a) (e b) = (P.loc (dat j) p).be η a b := by
  first | exact @GlobalTheory.exists_prov_prescribed_points | exact GlobalTheory.exists_prov_prescribed_points | (intros; apply GlobalTheory.exists_prov_prescribed_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocalDataAtConcretePointsExist
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalData

def FactorsFin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {p : ℕ} {C : SCF p} (P : PointsOfFlagModel.PtC Y C) : Prop :=
  ∃ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes ∧ Function.Injective g ∧
    (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) ∧ spMap g ≫ ιT = P.yt

theorem half_degree (D : D7) : Module.finrank ℚ D.host.E / 2 = D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  omega

theorem bar_eq_of_conj (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (x x' : 𝓞 D.host.E)
    (h : (x' : D.host.E) = D.host.conj (x : D.host.E)) : H.bar x = x' := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact (H.bar_eq x).trans ((barE_eq_conj D x).trans h.symm)

theorem laws_of_factorsFin (D : D7) (Q : Par D) (hQ : Q.Pins) {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) {p : ℕ}
    (hp : p.Prime) {O : Type} [CommRing O] {β : O →+* Q.c.F} {Y : Model (Q.Xo j) Q.c β} {C : SCF p}
    {P : PointsOfFlagModel.PtC Y C} (hf : FactorsFin Y P) (A : DatAt Y P) :
    (∀ a b, A.toLatB.beta a b = A.toLatB.beta b a) ∧
    (∀ a a' b, A.toLatB.beta (a + a') b = A.toLatB.beta a b + A.toLatB.beta a' b) ∧
    (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) →
      ∀ a b, A.toLatB.beta (x • a) b = A.toLatB.beta a (x' • b)) ∧
    (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.toLatB.Y), ∀ x : ι → ℝ, x ≠ 0 →
      0 < ∑ i, ∑ k, x i * x k * A.toLatB.beta (b i) (b k)) ∧
    ∃ ρ : ℕ, Module.finrank ℤ A.toLatB.Y = 2 * D.R.f * ρ ∧ ρ ≤ (D.R.sigW j).1 ∧ ρ + (D.R.sigW j).1 ≤ D.R.r := by
  obtain ⟨T, g, ιT, h1, h2, h3, h4⟩ := hf
  obtain ⟨ha, hb, hc, ρ, hr1, hr2, hr3⟩ := GlobalTheory.T.periodForm_additive_balanced_posDef_boundedRank D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c O β Y p C
    P hp T g ιT h1 h2 h3 h4 A
  obtain ⟨hp1, hq1, -⟩ := hQ.2.2.2 j ⟨hj, hm.le⟩
  rw [hp1] at hr2
  rw [hq1] at hr3
  rw [half_degree D] at hr1
  refine ⟨A.beta_symm, ha, fun x x' hx a b => ?_, hc, ρ, hr1, hr2, ?_⟩
  · rw [← bar_eq_of_conj D Q.H x x' hx]
    exact hb x a b
  · simp only [Ranks.sigW, Ranks.r] at hr3 ⊢
    omega

theorem uniq_of_factorsFin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {p : ℕ} (hp : p.Prime) {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (hf : FactorsFin Y P)
    (A A' : DatAt Y P) : ∃ e : A.toLatB.Y ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (e a) (e b) = A.toLatB.beta a b := by
  obtain ⟨T, g, ιT, h1, h2, h3, h4⟩ := hf
  exact (GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C P hp T g ιT h1 h2 h3 h4 A A').2

theorem localData_exists :
    ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → Packet66Rest Q := by
  intro D Q hQ hpq
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D Q.H Q.l hQ.1.2.1 hQ.2.1.1).1
  choose Tw hTw using fun j p => Towers.exists_tower D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c (hpq j) hgood p
  have hdat : ∀ j p (z : PointsOfFlagModel.Pt (Tw j p) .yy), p.Prime → FactorsFin ((Tw j p).Y z.1) z.2.2.1 →
      Nonempty (DatAt ((Tw j p).Y z.1) z.2.2.1) := by
    rintro j p z hp ⟨T, g, ιT, h1, h2, h3, h4⟩
    obtain ⟨A, -⟩ := GlobalTheory.T.exists_degeneration_data_algebraic_point_model D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c _ _ _ p _ z.2.2.1 hp T g ιT h1 h2 h3 h4
    exact ⟨A⟩
  let Pt : ℕ → ℕ → Type := fun j p => {z : PointsOfFlagModel.Pt (Tw j p) .yy //
    (1 ≤ j ∧ j < D.R.m) ∧ p.Prime ∧ FactorsFin ((Tw j p).Y z.1) z.2.2.1}
  have A0 : ∀ j p (y : Pt j p), DatAt ((Tw j p).Y y.1.1) y.1.2.2.1 := fun j p y =>
    Classical.choice (hdat j p y.1 y.2.2.1 y.2.2.2)
  obtain ⟨P, dat, hP⟩ := GlobalTheory.T.exists_localData_prescribed_points_flag D Pt (fun j p y => PointsOfFlagModel.fld y.1) (fun j p y => (A0 j p y).toLatB)
    (fun j p y => laws_of_factorsFin D Q hQ y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2 (A0 j p y))
  let G : In66 Q :=
    { P := P
      dat := dat
      Tw := Tw
      rel := fun j p η z => (P.loc (dat j) p).fld η = PointsOfFlagModel.fld z ∧
        ∀ A : DatAt ((Tw j p).Y z.1) z.2.2.1, ∃ e : (P.loc (dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] A.Ylat,
          ∀ a b, A.beta (e a) (e b) = (P.loc (dat j) p).be η a b }
  have hfac : ∀ j la z, G.IsAlgPt j la z → FactorsFin ((Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1 := by
    rintro j la z ⟨T, io, e, y, ho, hy, hz⟩
    obtain ⟨g, ιT, h2, h3, h4⟩ := (GlobalTheory.T.exists_flag_model_baseChange_integral_framed_point D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c la (Tw j _)
      (hTw j _ (resCh_prime la)) T io e ho y hy).2 z hz
    exact ⟨T, g, ιT, hy, h2, h3, h4⟩
  refine ⟨G, fun j hj hm => (hP j hj hm).1, fun j _ _ p hp => hTw j p hp,
    fun j _ _ la z hz => hdat j _ z (resCh_prime la) (hfac j la z hz), fun j hj hm la z hz => ⟨?_, fun η h => h.1⟩,
    fun j _ _ la z _ η h => h.2, fun j _ _ la T io e ho y hy => ?_⟩
  · let y : Pt j (WeightAlgebra.resCh la) := ⟨z, ⟨hj, hm⟩, resCh_prime la, hfac j la z hz⟩
    obtain ⟨η, h1, e, he⟩ := (hP j hj hm).2 _ y
    refine ⟨η, h1, fun A => ?_⟩
    exact (uniq_of_factorsFin (resCh_prime la) y.2.2.2 (A0 j _ y) A).elim fun e' he' =>
      ⟨e.trans e', fun a b => (he' (e a) (e b)).trans (he a b)⟩
  · exact (GlobalTheory.T.exists_flag_model_baseChange_integral_framed_point D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c la (Tw j _)
      (hTw j _ (resCh_prime la)) T io e ho y hy).1

end GlobalTheory.LocalData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocalDataAtConcretePointsExistStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDataAtConcretePoints_exist : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → Packet66Rest Q := by
  first | exact @GlobalTheory.LocalData.localData_exists | exact GlobalTheory.LocalData.localData_exists | (intros; apply GlobalTheory.LocalData.localData_exists <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Member

theorem exists_completion_of_core_satisfying_laws : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Core D), LawsCore T → (∀ j, 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) → (∀ j, InR D j → KPsiIn (Dw := T.Q.Dw j) T.Q.c) → (∀ j, InR D j → ∀ (_ : StarRing (𝓞 D.host.E)) (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab → ThInCusp (T.Q.Xo j) T.Q.c nab (T.cuspA j) ∧ (j < D.R.m → ThNe0 (T.Q.Xo j) T.Q.c nab)) → ∃ T' : Top D, LawsP T' ∧ T'.toCore = T := by
  intro hC D T hT hpq hK hth
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.localDataAtConcretePoints_exist D T.Q hT.pins hpq
  have hnab := fun j => GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  choose st nab hN using hnab
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D T.Q.H T.Q.l hT.pins.1.2.1 hT.pins.2.1.1).1
  have hreg := fun j => GlobalTheory.Reg.sCharts_and_transfer_of_good_level GlobalTheory.T.compactifiedModuli_partOne GlobalTheory.Moduli.moduli_scheme_exists
    D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (hpq j) hgood
  refine ⟨{ toCore := T, G := G, nab := nab,
            dδ := fun j n => noDelta (T.Q.Xo j) T.Q.c (nab j) (GlobalTheory.ObjLower.sabId (T.Q.Xo j).univ.t) n }, ?_, rfl⟩
  exact
    { toLawsCore := hT
      allTest := fun j _ => GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange D.host.E T.Q.H (T.Q.Dw j)
        T.Q.l (T.Q.Xo j) T.Q.c
      reg := fun j _ => (Formalism.L2.PjFree.regP_ofPj (T.U j)).1 ((hreg j).2.1 D.R.r _)
      datum_condition := h1
      tower := h2
      hasData_condition := h3
      points_condition := h4
      lattice_condition := h5
      bc66 := h6
      datIndep := fun j _ _ => GlobalTheory.T.latticePeriodForm_independent_of_models D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
      nabPin := fun j _ => ⟨st j, hN j⟩
      nabUniq := fun j _ => Formalism.MainNotions.ModuliIntegralCharts.H1.nabUniq_of_chartIndep2 hC (T.Q.Xo j) T.Q.c
      thTot := fun j _ => @GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 hC D.host.E _ _ _ T.Q.H (T.Q.Dw j) T.Q.l
        (T.Q.Xo j) T.Q.c (st j) (nab j) (hN j)
      thCusp := fun j hj => (hth j hj (st j) (nab j) (hN j)).1
      thNe := fun j h1 h2 => (hth j ⟨h1, h2.le⟩ (st j) (nab j) (hN j)).2 h2
      kPsi := hK }

end GlobalTheory.Member
