module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometry

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataWithTermSingleOrbitPrimeTo
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataWithTermSingleOrbitPrimeTo
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver GlobalTheory.HL
open scoped Pointwise Classical

namespace GlobalTheory.HL.PrimeToOrbit

theorem coord_one_orbit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : GlobalTheory.HL.Frames L r k) (hgg : S.gg = false) (hvG : vE L S.ϖ S.G = 0)
    (hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1)
    {δ δ' : S.Datum} {Λ Λ' : Submodule L.O S.V} (hT : S.IsTerm δ Λ) (hT' : S.IsTerm δ' Λ') :
    ∃ h ∈ S.H0, h • δ = δ' := by
  have ha : S.a = 0 := by simp [GlobalTheory.HL.Frames.a, GlobalTheory.HL.Frames.vth, hgg, hvG]
  obtain ⟨-, -, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hgg hDu
  have hint : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ h =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1
  have hdd : ∀ d d' Λ, S.IsTerm d Λ → S.IsTerm d' Λ → d' = d := fun d d' Λ h h' =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.2 d' h'
  have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S
  have hcom := GlobalTheory.HL.ComplAct.main L r k S
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  obtain ⟨s, hs, e⟩ := hall _ (hint _ _ hT)
  obtain ⟨s', hs', e'⟩ := hall _ (hint _ _ hT')
  have h1 := hact δ _ hT _ (S.St.inv_mem hs)
  have h1' := hact δ' _ hT' _ (S.St.inv_mem hs')
  have hFr₁ : S.Fr δ (s⁻¹ • Λ) = S.frameCls S.f S.f' := by
    rw [h1.2.2.2.2.1, e, smul_smul, inv_mul_cancel, one_smul]
  have hFr₁' : S.Fr δ' (s'⁻¹ • Λ') = S.frameCls S.f S.f' := by
    rw [h1'.2.2.2.2.1, e', smul_smul, inv_mul_cancel, one_smul]
  have hM : S.M δ (s⁻¹ • Λ) = S.M δ' (s'⁻¹ • Λ') := by
    have h3 : (S.fr δ (s⁻¹ • Λ), S.fr' δ (s⁻¹ • Λ)) ∈ S.Fr δ' (s'⁻¹ • Λ') := by
      rw [hFr₁', ← hFr₁]; exact (hcls _ _).1
    exact ((hcls _ _).2.1 _ h3).2
  obtain ⟨h, hh, e₁⟩ := GlobalTheory.HL.StdPlace.term_orbit L r k S ha h1.1 h1'.1 hM
  have h4 := (hcom δ' _ h1'.1 h hh).1
  rw [e₁] at h4
  refine ⟨h⁻¹, S.H0.inv_mem hh, ?_⟩
  have h5 : h • δ' = δ := hdd _ _ _ h1.1 h4
  rw [← h5, smul_smul, inv_mul_cancel, one_smul]

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → P.PrimeTo → ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → Datum.Rel d d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hdim hrel hpt d d' t t' ht ht'
  have := hM.loc
  have := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hdim hrel
  obtain ⟨-, -, hgg, hvG, -⟩ : _ ∧ _ ∧ (S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ True) := by
    obtain ⟨a1, a2, a3⟩ := GlobalTheory.HL.CoordHeight.height_eq M hM H r k P S c
    obtain ⟨b1, b2, -⟩ := a3 hpt
    exact ⟨a1, a2, b1, b2, trivial⟩
  obtain ⟨-, -, -, -, hD, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  have hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ M.L.O ∧ ∃ y ∈ M.L.O, S.D l * y = 1 := by
    intro l hl
    by_cases h0 : l = 0
    · have e : S.D l = 1 := by
        subst h0
        unfold GlobalTheory.HL.Frames.D GlobalTheory.HL.lead
        exact Matrix.det_isEmpty (n := Fin 0)
      rw [e]
      exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
    · have hmem : (l : ℕ) ∈ P.ends := by
        unfold LocNG.FPair.ends
        simp only [Finset.mem_filter, Finset.mem_range]
        rw [GlobalTheory.HL.CoordHeight.Dm_eq c]
        exact ⟨l.2, Nat.one_le_iff_ne_zero.mpr fun h => h0 (Fin.ext h), hD l hl⟩
      have := hpt.2.2 _ hmem
      rwa [GlobalTheory.HL.CoordHeight.Dm_eq c] at this
  have hT := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d t ht).1
  have hT' := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d' t' ht').1
  exact ((GlobalTheory.HL.CoordDatum.transport M hM H r k P S c).2.2.1 d d').2
    (coord_one_orbit M.L r k S hgg hvG hDu hT hT')

end GlobalTheory.HL.PrimeToOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataWithTermSingleOrbitPrimeToStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianData_with_term_single_orbit_primeTo : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → P.PrimeTo → ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → Datum.Rel d d' := by
  first | exact @GlobalTheory.HL.PrimeToOrbit.main | exact GlobalTheory.HL.PrimeToOrbit.main | (intros; apply GlobalTheory.HL.PrimeToOrbit.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKType
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKType
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

theorem exists_smooth_average_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro B d hD hK P u hu
  have hσ : IsURep B.σs := (tensorRep B d hD).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => by
    obtain ⟨_, hds, _, _⟩ := hD v
    obtain ⟨_, _, h, _⟩ := hds
    exact h
  have hw : ∀ v, B.w v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v) ∧ B.w v ≠ 0 := fun v => by
    obtain ⟨_, _, ⟨h1, h2⟩, _⟩ := hD v
    refine ⟨h2, fun h0 => ?_⟩
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1

  let A : Set B.Hs := {y | ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
    HasCompactSupport F ∧ y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)}
  have hint : ∀ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w)) (muInf B.I) :=
    fun F hF hc => integrable_inf B hσ (B.tens B.w) hF.continuous hc
  have hzero : (0 : B.Hs) ∈ A := ⟨0, contDiff_const, HasCompactSupport.zero, by simp⟩
  have hadd : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A := by
    rintro x y ⟨F, hF, hFc, rfl⟩ ⟨G, hG, hGc, rfl⟩
    refine ⟨F + G, hF.add hG, hFc.add hGc, ?_⟩
    rw [← integral_add (hint F hF hFc) (hint G hG hGc)]
    congr 1
    funext g
    simp [add_smul]
  have hsmul : ∀ (c : ℂ) x, x ∈ A → c • x ∈ A := by
    rintro c x ⟨F, hF, hFc, rfl⟩
    refine ⟨fun z => c * F z, contDiff_const.mul hF, hFc.mul_left (f := fun _ => c), ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have htens : ∀ u' : ∀ v, B.H v, (∀ v, u' v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → B.tens u' ∈ A := by
    intro u' hu'
    have hloc := fun v => GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v)
      (B.w v) (hU v) (hK v) (hw v).1 (hw v).2 (u' v) (hu' v)
    choose F hF hFc hFe using hloc
    obtain ⟨G, hG, hGc, hGe⟩ := tens_average B hU hσ B.w F hF hFc
    refine ⟨G, hG, hGc, ?_⟩
    rw [← hGe]
    congr 1
    funext v
    exact hFe v

  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (y : B.Hs), y ∈ A → wordAct B l y ∈ A := by
    intro l
    induction l with
    | nil => intro y hy; exact hy
    | cons X l ih =>
      intro y hy
      obtain ⟨F, hF, hFc, hFe⟩ := ih y hy
      obtain ⟨F', hF', hF'c, hd⟩ := GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B F (atPlace B X.1 X.2) (B.tens B.w)
        hσ hF hFc
      refine ⟨F', hF', hF'c, ?_⟩
      show dAct B (atPlace B X.1 X.2) (wordAct B l y) = _
      rw [hFe]
      exact hd.deriv

  let S : Submodule ℂ B.Hs :=
    { carrier := A
      add_mem' := fun hx hy => hadd _ _ hx hy
      zero_mem' := hzero
      smul_mem' := fun c x hx => hsmul c x hx }
  have hle : VP B P ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨l, u', -, hu', rfl⟩
    exact hword l _ (htens u' hu')
  exact hle hu

end GlobalTheory.StepAverage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKTypeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_average_lowest_KType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  first | exact @GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf | exact GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf | (intros; apply GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NegLogProdLValEtaLeAndPos
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NegLogProdLValEtaLeAndPos
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.LProd

private lemma eventually_abs_le_half_add_of_doubling_bounds (m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 / (x + 1) ^ (3 + m) + 4 / 2 ^ (3 + m) / ((x + 1) * (x + 1 + 1)) ≤
      4 / 2 ^ (3 + m) / (x * (x + 1)) := by
  have hx0 : 0 < x := by linarith
  have hp : (2 : ℝ) ^ m ≤ (x + 1) ^ m := pow_le_pow_left₀ (by norm_num) (by linarith) m
  have hp0 : (0 : ℝ) < 2 ^ m := by positivity

  have hdiff : 4 / 2 ^ (3 + m) / (x * (x + 1)) - 4 / 2 ^ (3 + m) / ((x + 1) * (x + 1 + 1)) =
      1 / (2 ^ m * (x * (x + 1) * (x + 2))) := by
    rw [pow_add]
    field_simp
    ring

  have hcube : x * (x + 1) * (x + 2) ≤ (x + 1) ^ 3 := by nlinarith
  have hle : 2 ^ m * (x * (x + 1) * (x + 2)) ≤ (x + 1) ^ (3 + m) := by
    calc 2 ^ m * (x * (x + 1) * (x + 2)) ≤ (x + 1) ^ m * (x + 1) ^ 3 :=
          mul_le_mul hp hcube (by positivity) (by positivity)
      _ = (x + 1) ^ (3 + m) := by ring
  have hterm : 1 / (x + 1) ^ (3 + m) ≤ 1 / (2 ^ m * (x * (x + 1) * (x + 2))) :=
    one_div_le_one_div_of_le (by positivity) hle
  linarith

theorem tsum_le (M : ℕ) (hM : 3 ≤ M) :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M) ≤ 1 + 2 / 2 ^ M := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hM

  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), 1 / ((i : ℝ) + 1) ^ (3 + m) +
      4 / 2 ^ (3 + m) / (((N : ℝ) + 1) * ((N : ℝ) + 1 + 1)) ≤ 1 + 2 / 2 ^ (3 + m) := by
    intro N
    induction N with
    | zero =>
      apply le_of_eq
      norm_num
      ring
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := eventually_abs_le_half_add_of_doubling_bounds m ((N : ℝ) + 1) (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
      push_cast
      linarith
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  | succ N =>
    have h := hpart N
    have : (0 : ℝ) ≤ 4 / 2 ^ (3 + m) / (((N : ℝ) + 1) * ((N : ℝ) + 1 + 1)) := by positivity
    linarith

theorem log_tsum_le (M : ℕ) (hM : 3 ≤ M) :
    Real.log (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M) ≤ 2 / 2 ^ M := by
  have h1 := tsum_le M hM
  have h0 : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M := tsum_nonneg fun n => by positivity
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]
    positivity
  · linarith [Real.log_le_sub_one_of_pos h]

private lemma sum_Ioc_two_div_two_pow (n₀ k : ℕ) :
    ∑ M ∈ Finset.Ioc n₀ (n₀ + k), (2 : ℝ) / 2 ^ M = 2 / 2 ^ n₀ - 2 / 2 ^ (n₀ + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (Nat.le_add_right n₀ k), ih, pow_succ]
    field_simp
    ring

theorem geom_le (n₀ n : ℕ) : ∑ M ∈ Finset.Ioc n₀ n, (2 : ℝ) / 2 ^ M ≤ (2 : ℝ) ^ ((1 : ℤ) - n₀) := by
  rw [zpow_sub₀ two_ne_zero, zpow_one, zpow_natCast]
  rcases le_or_gt n n₀ with h | h
  · rw [Finset.Ioc_eq_empty_of_le h, Finset.sum_empty]
    positivity
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    rw [sum_Ioc_two_div_two_pow]
    have : (0 : ℝ) ≤ 2 / 2 ^ (n₀ + k) := by positivity
    linarith

theorem neg_log_prod_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ n₀ n : ℕ, 2 ≤ n₀ → -Real.log (∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M) ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) ∧ 0 < ∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M := by
  intro E _ _ _ hE n₀ n hn₀
  have hL : ∀ M : ℕ, 2 ≤ M → 0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta E M)| ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * Real.log (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ M) :=
    fun M hM => (Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound E hE M hM).2
  have hpos : ∀ M ∈ Finset.Ioc n₀ n, 0 < Formalism.HermitianLatticesTheory.lValEta E M := fun M hM =>
    (hL M (by have := (Finset.mem_Ioc.mp hM).1; omega)).1
  refine ⟨?_, Finset.prod_pos hpos⟩
  rw [Real.log_prod (fun M hM => (hpos M hM).ne'), ← Finset.sum_neg_distrib]
  have hf : (0 : ℝ) ≤ Formalism.HermitianLatticesTheory.fDeg E := by positivity
  calc ∑ M ∈ Finset.Ioc n₀ n, -Real.log (Formalism.HermitianLatticesTheory.lValEta E M)
      ≤ ∑ M ∈ Finset.Ioc n₀ n, (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 / 2 ^ M) := by
        apply Finset.sum_le_sum
        intro M hM
        have hM3 : 3 ≤ M := by have := (Finset.mem_Ioc.mp hM).1; omega
        calc -Real.log (Formalism.HermitianLatticesTheory.lValEta E M) ≤ |Real.log (Formalism.HermitianLatticesTheory.lValEta E M)| := neg_le_abs _
          _ ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * Real.log (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ M) := (hL M (by omega)).2
          _ ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 / 2 ^ M) := mul_le_mul_of_nonneg_left (log_tsum_le M hM3) hf
    _ = (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ M ∈ Finset.Ioc n₀ n, (2 : ℝ) / 2 ^ M := by rw [Finset.mul_sum]
    _ ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) := mul_le_mul_of_nonneg_left (geom_le n₀ n) hf

end GlobalTheory.FlagMeas.LProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NegLogProdLValEtaLeAndPosStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_log_prod_lValEta_le_and_pos : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ n₀ n : ℕ, 2 ≤ n₀ → -Real.log (∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M) ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) ∧ 0 < ∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M := by
  first | exact @GlobalTheory.FlagMeas.LProd.neg_log_prod_le | exact GlobalTheory.FlagMeas.LProd.neg_log_prod_le | (intros; apply GlobalTheory.FlagMeas.LProd.neg_log_prod_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntPrimLatticeImageIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntPrimLatticeImageIsometry
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] [StarRing K] in
theorem primInv_span_gmap (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Submodule.span K ((Formalism.HermitianLatticesTheory.gmap γ M : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_coe, ← Submodule.span_image]
  try rfl


omit [NumberField K] [StarRing K] in
theorem primInv_gmap_injective (γ : V ≃ₗ[K] V) :
    Function.Injective (fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M) := by
  intro M N hMN
  exact Submodule.map_injective_of_injective (f := (γ : V →ₗ[K] V).restrictScalars (𝓞 K))
    γ.injective hMN

omit [NumberField K] [StarRing K] in
theorem primInv_gmap_symm (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap γ⁻¹ (Formalism.HermitianLatticesTheory.gmap γ M) = M := by
  ext x
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    change γ.symm (γ z) ∈ M
    rwa [γ.symm_apply_apply]
  · intro hx
    exact ⟨γ x, ⟨x, hx, rfl⟩, γ.symm_apply_apply x⟩

theorem primInv_mem (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) (M : Submodule (𝓞 K) V) (hM : M ∈ PrimSubs h L j de) :
    Formalism.HermitianLatticesTheory.gmap γ M ∈ PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
  obtain ⟨⟨hle, heq⟩, hrk, hdet⟩ := hM
  have hspan := primInv_span_gmap γ M
  refine ⟨⟨Submodule.map_mono hle, ?_⟩, ?_, ?_⟩
  ·
    have hres : ((Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V)).restrictScalars (𝓞 K) =
        ((Submodule.span K (M : Set V)).restrictScalars (𝓞 K)).map
          ((γ : V →ₗ[K] V).restrictScalars (𝓞 K)) := by
      ext x; exact Iff.rfl
    rw [hspan, hres]
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_inf ((γ : V →ₗ[K] V).restrictScalars (𝓞 K)) γ.injective, ← heq]
  · rw [hspan, LinearEquiv.finrank_map_eq]
    exact hrk
  · rw [← hdet]
    exact GlobalTheory.T.latDetH_map_injective_isometry K V V h h (γ : V →ₗ[K] V) γ.injective (fun x y => hγ x y) M

theorem primInv_le (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) : cntPrim h L j de ≤ cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
  unfold cntPrim
  rw [← Set.InjOn.encard_image (f := fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M)
    (s := PrimSubs h L j de) (fun _ _ _ _ hab => primInv_gmap_injective γ hab)]
  have hsub : (fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M) '' PrimSubs h L j de ⊆
      PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
    rintro _ ⟨M, hM, rfl⟩
    exact primInv_mem h γ hγ L j de M hM
  first
    | exact Set.encard_le_encard hsub
    | exact Set.encard_mono hsub
    | exact Set.encard_le_card hsub

end

theorem cntPrim_gmap_isom : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ (L : Submodule (𝓞 K) V) (j de : ℕ), cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de = cntPrim h L j de := by
  intro K V _ _ _ _ _ _ _ h γ hγ L j de
  refine le_antisymm ?_ (primInv_le h γ hγ L j de)
  have := primInv_le h γ⁻¹ (inv_mem hγ) (Formalism.HermitianLatticesTheory.gmap γ L) j de
  rwa [primInv_gmap_symm] at this

end GlobalTheory.LoopC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntPrimLatticeImageIsometryStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cntPrim_latticeImage_isometry : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ (L : Submodule (𝓞 K) V) (j de : ℕ), cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de = cntPrim h L j de := by
  first | exact @GlobalTheory.LoopC.cntPrim_gmap_isom | exact GlobalTheory.LoopC.cntPrim_gmap_isom | (intros; apply GlobalTheory.LoopC.cntPrim_gmap_isom <;> assumption)
end
end
