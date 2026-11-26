module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FactorActionAlgebra
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.ContinuousRingHom
noncomputable section

open NumberField IsDedekindDomain Polynomial Topology WithZero

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LemB

namespace ConjugationUpperEntries

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

instance compat : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
  Valuation.Compatible.ofValuation _

theorem isEquiv : (ValuativeRel.valuation (w.adicCompletion E)).IsEquiv Valued.v :=
  ValuativeRel.isEquiv _ _

theorem exists_nat_lt_one : ∃ d : ℕ, 0 < d ∧ Valued.v ((d : w.adicCompletion E)) < 1 := by
  refine ⟨Ideal.absNorm w.asIdeal, Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩
  have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w
    ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E)).mpr (Ideal.absNorm_mem w.asIdeal)
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w
    ((Ideal.absNorm w.asIdeal : ℕ) : E)
  simp only [map_natCast] at h1 h2
  rw [← map_natCast (algebraMap E (w.adicCompletion E))]
  exact (h2.trans_lt h1 : _)

theorem exists_root {d : ℕ} (hd : Valued.v ((d : w.adicCompletion E)) < 1) (t : ℕ) (x : w.adicCompletion E)
    (hx : Valued.v x ≤ 1) : ∃ y : w.adicCompletion E, y ^ (d * t + 1) = 1 + d * x ^ (d * t + 1) := by
  let O := Valuation.integer (ValuativeRel.valuation (w.adicCompletion E))
  have hxO : x ∈ O := by
    change ValuativeRel.valuation _ x ≤ 1
    exact ((isEquiv w).le_one_iff_le_one).mpr hx
  let xo : O := ⟨x, hxO⟩
  have hdO : (d : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb1 : Valued.v (b : w.adicCompletion E) ≤ 1 := ((isEquiv w).le_one_iff_le_one).mp b.2
    have h1 : Valued.v (((d : O) * b : O) : w.adicCompletion E) = 1 := by rw [hb]; simp
    have h2 : Valued.v (((d : O) * b : O) : w.adicCompletion E) < 1 := by
      have : (((d : O) * b : O) : w.adicCompletion E) = (d : w.adicCompletion E) * b := by push_cast; rfl
      rw [this, map_mul]
      calc Valued.v (d : w.adicCompletion E) * Valued.v (b : w.adicCompletion E)
          ≤ Valued.v (d : w.adicCompletion E) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hd
    exact (ne_of_lt h2) h1
  let f : O[X] := X ^ (d * t + 1) - C (1 + (d : O) * xo ^ (d * t + 1))
  have hmon : f.Monic := monic_X_pow_sub_C _ (Nat.succ_ne_zero _)
  have hf1 : f.eval 1 ∈ IsLocalRing.maximalIdeal O := by
    have : f.eval 1 = -(xo ^ (d * t + 1)) * d := by
      simp only [f, eval_sub, eval_pow, eval_X, one_pow, eval_C]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hdO
  have hf2 : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (f.derivative.eval 1)) := by
    have : f.derivative.eval 1 = (d : O) * t + 1 := by
      simp only [f, derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow,
        eval_X, one_pow, mul_one]
      push_cast; ring
    rw [this, map_add (f := _), map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ hdO), zero_add]
    exact isUnit_one
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O) f hmon 1 hf1 hf2
  refine ⟨(a : w.adicCompletion E), ?_⟩
  have ha' : a ^ (d * t + 1) = 1 + (d : O) * xo ^ (d * t + 1) := by
    have := ha
    simp only [f, IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this
    exact sub_eq_zero.mp this
  have := congrArg (fun z : O => (z : w.adicCompletion E)) ha'
  simpa using this

theorem no_root {d m : ℕ} (a : ℤ) (hda : Valued.v ((d : w.adicCompletion E)) = exp a) (ha : a < 0) (hm : -a < m)
    (x : w.adicCompletion E) (hx : 1 < Valued.v x) : ¬ ∃ y : w.adicCompletion E, y ^ m = 1 + d * x ^ m := by
  have hx0 : Valued.v x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  set k := log (Valued.v x)
  have hvx : Valued.v x = exp k := (exp_log hx0).symm
  have hk : 0 < k := by
    have : exp (0 : ℤ) < exp k := by rw [exp_zero, ← hvx]; exact hx
    exact exp_lt_exp.mp this
  have hbig : Valued.v ((d : w.adicCompletion E) * x ^ m) = exp (a + m * k) := by
    rw [map_mul, map_pow, hda, hvx, ← exp_nsmul, ← exp_add, nsmul_eq_mul]
  have hpos : 0 < a + m * k := by nlinarith
  have hsum : Valued.v (1 + (d : w.adicCompletion E) * x ^ m) = exp (a + m * k) := by
    rw [Valuation.map_add_eq_of_lt_right, hbig]
    rw [hbig, map_one, ← exp_zero]
    exact exp_lt_exp.mpr hpos
  rintro ⟨y, hy⟩
  have hy0 : Valued.v y ≠ 0 := by
    intro h0
    have : Valued.v (y ^ m) = 0 := by rw [map_pow, h0, zero_pow]; omega
    rw [hy, hsum] at this
    exact exp_ne_zero this
  set j := log (Valued.v y)
  have hvy : Valued.v y = exp j := (exp_log hy0).symm
  have h1 : exp ((m : ℤ) * j) = exp (a + m * k) := by
    rw [← hsum, ← hy, map_pow, hvy, ← exp_nsmul, nsmul_eq_mul]
  have h2 : (m : ℤ) * j = a + m * k := exp_injective h1
  have h3 : (m : ℤ) * (j - k) = a := by linarith
  rcases le_or_gt 0 (j - k) with h | h
  · nlinarith
  · nlinarith

theorem le_one_of_le_one (s : w.adicCompletion E →+* w.adicCompletion E) {d : ℕ} (hd0 : 0 < d)
    (hd : Valued.v ((d : w.adicCompletion E)) < 1) (x : w.adicCompletion E) (hx : Valued.v x ≤ 1) :
    Valued.v (s x) ≤ 1 := by
  have hne : Valued.v ((d : w.adicCompletion E)) ≠ 0 := by
    rw [Valuation.ne_zero_iff, ← map_natCast (algebraMap E (w.adicCompletion E))]
    exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hd0.ne')
  set a := log (Valued.v ((d : w.adicCompletion E)))
  have hda : Valued.v ((d : w.adicCompletion E)) = exp a := (exp_log hne).symm
  have ha : a < 0 := by
    have : exp a < exp (0 : ℤ) := by rw [exp_zero, ← hda]; exact hd
    exact exp_lt_exp.mp this
  have hm : -a < ((d * a.natAbs + 1 : ℕ) : ℤ) := by
    have h0 : ((d * a.natAbs + 1 : ℕ) : ℤ) = (d : ℤ) * (a.natAbs : ℤ) + 1 := by push_cast; ring
    have h1 : (1 : ℤ) ≤ d := by exact_mod_cast hd0
    have h2 : (0 : ℤ) ≤ a.natAbs := by positivity
    have h3 : -a ≤ (a.natAbs : ℤ) := by omega
    have h4 : (1 : ℤ) * (a.natAbs : ℤ) ≤ (d : ℤ) * (a.natAbs : ℤ) := mul_le_mul_of_nonneg_right h1 h2
    rw [h0]; linarith
  by_contra h
  push Not at h
  apply no_root w a hda ha hm (s x) h
  obtain ⟨y, hy⟩ := exists_root w hd a.natAbs x hx
  refine ⟨s y, ?_⟩
  rw [← map_pow, hy]
  simp

theorem continuous_ringHom (s : w.adicCompletion E →+* w.adicCompletion E) : Continuous s := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_lt_one w
  have hne : Valued.v ((d : w.adicCompletion E)) ≠ 0 := by
    rw [Valuation.ne_zero_iff, ← map_natCast (algebraMap E (w.adicCompletion E))]
    exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hd0.ne')
  have hdK : (d : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mp hne
  set a := log (Valued.v ((d : w.adicCompletion E)))
  have hda : Valued.v ((d : w.adicCompletion E)) = exp a := (exp_log hne).symm
  have ha : a < 0 := by
    have : exp a < exp (0 : ℤ) := by rw [exp_zero, ← hda]; exact hd
    exact exp_lt_exp.mp this
  refine continuous_of_continuousAt_zero s ?_
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' _)).mpr ?_
  intro γ hγ
  obtain ⟨r, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hr : Valued.v r ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (Valuation.ne_zero_iff _).mp hγ
  set b := log (Valued.v r)
  have hvr : Valued.v r = exp b := (exp_log hr).symm
  set n := b.natAbs + 1
  have hn : (n : ℤ) * a < b := by
    have h1 : (n : ℤ) = (b.natAbs : ℤ) + 1 := by simp only [n]; push_cast; ring
    have h2 : -b ≤ (b.natAbs : ℤ) := by omega
    have h3 : (n : ℤ) * (a + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    linarith
  refine ⟨ValuativeRel.valuation _ ((d : w.adicCompletion E) ^ n), ?_, ?_⟩
  · rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hdK
  intro x hx
  change ValuativeRel.valuation _ x < ValuativeRel.valuation _ _ at hx
  rw [(isEquiv w).lt_iff_lt] at hx
  change ValuativeRel.valuation _ (s x) < ValuativeRel.valuation _ r
  rw [(isEquiv w).lt_iff_lt]
  have hdn : (d : w.adicCompletion E) ^ n ≠ 0 := pow_ne_zero _ hdK
  have hz : Valued.v (x / (d : w.adicCompletion E) ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ (by rw [Valuation.pos_iff]; exact hdn)).mpr hx.le
  have hsz := le_one_of_le_one w s hd0 hd _ hz
  have hx' : x = (d : w.adicCompletion E) ^ n * (x / (d : w.adicCompletion E) ^ n) := by
    field_simp
  rw [hx', map_mul, map_pow, map_natCast, map_mul, map_pow, hda, hvr]
  calc exp a ^ n * Valued.v (s (x / (d : w.adicCompletion E) ^ n)) ≤ exp a ^ n * 1 := by gcongr
    _ = exp ((n : ℤ) * a) := by rw [mul_one, ← exp_nsmul, nsmul_eq_mul]
    _ < exp b := exp_lt_exp.mpr hn

end ConjugationUpperEntries

theorem cjEq : CjEq := by
  intro E _ _ _ w _ s hs
  have hc := ConjugationUpperEntries.continuous_ringHom w s
  have h : ∃ s' : w.adicCompletion E →+* w.adicCompletion E, Continuous s' ∧
      ∀ x : E, s' (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨s, hc, hs⟩
  have hcj : GlobalTheory.BCT.cj w = h.choose := by
    unfold GlobalTheory.BCT.cj
    rw [dite_eq_left h]
  rw [hcj]
  have hdense : DenseRange (algebraMap E (w.adicCompletion E)) := by
    apply HeightOneSpectrum.denseRange_algebraMap
  have := hdense.equalizer hc h.choose_spec.1 (funext fun x => by
    simp only [Function.comp_apply]
    rw [hs x, h.choose_spec.2 x])
  exact RingHom.ext fun x => congrFun this x

end PositivityTheory.Rg.BcB.F.LemB

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.PCandTb

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

set_option linter.unusedSectionVars false

theorem isLev_of {a b : ℕ} (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (Q : Finset (Pl E))
    (h : ∀ w, LocOk.IsLv (U w)) (hout : ∀ w ∉ Q, U w = K2 a b w) : IsLev U := by
  refine ⟨fun w => ?_, Filter.eventually_cofinite.2 (Q.finite_toSet.subset fun w hw => ?_)⟩
  · obtain ⟨K₁, K₂, h₁, h₂, he⟩ := h w
    rw [he]
    exact LocOk.prod_open_le h₁ h₂
  · by_contra hq
    exact hw (hout w hq)

variable {n : ℕ} (d : LocData E n) {a : ℕ}

theorem isLev_lev (hd : d.Ok) (ha : a ≤ n) : IsLev (d.lev a) :=
  isLev_of _ (d.T ∪ d.S₀ ∪ d.Bad) (LocOk.lev_lv d hd ha) fun _ hw =>
    LocOk.lev_out d (LocOk.out3 d hw).1 (LocOk.out3 d hw).2

theorem isLev_lev₂ (hd : d.Ok) (ha : a ≤ n) : IsLev (d.lev₂ a) :=
  isLev_of _ (d.T ∪ d.S₀ ∪ d.Bad) (LocOk.lev₂_lv d hd ha) fun _ hw => LocOk.lev₂_out d (LocOk.out3 d hw).2

theorem betaL_H (hd : d.Ok) (ha : a ≤ n) {u : Pl E} (hu : u ∈ d.P) (x y : d.kap u) :
    IsHecke (d.lev a u) ((d.betaL a ha).m u x y) := by
  show IsHecke _ (if u ∈ d.T then d.diag (fun x => d.qT a u x.1.1) x y else d.mac a ha u (d.e u) x.1.2 y.1.2)
  split_ifs with hT
  · rw [LocOk.level_eq_iwahori_pair_at_bad_places d hT]
    exact LocOk.diagH d _ (fun z => LocOk.qT_H d u z.1.1) x y
  · have hS : u ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hu
      tauto
    rw [LocOk.lev_S d hT (Finset.mem_union_left _ hS)]
    exact LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)

theorem gap_restr {m : ℕ} {x : Fin n → ℤ} (hx : x ∈ coneGL n 2) (S : Finset (Fin n)) (h : S.card = m) :
    Gap (PositivityTheory.Rg.Bc.ArchbcB.B.restr x S h) := by
  intro p q hpq
  have := hx _ _ ((S.orderEmbOfFin h).strictMono hpq)
  show x _ + 1 ≤ x _
  omega

theorem unrAt_pow {μ : HChar E} {w : Pl E} (h : μ.UnrAt w) (k : ℕ) : (μ ^ k).UnrAt w := by
  induction k with
  | zero => intro x _; rw [pow_zero]; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ]
    show (μ ^ k).loc w x * μ.loc w x = 1
    rw [ih x hx, h x hx, one_mul]

end PositivityTheory.Rg.BcB.F.PCandTb

namespace PositivityTheory.Rg.BcB.F

open PCandTb

theorem candT_of (h1 : Tail.ReadT) (h2 : Tail.ExpRead) (h3 : RS.JoinSat) : CandT := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwT hunr hns
  have hd := F.ok
  have hwd : w ∈ F.d.T := F.T_le w hwT hunr hns
  have hwSec : w ∈ F₀.Sec := (F.T_in w hwd).1
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h | h
    · exact (F.T_in u h).1
    · rw [F.same.1] at h
      exact (F₀.S₀ u h).1
  have hwP : w ∈ F.d.P := Finset.mem_union_left _ hwd
  obtain ⟨α, x, hx⟩ := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i)
    (Equiv.refl _) F₀.hSec hP (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (F.d.betaL _ (F₀.C.le i)) A G F.m
    (isLev_lev F.d hd (F₀.C.le i)) (isLev_lev₂ F.d hd (F₀.C.le i))
    (locOk idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 E n F.d hd _ (F₀.C.le i)).2.1 (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => (betaL_H F.d hd (F₀.C.le i) hu x y).2 k hk g) hl hne ⟨w, hwP⟩
  have hm : (F.d.betaL _ (F₀.C.le i)).m w = fun x y => if x = y then F.d.qT (F₀.C.a i) w x.1.1 else 0 := by
    funext x y
    show (if w ∈ F.d.T then _ else _) = _
    rw [if_pos hwd]
    rfl
  let G' : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ := fun y => G (α, Function.update x ⟨w, hwP⟩ y)
  change (locM w ((F.d.betaL _ (F₀.C.le i)).m w))^[F.m] G' ≠ 0 at hx
  rw [hm] at hx
  have hfix : ∀ y, G' y ∈ fixed (pairRt (F₀.C.a i) (n - F₀.C.a i) w) (I2 (F₀.C.a i) (n - F₀.C.a i) w) := fun y => by
    have h := ((hl (α, Function.update x ⟨w, hwP⟩ y)).2 w hwSec).1
    rwa [LocOk.level_eq_iwahori_pair_at_bad_places F.d hwd] at h
  have hIo : IsOpen (I2 (F₀.C.a i) (n - F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w)) := by
    have h := ((isLev_lev F.d hd (F₀.C.le i)).1 w).1
    rwa [LocOk.level_eq_iwahori_pair_at_bad_places F.d hwd] at h
  obtain ⟨s, hs⟩ := (locPow_holds E _ _ w _ _ G' F.m hIo hfix).2 (fun x => F.d.qT (F₀.C.a i) w x.1.1) (by convert hx)
  by_cases hadm : LocData.admitted n (F₀.C.a i) s.1.1
  swap
  · exfalso
    have h0 : F.d.qT (F₀.C.a i) w s.1.1 = 0 := by
      funext y
      simp only [LocData.qT, dif_neg hadm]
      rfl
    obtain ⟨k, hk⟩ : ∃ k, F.m = k + 1 := ⟨F.m - 1, by have := F.m_pos; omega⟩
    rw [h0, hk, Function.iterate_succ_apply', Psmall.actP_zero] at hs
    exact hs rfl
  have hq : F.d.qT (F₀.C.a i) w s.1.1 = fun g => ∑ j : (F.d.c w).support,
      (F.d.c w j * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf (j : Fin n → ℤ)) s.1.1) *
        (((I2 (F₀.C.a i) (n - F₀.C.a i) w).relIndex (K2 (F₀.C.a i) (n - F₀.C.a i) w) : ℕ) : ℂ)) *
      dc2 w (F.d.ϖ w) (restr (j : Fin n → ℤ) _ hadm.2.1) (restr (j : Fin n → ℤ) _ hadm.2.2) g := by
    funext g
    simp only [LocData.qT, dif_pos hadm, Finsupp.sum]
    rw [← Finset.sum_coe_sort]
  rw [hq] at hs
  obtain ⟨ξa, ξb, hJ, hsum⟩ := h1 E n (F₀.C.a i) (n - F₀.C.a i) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F.d.ϖ w)
    (F.d.c w).support _ (fun j => restr (j : Fin n → ℤ) _ hadm.2.1) (fun j => restr (j : Fin n → ℤ) _ hadm.2.2) F.m (G' s)
    (hd.unif w)
    (fun j => ⟨gap_restr (hd.cone w hwd (Finset.mem_coe.2 j.2)) _ _, gap_restr (hd.cone w hwd (Finset.mem_coe.2 j.2)) _ _⟩)
    ((F.choiceM i s₁ s₂ Pa Pb D hc).2 w hwd) (hG _) (hfix s) hs
  have hsum' : ((F.d.c w).sum fun x t => t * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf x) s.1.1) *
      ev2 w ξa ξb (restr x _ hadm.2.1) (restr x _ hadm.2.2)) ≠ 0 := by
    intro h0
    rw [Finsupp.sum, ← Finset.sum_coe_sort] at h0
    apply hsum
    rw [show (0 : ℂ) = (((I2 (F₀.C.a i) (n - F₀.C.a i) w).relIndex (K2 (F₀.C.a i) (n - F₀.C.a i) w) : ℕ) : ℂ) * 0 by ring,
      ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hJ' : JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb := by
    rw [← F.same.2.2.2.1]
    exact hJ
  obtain ⟨hma, hmb, hbc⟩ := F.choiceT i s₁ s₂ Pa Pb D hc w hwd s.1.1 hadm ξa ξb hJ' hsum'
  obtain ⟨hSa, hSb⟩ := h2 E (F₀.C.a i) (n - F₀.C.a i) Pa Pb w (F.d.ϖ w) ξa ξb (hd.unif w) hma hmb hJ
  have hS0 : w ∉ F₀.d₀.S₀ := by
    rw [← F.same.1]
    exact Finset.disjoint_left.1 hd.disj.1 hwd
  have hBad : w ∉ F₀.d₀.Bad := by
    rw [← F.same.2.1]
    exact Finset.disjoint_left.1 hd.disj.2.1 hwd
  have hμ := (F₀.good w hwSec hS0 hBad).2
  have hDs := h3 E n (F₀.C.a i) (n - F₀.C.a i) (F₀.μ ^ (n - F₀.C.a i)) (F₀.μ ^ F₀.C.a i) Pa Pb D w _ _ hc.ctx.join
    (unrAt_pow hμ _) (unrAt_pow hμ _) hSa hSb
  refine ⟨_, hDs, fun s' ϖ q hs' hq' α' hα' => ?_⟩
  have e := LemB.cjEq E w hns s' hs'
  subst e
  exact hbc ϖ q hq' α' hα'

end PositivityTheory.Rg.BcB.F

end
