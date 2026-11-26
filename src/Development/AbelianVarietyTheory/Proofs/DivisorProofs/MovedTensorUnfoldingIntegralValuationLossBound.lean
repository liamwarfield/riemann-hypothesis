module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqVolumeSumCharacterTwistedCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPlaceValuationResidueFieldCardEqZeroOfNotMe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPlaceValuationResidueFieldCardEqZeroOfNotMe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss.ResCardAway

theorem absNorm_eq_plc_pow {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, Ideal.absNorm P.asIdeal = ringChar (𝓞 K ⧸ P.asIdeal) ^ n := by
  classical
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI : Fintype (𝓞 K ⧸ P.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 K ⧸ P.asIdeal) (ringChar (𝓞 K ⧸ P.asIdeal))
  refine ⟨n, ?_⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact hn

theorem vw_resCard_eq_zero : ∀ {D : D7} (P : Pl D.host.E) (w : PlL D),
    ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
  intro D P w h
  obtain ⟨n, hn⟩ := absNorm_eq_plc_pow P
  have hq : resCard (Kw P) = Formalism.EigenvalueLevelCeiling.plc P ^ n :=
    (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw P).trans hn
  have hnot : ((resCard (Kw P) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
    rw [hq, Nat.cast_pow]
    exact fun hm => h (w.isPrime.mem_of_pow_mem n hm)
  letI : StarRing D.what₂.LL := starRingOfComm
  have := Formalism.DivisionValues.ValuationZeroReduction.vw_eq_zero_of_not_mem w _ hnot
  simpa using this

end GlobalTheory.UnfoldLoss.ResCardAway
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPlaceValuationResidueFieldCardEqZeroOfNotMeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffPlace_valuation_residueFieldCard_eq_zero_of_not_mem : ∀ {D : D7} (P : Pl D.host.E) (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
  first | exact @GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero | exact GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero | (intros; apply GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorFactorCoeffValuationLossLeAwayPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorFactorCoeffValuationLossLeAwayPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.MovedTwist

open _root_.Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_loc {L : Type} [Field L] [NumberField L] (χ : HChar L) {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ}
    (hinf : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 L)) {q : ℕ} (hq : (q : 𝓞 L) ∈ v.asIdeal) (x : (v.adicCompletion L)ˣ) :
    UnitOff q ((χ.loc v x : ℂˣ) : ℂ) := by
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt L χ
  have hinf' : (χ ^ N).HasInf φ fun i => n i * N := fun k => by
    have e : (χ ^ N).inf k = χ.inf k ^ N := rfl
    rw [e, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_mul, zpow_natCast]
  have hv := GlobalTheory.ValUnit.unitOff_val L (χ ^ N) I φ _ v q hinf' (by simp [hu]) (fun w x hx _ => hu w x hx) (hu v) hq
  refine unitOff_of_pow hN ?_
  have e : ((χ.loc v x : ℂˣ) : ℂ) ^ N = (((χ ^ N).loc v x : ℂˣ) : ℂ) := by
    rw [← Units.val_pow_eq_pow_val]; rfl
  rw [e]
  set u : (v.adicCompletion L)ˣ := atFin v (unif v) with hudef
  have h0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  have hu1 : Valued.v (u : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hx : Valued.v (x : v.adicCompletion L) = WithZero.exp (WithZero.log (Valued.v (x : v.adicCompletion L))) :=
    (WithZero.exp_log h0).symm
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (((x * u ^ m : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1 := by
    refine ⟨WithZero.log (Valued.v (x : v.adicCompletion L)), ?_⟩
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, hu1, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hx' : x = (x * u ^ m) * u ^ (-m) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx', map_mul, hu v _ hm, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  exact unitOff_zpow hv _

theorem unitOff_sqrt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) {q : ℕ} (hq0 : q ≠ 0)
    (hq : (q : 𝓞 L) ∈ v.asIdeal) : UnitOff q ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) := by
  refine unitOff_of_pow two_pos ?_
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hq)
  rw [Ideal.absNorm_span_natCast] at h
  obtain ⟨b, hb⟩ := h
  have hi : ∀ a : ℕ, IsIntegral ℤ (a : ℂ) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (a : ℤ))
  refine unitOff_of_mul_eq (m := Module.finrank ℤ (𝓞 L)) (hi _) (hi b) ?_ hq0
  rw [← Nat.cast_mul, ← hb, Nat.cast_pow]

variable {D : D7}

theorem unitOff_apow_half {P : Pl D.host.E} {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 D.host.E) ∈ P.asIdeal) (x : (Kw P)ˣ) (z : ℤ) :
    UnitOff q (apow x ((z : ℂ) / 2)) := by
  obtain ⟨n, hn⟩ := GlobalTheory.MovedField.exists_zpow_unit P x
  have h1 : valuation (Kw P) (((x * unifAt P ^ n : (Kw P)ˣ)) : Kw P) = 1 := (Good.isEquiv_Kw P).eq_one_iff_eq_one.2 hn
  have hx : x = (x * unifAt P ^ n) * unifAt P ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, apow_mul, apow_of_valuation_eq_one h1, one_mul, apow_zpow, (isUnif_unifAt P).apow_eq,
    GlobalTheory.LFun.SatBoundGL.resCard_completion]
  have e1 : -(((-n : ℤ) : ℂ) * ((z : ℂ) / 2)) = ((((n * z : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, GlobalTheory.MovedField.natCast_cpow_half]
  exact unitOff_zpow (unitOff_sqrt_absNorm P hq0 hq) _

theorem lossLe_unit_mul {w : PlL D} {q : ℕ} (hw : (q : 𝓞 D.what₂.LL) ∉ w.asIdeal) {u z : ℂ} {c : ℝ}
    (hu : u ∈ D.what₂.embLL.fieldRange) (hq : UnitOff q u) (hz : LossLe w z c) : LossLe w (u * z) c := by
  obtain ⟨y, rfl⟩ := hu
  obtain ⟨y', rfl, h'⟩ := hz
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y' = 0
  · exact Or.inl (by rw [h0, mul_zero])
  have h' := h'.resolve_left h0
  obtain ⟨hy, k, hk, -⟩ := hq
  have hy0 : y ≠ 0 := fun e => hy (by rw [e, map_zero])
  have hq0 : (q : D.what₂.LL) ≠ 0 := by
    have : q ≠ 0 := fun e => hw (by rw [e, Nat.cast_zero]; exact zero_mem _)
    exact_mod_cast this
  have hint : IsIntegral ℤ ((q : D.what₂.LL) ^ k * y) := by
    rw [← isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective]
    simpa using hk
  have hqk : ((q ^ k : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := fun h => hw (w.isPrime.mem_of_pow_mem k (by simpa using h))
  have h1 : vw w ((q ^ k : ℕ) : D.what₂.LL) = 0 := by
    have h0 : ((q ^ k : ℕ) : 𝓞 D.what₂.LL) ≠ 0 := fun e => hqk (e ▸ zero_mem _)
    have h1 := Formalism.EigenvalueLevelCeiling.intValuation_eq_exp' w _ h0
    rw [(w.intValuation_eq_one_iff).2 hqk, ← WithZero.exp_zero] at h1
    have h2 := WithZero.exp_injective h1
    have h3 : (((q ^ k : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((q ^ k : ℕ) : D.what₂.LL) := by simp
    rw [h3] at h2
    omega
  have h2 : 0 ≤ vw w ((q : D.what₂.LL) ^ k * y) := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (⟨_, hint⟩ : 𝓞 D.what₂.LL)
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hq0) hy0, ← Nat.cast_pow, h1, zero_add] at h2
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hy0 h0, Int.cast_add]
  have h3 : (0 : ℝ) ≤ (vw w y : ℝ) := by exact_mod_cast h2
  linarith

def UnitIn (K : Subfield ℂ) (q : ℕ) (u : ℂ) : Prop := u ∈ K ∧ UnitOff q u

theorem UnitIn.mul {K : Subfield ℂ} {q : ℕ} {u v : ℂ} (h : UnitIn K q u) (h' : UnitIn K q v) : UnitIn K q (u * v) :=
  ⟨mul_mem h.1 h'.1, unitOff_mul h.2 h'.2⟩

theorem UnitIn.inv {K : Subfield ℂ} {q : ℕ} {u : ℂ} (h : UnitIn K q u) : UnitIn K q u⁻¹ := ⟨inv_mem h.1, unitOff_inv h.2⟩

theorem UnitIn.pow {K : Subfield ℂ} {q : ℕ} {u : ℂ} (h : UnitIn K q u) (n : ℕ) : UnitIn K q (u ^ n) :=
  ⟨pow_mem h.1 n, unitOff_pow h.2 n⟩

theorem unitIn_one (K : Subfield ℂ) (q : ℕ) : UnitIn K q 1 := ⟨one_mem K, unitOff_one q⟩

theorem unitIn_prod {α : Type*} {K : Subfield ℂ} {q : ℕ} (f : α → ℂ) :
    ∀ l : List α, (∀ a ∈ l, UnitIn K q (f a)) → UnitIn K q (l.map f).prod
  | [], _ => by simpa using unitIn_one K q
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact (h a List.mem_cons_self).mul (unitIn_prod f l fun b hb => h b (List.mem_cons_of_mem _ hb))

end GlobalTheory.MovedTwist


open GlobalTheory.MovedTwist GlobalTheory.MovedField Formalism.L2.Host GlobalTheory.ChiUnit in
theorem GlobalTheory.MovedTwist.moved_lossLe : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∉ ch.G.pl.W0 → ∀ (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    ∀ (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z) c := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β _ P hP w hw c _ hT z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  set q : ℕ := Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) with hqdef
  have hq0 : q ≠ 0 := (Formalism.EigenvalueLevelCeiling.plc_prime _).ne_zero
  have hq : (q : 𝓞 D.host.E) ∈ (P : Pl D.host.E).asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem _
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (P : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt P.1 (.inr ⟨t, P.2⟩))
  have hmu : ∀ j (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).mu j x : ℂˣ) : ℂ) := fun j x => by
    show UnitIn K q ((((GlobalTheory.FunObj.muBase _ j * _).loc _) x : ℂˣ) : ℂ)
    change UnitIn K q (((GlobalTheory.FunObj.muBase R.toLevCh j).loc P.1 x * (R.xiH t).loc P.1 x : ℂˣ) : ℂ)
    rw [Units.val_mul]
    refine UnitIn.mul ?_ ⟨(hK _).1 (hF.chars.xi t _ x), ?_⟩
    · rcases j with _ | j
      · simpa [GlobalTheory.FunObj.muBase, HChar.loc] using unitIn_one K q
      · rw [GlobalTheory.FunObj.muBase]
        split_ifs with hj
        · obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf
          exact ⟨(hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x), unitOff_loc _ hn _ hq x⟩
        · simpa [HChar.loc] using unitIn_one K q
    · obtain ⟨n, hn, ho⟩ := hS.core.lev.xi_fin t
      refine unitOff_of_pow_eq_one q hn ?_
      have : ((R.toLevCh.xiH t) ^ n).loc P.1 x = 1 := by rw [show (R.toLevCh.xiH t) ^ n = 1 from ho]; rfl
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val this
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).chi i x : ℂˣ) : ℂ) :=
    fun i h1 h2 x => ⟨(hK _).1 (hF.chars.chi i h1 h2 _ x), unitOff_loc _ (ch.G.ch.inf i h1 h2) _ hq x⟩
  have heta : ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).eta x : ℂˣ) : ℂ) := fun x => by
    have hu := R.toLevCh.C.isEta.unr P.1
    obtain ⟨y, hy⟩ := hF.chars.eta P.1 hu
    exact ⟨loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x, unitOff_loc _ R.toLevCh.C.isEta.inf _ hq x⟩
  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).kappa e X x : ℂˣ) : ℂ) := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, div_eq_mul_inv]
    refine UnitIn.mul ?_ ((heta x).pow _).inv
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw P.1)ˣ) (n : ℕ), UnitIn K q (apow x ((n : ℂ) / 2)) ∧ UnitIn K q (apow x (-(n : ℂ) / 2)) := fun x n =>
    ⟨⟨by simpa using apow_half_mem hsq x n, by simpa using unitOff_apow_half hq0 hq x n⟩,
      by simpa using apow_half_mem hsq x (-n), by simpa using unitOff_apow_half hq0 hq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, UnitIn K q ((locGrid ch.G t P).edgeFactor .one g e) := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact (((hkap e he _ _).mul (hkap e he _ _).inv).mul (hap _ _).1).mul (hap _ _).2
  have hk : keepAt ch.G (P : Pl D.host.E) = true := by
    classical
    simp [keepAt, hP]
  have hg := unitIn_prod _ _ (hedge ((repsAt ch.G t P).elt (β P)))
  simp only [moved, Grid.pathAct, hk, if_true, one_mul]
  exact lossLe_unit_mul hw hg.1 hg.2 (hT _)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorFactorCoeffValuationLossLeAwayPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

open GlobalTheory.MovedTwist GlobalTheory.MovedField Formalism.L2.Host GlobalTheory.ChiUnit in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensorFactor_coeffValuationLossLe_awayPrime : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∉ ch.G.pl.W0 → ∀ (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    ∀ (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z) c := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β _ P hP w hw c _ hT z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  set q : ℕ := Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) with hqdef
  have hq0 : q ≠ 0 := (Formalism.EigenvalueLevelCeiling.plc_prime _).ne_zero
  have hq : (q : 𝓞 D.host.E) ∈ (P : Pl D.host.E).asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem _
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (P : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt P.1 (.inr ⟨t, P.2⟩))
  have hmu : ∀ j (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).mu j x : ℂˣ) : ℂ) := fun j x => by
    change UnitIn K q (((GlobalTheory.FunObj.muBase R.toLevCh j).loc P.1 x : ℂ) *
      ((R.xiH t).loc P.1 x : ℂ))
    refine UnitIn.mul ?_ ⟨(hK _).1 (hF.chars.xi t _ x), ?_⟩
    · rcases j with _ | j
      · exact unitIn_one K q
      · rw [GlobalTheory.FunObj.muBase]
        split_ifs with hj
        · obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf
          exact ⟨(hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x), unitOff_loc _ hn _ hq x⟩
        · exact unitIn_one K q
    · obtain ⟨n, hn, ho⟩ := hS.core.lev.xi_fin t
      refine unitOff_of_pow_eq_one q hn ?_
      have : ((R.toLevCh.xiH t) ^ n).loc P.1 x = 1 := by rw [show (R.toLevCh.xiH t) ^ n = 1 from ho]; rfl
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val this
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).chi i x : ℂˣ) : ℂ) :=
    fun i h1 h2 x => ⟨(hK _).1 (hF.chars.chi i h1 h2 _ x), unitOff_loc _ (ch.G.ch.inf i h1 h2) _ hq x⟩
  have heta : ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).eta x : ℂˣ) : ℂ) := fun x => by
    have hu := R.toLevCh.C.isEta.unr P.1
    obtain ⟨y, hy⟩ := hF.chars.eta P.1 hu
    exact ⟨loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x, unitOff_loc _ R.toLevCh.C.isEta.inf _ hq x⟩
  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).kappa e X x : ℂˣ) : ℂ) := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, div_eq_mul_inv]
    refine UnitIn.mul ?_ ((heta x).pow _).inv
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw P.1)ˣ) (n : ℕ), UnitIn K q (apow x ((n : ℂ) / 2)) ∧ UnitIn K q (apow x (-(n : ℂ) / 2)) := fun x n =>
    ⟨⟨by simpa using apow_half_mem hsq x n, by simpa using unitOff_apow_half hq0 hq x n⟩,
      by simpa using apow_half_mem hsq x (-n), by simpa using unitOff_apow_half hq0 hq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, UnitIn K q ((locGrid ch.G t P).edgeFactor .one g e) := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact (((hkap e he _ _).mul (hkap e he _ _).inv).mul (hap _ _).1).mul (hap _ _).2
  have hk : keepAt ch.G (P : Pl D.host.E) = true := by
    classical
    simp [keepAt, hP]
  have hg := unitIn_prod _ _ (hedge ((repsAt ch.G t P).elt (β P)))
  simp only [moved, Grid.pathAct, hk, ite_true, one_mul]
  exact lossLe_unit_mul hw hg.1 hg.2 (hT _)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariablesUniformizerPowerLatticeBasisOpenVolumeStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariablesUniformizerPowerLatticeBasisOpenVolume
open MeasureTheory ValuativeRel GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.UnfoldLoss

namespace GlobalTheory.UnfoldLoss.LatVol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem varLat_eq_pi (G : Grid k) (ϖ : kˣ) (n : ℕ) :
    (varLat G ϖ n : Set (Vars G)) = Set.univ.pi fun _ => Set.univ.pi fun _ => cball (ϖ ^ n) := by
  ext e
  exact ⟨fun h j _ r _ => h j r, fun h j r => h j trivial r trivial⟩

theorem eventually_cball_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {U : Set k} (hU : U ∈ nhds (0 : k)) :
    ∀ᶠ n : ℕ in Filter.atTop, cball (ϖ ^ n) ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  haveI : MulArchimedean (ValueGroupWithZero k) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 γ
  refine Filter.eventually_atTop.2 ⟨N, fun n hn z hz => hγ ?_⟩
  have hz' : valuation k z ≤ valuation k ((ϖ ^ n : kˣ) : k) := hz
  rw [Units.val_pow_eq_pow_val, map_pow] at hz'
  exact (hz'.trans (pow_le_pow_of_le_one zero_le h1.le hn)).trans_lt hN

theorem varLat_basis_open_vol : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (G : Grid k) (ν : Measure k), IsUnitVol ν → ∀ ϖ : kˣ, IsUnif ϖ →
    (∀ s ∈ nhds (0 : Vars G), ∃ n : ℕ, (varLat G ϖ n : Set (Vars G)) ⊆ s) ∧
    ∀ n : ℕ, IsOpen (varLat G ϖ n : Set (Vars G)) ∧ varsVol G ν (varLat G ϖ n : Set (Vars G)) ≠ ⊤ ∧
      (varsVol G ν).real (varLat G ϖ n : Set (Vars G)) = ((resCard k : ℝ)⁻¹) ^ (n * varCount G) := by
  intro k _ _ _ _ _ _ G ν hν ϖ hϖ
  classical
  refine ⟨fun s hs => ?_, fun n => ?_⟩
  · rw [nhds_pi, Filter.mem_pi'] at hs
    obtain ⟨I, t, ht, hts⟩ := hs
    have key : ∀ j, ∀ᶠ n : ℕ in Filter.atTop, (Set.univ.pi fun _ => cball (ϖ ^ n)) ⊆ t j := fun j => by
      have hj := ht j
      rw [nhds_pi, Filter.mem_pi'] at hj
      obtain ⟨J, u, hu, hut⟩ := hj
      filter_upwards [Filter.eventually_all.2 fun r => eventually_cball_subset hϖ (hu r)] with n hn e he
      exact hut fun r _ => hn r (he r trivial)
    obtain ⟨n, hn⟩ := (Filter.eventually_all.2 key).exists
    refine ⟨n, fun e he => hts fun j _ => hn j fun r _ => he j r⟩
  · haveI := hν.1
    haveI := secondCountable k
    have h1 : ((distribHaarChar k ϖ : NNReal) : ℝ) = (resCard k : ℝ)⁻¹ :=
      nabs_uniformiser hϖ.irreducible rfl
    have hv : varsVol G ν (varLat G ϖ n : Set (Vars G)) =
        ((distribHaarChar k ϖ ^ (n * varCount G) : NNReal) : ENNReal) := by
      rw [varLat_eq_pi, varsVol, Measure.pi_pi]
      simp only [Measure.pi_pi, measure_cball, hν.2, mul_one, Finset.prod_const, Finset.card_univ, map_pow,
        varCount, ← Nat.card_eq_fintype_card, ENNReal.coe_pow, ← pow_mul, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · rw [varLat_eq_pi]
      exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _
    · rw [hv]; exact ENNReal.coe_ne_top
    · rw [Measure.real, hv, ENNReal.coe_toReal, NNReal.coe_pow, h1]

end GlobalTheory.UnfoldLoss.LatVol
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.variablesUniformizerPowerLattice_basis_open_volume : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (G : Grid k) (ν : Measure k), IsUnitVol ν → ∀ ϖ : kˣ, IsUnif ϖ →
    (∀ s ∈ nhds (0 : Vars G), ∃ n : ℕ, (varLat G ϖ n : Set (Vars G)) ⊆ s) ∧
    ∀ n : ℕ, IsOpen (varLat G ϖ n : Set (Vars G)) ∧ varsVol G ν (varLat G ϖ n : Set (Vars G)) ≠ ⊤ ∧
      (varsVol G ν).real (varLat G ϖ n : Set (Vars G)) = ((resCard k : ℝ)⁻¹) ^ (n * varCount G) := by
  first | exact @GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol | exact GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol | (intros; apply GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorChosenPlaceCoeffValuationLossLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorChosenPlaceCoeffValuationLossLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.UnfoldLoss.MovedChosen

section Local

variable {k : Type} [Field k] {G : Grid k}

theorem gdet_stair (hs : 1 ≤ G.s) (ϖ : kˣ) (e j : ℕ) :
    ∃ a : ℕ, gdet (stair G ϖ e j) = ϖ ^ a ∧ a ≤ G.rank (G.m, j) * (e * G.m) := by
  refine ⟨∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j), ?_, ?_⟩
  · rw [stair, gdet, det_diagGL, Finset.prod_pow_eq_pow_sum]
  · calc ∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j) ≤ ∑ _a : Fin (G.rank (G.m, j)), e * G.m :=
          Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (by have := topRank_add hs j; have := a.2; omega)
      _ = _ := by simp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gdet_elt (hs : 1 ≤ G.s) (J : G.Level) (ϖ : kˣ) (e : ℕ) (X : ℕ × ℕ) :
    ∃ a : ℕ, gdet ((Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X) = ϖ ^ a ∧
      a ≤ G.rank X * (e * G.m) := by
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]
      exact gdet_stair hs ϖ e j
    · cases j with
      | zero =>
        rw [Reps.elt, onColumn_apply]
        exact gdet_stair hs ϖ e 0
      | succ i =>
        refine ⟨0, ?_, Nat.zero_le _⟩
        rw [Reps.elt, onColumn_apply]
        simp [show ¬ i < G.m - 2 by omega]
  · refine ⟨0, ?_, Nat.zero_le _⟩
    simp [Reps.elt, onColumn, hi]

theorem apow_half {ϖ : kˣ} (hϖ : IsUnif ϖ) (a n : ℕ) :
    apow (ϖ ^ a)⁻¹ ((n : ℂ) / 2) = ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (a * n) := by
  rw [apow_inv, apow_pow, hϖ.apow_eq, neg_neg, mul_comm a n, pow_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_mul_nat]
  push_cast
  congr 1
  ring

end Local

section Val

variable {D : D7}

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  refine Or.inr ?_
  have h1 := hy.resolve_left h0
  have h2 := hy'.resolve_left h0'
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

theorem lossLe_list_prod {w : PlL D} {ι : Type} (f : ι → ℂ) (a : ℝ) (l : List ι) (h : ∀ b ∈ l, LossLe w (f b) a) :
    LossLe w (l.map f).prod (l.length * a) := by
  induction l with
  | nil => exact ⟨1, by simp, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (lossLe_mul (h b (by simp)) (ih fun c hc => h c (by simp [hc]))).mono (le_of_eq ?_)
    simp only [List.length_cons]
    push_cast
    ring

theorem lossLe_sqrt {w : PlL D} {q : ℕ} (hq : q ≠ 0) (hs : ((Real.sqrt q : ℝ) : ℂ) ∈ Set.range D.what₂.embLL) (n n' : ℕ) :
    LossLe w (((Real.sqrt q : ℝ) : ℂ) ^ n * (((Real.sqrt q : ℝ) : ℂ) ^ n')⁻¹) (n' * (vw w (q : D.what₂.LL) : ℝ) / 2) := by
  obtain ⟨y, hy⟩ := hs
  have h2 : y ^ 2 = (q : D.what₂.LL) := D.what₂.embLL.injective (by
    rw [map_pow, hy, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast])
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (q : D.what₂.LL) = 0 := by rw [← h2]; simp
    exact hq (by exact_mod_cast this)
  have hv : (vw w (q : D.what₂.LL) : ℝ) = 2 * vw w y := by
    rw [← h2, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0]
    push_cast
    ring
  have hv0 : (0 : ℝ) ≤ (vw w (q : D.what₂.LL) : ℝ) := by exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w q
  refine ⟨y ^ n * (y ^ n')⁻¹, by rw [map_mul, map_inv₀, map_pow, map_pow, hy], Or.inr ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hy0) (inv_ne_zero (pow_ne_zero _ hy0)), Formalism.DivisionValues.ValuationRepresentative.vw_inv,
    ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, hv]
  rw [hv] at hv0
  have : (0 : ℝ) ≤ (n : ℝ) * vw w y := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  push_cast
  linarith

theorem rank_le {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (P : Pl D.host.E) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (locGrid G t P).rank (i, j) ≤ bigN D := by
  have h1 := Nat.mul_le_mul_right D.R.t hj
  have h2 := Nat.mul_le_mul_right (sLen D) hi
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
  nlinarith

end Val

theorem moved_loss : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∈ ch.G.pl.W0 → ∀ (w : PlL D) (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z)
      (c + (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) * (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β hβ P hW w c _ hT z
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := Test.pde_ne_q hS
  have hc' : ∀ Q ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal :=
    GlobalTheory.RowTest.guard_of_qGuard hS.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hTT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc' P.2
  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc').1 P.1 P.2).square 0 hm 0 hm).cond
  haveI := (isUnitVol_unitVol P.1).1
  set e := cosExp ch.G P with he
  have hdep : depthAt ch.G P = e := by
    obtain ⟨v, hv, hvP⟩ := Finset.mem_image.1 hW
    have := depthAt_w ch.G hv
    rw [he, ← hvP, this.1, this.2]
  rw [hdep] at hTT
  have hkeep : keepAt ch.G P = false := by simp [keepAt, hW]
  have hO := oneCoset one_le_sLen (psiAt ch.W P.1) (unitVol P.1) (givenLevel ch.G t P) (Tflip ch.W ch.S.B t Φ P) (unifAt P.1) e
    D.R.m_even (isUnif_unifAt P.1) hcond hTT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO ch.G t P hj)
  have hb : β P ∈ unfSupport (psiAt ch.W P.1) (unitVol P.1) false
      (Reps.through one_le_sLen (givenLevel ch.G t P) (stair (locGrid ch.G t P) (unifAt P.1) e)) (Tflip ch.W ch.S.B t Φ P) := by
    have := hβ P
    rw [hkeep] at this
    exact this
  have hβ' := funext (hO _ hb)
  have hdet : ∀ X, ∃ a : ℕ, gdet ((repsAt ch.G t P).elt (β P) X) = unifAt P.1 ^ a ∧
      a ≤ (locGrid ch.G t P).rank X * (e * D.R.m) := fun X => by
    rw [hβ']
    exact gdet_elt (G := locGrid ch.G t P) one_le_sLen _ _ _ X
  generalize (repsAt ch.G t P).elt (β P) = g at hdet ⊢
  have hq := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P.1
  have hsq : ((Real.sqrt (resCard (Kw (P : Pl D.host.E)) : ℕ) : ℝ) : ℂ) ∈ Set.range D.what₂.embLL := by
    rw [ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
    exact hF.sqrt P.1 (Or.inr ⟨t, P.2⟩)
  set v : ℝ := (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hv
  have hv0 : 0 ≤ v := by rw [hv]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
  rw [hkeep, moved_false]
  have hP := lossLe_list_prod (w := w) (fun b : Edge => apow (gdet (g b.src))⁻¹ (((locGrid ch.G t P).rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-((locGrid ch.G t P).rank b.src : ℂ) / 2))
      ((bigN D * (e * D.R.m) * bigN D : ℕ) * v / 2) (oppositePath (locGrid ch.G t P).m) (fun b hb => by
    have hr : (locGrid ch.G t P).rank b.src ≤ bigN D ∧ (locGrid ch.G t P).rank b.tgt ≤ bigN D := by
      change b ∈ oppositePath D.R.m at hb
      simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
      rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
      · exact ⟨rank_le _ _ _ hi.le le_rfl, rank_le _ _ _ hi le_rfl⟩
      · exact ⟨rank_le _ _ _ le_rfl hj, rank_le _ _ _ le_rfl hj.le⟩
    obtain ⟨a, ha, -⟩ := hdet b.src
    obtain ⟨a', ha', hle⟩ := hdet b.tgt
    rw [ha, ha', neg_div, apow_neg, apow_half (isUnif_unifAt P.1), apow_half (isUnif_unifAt P.1)]
    refine (lossLe_sqrt hq hsq _ _).mono ?_
    have h1 : a' * (locGrid ch.G t P).rank b.src ≤ bigN D * (e * D.R.m) * bigN D :=
      Nat.mul_le_mul (hle.trans (Nat.mul_le_mul_right _ hr.2)) hr.1
    have h2 : ((a' * (locGrid ch.G t P).rank b.src : ℕ) : ℝ) ≤ (bigN D * (e * D.R.m) * bigN D : ℕ) := by exact_mod_cast h1
    have h3 := mul_le_mul_of_nonneg_right h2 hv0
    rw [← hv]
    linarith)
  refine (lossLe_mul hP (hT _)).mono (le_of_eq ?_)
  have hlen : (oppositePath (locGrid ch.G t P).m).length = 2 * D.R.m := by
    change (oppositePath D.R.m).length = _
    simp [oppositePath]; ring
  rw [hlen]
  push_cast
  ring

end GlobalTheory.UnfoldLoss.MovedChosen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorChosenPlaceCoeffValuationLossLeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensorChosenPlace_coeffValuationLoss_le : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∈ ch.G.pl.W0 → ∀ (w : PlL D) (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z)
      (c + (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) * (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  first | exact @GlobalTheory.UnfoldLoss.MovedChosen.moved_loss | exact GlobalTheory.UnfoldLoss.MovedChosen.moved_loss | (intros; apply GlobalTheory.UnfoldLoss.MovedChosen.moved_loss <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepVariablesCountGridLocalFlipGridLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepVariablesCountGridLocalFlipGridLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

theorem varCount_le_of_rank_le {k : Type*} [Field k] (G : Grid k) (hs : 1 ≤ G.s) (N : ℕ)
    (hN : ∀ j < G.m, G.rank (G.m, j) ≤ N) : varCount G ≤ G.m * N ^ 2 := by
  unfold varCount
  have hterm : ∀ j : Fin (G.m - 1),
      Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) ≤ N ^ 2 := by
    intro j
    have hj := j.2
    refine (Finite.card_subtype_le _).trans ?_
    rw [Nat.card_prod, Nat.card_sum, Nat.card_sum]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    have h1 := topRank_add hs (G := G) (j + 1)
    have h2 := topRank_add hs (G := G) j
    have h3 := hN (j + 1) (by omega)
    have h4 := hN j (by omega)
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  calc _ ≤ ∑ _j : Fin (G.m - 1), N ^ 2 := Finset.sum_le_sum fun j _ => hterm j
    _ = (G.m - 1) * N ^ 2 := by simp
    _ ≤ G.m * N ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

theorem varCount_locGrid_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E),
    varCount (locGrid G t w) ≤ D.R.m * bigN D ^ 2 := by
  intro D T L sc G t w
  refine varCount_le_of_rank_le (locGrid G t w) (show 1 ≤ D.R.r + 6 by omega) _ fun j hj => ?_
  change j < D.R.m at hj
  have h1 := Nat.mul_le_mul_right D.R.t hj.le
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + D.R.m * (D.R.r + 6) ≤ D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  nlinarith

end GlobalTheory.UnfoldLoss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepVariablesCountGridLocalFlipGridLeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepVariablesCount_gridLocalFlipGrid_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E),
    varCount (locGrid G t w) ≤ D.R.m * bigN D ^ 2 := by
  first | exact @GlobalTheory.UnfoldLoss.varCount_locGrid_le | exact GlobalTheory.UnfoldLoss.varCount_locGrid_le | (intros; apply GlobalTheory.UnfoldLoss.varCount_locGrid_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorUnfoldingIntegralValuationLossBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.UnfoldLoss

theorem varsVol_isAddLeftInvariant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (G : Grid k) (ν : Measure k) [ν.IsAddHaarMeasure] : (varsVol G ν).IsAddLeftInvariant := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  unfold varsVol
  infer_instance

theorem lossLe_mul' {D : D7} {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  rcases hy with h1 | h1
  · exact absurd h1 h0
  rcases hy' with h2 | h2
  · exact absurd h2 h0'
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem datum_loss {large₂ : SizeData₂ D} {F : Face D A} {CF b : ℝ} (hS : HidaSetting large₂ R F) (ch : Choice R) (hIs : ch.Is)
    (hSc : ch.AtScale CF b) (hF : ch.FieldOK) (t : T) (Φ : ch.G.Datum) (β : CosFam ch.G t) (hβ : β ∈ ch.S.supp t Φ)
    (P : locPl ch.G t) (w : PlL D)
    (hcase : (P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal)
    (c : ℝ) (hc : 0 ≤ c) (hT : ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) (X Y) :
    LossLe w ((ch.S.term t Φ β P).datum X Y) (c + 2 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
      (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc' : ∀ Q ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal := hIs.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hTT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc' P.2
  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc').1 P.1 P.2).square 0 hm 0 hm).cond
  haveI := (isUnitVol_unitVol P.1).1
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := Kw P.1)
  haveI : (varsVol (locGrid ch.G t P) (unitVol P.1)).IsAddLeftInvariant := varsVol_isAddLeftInvariant _ _
  set S := moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) with hSdef
  set f := flatIntegrand one_le_sLen (psiAt ch.W P.1) S X Y with hf
  have hdat : (ch.S.term t Φ β P).datum X Y = ∫ e, f e ∂(varsVol (locGrid ch.G t P) (unitVol P.1)) := rfl
  have hcpt : HasCompactSupport f := hasCompactSupport_flatIntegrand one_le_sLen _ hTT _ _ X Y
  set q : ℕ := resCard (Kw (P : Pl D.host.E)) with hq
  set vq : ℝ := (vw w ((q : ℕ) : D.what₂.LL) : ℝ) with hvq
  have hvq0 : 0 ≤ vq := by
    rw [hvq]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w q
  have hq0 : 0 < q := Nat.pos_of_ne_zero (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P.1)
  by_cases h0 : (ch.S.term t Φ β P).datum X Y = 0
  · rw [h0]; exact ⟨0, map_zero _, Or.inl rfl⟩
  have hval : ∀ K1 : ℝ, (∀ z, LossLe w (S z) (c + K1)) → ∀ v, LossLe w (f v) (c + K1) := by
    intro K1 hK v
    by_cases hv : S (fill one_le_sLen X Y v) = 0
    · have : f v = 0 := by simp [hf, flatIntegrand, hv]
      rw [this]; exact ⟨0, map_zero _, Or.inl rfl⟩
    · have hψ := GlobalTheory.T.coeffValuationLossLe_addChar_neg_unfoldingPhase ch large₂ F CF b hS hIs hSc hF t Φ β hβ P X Y v h0 hv w
      have := lossLe_mul' (hK (fill one_le_sLen X Y v)) hψ
      rw [add_zero] at this
      exact this
  have hint : ∀ (n : ℕ) (K1 : ℝ), (∀ v, ∀ u ∈ varLat (locGrid ch.G t P) (unifAt P.1) n,
      ∀ u' ∈ varLat (locGrid ch.G t P) (unifAt P.1) n, f (v + u + u') * f v = f (v + u) * f (v + u')) →
      (∀ v, LossLe w (f v) (c + K1)) →
      LossLe w ((ch.S.term t Φ β P).datum X Y) (c + K1 + ((n * varCount (locGrid ch.G t P) : ℕ) : ℝ) * vq) := by
    intro n K1 hrel hv
    obtain ⟨-, hlat⟩ := GlobalTheory.T.variablesUniformizerPowerLattice_basis_open_volume (locGrid ch.G t P) (unitVol P.1) (isUnitVol_unitVol P.1) (unifAt P.1) (isUnif_unifAt P.1)
    obtain ⟨hop, hfin, hvol⟩ := hlat n
    obtain ⟨s, hs⟩ := GlobalTheory.T.integral_eq_volume_sum_characterTwistedCosets (varsVol (locGrid ch.G t P) (unitVol P.1)) _ hop hfin f hcpt hrel
    rw [hdat, hs, hvol]
    obtain ⟨h1, h2⟩ := GlobalTheory.T.coeffValuationLoss_finsetSum_and_invPow w
    exact lossLe_mul' (h1 s f _ fun i _ => hv i) (h2 q _ hq0)
  by_cases hW : (P : Pl D.host.E) ∈ ch.G.pl.W0
  · set e := cosExp ch.G P with he
    have hdep : depthAt ch.G P = e := by
      obtain ⟨v, hv, hvP⟩ := Finset.mem_image.1 hW
      have := depthAt_w ch.G hv
      rw [he, ← hvP, this.1, this.2]
    rw [hdep] at hTT
    have hkeep : keepAt ch.G P = false := by simp [keepAt, hW]
    have hO := oneCoset one_le_sLen (psiAt ch.W P.1) (unitVol P.1) (givenLevel ch.G t P) (Tflip ch.W ch.S.B t Φ P) (unifAt P.1) e
      D.R.m_even (isUnif_unifAt P.1) hcond hTT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO ch.G t P hj)
    have hb : β P ∈ unfSupport (psiAt ch.W P.1) (unitVol P.1) false
        (Reps.through one_le_sLen (givenLevel ch.G t P) (stair (locGrid ch.G t P) (unifAt P.1) e)) (Tflip ch.W ch.S.B t Φ P) := by
      have := hβ P
      rw [hkeep] at this
      exact this
    have hβ' := funext (hO _ hb)
    have hSeq : S = moved (locGrid ch.G t P) (keepAt ch.G P)
        ((Reps.through one_le_sLen (givenLevel ch.G t P) (stair (locGrid ch.G t P) (unifAt P.1) e)).elt
          fun i => DoubleCoset.mk _ _ (stair (locGrid ch.G t P) (unifAt P.1) e (i + 1))) (Tflip ch.W ch.S.B t Φ P) := by
      rw [hSdef, ← hβ']; rfl
    have hrel : ∀ v, ∀ u ∈ varLat (locGrid ch.G t P) (unifAt P.1) (D.R.m * e),
        ∀ u' ∈ varLat (locGrid ch.G t P) (unifAt P.1) (D.R.m * e), f (v + u + u') * f v = f (v + u) * f (v + u') := by
      intro v u hu u' hu'
      have hper := GlobalTheory.T.movedStaircaseTensor_periodic_uniformizerPow (locGrid ch.G t P) one_le_sLen (unifAt P.1) (isUnif_unifAt P.1) e _ hTT (givenLevel ch.G t P)
        (keepAt ch.G P) X Y
      have hψ2 := GlobalTheory.T.addChar_neg_unfoldingPhase_mul_uniformizerPowLattice (locGrid ch.G t P) (psiAt ch.W P.1) hcond (unifAt P.1) (isUnif_unifAt P.1) _ X v u u' hu hu'
      have e1 := hper (v + u) u' hu'
      have e2 := hper v u hu
      have e3 := hper v u' hu'
      rw [← hSeq] at e1 e2 e3
      simp only [hf, flatIntegrand]
      rw [e1, e2, e3]
      linear_combination (S (fill one_le_sLen X Y v)) ^ 2 * hψ2
    have hmov := GlobalTheory.T.movedTensorChosenPlace_coeffValuationLoss_le ch large₂ F CF b hS hIs hSc hF t Φ β hβ P hW w c hc hT
    have h1 := hint (D.R.m * e) _ hrel (hval _ hmov)
    refine h1.mono ?_
    have hcount := GlobalTheory.T.stepVariablesCount_gridLocalFlipGrid_le ch.G t P
    have hle : ((D.R.m * e * varCount (locGrid ch.G t P) : ℕ) : ℝ) ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (e : ℝ) := by
      have h2 : D.R.m * e * varCount (locGrid ch.G t P) ≤ D.R.m * e * (D.R.m * bigN D ^ 2) := Nat.mul_le_mul_left _ hcount
      calc ((D.R.m * e * varCount (locGrid ch.G t P) : ℕ) : ℝ) ≤ ((D.R.m * e * (D.R.m * bigN D ^ 2) : ℕ) : ℝ) := by
            exact_mod_cast h2
        _ = _ := by push_cast; ring
    have h3 := mul_le_mul_of_nonneg_right hle hvq0
    nlinarith
  · have hw : ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := hcase.resolve_left hW
    have hv0 : vq = 0 := by rw [hvq]; exact_mod_cast GlobalTheory.T.coeffPlace_valuation_residueFieldCard_eq_zero_of_not_mem P.1 w hw
    have he0 : cosExp ch.G P = 0 := (depthAt_of_notMem ch.G hW).1
    have hlc : IsLocallyConstant f := by
      have hmv : Continuous ((locGrid ch.G t P).moveArgs .one ((repsAt ch.G t P).elt (β P))) := continuous_pi fun b =>
        (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
      have hψ : IsLocallyConstant fun e => ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) :=
        ((hcond.isLocallyConstant.comp Subtype.val).comp_continuous (continuous_phase X).neg)
      exact ((IsLocallyConstant.const _).mul ((IsLocallyConstant.const _).mul
        ((isLocallyConstant_of_isTensor hTT).comp_continuous (hmv.comp (continuous_fill one_le_sLen X Y))))).mul hψ
    obtain ⟨hbasis, -⟩ := GlobalTheory.T.variablesUniformizerPowerLattice_basis_open_volume (locGrid ch.G t P) (unitVol P.1) (isUnitVol_unitVol P.1) (unifAt P.1) (isUnif_unifAt P.1)
    obtain ⟨n, hn⟩ := hbasis _ ((GlobalTheory.LCIntegralField.isOpen_stab hlc hcpt).mem_nhds (zero_mem _))
    have hrel : ∀ v, ∀ u ∈ varLat (locGrid ch.G t P) (unifAt P.1) n,
        ∀ u' ∈ varLat (locGrid ch.G t P) (unifAt P.1) n, f (v + u + u') * f v = f (v + u) * f (v + u') := by
      intro v u hu u' hu'
      have e1 : ∀ y, f (y + u) = f y := hn hu
      have e2 : ∀ y, f (y + u') = f y := hn hu'
      rw [e2, e1, e2]
    have hmov := GlobalTheory.T.movedTensorFactor_coeffValuationLossLe_awayPrime ch large₂ F CF b hS hIs hSc hF t Φ β hβ P hW w hw c hc hT
    have h1 := hint n 0 hrel (hval 0 fun z => by simpa using hmov z)
    simpa [he0, hv0] using h1

end Main

theorem unfold_loss : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₂ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t) (w : PlL D),
        ((P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ c : ℝ, 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
        ∀ X Y, LossLe w ((ch.S.term t Φ β P).datum X Y) (c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) :=
  ⟨0, fun _ _ => ⟨2, fun _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS ch hIs hSc hF t Φ β hβ P w hcase c hc hT X Y =>
    datum_loss hS ch hIs hSc hF t Φ β hβ P w hcase c hc hT X Y⟩⟩⟩

end GlobalTheory.UnfoldLoss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorUnfoldingIntegralValuationLossBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensor_unfolding_integral_valuation_loss_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₂ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t) (w : PlL D),
        ((P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ c : ℝ, 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
        ∀ X Y, LossLe w ((ch.S.term t Φ β P).datum X Y) (c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  first | exact @GlobalTheory.UnfoldLoss.unfold_loss | exact GlobalTheory.UnfoldLoss.unfold_loss | (intros; apply GlobalTheory.UnfoldLoss.unfold_loss <;> assumption)
end
