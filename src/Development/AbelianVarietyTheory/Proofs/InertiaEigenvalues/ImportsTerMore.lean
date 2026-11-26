module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramified
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
public import Formalism.LocalToGlobal.Columns.CoefModAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerMore
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.EtaPassage

theorem main : ∀ D : D7, KillingConditions.CommutingEndomorphismCondition D → TwistedPlaces.adm1 D := by
  intro D h i hi hl
  obtain ⟨α, hc, h1, h0⟩ := h i hi hl
  have hA : ((D.what₂.restRowsFiniteGroupCard : ℕ) : ℤ) ≠ 0 := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos.ne'
  have hP := Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D i (D.nd.Zgood i) (Formalism.L2.zgoodSub D i) α _ hA hc h1 h0
  rw [← Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.etaLoc_eq] at hP
  simp only [padicValInt.of_nat] at hP
  have hR := (Rat.cast_le (K := ℝ)).2 hP
  push_cast at hR
  simpa only [Nat.padicValNat_def] using hR

end GlobalTheory.EtaPassage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistAnnihilatesSelmerGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistAnnihilatesSelmerGroups
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem twist_kills_selmer : ∀ (D : D7) (C : NChoice D) (I : TwIn D) (ρ : FamilyRepresentationConstants.RhoFam D), NChTie D C → TwGoodAt D C I →
    KillingConditions.SignatureChoiceCondition ρ C → KillingConditions.KillAt ρ := by
  intro D C I ρ hT hG hA i hi
  have hw : D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0 := hi
  obtain ⟨-, hg⟩ := hG (D.nd.w i) hw
  obtain ⟨hA1, hA2⟩ := hA i hi
  obtain ⟨-, -, -, ⟨epsT, hT0, hTs, hTle⟩, -, hD⟩ := hg
  have hl : D.ntw.l (C.twI (D.nd.w i)) = D.nd.l i := by rw [← hT.twOf_eq]; exact D.ntw.twOf_l i
  have heps : twEps D (C.twI (D.nd.w i)) = Formalism.MainNotions.TwistedPlaces.epsL (D.nd.l i) := by
    rw [twEps, Formalism.MainNotions.TwistedPlaces.epsL, hl, one_div]
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, hs, hfin, hle⟩ := hA1 π hπ
    have h1 := hTle s hs
    have hsum : epsT s ≤ twEps D (C.twI (D.nd.w i)) :=
      le_trans (Finset.single_le_sum (fun s _ => hT0 s) ((Formalism.MainNotions.BlochKatoReduction.Gen.mem_SigG _ _ s).2 hs)) hTs
    have h0 : 0 ≤ (Formalism.MainNotions.BlochKatoReduction.Gen.nu D.ntw (C.twI (D.nd.w i)) : ℝ) + epsT s :=
      add_nonneg (Nat.cast_nonneg _) (hT0 s)
    have h2 := le_trans hle h1
    refine ⟨hfin (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1), ?_⟩
    rw [ENNReal.ofReal_le_ofReal_iff h0] at h2
    rw [← heps]
    rw [UpperTheory.KStar.nu_eq_nuL, hl] at h2
    linarith
  · rw [← heps]
    exact le_trans (mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg _)) hD

end GlobalTheory.NLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistAnnihilatesSelmerGroupsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenTwist_annihilates_selmerGroups : ∀ (D : D7) (C : NChoice D) (I : TwIn D) (ρ : FamilyRepresentationConstants.RhoFam D), NChTie D C → TwGoodAt D C I → KillingConditions.SignatureChoiceCondition ρ C → KillingConditions.KillAt ρ := by
  first | exact @GlobalTheory.NLink.twist_kills_selmer | exact GlobalTheory.NLink.twist_kills_selmer | (intros; apply GlobalTheory.NLink.twist_kills_selmer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoEALe
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowA

theorem two_eA_le {D : D7} (L : SizeData₂ D) {CA C : ℝ} (hCA : 0 ≤ CA) (hC : 2 * (3 * CA + 1) ≤ C)
    {l : ℕ} (hl : 5 ≤ l) : 2 * (eA L CA l : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eP L C l := by
  have h1 : 1 ≤ Formalism.MainNotions.TwistedPlaces.hB L := Formalism.MainNotions.TwistedPlaces.one_le_hB L
  set h := Formalism.MainNotions.TwistedPlaces.hB L with hh
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hl1 : (1 : ℝ) < l := by linarith
  set a : ℝ := ((hN L : ℕ) : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have haN : a ≤ h := Nat.floor_le (by linarith)
  have hlog1 : 0 ≤ Real.logb l (a + a + 1) := Real.logb_nonneg hl1 (by linarith)
  have hlh : 0 ≤ Real.logb l h := Real.logb_nonneg hl1 h1
  have hlog2 : Real.logb l (a + a + 1) ≤ 1 + Real.logb l h := by
    have hle : a + a + 1 ≤ l * h := by nlinarith
    calc Real.logb l (a + a + 1) ≤ Real.logb l (l * h) :=
          Real.logb_le_logb_of_le hl1 (by linarith) hle
      _ = 1 + Real.logb l h := by
          rw [Real.logb_mul hl0.ne' (by linarith), Real.logb_self_eq_one hl1]
  have hdiv : (a + a) / l ≤ 2 * (h / l) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hl0.le
  have hhl : 0 ≤ h / l := div_nonneg (by linarith) hl0.le
  have hY : 1 ≤ 1 + h / l + Real.logb l h := by linarith
  have hin : 1 + (a + a) / l + (1 + Real.logb l (a + a + 1)) ≤ 3 * (1 + h / l + Real.logb l h) := by
    linarith
  have hnn : 0 ≤ CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) := by
    apply mul_nonneg hCA
    have : 0 ≤ (a + a) / l := div_nonneg (by linarith) hl0.le
    linarith
  have hceil : (eA L CA l : ℝ) < CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) + 1 := by
    unfold eA
    push_cast
    exact Nat.ceil_lt_add_one hnn
  have harg : CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) ≤
      CA * (3 * (1 + h / l + Real.logb l h)) := mul_le_mul_of_nonneg_left hin hCA
  have hE : (eA L CA l : ℝ) ≤ (3 * CA + 1) * (1 + h / l + Real.logb l h) := by nlinarith
  unfold Formalism.MainNotions.TwistedPlaces.eP
  rw [← hh]
  nlinarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admA L (tabX L X) C := by
  intro D L P HW X R C hD hR i _htw hcond
  obtain ⟨h5, hsp, _, _⟩ := hcond
  obtain ⟨_, _, _, hCA, hC1, _, _, _, _, _, hCC⟩ := hR
  have hl0 : D.nd.l i ≠ 0 := by omega
  have hfin := FamilyRepresentationConstants.placesOver_finite D.host.E (D.nd.l i) hl0
  have he := two_eA_le L hCA hCC h5
  have heP : 0 ≤ Formalism.MainNotions.TwistedPlaces.eP L C (D.nd.l i) := Formalism.MainNotions.TwistedPlaces.eP_nonneg L (by linarith) _
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro lam _
  have hk : (0 : ℝ) ≤ 2 * (TwistedPlaces.nLam D lam : ℝ) * D.R.m + 1 := by positivity
  have hconst : (fun π => X.len0 i π lam) =
      fun _ => ((lenA i (X.dc i) (eA L R.CA (D.nd.l i)) lam : ℚ) : ℝ) := by
    funext π
    rw [hD.len0S i hsp π lam, hD.eS i hsp]
  show 2 * KillingConditions.supZ i (fun π => X.len0 i π lam) ≤ _
  rw [hconst]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenA
    split_ifs
    · push_cast
      have : (TwistedPlaces.nLam D lam : ℝ) = (locDeg D.host.E lam : ℝ) := rfl
      rw [← this]
      nlinarith
    · push_cast; nlinarith
  · nlinarith

end GlobalTheory.NLink.RowA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolyValLeSumMulPow
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem polyVal_le_sum_mul_pow (Q : MvPolynomial (Fin 3) ℕ) (f r t : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    EmbeddingTypeJumps.polyVal Q f r t ≤ (∑ m ∈ Q.support, Q.coeff m) * (f * r * t) ^ Q.totalDegree := by
  unfold EmbeddingTypeJumps.polyVal
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  refine Nat.mul_le_mul_left _ ?_
  have hM : ∀ i : Fin 3, (![f, r, t] : Fin 3 → ℕ) i ≤ f * r * t := by
    intro i
    fin_cases i
    · show f ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul (le_refl f) hr) ht
    · show r ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf (le_refl r)) ht
    · show t ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf hr) (le_refl t)
  have hpos : 0 < f * r * t := by positivity
  calc ∏ i, (![f, r, t] : Fin 3 → ℕ) i ^ m i ≤ ∏ i : Fin 3, (f * r * t) ^ m i :=
        Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hM i) _
    _ = (f * r * t) ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (f * r * t) ^ Q.totalDegree := by
        apply Nat.pow_le_pow_right hpos
        have := MvPolynomial.le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ (by simp)] at this

theorem starG_of_thmB : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (constantFirstHub C : ℝ)
    (Q : MvPolynomial (Fin 3) ℕ), FamilyRepresentationConstants.CG constantFirstHub Q ≤ C → EmbeddingTypeJumps.Conclusion2 ρ L constantFirstHub Q → KillingConditions.KillAt ρ →
    TwistedPlaces.ShaFinOdd D → StarG L ρ C := by
  intro D L P ρ constantFirstHub C Q hCG hB hK hSha
  unfold StarG
  intro i hi hl π hπ
  unfold Bd
  unfold FamilyRepresentationConstants.CG at hCG
  have hC67 : constantFirstHub ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCG
  have hS : ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCG
  have hdeg : (Q.totalDegree : ℝ) ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCG
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCG

  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by
    unfold Ranks.r
    have := D.R.m_add_three_le_k
    omega
  have hf1 : 1 ≤ D.R.f := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have htr : 1 ≤ D.R.t * D.R.r := by simpa using Nat.mul_le_mul ht1 hr1

  have hlp : (D.nd.l i).Prime := by
    rcases hl with h | h <;> rw [h]
    exacts [D.host.hyp.1, D.host.hyp.2.1]
  have hl2 : 2 < D.nd.l i := by
    have hqd := D.host.qd_big
    rcases hl with h | h <;> rw [h] <;> nlinarith [hqd.1, hqd.2]
  have hodd : Odd (D.nd.l i) := hlp.odd_of_ne_two (by omega)
  have hlbig : L.sc.x ^ (2 * L.Ct + 5) < (D.nd.l i : ℝ) := by
    rcases hl with h | h <;> rw [h]
    exacts [P.qd_pow.1, P.qd_pow.2]
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    haveI : Fact (D.nd.l i).Prime := ⟨hlp⟩
    exact lt_top_iff_ne_top.2 (hSha (D.nd.l i) e he.1 he.2)
  have hK' := (hK i hi).1 π hπ
  have h := hB i hl hi hlbig π hπ hK'.1 hsha

  have hVV : TwistedPlaces.VVr D (D.nd.l i) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    show ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) = _
    congr 2
  have hvh : TwistedPlaces.vhE D (D.nd.l i) = (padicValNat (D.nd.l i) (hE D.host) : ℝ) := rfl
  have heps : TwistedPlaces.epsL (D.nd.l i) = EmbeddingTypeJumps.epsL (D.nd.l i) := by
    unfold TwistedPlaces.epsL EmbeddingTypeJumps.epsL
    rw [one_div]

  have hLpos : 0 < TwistedPlaces.large₂ L := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  have hlog : Real.log L.sc.b = TwistedPlaces.large₂ L := Real.log_exp _
  have hbpos : 0 < L.sc.b := Real.exp_pos _
  have hlpos : (0 : ℝ) < D.nd.l i := by exact_mod_cast hlp.pos
  have hbr : 0 ≤ (D.R.r : ℝ) * (L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L) +
      D.R.m * L.sc.b := by
    have h1 := L.Sc_pos
    have h2 := L.etaSz_pos
    have h3 : 0 ≤ L.sc.b / (D.nd.l i) := div_nonneg hbpos.le hlpos.le
    have h4 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have h5 : 0 ≤ L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L := by linarith
    positivity
  have hM1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.t := by exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul hf1 hr1) ht1
  have hpoly : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤ C * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
    have h1 : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤
        ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree := by
      exact_mod_cast polyVal_le_sum_mul_pow Q _ _ _ hf1 hr1 ht1
    have hpow : ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree ≤ ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hM1 hdeg
    exact h1.trans (mul_le_mul hS hpow (by positivity) (by linarith))
  have hbnd : EmbeddingTypeJumps.bndB D L constantFirstHub Q (D.nd.l i) ≤ TwistedPlaces.midG L C (D.nd.l i) := by
    unfold EmbeddingTypeJumps.bndB TwistedPlaces.midG
    rw [hlog]
    have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC67 (Nat.cast_nonneg D.R.f)) hbr
    have e2 := mul_le_mul_of_nonneg_right hpoly hLpos.le
    linarith
  rw [hVV, hvh, heps]
  linarith

end GlobalTheory.NLink

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableFromDataBandCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableFromDataBandCondition
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NBand

theorem prime_eq_of_mem {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {w : HeightOneSpectrum (𝓞 E)} (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    p = q := by
  by_contra hne
  have hc : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h1) (w.asIdeal.mul_mem_left b h2)

theorem logb_le_of_le_four_exp {l : ℕ} (hl : (11 : ℝ) ≤ l) {large₂ h : ℝ} (hL : 1 ≤ large₂) (h0 : 0 ≤ h)
    (hh : h ≤ 4 * Real.exp large₂) : Real.logb l h ≤ large₂ := by
  have hl1 : (1 : ℝ) < l := by linarith
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hloge : Real.log 4 + 1 ≤ Real.log l := by
    have he := Real.exp_one_lt_d9
    have : Real.log (4 * Real.exp 1) = Real.log 4 + 1 := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
    rw [← this]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlpos : 0 < Real.log l := Real.log_pos hl1
  rcases h0.eq_or_lt with h0' | h0'
  · rw [← h0', Real.logb_zero]; linarith
  have h1 : Real.logb l h ≤ Real.logb l (4 * Real.exp large₂) := Real.logb_le_logb_of_le hl1 h0' hh
  refine h1.trans ?_
  rw [Real.logb, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, div_le_iff₀ hlpos]
  nlinarith

theorem band_arith {lr s z Wb Lb e S Sc eta₃ lg large₂ T CB C : ℝ} (hl : 11 ≤ lr) (hs0 : 0 ≤ s)
    (hzs : |z - s| ≤ T) (hb1 : Lb - T ≤ Wb) (hb2 : Wb ≤ Lb - T + 1) (he : e ≤ eta₃) (hS : S ≤ Sc)
    (hlg : lg ≤ large₂) (hLg : 1 ≤ large₂) (hSc : 0 ≤ Sc) (hLb : 0 ≤ Lb) (hT : 1 / 2 ≤ T) (hTe : 2 * T + 1 ≤ eta₃)
    (hCB : 0 ≤ CB) (hC : 6 * CB + 1 ≤ C)
    (habs : |lr * z - Wb| ≤ CB * (lr * e + lr * S + Wb / lr + z + lr * lg)) :
    |lr * s - Lb| ≤ C * (lr * eta₃ + lr * Sc + Lb / lr + s + lr * large₂) := by
  set E := lr * eta₃ + lr * Sc + Lb / lr + s + lr * large₂ with hE
  have hlr0 : 0 < lr := by linarith
  rw [abs_le] at hzs habs
  have hA : lr * e + lr * S + Wb / lr + z + lr * lg ≤ E + lr * eta₃ := by
    have e1 : lr * e ≤ lr * eta₃ := mul_le_mul_of_nonneg_left he hlr0.le
    have e2 : lr * S ≤ lr * Sc := mul_le_mul_of_nonneg_left hS hlr0.le
    have e3 : Wb / lr ≤ Lb / lr + 1 / lr := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hlr0.le
    have e3' : 1 / lr ≤ 1 := by rw [div_le_one hlr0]; linarith
    have e5 : lr * lg ≤ lr * large₂ := mul_le_mul_of_nonneg_left hlg hlr0.le
    have e6 : eta₃ ≤ lr * eta₃ := by nlinarith
    rw [hE]; linarith
  have hEge : lr * eta₃ ≤ E := by
    have : 0 ≤ Lb / lr := div_nonneg hLb hlr0.le
    have : 0 ≤ lr * Sc := mul_nonneg hlr0.le hSc
    have : 0 ≤ lr * large₂ := mul_nonneg hlr0.le (by linarith)
    rw [hE]; linarith
  have hEt0 : 0 ≤ lr * eta₃ := mul_nonneg hlr0.le (by linarith)
  have hx1 : lr * T + T ≤ lr * eta₃ := by nlinarith
  have hCBA : CB * (lr * e + lr * S + Wb / lr + z + lr * lg) ≤ CB * (E + lr * eta₃) :=
    mul_le_mul_of_nonneg_left hA hCB
  have hCE : (2 * CB + 1) * E ≤ C * E := mul_le_mul_of_nonneg_right (by linarith) (hEt0.trans hEge)
  have hm1 : lr * (s - z) ≤ lr * T := mul_le_mul_of_nonneg_left (by linarith) hlr0.le
  have hm2 : -(lr * T) ≤ lr * (s - z) := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (by linarith) hlr0.le
  have hCBE : CB * (lr * eta₃) ≤ CB * E := mul_le_mul_of_nonneg_left hEge hCB
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.NBand

theorem GlobalTheory.NBand.bandPlaceWeightApproximation_tabX : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → TwistedPlaces.BandPlaceWeightApproximation L (tabX L X) C := by
  intro D L P HW X R C hX hR hpar
  intro i lam hTw hb l hl hlp
  obtain ⟨h11, π, hπ, hw, Cx, hG, Wd, hBase, hBox, hNT, hBand⟩ := (hX.band i lam).1 hb
  have hli : l = D.nd.l i := prime_eq_of_mem hlp (D.nd.lPrime i).out hl hw
  subst hli
  obtain ⟨a, hnt, -, habs⟩ := hBand
  obtain ⟨s, hs1, hs2, hs3⟩ := hBox.nt a hnt
  refine ⟨s, hs1, hs2, ?_⟩
  obtain ⟨-, hCB, -, -, -, -, -, -, -, hC6, -⟩ := hR
  have hl11 : (11 : ℝ) ≤ (D.nd.l i : ℝ) := by exact_mod_cast h11
  have hLg : 1 ≤ TwistedPlaces.large₂ L := by
    unfold TwistedPlaces.large₂ Scale.L
    exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hbexp : L.sc.b = Real.exp (TwistedPlaces.large₂ L) := rfl
  have hpar' : L.Sc + L.etaSz + (D.R.t : ℝ) + 2 ≤ L.sc.b := hpar
  have hSc := L.Sc_pos
  have hEt := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hetaP : TwistedPlaces.eta₃ L = L.etaSz + D.R.t + 2 := rfl
  have hhB : TwistedPlaces.hB L = L.sc.b + L.Sc + L.etaSz + D.R.t + 2 := rfl
  have hh17n : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz ≤ Wd.b + Wd.η + Wd.S := by
    have := hNT.w20
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; split_ifs <;> omega
  have hh17 : ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ) ≤ (Wd.b : ℝ) + Wd.η + Wd.S := by
    exact_mod_cast hh17n
  have hhle := hBase.h_le
  have hlg : Real.logb (D.nd.l i : ℝ) (2 * ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ)) ≤ TwistedPlaces.large₂ L := by
    apply logb_le_of_le_four_exp hl11 hLg (by positivity)
    rw [← hbexp]; linarith
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
    unfold Scale.w'' Scale.b' Scale.a Scale.X' Scale.b
    apply div_nonneg
    · exact div_nonneg (mul_nonneg hx.le (Real.exp_pos _).le) (Real.exp_pos _).le
    · exact mul_nonneg hx.le (Nat.cast_nonneg _)
  exact band_arith hl11 (hw0.trans hs1) hs3 hBox.b_lo hBox.b_hi hBase.η_le hBase.S_le hlg hLg hSc.le
    (by rw [hbexp]; exact (Real.exp_pos _).le) (by linarith) (by rw [hetaP]; linarith) hCB hC6 habs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableFromDataBandConditionStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableFromData_bandCondition : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → TwistedPlaces.BandPlaceWeightApproximation L (tabX L X) C := by
  first | exact @GlobalTheory.NBand.bandPlaceWeightApproximation_tabX | exact GlobalTheory.NBand.bandPlaceWeightApproximation_tabX | (intros; apply GlobalTheory.NBand.bandPlaceWeightApproximation_tabX <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem mat_mul {Γ k : Type} [Group Γ] [CommRing k] {r : ℕ} (σ : Γ →* GL (Fin r) k) (g h : Γ) :
    mat σ g * mat σ h = mat σ (g * h) := by
  simp [mat]

theorem span_eq_top_of_trace_eq {Γ k : Type} [Group Γ] [Field k] {r : ℕ}
    (σ ρ : Γ →* GL (Fin r) k) (ht : ∀ g, (mat σ g).trace = (mat ρ g).trace)
    (h : Submodule.span k (Set.range (mat ρ)) = ⊤) :
    Submodule.span k (Set.range (mat σ)) = ⊤ := by
  classical
  let L := Finsupp.linearCombination k (mat σ)
  let L0 := Finsupp.linearCombination k (mat ρ)
  have hker : LinearMap.ker L ≤ LinearMap.ker L0 := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have h1 : ∀ y : Γ, (L0 c * mat ρ y).trace = 0 := by
      intro y
      have e1 : (L c * mat σ y).trace = 0 := by rw [hc]; simp
      rw [← e1]
      simp only [L, L0, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul, Matrix.smul_mul,
        Matrix.trace_sum, Matrix.trace_smul, mat_mul, ht]
    have h2 : ∀ Y : Matrix (Fin r) (Fin r) k, (L0 c * Y).trace = 0 := by
      intro Y
      have hY : Y ∈ Submodule.span k (Set.range (mat ρ)) := h ▸ Submodule.mem_top
      induction hY using Submodule.span_induction with
      | mem Y hY => obtain ⟨y, rfl⟩ := hY; exact h1 y
      | zero => simp
      | add Y Z _ _ hY hZ => rw [Matrix.mul_add, Matrix.trace_add, hY, hZ, add_zero]
      | smul a Y _ hY => rw [Matrix.mul_smul, Matrix.trace_smul, hY, smul_zero]
    ext p q
    have := h2 (Matrix.single q p 1)
    simpa [Matrix.trace_mul_single] using this
  have hL0 : LinearMap.range L0 = ⊤ := by
    rw [Finsupp.range_linearCombination]; exact h
  let f : LinearMap.range L →ₗ[k] Matrix (Fin r) (Fin r) k :=
    ((LinearMap.ker L).liftQ L0 hker).comp (L.quotKerEquivRange.symm : LinearMap.range L →ₗ[k] _)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_liftQ, hL0]
  have h3 := LinearMap.finrank_range_le f
  rw [hf, finrank_top] at h3
  have h4 : LinearMap.range L = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h3)
  rw [← Finsupp.range_linearCombination]; exact h4

theorem absIrrSub_of_span_eq_top {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (hr : 0 < r)
    (σ : Γ →* GL (Fin r) k) (h : Submodule.span k (Set.range (mat σ)) = ⊤) : AbsIrrSub σ ⊤ := by
  refine GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (algebraMap k (AlgebraicClosure k)) hr σ fun W hW => ?_
  refine GlobalTheory.BurnsideIff.eq_bot_or_top_of_span_eq_top (mat σ) h W fun g x hx => ?_
  have e : (mat σ g).map (algebraMap k (AlgebraicClosure k)) =
      ((mapRep (algebraMap k (AlgebraicClosure k)) σ g : GL (Fin r) (AlgebraicClosure k)) :
        Matrix (Fin r) (Fin r) (AlgebraicClosure k)) := by
    ext p q; simp [mat, mapRep]
  rw [e]; exact hW g x hx

theorem pos_of_absIrrSub {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (σ : Γ →* GL (Fin r) k)
    (h : AbsIrrSub σ ⊤) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    exact absurd (Subsingleton.elim _ _) h.1
  · exact h0

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem mat_mapRep {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {k : ℕ} (f : A →+* B)
    (σ : Γ →* GL (Fin k) A) (g : Γ) : mat (mapRep f σ) g = (mat σ g).map f := by
  ext p q; simp [mat, mapRep]

theorem charpoly_eq_of_isHeckeGalois (hC : GlobalTheory.TwSys.Cheb) (D : D7) (i : D.nd.Loc)
    (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i rep) (π : D.nd.X i)
    (r0 : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (hr0 : IsHeckeGalois D.nd i π r0) (g : GE D.nd) :
    (mat (rep π) g).charpoly = (mat r0 g).charpoly := by
  classical
  let rep' := Function.update rep π r0
  have hr' : GoodR D.nd i rep' := by
    intro y
    by_cases hy : y = π
    · subst hy; simpa [rep'] using hr0
    · simpa [rep', Function.update_of_ne hy] using hr y
  obtain ⟨Pm, hPm⟩ := GlobalTheory.PointRepConj.main hC D.nd i rep rep' hr hr' π
  have h1 := hPm g
  have h2 : (rO D.nd i rep' π g) = mat r0 g := by simp [rep', rO, mat]
  rw [h2] at h1
  apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
  have h1' : (Pm : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (mat (rep π) g).map (toK D.nd i) =
      (mat r0 g).map (toK D.nd i) * (Pm : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := h1
  have h3 : (mat (rep π) g).map (toK D.nd i) =
      ((Pm⁻¹ : GL (Fin D.R.nV) (KK D.nd i)) : Matrix _ _ _) * (mat r0 g).map (toK D.nd i) *
        (Pm : Matrix _ _ _) := by
    rw [Matrix.mul_assoc, ← h1', ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  rw [h3]
  have := Matrix.charpoly_units_conj (Pm⁻¹) ((mat r0 g).map (toK D.nd i))
  rwa [← Matrix.coe_units_inv, inv_inv] at this

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeLAdicCharacterAboveOfPublished
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published

namespace GlobalTheory.HeckeAboveBridge

theorem heckeLAdicCharacterAbove_of_potSemistable :
    HeckeLAdicCharacterDeRham → HeckeLAdicCharacterCrystalline → DeRhamPotSemistable →
      HeckeLAdicCharacterAbove := by
  intro hdR hcr hpst
  rw [heckeLAdicCharacterAbove_iff]
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hl w A hA O _ _ _ Bw hB
  have h1 := hdR E Ω l P AI hT ι art hart χ n μ hχ hμ hl w A hA O Bw hB
  exact ⟨h1.1, GlobalTheory.PotCrysRankOne.isPotCrystalline_of_deRham_character hpst E Ω l P AI hT μ hμ A O Bw hB h1.1,
    hcr E Ω l P AI hT ι art hart χ n μ hχ hμ hl w A hA O Bw hB, h1.2⟩

end GlobalTheory.HeckeAboveBridge

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHermNDInvTranspose
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus.Row

theorem transpose_unitary {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) {J K g : Matrix n n A} (hKJ : K * J = 1)
    (hg : Formalism.UG.cT s g * J * g = J) : Formalism.UG.cT s gᵀ * Kᵀ * gᵀ = Kᵀ := by
  have hJK : J * K = 1 := mul_eq_one_comm.1 hKJ
  have h1 : (K * Formalism.UG.cT s g * J) * g = 1 := by
    rw [Matrix.mul_assoc K, Matrix.mul_assoc K, hg, hKJ]
  have h2 : g * (K * Formalism.UG.cT s g * J) = 1 := mul_eq_one_comm.1 h1
  have h3 : g * (K * Formalism.UG.cT s g) = K := by
    calc g * (K * Formalism.UG.cT s g) = g * (K * Formalism.UG.cT s g) * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = g * (K * Formalism.UG.cT s g * J) * K := by simp only [Matrix.mul_assoc]
      _ = K := by rw [h2, Matrix.one_mul]
  have h4 := congrArg Matrix.transpose h3
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at h4
  exact h4

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_inv_transpose {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) : IsHermND σ (J⁻¹)ᵀ := by
  have hu : IsUnit J.det := hJ.2.isUnit
  have hm : J.map (σ : E →+* E) = Jᵀ := by
    ext i j
    exact hJ.1 j i
  have h1 : (J⁻¹).map (σ : E →+* E) * Jᵀ = 1 := by
    rw [← hm, ← Matrix.map_mul, Matrix.nonsing_inv_mul J hu]
    simp
  have h2 : (Jᵀ)⁻¹ = (J⁻¹).map (σ : E →+* E) := Matrix.inv_eq_left_inv h1
  refine ⟨fun i j => ?_, ?_⟩
  · have h3 := congrFun (congrFun h2 i) j
    rw [← Matrix.transpose_nonsing_inv] at h3
    exact h3.symm
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det J hu).ne_zero

def transposeGL {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (g : GL n A) : GL n A :=
  ⟨g.1ᵀ, (g⁻¹).1ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem exists_transpose (R : Type) [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (g : HA R σ J) :
    ∃ g' : HA R σ (J⁻¹)ᵀ, (HA.mat R σ (J⁻¹)ᵀ g').1 = ((HA.mat R σ J g).1)ᵀ := by
  have hu : IsUnit J.det := hJ.2.isUnit
  have hKJ : JR (F := F) R J⁻¹ * JR (F := F) R J = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J hu]
    simp
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).1 * JR (F := F) R J * (HA.mat R σ J g).1 =
      JR (F := F) R J := (show HR R σ J from g).2
  exact ⟨(⟨transposeGL (HA.mat R σ J g), transpose_unitary (sigR R σ) hKJ hg⟩ : HR R σ (J⁻¹)ᵀ), rfl⟩

theorem map_vecMul_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : HA (AF F) σ J) (μ : Measure (Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → μ.map (fun x => Matrix.vecMul x ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) = μ := by
  intro F E _ _ _ _ _ σ hσ M J hJ g μ hμ
  obtain ⟨g', hg'⟩ := exists_transpose (AF F) hJ g
  have h := PI.VolSemiDirect.W.Cj.unipotent_modulus_holds F E σ hσ M _ (isHermND_inv_transpose hJ) g' μ hμ
  have e : (fun x => Matrix.vecMul x ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) =
      fun x => ((HA.mat (AF F) σ (J⁻¹)ᵀ g').1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).mulVec x := by
    funext x
    rw [hg', Matrix.mulVec_transpose]
  rw [e]
  exact h

end GlobalTheory.AdelicModulus.Row
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
open NumberField

noncomputable section

namespace GlobalTheory.NabScale

open MvPolynomial IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def IntAt (w : HeightOneSpectrum (𝓞 K)) (m : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix (Fin n) (Fin n) (𝓞 K),
    A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • m

theorem IntAt.det {w : HeightOneSpectrum (𝓞 K)} {m : Matrix (Fin n) (Fin n) K} (h : IntAt w m) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * m.det := by
  obtain ⟨t, ht, A, hA⟩ := h
  refine ⟨t ^ n, Submonoid.pow_mem _ ht n, A.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_smul, map_pow]
  simp

theorem detPow_scaled (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (c : K)
    (hc : IntAt w (c • (g : Matrix (Fin n) (Fin n) K)))
    (hc' : IntAt w (c • ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) (e : ℤ) :
    ∃ u ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K u * (c ^ (n * e.natAbs) * detPow K n g e) := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · obtain ⟨t, ht, y, hy⟩ := hc.det
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_natCast, detPow, zpow_natCast, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.val_det_apply]
    simp only [Fintype.card_fin]
    ring
  · obtain ⟨t, ht, y, hy⟩ := hc'.det
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_neg, Int.natAbs_natCast, detPow, zpow_neg, zpow_natCast,
      ← inv_pow, Units.val_pow_eq_pow_val, ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    simp only [Fintype.card_fin]
    ring

theorem sqAct_scaled (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (c : K)
    (hc : IntAt w (c • (g : Matrix (Fin n) (Fin n) K)))
    (hc' : IntAt w (c • ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) K) (hf : f ∈ (nablaSq (𝓞 K) n lam).map (toK K _)) :
    ∃ s ∈ w.asIdeal.primeCompl,
      algebraMap (𝓞 K) K s • (c ^ (∑ j, lam.natW j + n * lam.detShift.natAbs) • sqAct K n lam g f) ∈
        (nablaSq (𝓞 K) n lam).map (toK K _) := by
  obtain ⟨f, hf, rfl⟩ := hf
  obtain ⟨t, ht, A, hA⟩ := hc
  obtain ⟨u, hu, y, hy⟩ := detPow_scaled w g c ⟨t, ht, A, hA⟩ hc' lam.detShift
  refine ⟨u * t ^ (∑ j, lam.natW j), Submonoid.mul_mem _ hu (Submonoid.pow_mem _ ht _),
    y • Formalism.GradedWeylDivisibility.rowAct (𝓞 K) Aᵀ f,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable (𝓞 K) n n _ _ f hf), ?_⟩
  have hK : map (algebraMap (𝓞 K) K) f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n lam.natW :=
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ f hf
  have hT : Aᵀ.map (algebraMap (𝓞 K) K) = (algebraMap (𝓞 K) K t * c) • (g : Matrix (Fin n) (Fin n) K)ᵀ := by
    rw [Matrix.transpose_map, hA, Matrix.transpose_smul, Matrix.transpose_smul, smul_smul]
  rw [map_smul, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.map_rowAct, hT,
    GlobalTheory.NabStab.rowAct_smul _ _ _ hK.1, sqAct, ← IsScalarTower.algebraMap_smul K y, hy, smul_smul, smul_smul, smul_smul,
    map_mul, map_pow]
  congr 1
  ring

def scaleExp {ι : Type} [Fintype ι] (lam : ι → DomWeight n) : ℕ :=
  ∑ τ, (∑ j, (lam τ).natW j + n * (lam τ).detShift.natAbs)

theorem polyAction_scaled_mem_locP_nabStd {ι : Type} [Fintype ι] (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K) (c : K)
    (hc : ∀ τ, IntAt w (c • ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hc' : ∀ τ, IntAt w (c • (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam),
      c ^ scaleExp lam • actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have key : ∀ F ∈ nabStd K lam, c ^ scaleExp lam • actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
    intro F hF
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      choose s hs hs' using fun τ => sqAct_scaled w (g τ) c (hc τ) (hc' τ) (lam τ) (f τ) (hf τ)
      refine ⟨∏ τ, s τ, Submonoid.prod_mem _ fun τ _ => hs τ, Submodule.subset_span ⟨_, hs', ?_⟩⟩
      have h1 := actTen K ι n lam g f
      unfold ten at h1
      rw [h1, ← IsScalarTower.algebraMap_smul K, map_prod, scaleExp, ← Finset.prod_pow_eq_pow_sum, smul_smul,
        ← Finset.prod_mul_distrib]
      simp only [map_smul, smul_smul]
      rw [Finset.prod_smul]
    | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [LinearMap.map_smul_of_tower, smul_comm]
      exact Submodule.smul_mem _ _ hx
  rintro F ⟨s, hs, hF⟩
  obtain ⟨t, ht, h2⟩ := key _ hF
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [LinearMap.map_smul_of_tower] at h2
  rw [mul_smul, smul_comm s (c ^ scaleExp lam)]
  exact h2

theorem intAt_of_cols (w : HeightOneSpectrum (𝓞 K)) (m : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, ∃ t ∈ w.asIdeal.primeCompl, ∀ a, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * m a j) :
    IntAt w m := by
  classical
  choose s hs hs' using h
  have h2 : ∀ a j : Fin n, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K (∏ i, s i) * m a j := by
    intro a j
    obtain ⟨y, hy⟩ := hs' j a
    refine ⟨(∏ i ∈ Finset.univ.erase j, s i) * y, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, map_mul, hy, mul_assoc]
  choose A hA using h2
  refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, Matrix.of A, ?_⟩
  ext a j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hA]

theorem intAt_transition (w : HeightOneSpectrum (𝓞 K)) {L L' : Submodule (𝓞 K) (Fin n → K)} {B B' : GL (Fin n) K}
    (hB : IsBasisAt w L B) (hB' : IsBasisAt w L' B') (c : K) (h : ∀ x ∈ L, c • x ∈ L') :
    IntAt w (c • ((B'⁻¹ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  apply intAt_of_cols
  intro j
  have h1 : (fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
    unfold IsBasisAt at hB
    rw [hB]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  obtain ⟨s, hs, hx⟩ := h1
  have h2 : c • (s • fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B') := by
    unfold IsBasisAt at hB'
    rw [← hB']
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact h _ hx⟩
  obtain ⟨s', hs', hx'⟩ := h2
  have h3 : colLat B' = gLat B' (colLat 1) := by rw [← colLat_mul, mul_one]
  rw [h3] at hx'
  obtain ⟨z, hz, hzx⟩ := hx'
  refine ⟨s' * s, Submonoid.mul_mem _ hs' hs, fun a => ?_⟩
  obtain ⟨y, hy⟩ := GlobalTheory.NabStab.int_of_mem_colLat_one hz a
  refine ⟨y, ?_⟩
  have hz' : z = ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j) := by
    have hzx' : (B' : Matrix (Fin n) (Fin n) K) *ᵥ z = s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j := hzx
    rw [← hzx', Matrix.mulVec_mulVec]
    simp
  rw [hy, hz']
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Units.val_mul, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

section ESide

variable {E : Type} [Field E] [NumberField E] {ι : Type}

theorem tauLat_smul_mem (emb : ι → E →+* K) (τ : ι) {M M' : Submodule (𝓞 E) (Fin n → E)} (N : ℕ)
    (h : ∀ x ∈ M, (N : 𝓞 E) • x ∈ M') : ∀ x ∈ tauLat emb τ M, (N : 𝓞 K) • x ∈ tauLat emb τ M' := by
  intro x hx
  unfold tauLat at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    refine Submodule.subset_span ⟨(N : 𝓞 E) • m, h m hm, ?_⟩
    funext a
    simp [Algebra.smul_def]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem dualFr_tauLat_smul_mem (emb : ι → E →+* K) (τ : ι) {M M' : Submodule (𝓞 E) (Fin n → E)} (N : ℕ)
    (h : ∀ x ∈ M', (N : 𝓞 E) • x ∈ M) :
    ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M') := by
  intro φ hφ x hx
  have h1 := hφ _ (tauLat_smul_mem emb τ N h x hx)
  show ((N : K) • φ) ⬝ᵥ x ∈ _
  rw [smul_dotProduct]
  rw [dotProduct_smul] at h1
  convert h1 using 1
  simp [Algebra.smul_def]

end ESide

theorem nabAtr_smul_pow_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ),
    N ≠ 0 → Submodule.IsFullLattice E M → Submodule.IsFullLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') →
    (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) →
    ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  intro E K _ _ _ _ ι _ n emb lam M M' N _ hM _ h1 h2
  refine ⟨scaleExp lam, fun F hF => ?_⟩
  have hL : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat emb τ M)) := fun τ => dualFr_tauLat_isLattice emb τ M hM
  have hLL' : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M') :=
    fun τ => dualFr_tauLat_smul_mem emb τ N h2
  have hL'L : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M'), (N : K) • φ ∈ dualFr (tauLat emb τ M) :=
    fun τ => dualFr_tauLat_smul_mem emb τ N h1
  unfold nabAtr nabK at hF ⊢
  rw [Submodule.mem_comap] at hF ⊢
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype] at hF ⊢
  intro w B' hB'
  choose B hB using fun τ => basisAtEx K n _ (hL τ) w
  have hF' := hF w B hB
  have e : B'⁻¹ = (B'⁻¹ * B) * B⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [SetLike.val_smul, map_smul, e, polyAction_mul]
  refine polyAction_scaled_mem_locP_nabStd lam w (B'⁻¹ * B) (N : K) (fun τ => ?_) (fun τ => ?_) _ hF'
  · exact intAt_transition w (hB τ) (hB' τ) (N : K) (hLL' τ)
  · have h3 : ((B'⁻¹ * B) τ)⁻¹ = (B τ)⁻¹ * B' τ := by simp [mul_inv_rev]
    rw [h3]
    exact intAt_transition w (hB' τ) (hB τ) (N : K) (hL'L τ)

end GlobalTheory.NabScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMemStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → Submodule.IsFullLattice E M → Submodule.IsFullLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') → (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) → ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  first
  | exact @GlobalTheory.NabScale.nabAtr_smul_pow_mem
  | intro E K _ _ _ _ ι _ n emb lam M M' N hN hM hM' h1 h2
    exact GlobalTheory.NabScale.nabAtr_smul_pow_mem E K ι n emb lam M M' N hN
      hM.toIsLattice hM'.toIsLattice h1 h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulUnramifiedEqWittBcris
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulUnramifiedEqWittBcris
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.TeichmullerPowerUnit

theorem exists_pow_mul_u_eq_aB : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) ∈ K.1 → ∃ (n : ℕ) (w : Wq l bk.a), (l : Per.Bcris l) ^ n * C.u c = Per.aB l (wA l bk.a w) := by
  intro l _ K bk C c hc
  obtain ⟨n, w, hw⟩ := GlobalTheory.T.exists_prime_pow_mul_eq_theta_witt l K bk (c : Om l) hc c.2
  have ho := GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus l bk.a C w ((l : Om l) ^ n * (c : Om l)) hw
  refine ⟨n, w, ?_⟩
  apply GlobalTheory.Published.FontaineBcris.iotaInj GlobalTheory.T.fontaineBcrisBasicTheorems_proof C
  have hB : C.ι (Per.aB l (wA l bk.a w)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (wA l bk.a w)) :=
    GlobalTheory.MemLoc.ULaws.iota_aB C (wA l bk.a w)
  rw [hB, ← ho, map_mul, map_pow, map_natCast, C.ι_u, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]

end GlobalTheory.TeichmullerPowerUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulUnramifiedEqWittBcrisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_unramified_eq_witt_bcris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) ∈ K.1 → ∃ (n : ℕ) (w : Wq l bk.a), (l : Per.Bcris l) ^ n * C.u c = Per.aB l (wA l bk.a w) := by
  first | exact @GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB | exact GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB | (intros; apply GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB <;> assumption)
end
end
