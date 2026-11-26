module

public import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
public import Formalism.GaussJetBounds.GaussJetProofs.PureCrossTermWeight
public import Formalism.GaussJetBounds.GaussJetProofs.SwappedParitySeriesBinomialForm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan
public import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffEvenDerivativeEqZero

@[expose] public section

section -- merged from Formalism.GaussJetBounds.GaussJetProofs.LogStep
noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff)

theorem padicValNat_factorial_le_sub_one_div {l : ℕ} (hl : l.Prime) {k : ℕ} (hk : k ≠ 0) :
    (padicValNat l k.factorial : ℝ) ≤ ((k : ℝ) - 1) * (1 / ((l : ℝ) - 1)) := by
  have := Fact.mk hl
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l hk
  have hl2 := hl.two_le
  have h1 : (l - 1) * padicValNat l k.factorial ≤ k - 1 := by
    rw [Nat.padicValNat_def]
    omega
  have h2 : (((l - 1) * padicValNat l k.factorial : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hk),
    Nat.cast_one] at h2
  have hpos : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
    linarith
  rw [mul_one_div, le_div_iff₀ hpos, mul_comm]
  exact h2

theorem norm_coeff_exp {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ}
    (hl : l.Prime) (hπ : ‖(l : K)‖ < 1) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.exp K)‖ = (‖(l : K)‖ ^ padicValNat l k.factorial)⁻¹ := by
  rw [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, norm_div, norm_one, one_div,
    Formalism.LT.ExpP.norm_natCast_eq hl hπ (Nat.factorial_ne_zero k)]

theorem logarithm_weight_induction : LogStep.{u, v} := by
  intro K _ _ _ l hl hπ ι r D hD0 hE
  classical
  have hπ0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have hπ1 : ‖(l : K)‖ ≤ 1 := hπ.le
  have hD1 : Low 1 D := (low_one_iff _).2 hD0
  have hs : PowerSeries.HasSubst D := PowerSeries.HasSubst.of_constantCoeff_zero hD0
  suffices H : ∀ N, ∀ n : ι →₀ ℕ, n.degree = N →
      MonoWtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) n (coeff n D) from fun n => H _ n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hn
  by_cases hn0 : n = 0
  · subst hn0
    rw [monoWtGe_iff, coeff_zero_eq_constantCoeff_apply, hD0, norm_zero]
    exact Real.rpow_nonneg hπ0.le _
  have hTw : WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (truncBelow N D) := by
    intro m
    rw [monoWtGe_iff, coeff_truncBelow]
    split_ifs with hm
    · exact ih _ hm m rfl
    · simpa using Real.rpow_nonneg hπ0.le _
  have hlow : Low N (D - truncBelow N D) := by
    intro m hm
    rw [map_sub, coeff_truncBelow, if_pos hm, sub_self]
  have hT1 : Low 1 (truncBelow N D) := by
    intro m hm
    rw [coeff_truncBelow]
    split_ifs
    · exact hD1 m hm
    · rfl
  have hpow : ∀ k, Low (N + k) (D ^ (k + 1) - truncBelow N D ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hlow
    | succ k ihk =>
      have e : D ^ (k + 1 + 1) - truncBelow N D ^ (k + 1 + 1) =
          (D ^ (k + 1) - truncBelow N D ^ (k + 1)) * D +
            truncBelow N D ^ (k + 1) * (D - truncBelow N D) := by ring
      rw [e]
      exact low_add (low_mono (le_of_eq (by omega)) (low_mul ihk hD1))
        (low_mono (le_of_eq (by omega)) (low_mul (low_pow hT1 (k + 1)) hlow))

  set a : ℕ → K := fun k => PowerSeries.coeff k (PowerSeries.exp K) • coeff n (D ^ k) with ha
  have hafin : (Function.support a).Finite := PowerSeries.coeff_subst_finite hs _ n
  set b : ℕ → K := fun k => if k = 1 then 0 else a k with hb
  set c : ℕ → K := fun k => if k = 1 then a 1 else 0 with hc
  have hbfin : (Function.support b).Finite :=
    hafin.subset fun k hk => by
      simp only [Function.mem_support, hb] at hk ⊢
      split_ifs at hk with h
      · exact absurd rfl hk
      · exact hk
  have hcfin : (Function.support c).Finite :=
    (Set.finite_singleton 1).subset fun k hk => by
      simp only [Function.mem_support, hc] at hk
      split_ifs at hk with h
      · exact h
      · exact absurd rfl hk
  have habc : a = fun k => b k + c k := by
    funext k
    simp only [hb, hc]
    split_ifs with h
    · subst h; simp
    · simp
  have ha1 : a 1 = coeff n D := by
    simp [ha, PowerSeries.coeff_exp]
  have hsum : coeff n (mvExp D) = (∑ᶠ k, b k) + coeff n D := by
    unfold mvExp
    rw [PowerSeries.coeff_subst hs]
    change ∑ᶠ k, a k = _
    rw [habc, finsum_add_distrib hbfin hcfin, finsum_eq_single c 1 (fun k hk => if_neg hk)]
    simp only [hc, if_pos rfl, ha1]
  have hEq : coeff n D = coeff n (mvExp D - 1) + -(∑ᶠ k, b k) := by
    rw [map_sub, coeff_one, if_neg hn0, sub_zero, hsum]
    ring
  rw [monoWtGe_iff, hEq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE n) ?_)
  rw [norm_neg]
  refine norm_finsum_le_of (Real.rpow_nonneg hπ0.le _) fun k => ?_
  simp only [hb]
  split_ifs with hk1
  · simpa using Real.rpow_nonneg hπ0.le _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk0 : k = 0 := by omega
    subst hk0
    simp only [ha, pow_zero, coeff_one, if_neg hn0, smul_zero, norm_zero]
    exact Real.rpow_nonneg hπ0.le _

  have hce : coeff n (D ^ k) = coeff n (truncBelow N D ^ k) := by
    have := hpow (k - 1) n (by omega)
    rw [Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero] at this
    exact this
  have hbd := wtGe_pow hπ0 hTw k n
  rw [monoWtGe_iff] at hbd
  have hv := padicValNat_factorial_le_sub_one_div hl (k := k) (by omega)
  simp only [ha]
  rw [smul_eq_mul, norm_mul, norm_coeff_exp hl hπ, hce]
  set v := padicValNat l k.factorial
  calc (‖(l : K)‖ ^ v)⁻¹ * ‖coeff n (truncBelow N D ^ k)‖
      ≤ (‖(l : K)‖ ^ v)⁻¹ * ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 (pow_nonneg hπ0.le _))
    _ = ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r - (v : ℝ)) := by
        rw [Real.rpow_sub hπ0 _ (v : ℝ), Real.rpow_natCast]
        ring
    _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - dot n r) := by
        apply Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1
        nlinarith

end Formalism.DworkPowerSeriesWeights
end
end

section -- merged from Formalism.GaussJetBounds.GaussJetProofs.AsmOne
noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem asmOne_one_le_norm_two {K : Type u} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hodd : Odd l) (hpi : ‖(l : K)‖ < 1) : 1 ≤ ‖(2 : K)‖ := by
  by_contra h
  push_neg at h
  obtain ⟨m, rfl⟩ := hodd
  have hnat : ∀ k : ℕ, ‖(k : K)‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
  have h1 : (1 : K) = ((2 * m + 1 : ℕ) : K) - 2 * (m : K) := by
    push_cast
    ring
  have h2 : ‖(2 : K) * (m : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(2 : K)‖ * ‖(m : K)‖ ≤ ‖(2 : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hnat m) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h
  have h3 : ‖(1 : K)‖ < 1 := by
    rw [h1, sub_eq_add_neg]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hpi (by rwa [norm_neg]))
  simp at h3

theorem asmOne_lin_wt {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v} [Fintype ι]
    {pi : ℝ} (h0 : 0 < pi) (c : ι → K) (hc : ∀ i, ‖c i‖ ≤ 1) (t : ℝ) :
    WtGe pi (fun _ : ι => t) t (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) := by
  classical
  intro n
  unfold MonoWtGe
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  by_cases hn : ∃ i, n = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := hn
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_one, asmR_dot_single]
      simp only [Nat.cast_one, one_mul, sub_self, Real.rpow_zero]
      exact hc i
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      exact hj ((Finsupp.single_left_injective one_ne_zero) h).symm
    · simp
  · push_neg at hn
    rw [Finset.sum_eq_zero (fun i _ => by rw [if_neg (hn i), mul_zero]), norm_zero]
    exact Real.rpow_nonneg h0.le _

theorem asmOne_lin_const {K : Type u} [NormedField K] {ι : Type v} [Fintype ι] (c : ι → K) :
    MvPowerSeries.constantCoeff (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

theorem asmOne_smul_wt {K : Type u} [NormedField K] {ι : Type v} {pi : ℝ} {r : ι → ℝ} {w : ℝ}
    {c : K} (hc : ‖c‖ ≤ 1) {f : MvPowerSeries ι K} (hf : WtGe pi r w f) :
    WtGe pi r w (c • f) := by
  intro n
  have h := hf n
  unfold MonoWtGe at h ⊢
  rw [map_smul, smul_eq_mul, norm_mul]
  calc ‖c‖ * ‖MvPowerSeries.coeff n f‖ ≤ 1 * ‖MvPowerSeries.coeff n f‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h

theorem asmOne_smul_const {K : Type u} [NormedField K] {ι : Type v} (c : K)
    {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (c • f) = 0 := by
  first
    | simp [hf]
    | rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]

theorem asmOne_zmod2 : ∀ s s' a b : ZMod 2, s.val % 2 = 0 → s'.val % 2 = 1 → s + a = s' + b →
    a + b = 1 := by
  decide

theorem oneLetterR_of (hS : LemmaS.{u}) (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u})
    (hW1 : SubstWt.{u, 0, v}) (hW0 : SubstWt.{u, 0, 0}) (hRM : RadMono.{u, v})
    (hMW : MulWtLe.{u, v}) (hE : ExpWtLe.{u, v}) (hF : FactVal.{u, v})
    (hOR : OneLetterRadius) : OneLetterR.{u, v} := by
  intro K _ _ _ l N0 N1 hl hodd hpi K0 hK0 ζ hζ be hbe ep hep ι _ _ M hM g hg0 hgl U hU sgn hsgn κ
  classical
  have h2n : 1 ≤ ‖(2 : K)‖ := asmOne_one_le_norm_two hodd hpi
  set π : ℝ := ‖(l : K)‖ with hπdef
  have hl3 : 3 ≤ l := by
    obtain ⟨m, rfl⟩ := hodd
    rcases m with _ | m
    · exact absurd hl Nat.not_prime_one
    · omega
  have hπ0 : 0 < π := by
    rw [hπdef, norm_pos_iff]
    exact_mod_cast hl.ne_zero
  have hπ1 : π ≤ 1 := hpi.le
  have hlR : (3 : ℝ) ≤ l := by exact_mod_cast hl3
  have hl1 : (l : ℝ) - 1 ≠ 0 := by linarith
  have hl2 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hl2p : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  obtain ⟨hOR1, hOR2⟩ := hOR l hl3
  have hrho0 : 0 ≤ rho l := by
    unfold rho
    positivity
  have hrg : rho l ≤ gam l := by
    unfold rho gam
    gcongr
    linarith
  have key : 1 / ((l : ℝ) - 1) - gam l = rho l := by
    unfold rho gam
    field_simp
    ring

  have wt_sum : ∀ (r : ι → ℝ) (w : ℝ) (s : Finset (Fin N0 × Fin N1))
      (f : Fin N0 × Fin N1 → MvPowerSeries ι K), (∀ x ∈ s, WtGe π r w (f x)) →
      WtGe π r w (∑ x ∈ s, f x) := by
    intro r w s f
    refine Finset.induction_on s ?_ ?_
    · intro _ n
      unfold MonoWtGe
      rw [Finset.sum_empty, map_zero, norm_zero]
      exact Real.rpow_nonneg hπ0.le _
    · intro a s ha ih hf n
      rw [Finset.sum_insert ha]
      have h1 := hf a (Finset.mem_insert_self a s) n
      have h2 := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)) n
      unfold MonoWtGe at h1 h2 ⊢
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

  have cc_subst : ∀ (a : ZMod 2 → MvPowerSeries ι K), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      ∀ f : MvPowerSeries (ZMod 2) K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
    intro a ha f hf
    have hs : MvPowerSeries.HasSubst a := by
      first
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
        | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
    rw [MvPowerSeries.constantCoeff_subst hs]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
        by_contra h
        push_neg at h
        exact hd (Finsupp.ext h)
      have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
        rw [Finsupp.prod, map_prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs') (by rw [map_pow, ha, zero_pow hs'])
      rw [h0, smul_zero]
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra h
    have h' := hbe.2.2.1 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
    exact absurd h'.1 (by simp [degE])

  have hUw : WtGe π (fun _ => rho l) 0 U := by
    intro n
    unfold MonoWtGe
    refine (hU n).trans ?_
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hπ0 hπ1
      (by linarith [asmR_dot_nonneg n (r := fun _ => rho l) (fun _ => hrho0)])
  have hlog : ∀ x, oneLog (K := K) l x = genLog (K := K) l id x := fun x => (hB K l 2 N0 N1).2.2 x
  have hgw : ∀ x, WtGe π (fun _ => rho l) (rho l) (g x) :=
    hG K l hl hpi (Fin N0 × Fin N1) id g hg0 (fun x => by rw [← hlog x]; exact hgl x)
  have hGU : WtGe π (fun _ => rho l) 0 (MvPowerSeries.subst g U) :=
    hW0 K π hπ0 hpi (Fin N0 × Fin N1) (Fin N0 × Fin N1) g (fun _ => rho l) (fun _ => rho l) 0 U
      hg0 hgw hUw
  have hlinw : ∀ (t : ℝ) x,
      WtGe π (fun _ : ι => t) t (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) :=
    fun t x => asmOne_lin_wt hπ0 (M x) (hM x) t
  have hlinA : ∀ x, WtGe π (fun _ : ι => gam l) (rho l)
      (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) := fun x =>
    (hRM K π hπ0 hpi ι (fun _ => rho l) (fun _ => gam l) (rho l) (fun _ => hrg)).1 _ (hlinw (rho l) x)
  have hA : WtGe π (fun _ : ι => gam l) 0
      (MvPowerSeries.subst (fun x => ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)
        (MvPowerSeries.subst g U)) :=
    hW1 K π hπ0 hpi (Fin N0 × Fin N1) ι _ (fun _ => rho l) (fun _ => gam l) 0 _
      (fun x => asmOne_lin_const (M x)) hlinA hGU
  obtain ⟨hS1, hS2⟩ := hS K l 2 hl hodd le_rfl even_two hpi K0 hK0 ζ hζ be hbe
  have hbeW : WtGe π (fun _ : ZMod 2 => gam l) (1 / ((l : ℝ) - 1)) be := by
    intro n
    by_cases hbi : IsBiPower l n
    · obtain ⟨s, s', α, β, hs, hs', _, hsum, rfl⟩ := hbi
      have h1 := hS1 (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))
      unfold MonoWtGe at h1 ⊢
      have hodd' : Odd (α + β) := by
        have h := asmOne_zmod2 s s' α β hs hs' hsum
        have h' : ((α + β : ℕ) : ZMod 2) = 1 := by
          push_cast
          exact h
        have h'' := congrArg ZMod.val h'
        rw [ZMod.val_natCast] at h''
        exact Nat.odd_iff.2 (h''.trans (by decide))
      have hD := hOR1 α β hodd'
      have e1 : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ : ZMod 2 => rho l) =
          ((l : ℝ) ^ α + (l : ℝ) ^ β) * rho l := by
        rw [show Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) = pureMon l s s' α β from rfl,
          asmR_dot_pureMon]
        ring
      have e2 : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ : ZMod 2 => gam l) =
          ((l : ℝ) ^ α + (l : ℝ) ^ β) * gam l := by
        rw [show Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) = pureMon l s s' α β from rfl,
          asmR_dot_pureMon]
        ring
      rw [e1] at h1
      rw [e2]
      refine h1.trans (Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1 ?_)
      have hg : gam l - rho l = 1 / ((l : ℝ) + 1) := by linarith [hOR2]
      have h3 : 1 ≤ ((l : ℝ) ^ α + (l : ℝ) ^ β) * (gam l - rho l) := by
        rw [hg, mul_one_div]
        exact hD
      nlinarith
    · exact asmR_monoWtGe_rad hπ0 hπ1 (fun _ => hrg) (hS2 n hbi)
  have haw : ∀ x (s : ZMod 2), WtGe π (fun _ : ι => gam l) (gam l)
      ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) := by
    intro x s
    refine asmOne_smul_wt ?_ (hlinw (gam l) x)
    split_ifs <;> simp [hep]
  have hac : ∀ x (s : ZMod 2), MvPowerSeries.constantCoeff
      ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) = 0 :=
    fun x s => asmOne_smul_const _ (asmOne_lin_const (M x))
  have hBx : ∀ x, WtGe π (fun _ : ι => gam l) (1 / ((l : ℝ) - 1))
      (MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
        ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) := fun x =>
    hW1 K π hπ0 hpi (ZMod 2) ι _ (fun _ => gam l) (fun _ => gam l) _ be (hac x) (haw x) hbeW
  have hsgn1 : ‖sgn‖ = 1 := by rcases hsgn with rfl | rfl <;> simp
  have hsgn2 : ‖sgn / 2‖ ≤ 1 := by
    rw [norm_div, hsgn1]
    exact div_le_one_of_le₀ h2n (by positivity)
  have hBw := asmOne_smul_wt hsgn2 (wt_sum _ _ Finset.univ _ (fun x _ => hBx x))
  have hBc : MvPowerSeries.constantCoeff ((sgn / 2) • ∑ x : Fin N0 × Fin N1,
      MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
        ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) = 0 := by
    refine asmOne_smul_const _ ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun x _ => cc_subst _ (hac x) be hbe0
  have hExp := hE K l hl hpi ι (fun _ => gam l) κ _ hBc (fun n _ => hBw n)
  have hMul := hMW K π hπ0 ι (fun _ => gam l) 0 0 κ _ _ (fun n _ => hA n) hExp
  have hk := hMul κ le_rfl
  have hf := hF K l hl hpi ι κ
  unfold MonoWtGe at hk
  have hdeg : (κ.degree : ℝ) = ∑ i, (κ i : ℝ) := by
    rw [Finsupp.degree_eq_sum]
    push_cast
    rfl
  have e : (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * gam l = rho l * ∑ i, (κ i : ℝ) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← key]
    ring
  rw [norm_mul]
  refine (mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg hπ0.le _)).trans (le_of_eq ?_)
  rw [← Real.rpow_add hπ0, asmR_dot_fintype, hdeg]
  congr 1
  beta_reduce
  linarith [e]

end Formalism.DworkPowerSeriesWeights
end
end

section -- merged from Formalism.GaussJetBounds.GaussJetProofs.ExistsNeZeroOfFinsumNeZero
noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

namespace ExponentialDerivativeInverse

section Sub

variable {K : Type u} [NormedField K] {ι : Type v} {K0 : Subfield K}

def InSub (K0 : Subfield K) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ∈ K0

theorem inSub_add {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f + g) := fun n => by rw [map_add (f := _)]; exact K0.add_mem (hf n) (hg n)

theorem inSub_sub {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f - g) := fun n => by rw [map_sub]; exact K0.sub_mem (hf n) (hg n)

theorem inSub_zero : InSub K0 (0 : MvPowerSeries ι K) := fun n => by
  rw [map_zero]; exact K0.zero_mem

theorem inSub_one : InSub K0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact K0.one_mem
  · exact K0.zero_mem

theorem inSub_X (x : ι) : InSub K0 (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact K0.one_mem
  · exact K0.zero_mem

theorem inSub_mul {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact K0.sum_mem fun p _ => K0.mul_mem (hf p.1) (hg p.2)

theorem inSub_pow {f : MvPowerSeries ι K} (hf : InSub K0 f) (k : ℕ) : InSub K0 (f ^ k) := by
  induction k with
  | zero => simpa using (inSub_one : InSub K0 (1 : MvPowerSeries ι K))
  | succ k ih => rw [pow_succ]; exact inSub_mul ih hf

theorem inSub_prod {α : Type w} (s : Finset α) (F : α → MvPowerSeries ι K)
    (h : ∀ i ∈ s, InSub K0 (F i)) : InSub K0 (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (inSub_one : InSub K0 (1 : MvPowerSeries ι K))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact inSub_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem finsum_mem_sub {α : Type w} (g : α → K) (h : ∀ i, g i ∈ K0) : ∑ᶠ i, g i ∈ K0 := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact K0.sum_mem fun i _ => h i
  · rw [finsum_of_infinite_support hfin]
    exact K0.zero_mem

theorem inSub_subst {σ : Type w} [Finite σ] {a : σ → MvPowerSeries ι K}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, InSub K0 (a s))
    {f : MvPowerSeries σ K} (hf : InSub K0 f) : InSub K0 (MvPowerSeries.subst a f) := by
  intro n
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]
  refine finsum_mem_sub _ fun m => ?_
  rw [smul_eq_mul]
  exact K0.mul_mem (hf m) (inSub_prod m.support _ (fun s _ => inSub_pow (ha s) _) n)

theorem inSub_mvExp [CharZero K] {D : MvPowerSeries ι K}
    (hD0 : MvPowerSeries.constantCoeff D = 0) (hD : InSub K0 D) : InSub K0 (mvExp D) := by
  intro n
  unfold mvExp
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hD0)]
  refine finsum_mem_sub _ fun k => ?_
  rw [smul_eq_mul, PowerSeries.coeff_exp]
  have hq : algebraMap ℚ K (1 / (k.factorial : ℚ)) ∈ K0 := by
    rw [map_div₀, map_one, map_natCast]
    exact K0.div_mem K0.one_mem (natCast_mem K0 _)
  exact K0.mul_mem hq (inSub_pow hD k n)

end Sub

section Wt

variable {K : Type u} [NormedField K] {ι : Type v}

def wsum (w : ι → ℤ) (n : ι →₀ ℕ) : ℤ := n.sum fun x k => (k : ℤ) * w x

theorem wsum_add (w : ι → ℤ) (m n : ι →₀ ℕ) : wsum w (m + n) = wsum w m + wsum w n := by
  classical
  unfold wsum
  exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by push_cast; ring)

theorem wsum_zero (w : ι → ℤ) : wsum w (0 : ι →₀ ℕ) = 0 := by simp [wsum]

theorem wsum_single (w : ι → ℤ) (x : ι) (k : ℕ) : wsum w (Finsupp.single x k) = k * w x := by
  simp [wsum]

def HomW (w : ι → ℤ) (c : ℤ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → wsum w n = c

def CongW (N : ℤ) (w : ι → ℤ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → N ∣ wsum w n

theorem exists_ne_zero_of_finsum_ne_zero {α : Type w} {g : α → K} (h : ∑ᶠ i, g i ≠ 0) :
    ∃ i, g i ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (finsum_eq_zero_of_forall_eq_zero hc)

variable {w : ι → ℤ}

theorem homW_X (x : ι) : HomW w (w x) (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_X] at hn
  split_ifs at hn with h
  · rw [h, wsum_single]; simp
  · exact absurd rfl hn

theorem homW_zero (c : ℤ) : HomW w c (0 : MvPowerSeries ι K) := by
  intro n hn; simp at hn

theorem homW_one : HomW w 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_one] at hn
  split_ifs at hn with h
  · rw [h, wsum_zero]
  · exact absurd rfl hn

theorem homW_add {c : ℤ} {f g : MvPowerSeries ι K} (hf : HomW w c f) (hg : HomW w c g) :
    HomW w c (f + g) := by
  intro n hn
  rw [map_add (f := _)] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · rw [h, zero_add] at hn; exact hg n hn
  · exact hf n h

theorem homW_mul {c c' : ℤ} {f g : MvPowerSeries ι K} (hf : HomW w c f) (hg : HomW w c' g) :
    HomW w (c + c') (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, wsum_add, hf p.1 (left_ne_zero_of_mul hpn), hg p.2 (right_ne_zero_of_mul hpn)]

theorem homW_pow {c : ℤ} {f : MvPowerSeries ι K} (hf : HomW w c f) (k : ℕ) :
    HomW w (k * c) (f ^ k) := by
  induction k with
  | zero => intro n hn; simpa using homW_one n (by simpa using hn)
  | succ k ih =>
    rw [pow_succ]
    intro n hn
    rw [homW_mul ih hf n hn]
    push_cast; ring

theorem homW_prod {α : Type w} (s : Finset α) (c : α → ℤ) (F : α → MvPowerSeries ι K)
    (h : ∀ i ∈ s, HomW w (c i) (F i)) : HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  first | exact UpperTheory.Reformulated.B.Qi22.homW_prod .. | (apply UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi22.homW_prod <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s c F h | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s c F | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s c | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K

variable {N : ℤ}

theorem congW_sub {f g : MvPowerSeries ι K} (hf : CongW N w f) (hg : CongW N w g) :
    CongW N w (f - g) := by
  intro n hn
  rw [map_sub] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · rw [h, zero_sub, neg_ne_zero] at hn; exact hg n hn
  · exact hf n h

theorem congW_one : CongW N w (1 : MvPowerSeries ι K) := by
  intro n hn
  rw [homW_one n hn]
  exact dvd_zero N

theorem congW_mul {f g : MvPowerSeries ι K} (hf : CongW N w f) (hg : CongW N w g) :
    CongW N w (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, wsum_add]
  exact dvd_add (hf p.1 (left_ne_zero_of_mul hpn)) (hg p.2 (right_ne_zero_of_mul hpn))

theorem congW_pow {f : MvPowerSeries ι K} (hf : CongW N w f) (k : ℕ) : CongW N w (f ^ k) := by
  induction k with
  | zero => simpa using (congW_one : CongW N w (1 : MvPowerSeries ι K))
  | succ k ih => rw [pow_succ]; exact congW_mul ih hf

theorem congW_subst {σ : Type w} [Finite σ] {w1 : σ → ℤ} {a : σ → MvPowerSeries ι K}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, HomW w (w1 s) (a s))
    {f : MvPowerSeries σ K} (hf : CongW N w1 f) : CongW N w (MvPowerSeries.subst a f) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)] at hn
  obtain ⟨m, hm⟩ := exists_ne_zero_of_finsum_ne_zero hn
  simp only [smul_eq_mul] at hm
  have h1 := hf m (left_ne_zero_of_mul hm)
  have h2 := homW_prod m.support (fun s => (m s : ℤ) * w1 s) (fun s => a s ^ m s)
    (fun s _ => homW_pow (ha s) (m s)) n (right_ne_zero_of_mul hm)
  rw [h2]
  exact h1

theorem congW_mvExp [CharZero K] {D : MvPowerSeries ι K}
    (hD0 : MvPowerSeries.constantCoeff D = 0) (hD : CongW N w D) : CongW N w (mvExp D) := by
  intro n hn
  unfold mvExp at hn
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hD0)] at hn
  obtain ⟨k, hk⟩ := exists_ne_zero_of_finsum_ne_zero hn
  simp only [smul_eq_mul] at hk
  exact congW_pow hD k n (right_ne_zero_of_mul hk)

theorem zpow_sum_of_ne {α : Type w} (s : Finset α) {ζ : K} (hζ : ζ ≠ 0) (f : α → ℤ) :
    ζ ^ (∑ i ∈ s, f i) = ∏ i ∈ s, ζ ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hζ, ih]

end Wt

section Torus

variable {K : Type u} [NormedField K] {d : ℕ}

theorem congW_of_torus {l : ℕ} [NeZero d] {ζ : K} (hN : l ^ d - 1 ≠ 0)
    (hζ : IsPrimitiveRoot ζ (l ^ d - 1)) {be : MvPowerSeries (ZMod d) K}
    (hbe : MvPowerSeries.subst (torus l ζ) be = be) :
    CongW ((l ^ d - 1 : ℕ) : ℤ) (lw l) be := by
  classical
  intro n hn
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  have ht : torus (d := d) l ζ = (fun s : ZMod d => ζ ^ lw l s) • (MvPowerSeries.X : ZMod d → MvPowerSeries (ZMod d) K) := by
    funext s
    simp [torus, MvPowerSeries.smul_eq_C_mul]
  rw [ht, ← MvPowerSeries.rescale_eq_subst] at hbe
  have hc := congrArg (MvPowerSeries.coeff n) hbe
  rw [MvPowerSeries.coeff_rescale] at hc
  have hprod : (n.prod fun s m => (ζ ^ lw l s) ^ m) = ζ ^ wsum (lw l) n := by
    unfold wsum Finsupp.prod Finsupp.sum
    rw [zpow_sum_of_ne _ hζ0]
    refine Finset.prod_congr rfl fun s _ => ?_
    beta_reduce
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hprod] at hc
  have hu : ζ ^ wsum (lw l) n = 1 := by
    have h2 : (ζ ^ wsum (lw l) n - 1) * MvPowerSeries.coeff n be = 0 := by
      rw [sub_mul, hc, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hn
  exact (hζ.zpow_eq_one_iff_dvd _).mp hu

end Torus

section Diff

variable {K : Type u} [NormedField K] {d : ℕ}

def Good (K0 : Subfield K) (N : ℤ) (w : V2 d → ℤ) (f : MvPowerSeries (V2 d) K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ InSub K0 f ∧ CongW N w f

theorem good_sub {K0 : Subfield K} {N : ℤ} {w : V2 d → ℤ} {f g : MvPowerSeries (V2 d) K}
    (hf : Good K0 N w f) (hg : Good K0 N w g) : Good K0 N w (f - g) :=
  ⟨by rw [map_sub, hf.1, hg.1, sub_zero], inSub_sub hf.2.1 hg.2.1, congW_sub hf.2.2 hg.2.2⟩

def Fam (K0 : Subfield K) (l : ℕ) (a : ZMod d → MvPowerSeries (V2 d) K) : Prop :=
  ∀ s, MvPowerSeries.constantCoeff (a s) = 0 ∧ InSub K0 (a s) ∧
    HomW (fun x : V2 d => lw l x.2) (lw l s) (a s)

theorem good_subst [NeZero d] {K0 : Subfield K} {l : ℕ} {N : ℤ} {be : MvPowerSeries (ZMod d) K}
    (hK0 : InSub K0 be) (hcc : MvPowerSeries.constantCoeff be = 0) (hcb : CongW N (lw l) be)
    {a : ZMod d → MvPowerSeries (V2 d) K} (ha : Fam K0 l a) :
    Good K0 N (fun x : V2 d => lw l x.2) (MvPowerSeries.subst a be) :=
  ⟨MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (ha s).1) (fun s => (ha s).1) hcc,
    inSub_subst (fun s => (ha s).1) (fun s => (ha s).2.1) hK0,
    congW_subst (fun s => (ha s).1) (fun s => (ha s).2.2) hcb⟩

variable {K0 : Subfield K} {l : ℕ}

theorem zero_series_family : Fam K0 l (s0 (K := K) (d := d)) := fun s =>
  ⟨by simp [s0], inSub_X _, homW_X (false, s)⟩

theorem oddIndicator_alt_series_family : Fam K0 l (s1 (K := K) (d := d)) := by
  intro s
  unfold s1
  split_ifs
  · exact ⟨by simp, inSub_add (inSub_X _) (inSub_X _),
      homW_add (homW_X (false, s)) (homW_X (true, s))⟩
  · exact ⟨by simp, inSub_add (inSub_X _) inSub_zero,
      homW_add (homW_X (false, s)) (homW_zero _)⟩

theorem swappedParity_series_family : Fam K0 l (s2 (K := K) (d := d)) := by
  intro s
  unfold s2
  split_ifs
  · exact ⟨by simp, inSub_X _, homW_X (true, s)⟩
  · exact ⟨by simp, inSub_X _, homW_X (false, s)⟩

theorem oddIndicator_series_family : Fam K0 l (s1' (K := K) (d := d)) := by
  intro s
  unfold s1'
  split_ifs
  · exact ⟨by simp, inSub_add (inSub_X _) inSub_zero,
      homW_add (homW_X (false, s)) (homW_zero _)⟩
  · exact ⟨by simp, inSub_add (inSub_X _) (inSub_X _),
      homW_add (homW_X (false, s)) (homW_X (true, s))⟩

theorem parityIndicator_series_family : Fam K0 l (s2' (K := K) (d := d)) := by
  intro s
  unfold s2'
  split_ifs
  · exact ⟨by simp, inSub_X _, homW_X (false, s)⟩
  · exact ⟨by simp, inSub_X _, homW_X (true, s)⟩

end Diff

end ExponentialDerivativeInverse


open ExponentialDerivativeInverse in
theorem exponential_derivative_inverse : ExpDeInv.{u} := open ExponentialDerivativeInverse in by
  intro K _ _ l d _ hl hd _ K0 ζ hζ be hK0 htor hcc D hD
  have hN : l ^ d - 1 ≠ 0 := by
    have h2 : 2 ≤ l ^ d := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
    omega
  have hcb := congW_of_torus hN hζ htor
  have hD' : Good K0 ((l ^ d - 1 : ℕ) : ℤ) (fun x : V2 d => lw l x.2) D := by
    rcases hD with rfl | rfl
    · exact good_sub (good_sub (good_subst hK0 hcc hcb oddIndicator_alt_series_family) (good_subst hK0 hcc hcb zero_series_family))
        (good_subst hK0 hcc hcb swappedParity_series_family)
    · exact good_sub (good_sub (good_subst hK0 hcc hcb oddIndicator_series_family) (good_subst hK0 hcc hcb zero_series_family))
        (good_subst hK0 hcc hcb parityIndicator_series_family)
  exact ⟨inSub_mvExp hD'.1 hD'.2.1, fun n hn => congW_mvExp hD'.1 hD'.2.2 n hn⟩

end Formalism.DworkPowerSeriesWeights
end
end

universe u v

namespace Formalism.DworkPowerSeriesWeights

theorem lemmaS : LemmaS.{u} :=
  lemmaS_of generalized_log_weight generalized_log_inverse logarithm_weight_comparison substitution_weight_bound exponential_derivative_inverse
    weightQuantization logarithm_weight_induction binomial_coefficient_extraction

theorem oneLetterR : OneLetterR.{u, v} :=
  oneLetterR_of lemmaS generalized_log_weight logarithm_weight_comparison substitution_weight_bound substitution_weight_bound radical_weight_monotone
    multiplicative_weight_le exponential_weight_le factorial_valuation_bound oneLetterRadiusIdentity

end Formalism.DworkPowerSeriesWeights
