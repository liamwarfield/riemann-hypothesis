module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WittPNe
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.Pf14

theorem wittVector_prime_ne_zero (p n' : ℕ) [Fact p.Prime] : ((p : ℕ) : WF p n') ≠ 0 := by
  intro h
  have h1 := WittVector.coeff_p_one (p := p) (R := GaloisField p n')
  rw [h] at h1
  simp at h1

theorem planeAt : PlaneAt := by
  intro p n' _ W Qq _ _ _ _ _ m φ h g g' e e' hfr hg hg' he he' hpl
  have hp0 : (p : W) ≠ 0 := by
    intro h0
    apply wittVector_prime_ne_zero p n'
    apply φ.injective
    rw [map_natCast, h0, map_zero]
  have hpQ : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact fun h1 => hp0 ((IsFractionRing.injective W Qq) (by rw [h1, map_zero]))
  obtain ⟨-, hs, ht⟩ := he
  obtain ⟨-, hs', ht'⟩ := he'
  rw [src_eq φ g hg h] at hs
  rw [src_eq φ g' hg' h] at hs'
  rw [matQ_inv φ g hg] at ht
  rw [matQ_inv φ g' hg'] at ht'
  change e.tgt = colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht
  change e'.tgt = colSpan W (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht'
  obtain ⟨s, t⟩ := e
  obtain ⟨s', t'⟩ := e'
  simp only at hs hs' ht ht'
  rw [Edge.mk.injEq]
  refine ⟨by rw [hs, hs'], ?_⟩
  rw [ht, ht']
  apply le_antisymm
  · exact tgt_le_of_plane φ 1 hpQ g' g hg' hg h hpl.le
  · exact tgt_le_of_plane φ 1 hpQ g g' hg hg' h hpl.ge

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCZ
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem settingCZ : SettingCharZeroAt := by
  unfold SettingCharZeroAt
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS
  have hpW : ¬IsUnit (p : W) := hS.p_unif.1

  have hW : CharZero W := by
    rcases CharP.char_is_prime_or_zero W (ringChar W) with hq | hq
    · exfalso
      haveI hcp : CharP W (ringChar W) := ringChar.charP W
      by_cases hqp : ringChar W = p
      · apply hS.p_unif.ne_zero
        rw [← hqp]
        exact CharP.cast_eq_zero W (ringChar W)
      · have hcop : Nat.Coprime p (ringChar W) :=
          (Nat.coprime_primes hS.prime hq).mpr (Ne.symm hqp)
        apply hpW
        have hu : IsUnit (p : ZMod (ringChar W)) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]
          exact Units.isUnit _
        have hu' := hu.map (ZMod.castHom (dvd_refl (ringChar W)) W)
        simpa using hu'
    · haveI : CharP W 0 := by
        rw [← hq]
        exact ringChar.charP W
      exact CharP.charP_to_charZero W
  haveI := hS.frac_alt
  have hQ : CharZero Qq := charZero_of_injective_algebraMap (IsFractionRing.injective W Qq)
  have hK : CharZero Kf := (RingHom.charZero_iff ι.injective).mp hQ

  have hpO : ¬IsUnit (p : O) := by
    intro hu
    have hint : jO.IsIntegral := RingHom.IsIntegral.of_finite hS.finite
    have hmax : ((IsLocalRing.maximalIdeal O).comap jO).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' jO hint (IsLocalRing.maximalIdeal O)
    have hle : (IsLocalRing.maximalIdeal O).comap jO = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal hmax
    have hpm : (p : W) ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hpW
    rw [← hle, Ideal.mem_comap, map_natCast] at hpm
    exact (IsLocalRing.mem_maximalIdeal _).mp hpm hu
  exact ⟨hK, hpO⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairFacts
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Finset

theorem pf_tele (L K : ℕ → ℤ) (q : ℕ) (h : ∀ t, t < q → L (t + 1) ≤ K t) :
    ∑ t ∈ range (q + 1), (L t - K t) ≤ L 0 - K q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ]
    have h1 := ih fun t ht => h t (by omega)
    have h2 := h q (by omega)
    linarith

def pfMass {r : ℕ} (v : Fin r → ℤ) : ℤ := ∑ t, max 0 (-(v t))

theorem pfMass_up {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : pfMass nu ≤ pfMass mu :=
  Finset.sum_le_sum fun t _ => max_le_max le_rfl (neg_le_neg (h.1 t))

theorem pfMass_down {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : pfMass mu ≤ pfMass nu + g := by
  have e : ∀ t, max 0 (-(mu t)) ≤ max 0 (-(nu t)) + (nu t - mu t) := fun t => by
    have := h.1 t
    rcases le_total 0 (-(mu t)) with h1 | h1 <;> rcases le_total 0 (-(nu t)) with h2 | h2 <;>
      simp only [max_eq_left, max_eq_right, h1, h2] <;> omega
  calc pfMass mu ≤ ∑ t, (max 0 (-(nu t)) + (nu t - mu t)) := Finset.sum_le_sum fun t _ => e t
    _ = pfMass nu + g := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h.2.2]; rfl

variable {s r : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

theorem pf_mass (h : IsChain (kLetters A Ai Ci) mu) : ∀ (n : ℕ) (hn : n ≤ s),
    pfMass (fun t : Fin r => mu ⟨2 * n + 1, by omega⟩ t.succ) ≤ ∑ x : Fin s, if x.val < n then (Ci x : ℤ) else 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : (⟨2 * 0 + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = 1 := rfl
    rw [e]
    unfold pfMass
    simp [chain_first_tail (N := 2 * s) h (by simp [kLetters])]
  | succ n ih =>
    intro hn
    have h0 := ih (by omega)
    obtain ⟨hW, hC, -, -, -, -, -, -⟩ := pair_top h (⟨n, by omega⟩ : Fin s)
    have h1 := pfMass_up hW
    have h2 := pfMass_down hC
    have h3 := sum_lt_succ (fun x : Fin s => (Ci x : ℤ)) (⟨n, by omega⟩ : Fin s)
    simp only at h3
    rw [h3]
    have e : (⟨2 * (n + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * n + 3, by omega⟩ := Fin.ext (by show 2 * (n + 1) + 1 = 2 * n + 3; omega)
    rw [e]
    have h4 : ((Ci ⟨n, by omega⟩ - (pairSg mu Ai ⟨n, by omega⟩).toNat : ℕ) : ℤ) ≤ (Ci ⟨n, by omega⟩ : ℤ) := by
      exact_mod_cast Nat.sub_le _ _
    linarith

theorem pf_prev_le [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) : ∀ (n : ℕ) (hn : n ≤ s),
    mu ⟨2 * n + 1, by omega⟩ (0 : Fin r).succ ≤ ∑ x : Fin s, if x.val < n then pairW mu x.val else 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : (⟨2 * 0 + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = 1 := rfl
    rw [e, chain_first_tail (N := 2 * s) h (by simp [kLetters])]
    exact (Finset.sum_eq_zero fun x _ => if_neg (Nat.not_lt_zero _)).symm.le
  | succ n ih =>
    intro hn
    have h0 := ih (by omega)
    obtain ⟨hW, hC, hw, -, -, -, -, -⟩ := pair_top h (⟨n, by omega⟩ : Fin s)
    have h1 := strip_first hW
    have h2 := hC.1 (0 : Fin r)
    have h3 := sum_lt_succ (fun x : Fin s => pairW mu x.val) (⟨n, by omega⟩ : Fin s)
    simp only at h3 h1 h2 hw
    rw [h3]
    have e : (⟨2 * (n + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * n + 3, by omega⟩ := Fin.ext (by show 2 * (n + 1) + 1 = 2 * n + 3; omega)
    rw [e]
    rw [Int.toNat_of_nonneg hw] at h1
    linarith

theorem pf_rho_le [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    pairRho mu i.val ≤ mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin r).succ + pairW mu i.val := by
  obtain ⟨hW, -, hw, -, -, -, -, -⟩ := pair_top h i
  have h1 := strip_first hW
  rw [Int.toNat_of_nonneg hw] at h1
  unfold pairRho
  rw [finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega)]
  exact h1

theorem pf_u_ge [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    pairSg mu Ai i - mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin r).succ ≤ pairO mu Ai i - pairRho mu i.val := by
  have h1 := pf_rho_le h i
  have hs : pairSg mu Ai i = pairO mu Ai i - pairW mu i.val := rfl
  linarith

theorem pf_rho_le_c [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    pairRho mu i.val ≤ pairC mu i.val ∧ pairRho mu i.val ≤ pairC mu (i.val + 1) := by
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := pair_top h i
  unfold pairRho
  rw [finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega)]
  exact ⟨h1 0 (by simp), h2 0 (by simp)⟩

theorem pf_d_le (h : IsPair A Ai Ci mu lam) (hr : s + 1 ≤ r) :
    pairD mu lam ≤ pairC mu s + ∑ i, (Ci i : ℤ) - ∑ i : Fin s, pairN (s := s) lam i := by
  obtain ⟨hch, hint⟩ := h
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 + s := ⟨r - 1 - s, by omega⟩
  set ka : Fin (q + 1 + s) → ℤ := fun t => mu (Fin.last _) t.succ with hka
  let L : ℕ → ℤ := fun t => if h : t < q + 1 + s then lam ⟨t, h⟩ else 0
  let K : ℕ → ℤ := fun t => if h : t < q + 1 + s then ka ⟨t, h⟩ else 0
  have hlast : (Fin.last (2 * s + 1) : Fin (2 * s + 1 + 1)) = ⟨2 * s + 1, by omega⟩ := rfl
  have hD : pairD mu lam = ∑ t ∈ range (q + 1 + s), (L t - K t) := by
    unfold pairD pairTail
    rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega), ← Finset.sum_sub_distrib]
    rw [← Fin.sum_univ_eq_sum_range (fun t => L t - K t)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [L, K, dif_pos t.2, hka, hlast]
  have hmass := pf_mass hch s le_rfl
  have hmass' : pfMass ka ≤ ∑ i, (Ci i : ℤ) := by
    have e : ∀ x : Fin s, (if x.val < s then (Ci x : ℤ) else 0) = Ci x := fun x => if_pos x.2
    rw [Finset.sum_congr rfl fun x _ => e x] at hmass
    exact hmass
  rw [hD, Finset.sum_range_add]

  have hup : ∑ t ∈ range (q + 1), (L t - K t) ≤ L 0 - K q := pf_tele L K q fun t ht => by
    simp only [L, K, dif_pos (show t + 1 < q + 1 + s by omega), dif_pos (show t < q + 1 + s by omega), hka]
    have := (hint ⟨t + 1, by omega⟩).2
    have e : (⟨t + 1, by omega⟩ : Fin (q + 1 + s)).castSucc = (⟨t, by omega⟩ : Fin (q + 1 + s)).succ := Fin.ext rfl
    rw [e] at this
    exact this
  have hL0 : L 0 ≤ pairC mu s := by
    simp only [L, dif_pos (show 0 < q + 1 + s by omega)]
    have := (hint ⟨0, by omega⟩).2
    unfold pairC
    rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]
    exact this
  have hKq : 0 ≤ K q := by
    simp only [K, dif_pos (show q < q + 1 + s by omega), hka]
    have hM : ∀ i, Ai i ≤ ∑ i, Ai i + ∑ i, Ci i := fun i =>
      le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_right _ _)
    have hM' : ∀ i, Ci i ≤ ∑ i, Ai i + ∑ i, Ci i := fun i =>
      le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)
    have := (pc_shape hM hM' hch (Fin.last _) (⟨q, by omega⟩ : Fin (q + 1 + s)).succ).2.1
    apply this
    simp only [Fin.val_succ, Fin.val_last, pcL]
    omega

  have hlowL : ∑ x ∈ range s, L (q + 1 + x) = -∑ i : Fin s, pairN (s := s) lam i := by
    rw [← Fin.sum_univ_eq_sum_range (fun x => L (q + 1 + x)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold pairN
    have e : q + 1 + s - s + i.val = q + 1 + i.val := by omega
    simp only [L, e, neg_neg]
  have hlowK : -∑ x ∈ range s, K (q + 1 + x) ≤ pfMass ka := by
    have h1 : -∑ x ∈ range s, K (q + 1 + x) ≤ ∑ x ∈ range s, max 0 (-(K (q + 1 + x))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun x _ => le_max_right _ _
    have h2 : ∑ t ∈ range (q + 1 + s), max 0 (-(K t)) = pfMass ka := by
      unfold pfMass
      rw [← Fin.sum_univ_eq_sum_range (fun t => max 0 (-(K t)))]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [K, dif_pos t.2]
    have h3 : ∑ x ∈ range s, max 0 (-(K (q + 1 + x))) ≤ ∑ t ∈ range (q + 1 + s), max 0 (-(K t)) := by
      rw [Finset.sum_range_add]
      have : 0 ≤ ∑ t ∈ range (q + 1), max 0 (-(K t)) := Finset.sum_nonneg fun _ _ => le_max_left _ _
      linarith
    linarith
  have hsplit : ∑ x ∈ range s, (L (q + 1 + x) - K (q + 1 + x)) =
      ∑ x ∈ range s, L (q + 1 + x) - ∑ x ∈ range s, K (q + 1 + x) := Finset.sum_sub_distrib _ _
  rw [hsplit, hlowL]
  linarith

theorem pf_X (h : IsPair A Ai Ci mu lam) (hr : s + 1 ≤ r) (La : ℝ)
    (hK : ∀ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) ≤ ((pairN (s := s) lam i : ℤ) : ℝ)) :
    ((pairD mu lam : ℤ) : ℝ) ≤ ((pairC mu s : ℤ) : ℝ) + La / ((r : ℝ) + 1) * ∑ i, (Ci i : ℝ) := by
  have h1 := pf_d_le h hr
  have h2 : ((pairD mu lam : ℤ) : ℝ) ≤ ((pairC mu s : ℤ) : ℝ) + ∑ i, (Ci i : ℝ) - ∑ i : Fin s, ((pairN (s := s) lam i : ℤ) : ℝ) := by
    have := (Int.cast_le (R := ℝ)).2 h1
    push_cast at this
    exact this
  have h3 : ∑ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) ≤ ∑ i : Fin s, ((pairN (s := s) lam i : ℤ) : ℝ) :=
    Finset.sum_le_sum fun i _ => hK i
  have h4 : ∑ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) =
      ∑ i, (Ci i : ℝ) - La / ((r : ℝ) + 1) * ∑ i, (Ci i : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

end Formalism.MainNotions.ColumnSystems.Pf
end
end
