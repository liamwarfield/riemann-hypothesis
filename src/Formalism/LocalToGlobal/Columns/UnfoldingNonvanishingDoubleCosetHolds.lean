module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwistedEisensteinNonvanishing
public import Formalism.LocalToGlobal.Columns.ChainTwPsi
public import Formalism.LocalToGlobal.Columns.ChainLawXiQF

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwNormLat
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.TwNormLatMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.IdealForm
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.CombinationEquivInvMemUnipotentFlagGroup
open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {K : Type} [Field K] {n : ℕ}

def Zab (k : ℕ) (v : Fin n → K) : Prop := ∀ l : Fin n, k ≤ l.1 → v l = 0

def UT (b : Fin n → Fin n → K) : Prop := ∀ l k : Fin n, l < k → b l k = 0

theorem comb_zab {b : Fin n → Fin n → K} (hb : UT b) (w : Fin n → K) (k0 : ℕ) (hw : Zab k0 w) :
    Zab k0 (∑ i, w i • b i) := by
  intro l hl
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : k0 ≤ i.1
  · rw [hw i hi, zero_mul]
  · have hil : i < l := Fin.lt_def.2 (by omega)
    rw [hb i l hil, mul_zero]

theorem comb_reflect {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) (w : Fin n → K) (k0 : ℕ)
    (h : Zab k0 (∑ i, w i • b i)) : Zab k0 w := by
  have key : ∀ d : ℕ, ∀ l : Fin n, n - l.1 ≤ d → k0 ≤ l.1 → w l = 0 := by
    intro d
    induction d with
    | zero => intro l hl _; have := l.2; omega
    | succ d ih =>
      intro l hl hk
      have hs := h l hk
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
      rw [Finset.sum_eq_single l] at hs
      · exact (mul_eq_zero.1 hs).resolve_right (hd l)
      · intro i _ hil
        rcases lt_or_gt_of_ne hil with hlt | hgt
        · rw [hb i l hlt, mul_zero]
        · have h2 := Fin.lt_def.1 hgt
          have h3 := i.2
          rw [ih i (by omega) (by omega), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ l) h'
  intro l hl
  exact key (n - l.1) l le_rfl hl

def combL (b : Fin n → Fin n → K) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun w := ∑ i, w i • b i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' t x := by simp [Finset.smul_sum, mul_smul]

theorem combL_apply (b : Fin n → Fin n → K) (w : Fin n → K) : combL b w = ∑ i, w i • b i := rfl

theorem combL_single (b : Fin n → Fin n → K) (l : Fin n) : combL b (Pi.single l 1) = b l := by
  rw [combL_apply, Finset.sum_eq_single l (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul])
    (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same, one_smul]

theorem combL_inj {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) : Function.Injective (combL b) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  have hz : Zab 0 (∑ i, w i • b i) := by
    intro l _
    rw [← combL_apply, hw]
    rfl
  funext l
  exact comb_reflect hb hd w 0 hz l (Nat.zero_le _)

def combE {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofInjectiveEndo (combL b) (combL_inj hb hd)

theorem combE_apply {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) (w : Fin n → K) :
    combE hb hd w = ∑ i, w i • b i := rfl

theorem combE_symm_zab {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) (k0 : ℕ) (v : Fin n → K)
    (hv : Zab k0 v) : Zab k0 ((combE hb hd).symm v) := by
  have h := combE_apply hb hd ((combE hb hd).symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  refine comb_reflect hb hd _ k0 ?_
  rw [← h]
  exact hv

theorem eN_eq_single (l : Fin n) : Loc.eN K n l.1 = Pi.single l 1 := by
  funext m
  simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem eN_eq_zero {i : ℕ} (hi : n ≤ i) : Loc.eN K n i = 0 := by
  funext m
  have := m.2
  simp only [Loc.eN, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem mem_Ufl_iff {N c i : ℕ} (v : Fin (N + c) → K) : v ∈ Loc.Ufl K N c i ↔ Zab (N + i) v := by
  show (∀ l : Fin (N + c), l.1 ∉ {l : ℕ | l < N + i} → v l = 0) ↔ ∀ l : Fin (N + c), N + i ≤ l.1 → v l = 0
  simp only [Set.mem_ofPred_eq, not_lt]

private theorem R1cond_combE {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    Loc.R1cond K N c (combE hb hd) := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [mem_Ufl_iff] at hv ⊢
    rw [combE_apply]
    exact comb_zab hb v _ hv
  · by_cases hN : N < N + c
    · have he : Loc.eN K (N + c) N = Pi.single (⟨N, hN⟩ : Fin (N + c)) 1 := eN_eq_single (⟨N, hN⟩ : Fin (N + c))
      rw [he]
      change combL b (Pi.single _ 1) = _
      rw [combL_single, ha hN]
    · have he : Loc.eN K (N + c) N = 0 := eN_eq_zero (by omega)
      rw [he, map_zero]
  · rw [mem_Ufl_iff]
    by_cases hi : N + i < N + c
    · have he : Loc.eN K (N + c) (N + i) = Pi.single (⟨N + i, hi⟩ : Fin (N + c)) 1 := eN_eq_single (⟨N + i, hi⟩ : Fin (N + c))
      rw [he]
      change Zab (N + i) (combL b (Pi.single _ 1) - _)
      rw [combL_single]
      intro m hm
      simp only [Pi.sub_apply]
      rcases lt_or_eq_of_le hm with hlt | heq
      · have hne : m ≠ ⟨N + i, hi⟩ := by
          intro h
          subst h
          exact lt_irrefl _ hlt
        rw [hb _ _ (Fin.lt_def.2 hlt), Pi.single_eq_of_ne hne, sub_zero]
      · have hm' : m = ⟨N + i, hi⟩ := Fin.ext heq.symm
        subst hm'
        rw [Pi.single_eq_same, h1 _ (Nat.le_add_right N i), sub_self]
    · have he : Loc.eN K (N + c) (N + i) = 0 := eN_eq_zero (by omega)
      rw [he, map_zero, sub_zero]
      intro m _
      rfl

private theorem R1cond_combE_symm {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    Loc.R1cond K N c (combE hb hd).symm := by
  have hT := R1cond_combE hb hd h1 ha
  have hs : ∀ i, ∀ v ∈ Loc.Ufl K N c i, (combE hb hd).symm v ∈ Loc.Ufl K N c i := fun i v hv =>
    (mem_Ufl_iff _).2 (combE_symm_zab hb hd _ v ((mem_Ufl_iff _).1 hv))
  refine ⟨hs, (LinearEquiv.symm_apply_eq _).2 hT.2.1.symm, fun i => ?_⟩
  have h3 := hs i _ (hT.2.2 i)
  rw [map_sub, LinearEquiv.symm_apply_apply] at h3
  have h4 := (Loc.Ufl K N c i).neg_mem h3
  rwa [neg_sub] at h4

theorem combinationEquiv_inv_mem_unipotentFlagGroup {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    (combE hb hd)⁻¹ ∈ Loc.R1 K N c := by
  show Loc.R1cond K N c (combE hb hd)⁻¹ ∧ Loc.R1cond K N c (combE hb hd)⁻¹⁻¹
  rw [inv_inv]
  exact ⟨R1cond_combE_symm hb hd h1 ha, R1cond_combE hb hd h1 ha⟩

end PI.TwNormLat.W
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem ideal_form (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : ℕ) (I : E → Prop) (hI1 : I 1)
    (hIm : ∀ t x, IntAt P t → I x → I (t * x)) (hIb : ∀ x, I x → IntAt P (qE P ^ j * x)) :
    ∃ K, K ≤ j ∧ I (qE P ^ K)⁻¹ ∧ ∀ x, I x → IntAt P (qE P ^ K * x) := by
  classical
  have hq0 := qE_ne_zero P hp
  refine ⟨Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j, Nat.findGreatest_le j,
    Nat.findGreatest_spec (P := fun k => I (qE P ^ k)⁻¹) (Nat.zero_le j) (by simpa using hI1), ?_⟩
  intro x hx
  by_contra hxK
  have hx0 : x ≠ 0 := by rintro rfl; exact hxK (by simpa using intAt_zero P)
  have hex : ∃ k, IntAt P (qE P ^ k * x) := ⟨j, hIb x hx⟩
  have hk0 : IntAt P (qE P ^ Nat.find hex * x) := Nat.find_spec hex
  have hk0j : Nat.find hex ≤ j := Nat.find_min' hex (hIb x hx)
  have hKk0 : Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j < Nat.find hex := by
    by_contra hle; rw [not_lt] at hle
    apply hxK
    have : qE P ^ Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j * x =
        qE P ^ (Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j - Nat.find hex) * (qE P ^ Nat.find hex * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]; exact intAt_mul P (intAt_pow P (intAt_natCast P _) _) hk0
  obtain ⟨k1, hk1⟩ : ∃ k1, Nat.find hex = k1 + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnot : ¬ IntAt P (qE P ^ Nat.find hex * x / qE P) := by
    have : qE P ^ Nat.find hex * x / qE P = qE P ^ k1 * x := by rw [hk1, pow_succ]; field_simp
    rw [this]; exact Nat.find_min hex (by omega)
  have hu := unit_of_not_div P hp hq hk0 hnot
  have hI := hIm _ _ hu hx
  have e : (qE P ^ Nat.find hex * x)⁻¹ * x = (qE P ^ Nat.find hex)⁻¹ := by
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
  rw [e] at hI
  exact Nat.findGreatest_is_greatest hKk0 hk0j hI

section M

variable {n : ℕ} (Mm : (Fin n → E) → Prop) (Madd : ∀ u v, Mm u → Mm v → Mm (u + v))
  (Msmul : ∀ t v, IntAt P t → Mm v → Mm (t • v)) (Mlam : ∀ v, (∀ l, IntAt P (v l)) → Mm v)

include Madd Msmul Mlam in
theorem comb_mem (b : Fin n → Fin n → E) (hbM : ∀ l, Mm (b l)) (w : Fin n → E) (hw : ∀ l, IntAt P (w l)) :
    Mm (∑ l, w l • b l) := by
  classical
  have h0 : Mm 0 := Mlam 0 (fun l => by
    first
    | exact ⟨0, 1, (fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)), by simp⟩
    | (unfold IntAt; done))
  exact Finset.sum_induction _ Mm (fun a b ha hb => Madd a b ha hb) h0
    (fun l _ => Msmul _ _ (hw l) (hbM l))

include Madd Msmul Mlam in

include Madd Msmul Mlam in
theorem herm (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : ℕ)
    (Mbd : ∀ v, Mm v → ∀ l, IntAt P (qE P ^ j * v l)) :
    ∃ (K : Fin n → ℕ) (b : Fin n → Fin n → E), (∀ l, K l ≤ j) ∧ (∀ l, Mm (b l)) ∧
      (∀ l, b l l = (qE P ^ K l)⁻¹) ∧ UT b ∧
      ∀ v, Mm v → ∃ w : Fin n → E, (∀ l, IntAt P (w l)) ∧ v = ∑ l, w l • b l := by
  classical
  have hIl : ∀ l : Fin n, ∃ K, K ≤ j ∧ (∃ v, Mm v ∧ v l = (qE P ^ K)⁻¹ ∧ ∀ k, l < k → v k = 0) ∧
      ∀ x, (∃ v, Mm v ∧ v l = x ∧ ∀ k, l < k → v k = 0) → IntAt P (qE P ^ K * x) := by
    intro l
    apply ideal_form P hp hq j (fun x => ∃ v, Mm v ∧ v l = x ∧ ∀ k, l < k → v k = 0)
    · refine ⟨Pi.single l 1, Mlam _ fun k => ?_, by simp, fun k hk => by simp [Pi.single_apply, hk.ne']⟩
      by_cases hk : k = l
      · rw [hk]; simpa using intAt_one P
      · simpa [Pi.single_apply, hk] using intAt_zero P
    · rintro t x ht ⟨v, hv, rfl, hz⟩
      exact ⟨t • v, Msmul t v ht hv, by simp, fun k hk => by simp [hz k hk]⟩
    · rintro x ⟨v, hv, rfl, -⟩; exact Mbd v hv l
  choose K hKj hKb hKall using hIl
  choose b hbM hbl hbz using hKb
  refine ⟨K, b, hKj, hbM, hbl, fun l k hlk => hbz l k hlk, ?_⟩
  have hq0 := qE_ne_zero P hp
  have main : ∀ k, k ≤ n → ∀ v, Mm v → Zab k v →
      ∃ w : Fin n → E, (∀ l, IntAt P (w l)) ∧ v = ∑ l, w l • b l := by
    intro k
    induction k with
    | zero =>
      intro _ v _ hz
      refine ⟨0, fun _ => intAt_zero P, ?_⟩
      funext l; simp [hz l (Nat.zero_le _)]
    | succ k ih =>
      intro hk v hv hz
      have ht : IntAt P (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩) :=
        hKall ⟨k, by omega⟩ _ ⟨v, hv, rfl, fun k' hk' => hz k' (by rw [Fin.lt_def] at hk'; simp at hk'; omega)⟩
      have hv' := Madd _ _ hv (Msmul _ _ (intAt_neg P ht) (hbM ⟨k, by omega⟩))
      have hz' : Zab k (v + (-(qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩)) • b ⟨k, by omega⟩) := by
        intro l hl
        rcases Nat.lt_or_eq_of_le hl with hlt | heq
        · rw [Pi.add_apply, hz l hlt, Pi.smul_apply, hbz _ l (by rw [Fin.lt_def]; simpa using hlt)]; simp
        · have : l = ⟨k, by omega⟩ := Fin.ext heq.symm
          rw [this, Pi.add_apply, Pi.smul_apply, hbl, smul_eq_mul]
          field_simp; ring
      obtain ⟨w', hw', e'⟩ := ih (by omega) _ hv' hz'
      refine ⟨w' + Pi.single ⟨k, by omega⟩ (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩), fun l => ?_, ?_⟩
      · rw [Pi.add_apply]
        refine intAt_add P (hw' l) ?_
        by_cases hl : l = ⟨k, by omega⟩
        · rw [hl]; simpa using ht
        · simpa [Pi.single_apply, hl] using intAt_zero P
      · have : v = (v + (-(qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩)) • b ⟨k, by omega⟩) +
            (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩) • b ⟨k, by omega⟩ := by rw [neg_smul]; abel
        conv_lhs => rw [this]
        rw [e']
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single ⟨k, by omega⟩]
        · simp
        · intro i _ hi; simp [Pi.single_apply, hi]
        · simp
  exact fun v hv => main n le_rfl v hv (fun l hl => absurd l.2 (by omega))

end M

end PI.TwNormLat.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.PrXLeOfNf
open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

def Crit (N c : ℕ) (n : ℕ → ℤ) (z : Sp E N) (v : Sp E (N + c)) : Prop :=
  (∀ l : Fin N, IntAt P (v (Fin.castAdd _ l) - Loc.atN v N * z l)) ∧
    ∀ i : Fin c, IntAt P ((((Ideal.absNorm P.asIdeal : ℕ) : E) ^ n i.1)⁻¹ * v (Fin.natAdd _ i))

theorem fin_split {N c : ℕ} (l : Fin (N + c)) :
    (∃ l' : Fin N, l = Fin.castAdd c l') ∨ ∃ i : Fin c, l = Fin.natAdd N i := by
  by_cases h : l.1 < N
  · exact Or.inl ⟨⟨l.1, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨l.1 - N, by omega⟩, Fin.ext (by simp; omega)⟩

theorem intAt_zpow (m : ℤ) (hm : 0 ≤ m) : IntAt P (qE P ^ m) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [zpow_natCast]; exact intAt_pow P (intAt_natCast P _) _

theorem intAt_scale (hp : (Ideal.absNorm P.asIdeal).Prime) {j : ℕ} {m : ℤ} (hm : -(j : ℤ) ≤ m) {a : E}
    (ha : IntAt P ((qE P ^ m)⁻¹ * a)) : IntAt P (qE P ^ j * a) := by
  have hq0 := qE_ne_zero P hp
  have h1 : qE P ^ m ≠ 0 := zpow_ne_zero m hq0
  have : qE P ^ j * a = qE P ^ ((j : ℤ) + m) * ((qE P ^ m)⁻¹ * a) := by
    rw [zpow_add₀ hq0, zpow_natCast, mul_assoc (qE P ^ j), ← mul_assoc (qE P ^ m), mul_inv_cancel₀ h1, one_mul]
  rw [this]; exact intAt_mul P (intAt_zpow P _ (by omega)) ha

theorem bdd_of_nf (hp : (Ideal.absNorm P.asIdeal).Prime) {N c j : ℕ} (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c))
    (n : ℕ → ℤ) (z : Sp E N) (hn : ∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0) (hz : z ∈ stdAt E N P)
    (hc : ∀ v, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ Crit P N c n z v) : Bdd P N c j h := by
  rw [mem_stdAt] at hz
  intro x hx
  rw [mem_lam] at hx
  constructor
  · rw [hc]
    refine ⟨fun l => intAt_sub P (hx _) (intAt_mul P ?_ (hz l)), fun i => intAt_mul P ?_ (hx _)⟩
    · unfold Loc.atN; split_ifs
      · exact hx _
      · exact intAt_zero P
    · rw [← zpow_neg]; exact intAt_zpow P _ (by have := (hn i.1).2; omega)
  · have hv : Crit P N c n z (h x) := by
      rw [← hc]; rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, mem_lam]; exact hx
    have hN : IntAt P (qE P ^ j * Loc.atN (h x) N) := by
      unfold Loc.atN; split_ifs with hN
      · have := hv.2 ⟨0, by omega⟩
        exact intAt_scale P hp (hn 0).1 this
      · simpa using intAt_zero P
    rw [mem_lam]
    intro l
    rw [Pi.smul_apply, smul_eq_mul]
    rcases fin_split l with ⟨l', rfl⟩ | ⟨i, rfl⟩
    · have e : qE P ^ j * h x (Fin.castAdd c l') = qE P ^ j * (h x (Fin.castAdd c l') - Loc.atN (h x) N * z l') +
          qE P ^ j * Loc.atN (h x) N * z l' := by ring
      rw [e]
      exact intAt_add P (intAt_mul P (intAt_pow P (intAt_natCast P _) _) (hv.1 l')) (intAt_mul P hN (hz l'))
    · exact intAt_scale P hp (hn i.1).1 (hv.2 i)

theorem prX_le_of_nf {N c : ℕ} (kj : ℕ) (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) (n : ℕ → ℤ) (z : Sp E N)
    (hc : ∀ v, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ Crit P N c n z v) :
    Loc.prX (Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h) ≤ GLint E N P := by
  rintro g ⟨r, hr, hg⟩
  have hJ := (Subgroup.mem_comap.1 hr.2).1
  have lamEq : ∀ w, w ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ w ∈ stdAt E (N + c) P := by
    intro w; rw [mem_lam, mem_stdAt]
  have hstab : ∀ v, h⁻¹ (r v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔
      h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 := by
    intro v
    have := hJ (h⁻¹ v)
    rw [lamEq, lamEq, ← this]
    simp [MulAut.conj_apply, LinearEquiv.mul_apply]
  have hX : ∀ x : Sp E N, h⁻¹ (Loc.inX E N c x) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ x ∈ stdAt E N P := by
    intro x
    rw [hc, mem_stdAt]
    have h1 : ∀ l : Fin N, Loc.inX E N c x (Fin.castAdd c l) = x l := fun l => by simp [Loc.inX]
    have h2 : ∀ i : Fin c, Loc.inX E N c x (Fin.natAdd N i) = 0 := fun i => by simp [Loc.inX]
    have h3 : Loc.atN (Loc.inX E N c x) N = 0 := by simp [Loc.atN, Loc.inX]
    simp only [Crit, h1, h2, h3, zero_mul, sub_zero, mul_zero]
    exact ⟨fun H => H.1, fun H => ⟨H, fun _ => intAt_zero P⟩⟩
  show ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P
  intro x
  rw [← hX, ← hX, ← hg x, hstab]

end PI.TwNormLat.W
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

theorem twNormLat_main : PI.TwNormLat.TwNormLat := by
  intro E _ _ _ P N c kj j hp hq h hB
  have Madd : ∀ u v : Fin (N + c) → E, h⁻¹ u ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 →
      h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 → h⁻¹ (u + v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 :=
    fun u v hu hv => by rw [map_add]; exact add_mem hu hv
  have Msmul : ∀ (t : E) (v : Fin (N + c) → E), IntAt P t → h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 →
      h⁻¹ (t • v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 := fun t v ht hv => by
    rw [map_smul, mem_lam]; rw [mem_lam] at hv
    intro l; rw [Pi.smul_apply, smul_eq_mul]; exact intAt_mul P ht (hv l)
  have Mlam : ∀ v : Fin (N + c) → E, (∀ l, IntAt P (v l)) → h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 :=
    fun v hv => (hB v ((mem_lam P N c v).2 hv)).1
  have Mbd : ∀ v : Fin (N + c) → E, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 →
      ∀ l, IntAt P (qE P ^ j * v l) := fun v hv l => by
    have := (hB _ hv).2
    rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, mem_lam] at this
    simpa [smul_eq_mul] using this l
  obtain ⟨K, b, hKj, hbM, hbl, hUT, hrep⟩ :=
    herm P (fun v => h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0)
      (Madd := Madd) (Msmul := Msmul) (Mlam := Mlam) hp hq j Mbd
  have hq0 := qE_ne_zero P hp
  have hbd : ∀ l, b l l ≠ 0 := fun l => by rw [hbl]; exact inv_ne_zero (pow_ne_zero _ hq0)
  let d : Fin (N + c) → E := fun l => if l.1 < N then 1 else qE P ^ K l
  let x1 : Fin (N + c) → E := if hN : N < N + c then d ⟨N, hN⟩ • b ⟨N, hN⟩ - Pi.single ⟨N, hN⟩ 1 else 0
  have hx1M : h⁻¹ x1 ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 := by
    by_cases hN : N < N + c
    · simp only [x1, dif_pos hN]
      rw [sub_eq_add_neg, ← neg_one_smul E (Pi.single _ _)]
      refine Madd _ _ (Msmul _ _ ?_ (hbM _)) (Msmul _ _ (intAt_neg P (intAt_one P)) (Mlam _ fun k => ?_))
      · simp only [d, lt_irrefl, if_false]; exact intAt_pow P (intAt_natCast P _) _
      · by_cases hk : k = ⟨N, hN⟩
        · rw [hk]; simpa using intAt_one P
        · simpa [Pi.single_apply, hk] using intAt_zero P
    · simp only [x1, dif_neg hN, map_zero]; exact zero_mem _
  have hx1Z : Zab N x1 := by
    intro l hl
    by_cases hN : N < N + c
    · simp only [x1, dif_pos hN, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rcases Nat.lt_or_eq_of_le hl with hlt | heq
      · rw [hUT _ l (by rw [Fin.lt_def]; exact hlt)]
        have : l ≠ ⟨N, hN⟩ := fun e => by rw [e] at hlt; exact lt_irrefl _ hlt
        simp [Pi.single_apply, this]
      · have : l = ⟨N, hN⟩ := Fin.ext heq.symm
        rw [this, hbl]
        simp only [d, lt_irrefl, if_false, Pi.single_eq_same]
        field_simp; ring
    · simp [x1, dif_neg hN]
  obtain ⟨ζ, hζ, hx1ζ⟩ := hrep x1 hx1M
  have hζZ : Zab N ζ := comb_reflect hUT hbd ζ N (by rw [← hx1ζ]; exact hx1Z)
  let c' : Fin (N + c) → Fin (N + c) → E := fun l => d l • b l - (if l.1 = N then x1 else 0)
  have hcUT : UT c' := by
    intro l k hlk
    simp only [c', Pi.sub_apply, Pi.smul_apply, hUT l k hlk, smul_zero, zero_sub, neg_eq_zero]
    split_ifs with h1
    · exact hx1Z k (by rw [Fin.lt_def] at hlk; omega)
    · rfl
  have hc1 : ∀ l : Fin (N + c), N ≤ l.1 → c' l l = 1 := by
    intro l hl
    by_cases h1 : l.1 = N
    · simp only [c', if_pos h1, d, if_neg (not_lt.2 hl), Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbl, hx1Z l hl]
      field_simp
      try simp
    · simp only [c', if_neg h1, d, if_neg (not_lt.2 hl), Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbl,
        Pi.zero_apply, sub_zero]
      field_simp
      try simp
  have hcd : ∀ l, c' l l ≠ 0 := by
    intro l
    by_cases hl : N ≤ l.1
    · rw [hc1 l hl]; exact one_ne_zero
    · have h1 : l.1 ≠ N := by omega
      simp only [c', if_neg h1, d, if_pos (not_le.1 hl), Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbl,
        Pi.zero_apply, sub_zero, one_mul]
      exact inv_ne_zero (pow_ne_zero _ hq0)
  have hca : ∀ hN : N < N + c, c' ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1 := by
    intro hN
    show d _ • b _ - (if N = N then x1 else 0) = _
    rw [if_pos rfl]
    simp only [x1, dif_pos hN]
    exact sub_sub_cancel _ _
  have hr : (combE hcUT hcd)⁻¹ ∈ Loc.R1 E N c := combinationEquiv_inv_mem_unipotentFlagGroup hcUT hcd hc1 hca
  refine ⟨(combE hcUT hcd)⁻¹, hr, 1, Subgroup.one_mem _, ?_⟩
  have hinv : ∀ v, ((combE hcUT hcd)⁻¹ * h * 1)⁻¹ v = h⁻¹ (combE hcUT hcd v) := fun v => by
    rw [mul_one, mul_inv_rev, inv_inv]; rfl
  let u : (Fin (N + c) → E) → Fin (N + c) → E := fun v l => v l * d l - Loc.atN v N * ζ l
  have hsv : ∀ v, combE hcUT hcd v = ∑ l, u v l • b l := by
    intro v
    rw [combE_apply]
    have e1 : ∀ l, v l • c' l = (v l * d l) • b l - v l • (if l.1 = N then x1 else 0) := fun l => by
      simp only [c', smul_sub, smul_smul]
    have e2 : ∑ l, v l • (if l.1 = N then x1 else 0) = Loc.atN v N • x1 := by
      by_cases hN : N < N + c
      · rw [Finset.sum_eq_single ⟨N, hN⟩]
        · simp [Loc.atN, hN]
        · intro l _ hl
          have : l.1 ≠ N := fun e => hl (Fin.ext e)
          simp [this]
        · simp
      · have hz : Loc.atN v N = 0 := by simp [Loc.atN, hN]
        rw [hz, zero_smul]
        refine Finset.sum_eq_zero fun l _ => ?_
        have : l.1 ≠ N := by have := l.2; omega
        simp [this]
    rw [Finset.sum_congr rfl (fun l _ => e1 l), Finset.sum_sub_distrib, e2, hx1ζ, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, ← sub_smul]
  let n : ℕ → ℤ := fun i => if hi : i < c then -(K (Fin.natAdd N ⟨i, hi⟩) : ℤ) else 0
  let z : Sp E N := fun l => ζ (Fin.castAdd c l)
  have hu1 : ∀ v (l : Fin N), u v (Fin.castAdd c l) = v (Fin.castAdd c l) - Loc.atN v N * z l := by
    intro v l
    simp only [u, d, z]
    rw [if_pos (show (Fin.castAdd c l).1 < N from l.2), mul_one]
  have hu2 : ∀ v (i : Fin c), u v (Fin.natAdd N i) = (qE P ^ (n i.1))⁻¹ * v (Fin.natAdd N i) := by
    intro v i
    simp only [u, d, n]
    rw [if_neg (show ¬ (Fin.natAdd N i).1 < N by simp), hζZ _ (by simp), dif_pos i.2, zpow_neg, inv_inv,
      zpow_natCast, mul_zero, sub_zero, mul_comm]
  have hU : ∀ v, (∀ l, IntAt P (u v l)) ↔ Crit P N c n z v := by
    intro v
    constructor
    · intro H
      refine ⟨fun l => ?_, fun i => ?_⟩
      · have := H (Fin.castAdd c l); rwa [hu1] at this
      · have := H (Fin.natAdd N i); rwa [hu2] at this
    · intro H l
      rcases fin_split l with ⟨l', rfl⟩ | ⟨i, rfl⟩
      · rw [hu1]; exact H.1 l'
      · rw [hu2]; exact H.2 i
  have hcrit : ∀ v, ((combE hcUT hcd)⁻¹ * h * 1)⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔
      Crit P N c n z v := by
    intro v
    rw [hinv, hsv, ← hU]
    constructor
    · intro hm
      obtain ⟨w, hw, hwe⟩ := hrep _ hm
      have hz0 : Zab 0 (u v - w) := by
        apply comb_reflect hUT hbd _ 0
        have : ∑ l, (u v - w) l • b l = 0 := by
          simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]; rw [hwe, sub_self]
        rw [this]; intro _ _; rfl
      intro l
      have := hz0 l (Nat.zero_le _)
      rw [Pi.sub_apply, sub_eq_zero] at this
      rw [this]; exact hw l
    · intro H
      exact comb_mem P _ (Madd := Madd) (Msmul := Msmul) (Mlam := Mlam) b hbM _ H
  have hn : ∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0 := by
    intro i
    simp only [n]
    split_ifs with hi
    · have := hKj (Fin.natAdd N ⟨i, hi⟩); constructor <;> omega
    · constructor <;> omega
  have hz : z ∈ stdAt E N P := (mem_stdAt P z).2 fun l => hζ _
  exact ⟨bdd_of_nf P hp _ n z hn hz hcrit, ⟨n, z, hn, hz, hcrit⟩, prX_le_of_nf P kj _ n z hcrit⟩

end PI.TwNormLat.W
end
end

theorem TwNormLat : PI.TwNormLat.TwNormLat := PI.TwNormLat.W.twNormLat_main
end

section -- merged from Formalism.LocalToGlobal.Columns.ChainTwFinal
section -- merged from Formalism.LocalToGlobal.Columns.ChainTwAux
section -- merged from Formalism.LocalToGlobal.Columns.ChainTwAll
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwAll

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {m2 : ℕ}

theorem twIdx_ok' (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hK : TwCstQ (Pr := Pr) sel mu G) (hF : TwFinQ X Pr R true) (hN : TwNormDC Ch sel mu (twCst Ch sel mu G) m2)
    (hC : TwChrQ Ch sel mu (twCst Ch sel mu G) m2) (hAn : TwAnQ Ch sel mu (twCst Ch sel mu G) m2) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 :=
  twIdx_ok hX hPr hCh h4 G hT hW hval hm hQG hd hK hF hN hC (twZeroQ_of (twCst_ok hPr hCh h4 hK)) hAn

theorem twIdx_ok'' (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0)
    (hN : TwNormDC Ch sel mu (twCst Ch sel mu G) m2) (hC : TwChrQ Ch sel mu (twCst Ch sel mu G) m2)
    (hAn : TwAnQ Ch sel mu (twCst Ch sel mu G) m2) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 :=
  twIdx_ok' hX hPr hCh h4 G hT hW hval hm hQG hd (twCstQ_of hd hz hs hxi) (finiteness_bounded_holds true) hN hC hAn

theorem twIdx_ok_full (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0)
    (hN : TwNormDC Ch sel mu (twCst Ch sel mu G) m2) (hC : TwChrQ Ch sel mu (twCst Ch sel mu G) m2) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 :=
  twIdx_ok'' hX hPr hCh h4 G hT hW hval hm hQG hd hz hs hxi hN hC
    (twAnQ_twCst hm hPr hCh h4 (twCstQ_of hd hz hs hxi) hd)

end TwAll

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwAux

theorem twNormRep {X : Fields} {Pr : Primes X} {R : Ranks} (sharp : Bool) (j : ℕ)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (hd : TwDegOne X P) (h : AutY X R j) (hb : TwBdd (Pr := Pr) j P h) :
    ∃ h', SameDC (Pr := Pr) sharp j P h h' ∧ TwBdd (Pr := Pr) j P h' ∧ TwNF (Pr := Pr) j P h' ∧
      prCat (Pr := Pr) sharp j P h' ≤ GLint X.E (R.N j) P := by
  have hL : lamYat (Pr := Pr) (R := R) j P = LocE.lamY P (qOf P) (R.N j) (cOf R j) 0 := by
    unfold lamYat; rw [if_neg hP]
  have hJ : Jat (Pr := Pr) (R := R) sharp j P = LocE.JQ P (qOf P) (R.k + j) (R.N j) (cOf R j) := by
    unfold Jat; rw [if_neg hP]
  have hb0 : PI.TwNormLat.Bdd P (R.N j) (cOf R j) j h := by
    intro x hx
    have := hb x (by rw [hL]; exact hx)
    rw [hL] at this
    exact this
  obtain ⟨r, hr, κ, hκ, hb', hnf, hpr⟩ := _root_.TwNormLat X.E P (R.N j) (cOf R j) (R.k + j) j hd.1 hd.2 h hb0
  refine ⟨r * h * κ, ⟨r, hr, κ, by rw [hJ]; exact hκ, rfl⟩, ?_, ?_, ?_⟩
  · intro x hx
    rw [hL] at hx ⊢
    exact hb' x hx
  · obtain ⟨n, z, hn, hz, hv⟩ := hnf
    refine ⟨n, z, hn, hz, fun v => ?_⟩
    rw [hL]
    exact hv v
  · unfold prCat
    rw [hJ]
    exact hpr

theorem twChrOk_one {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hpsi : ∀ x, IntAt P.1 x → cst.psi P x = 1) : TwChrOk Ch sel mu cst j P 1 := by
  have hJ : Jat (Pr := Pr) (R := R) cst.sharp j P.1 = LocE.JQ P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) := by
    unfold Jat; rw [if_neg hP]
  have hchi : ∀ r, chiInv Ch sel mu cst j P 1 r =
      PI.TwChrOne.ChiL P.1 (cst.psi P) (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + j) (R.N j) (cOf R j) 1 r := by
    intro r
    unfold chiInv lamRow
    rw [if_neg hP]
    rfl
  obtain ⟨h1, h2⟩ := _root_.TwChrOne X.E X.K P.1 (cst.psi P) (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + j) (R.N j) (cOf R j) hpsi
  refine ⟨fun r hr => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩
  · rw [hchi]
    rw [hJ] at hr
    exact h1 r hr
  · rw [hchi, hchi, hchi]
    rw [hJ] at hr hr' hr''
    exact h2 r hr r' hr' r'' hr'' hx

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def UnfoldingNonvanishingDoubleCoset (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h h' : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 h → TwBdd (Pr := Pr) (i + 1) P.1 h' →
      SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h'

def TwChrNFQ (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwNF (Pr := Pr) i P.1 hal →
    TwBdd (Pr := Pr) (i + 1) P.1 h → TwNF (Pr := Pr) (i + 1) P.1 h → prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1 →
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → TwChrOk Ch sel mu cst (i + 1) P h

variable {Ch sel mu cst}

theorem twNormDC_of {m2 : ℕ} (HE : UnfoldingNonvanishingDoubleCoset Ch sel mu cst m2) : TwNormDC Ch sel mu cst m2 := by
  intro i hi P hP hdeg hal h hbal _ hb hne
  obtain ⟨h', hs, hb', hnf, hpr⟩ := twNormRep (Pr := Pr) cst.sharp (i + 1) hP hdeg h hb
  exact ⟨h', hs, hb', hnf, hpr, HE i hi P hP hdeg hal h h' hbal hb hb' hs hne⟩

theorem twChrQ_of {m2 : ℕ} (HF : TwChrNFQ Ch sel mu cst m2) (hpsi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ x, IntAt P.1 x → cst.psi P x = 1) :
    TwChrQ Ch sel mu cst m2 :=
  ⟨HF, fun P hP _ => twChrOk_one Ch sel mu cst (m2 + 1) P hP (hpsi P hP)⟩

theorem twistedIndex_firstUnfolding_ok (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0)
    (HE : UnfoldingNonvanishingDoubleCoset Ch sel mu (twCst Ch sel mu G) m2) (HF : TwChrNFQ Ch sel mu (twCst Ch sel mu G) m2) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 :=
  twIdx_ok_full hX hPr hCh h4 G hT hW hval hm hQG hd hz hs hxi (twNormDC_of HE)
    (twChrQ_of HF fun P hP x hx => (twCst_ok hPr hCh h4 (twCstQ_of hd hz hs hxi)).psi_int P x hx)

end TwAux

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwFinal

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem characterNonvanishing_holds {G : ChGlob X R.m} {m2 : ℕ} (hm : R.m = m2 + 2) (hc : (twCst Ch sel mu G).Ok) :
    TwChrNFQ Ch sel mu (twCst Ch sel mu G) m2 := by
  intro i hi P hP hd hal h hba _ hbb _ hint hne
  exact clXQ_chrOk_holds hc hP hd (by omega) (by rw [twCst_D_Q hP]; omega) hba hbb hint hne

end TwFinal

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def toTwistedEisensteinRanks (R : Ranks) : PI.TwistedEisensteinNonvanishing.Ranks :=
  { ord := R.ord, k := R.k, m := R.m, t := R.t, k_even := R.k_even, m_even := R.m_even, t_odd := R.t_odd, two_le_m := R.two_le_m,
    m_add_three_le_k := R.m_add_three_le_k, rank_add_five_le := R.rank_add_five_le, three_m_lt_t := R.three_m_lt_t,
    m_le_f := R.m_le_f, f_le_k := R.f_le_k, m_sq_le_N := R.m_sq_le_N }

section Br

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem doubleCosetDatum_psi_ok (G : ChGlob X R.m) (P : rowSG Pr sel mu)
    (hadd : ∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * x) → IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * y) →
      twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) (x + y) = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x * twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) y)
    (hint : ∀ x : X.E, IntAt P.1 x → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x = 1) :
    PI.TwistedEisensteinNonvanishing.PsiOk (2 * (toTwistedEisensteinRanks R).m) P.1 (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)) := by
  refine ⟨fun x y hx hy => hadd x y hx hy, fun x hx => hint x hx, fun x hx => ?_⟩
  unfold twPsiQ
  rw [dite_eq_right]
  rintro ⟨b, hb, -⟩
  exact hx hb

theorem twistedMultiplier_ne_zero (G : ChGlob X R.m) (i : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) : twMuq Ch sel mu G (i + 1) P ≠ 0 := by
  unfold twMuq
  rw [if_neg hP]
  split_ifs
  · exact Units.ne_zero _
  · exact one_ne_zero

theorem squareRoot_norm_ne_zero (P : rowSG Pr sel mu) (hq : (Ideal.absNorm P.1.asIdeal).Prime) (hsq : twSqrt P.1 ^ 2 = (qOf P.1 : X.K)) :
    twSqrt (X := X) P.1 ≠ 0 := by
  intro h0
  rw [h0, zero_pow two_ne_zero] at hsq
  have : (qOf P.1 : X.K) ≠ 0 := by exact_mod_cast hq.ne_zero
  exact this hsq.symm

theorem firstUnfolding_eq_doubleCosetDatum (G : ChGlob X R.m) (i : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (A' B' : ℕ) (hal : AutY X R i) (h : AutY X R (i + 1)) :
    E1at Ch sel mu { twCst Ch sel mu G with A := A', B := B' } i P hal h =
      PI.TwistedEisensteinNonvanishing.TwistedEisensteinCoefficient (toTwistedEisensteinRanks R) P.1 (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)) (twSqrt P.1) (twMuq Ch sel mu G (i + 1) P)
        (resChar (mu : Chr X.F X.E X.K) P.1) A' B' i hal h := by
  unfold E1at omPhi muAt PhiAt
  simp only [twCst, if_neg hP]
  rfl

theorem doubleCosetDatum_hypotheses (H : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing) (G : ChGlob X R.m) {i : ℕ} (hi : i + 3 ≤ R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hq : (Ideal.absNorm P.1.asIdeal).Prime) (hu : ((Ideal.absNorm P.1.asIdeal : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hadd : ∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * x) → IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * y) →
      twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) (x + y) = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x * twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) y)
    (hint : ∀ x : X.E, IntAt P.1 x → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x = 1) (hsq : twSqrt P.1 ^ 2 = (qOf P.1 : X.K))
    (hal : AutY X R i) (h h' : AutY X R (i + 1)) (hbal : TwBdd (Pr := Pr) i P.1 hal) (hb : TwBdd (Pr := Pr) (i + 1) P.1 h)
    (hb' : TwBdd (Pr := Pr) (i + 1) P.1 h') (hdc : SameDC (Pr := Pr) true (i + 1) P.1 h h')
    (hne : FiniteSumNonzeroLargeDepth Ch sel mu (twCst Ch sel mu G) i P hal h) : FiniteSumNonzeroLargeDepth Ch sel mu (twCst Ch sel mu G) i P hal h' := by
  have hL : ∀ j, lamYat (Pr := Pr) (R := R) j P.1 = LocE.lamY P.1 (qOf P.1) (R.N j) (cOf R j) 0 := fun j => by
    unfold lamYat; rw [if_neg hP]
  have hJ : ∀ j, Jat (Pr := Pr) (R := R) true j P.1 = LocE.JQ P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) := fun j => by
    unfold Jat; rw [if_neg hP]
  have bdd : ∀ j (g : AutY X R j), TwBdd (Pr := Pr) j P.1 g → PI.TwistedEisensteinNonvanishing.BddL (toTwistedEisensteinRanks R) P.1 j g := fun j g hg x hx => by
    have := hg x (by rw [hL]; exact hx)
    rw [hL] at this
    exact this
  obtain ⟨A₀, B₀, hAB⟩ := hne
  have := H X.E X.K (toTwistedEisensteinRanks R) P.1 hq hu (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)) (twSqrt P.1) (twMuq Ch sel mu G (i + 1) P)
    (resChar (mu : Chr X.F X.E X.K) P.1) (doubleCosetDatum_psi_ok G P hadd hint) (squareRoot_norm_ne_zero P hq hsq) (twistedMultiplier_ne_zero G i P hP) i hi hal h h'
    (bdd i hal hbal) (bdd (i + 1) h hb) (bdd (i + 1) h' hb')
    (by obtain ⟨r, hr, κ, hκ, e⟩ := hdc; exact ⟨r, hr, κ, by rw [hJ] at hκ; exact hκ, e⟩)
    ⟨A₀, B₀, fun A' B' hA hB => by rw [← firstUnfolding_eq_doubleCosetDatum G i P hP]; exact hAB A' B' hA hB⟩
  obtain ⟨A₁, B₁, h1⟩ := this
  exact ⟨A₁, B₁, fun A' B' hA hB => by rw [firstUnfolding_eq_doubleCosetDatum G i P hP]; exact h1 A' B' hA hB⟩

theorem unfoldingNonvanishingDoubleCoset_holds (G : ChGlob X R.m) {m2 : ℕ} (hm : R.m = m2 + 2) (hK : TwCstQ (Pr := Pr) sel mu G) :
    UnfoldingNonvanishingDoubleCoset Ch sel mu (twCst Ch sel mu G) m2 := by
  intro i hi P hP hd hal h h' hbal hb hb' hs hne
  exact doubleCosetDatum_hypotheses _root_.TwistedEisensteinNonvanishing G (by omega) P hP hd.1 hd.2 (hK.psi_add P hP) (hK.psi_int P hP) (hK.sq_sq P hP)
    hal h h' hbal hb hb' hs hne

theorem twIdx_ok_closed (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 := by
  have hK := twCstQ_of hd hz hs hxi
  have hc := twCst_ok hPr hCh h4 hK
  exact twistedIndex_firstUnfolding_ok hX hPr hCh h4 G hT hW hval hm hQG hd hz hs hxi (unfoldingNonvanishingDoubleCoset_holds G hm hK) (characterNonvanishing_holds hm hc)

end Br

end Formalism.L2.Col
