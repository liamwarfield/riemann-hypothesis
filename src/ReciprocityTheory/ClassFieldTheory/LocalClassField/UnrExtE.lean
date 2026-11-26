module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtE
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem exists_closest {M : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (x : PadicAlgCl p) :
    ∃ m0 ∈ M, ∀ m ∈ M, ‖x - m0‖ ≤ ‖x - m‖ := by
  have : ProperSpace M := FiniteDimensional.proper ℚ_[p] M
  have hc : IsCompact (Metric.closedBall (0 : M) ‖x‖) := isCompact_closedBall 0 ‖x‖
  have hcont : Continuous (fun m : M => ‖x - (m : PadicAlgCl p)‖) :=
    (continuous_const.sub continuous_subtype_val).norm
  have hne : (Metric.closedBall (0 : M) ‖x‖).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (norm_nonneg x)⟩
  obtain ⟨m0, hm0, hmin⟩ := hc.exists_isMinOn hne hcont.continuousOn
  have hmin' : ∀ m : M, m ∈ Metric.closedBall (0 : M) ‖x‖ →
      ‖x - (m0 : PadicAlgCl p)‖ ≤ ‖x - (m : PadicAlgCl p)‖ := fun m hm => hmin hm
  have hle0 : ‖x - (m0 : PadicAlgCl p)‖ ≤ ‖x‖ := by
    have h2 := hmin' 0 (Metric.mem_closedBall_self (norm_nonneg x))
    rwa [ZeroMemClass.coe_zero, sub_zero] at h2
  refine ⟨m0, m0.2, fun m hm => ?_⟩
  by_cases hmx : ‖m‖ ≤ ‖x‖
  · exact hmin' ⟨m, hm⟩ (by rw [mem_closedBall_zero_iff]; exact hmx)
  · rw [not_le] at hmx
    refine hle0.trans ?_
    by_contra hlt
    rw [not_le] at hlt
    have e : m = x - (x - m) := by ring
    have h3 : ‖m‖ ≤ max ‖x‖ ‖x - m‖ := by
      conv_lhs => rw [e]
      exact UnramifiedExtensions.norm_sub_le_max' _ _
    exact absurd (h3.trans (max_le le_rfl hlt.le)) (not_le.2 hmx)

theorem le_of_resK_le_of_norm {M L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (hML : M ≤ L) (hres : resK p L ≤ resK p M)
    (h : ∀ x ∈ L, ∃ y ∈ M, ‖x‖ = ‖y‖) : L ≤ M := by
  intro x hx
  obtain ⟨m0, hm0, hmin⟩ := exists_closest p hM x
  by_contra hxM
  have hy0 : x - m0 ≠ 0 := fun h0 => hxM (by rw [sub_eq_zero.1 h0]; exact hm0)
  have hyL : x - m0 ∈ L := L.sub_mem hx (hML hm0)
  obtain ⟨k, hk, hyk⟩ := h _ hyL
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at hyk
    exact hy0 hyk
  have hkn : 0 < ‖k‖ := norm_pos_iff.2 hk0
  have h1 : ‖(x - m0) / k‖ = 1 := by rw [norm_div, hyk, div_self hkn.ne']
  have hmem : IsLocalRing.residue (Obar p) ⟨(x - m0) / k, mem_Obar_iff.2 h1.le⟩ ∈ resK p L :=
    (mem_resK_iff p L _).2 ⟨_, L.div_mem hyL (hML hk), rfl⟩
  obtain ⟨z, hz, hzr⟩ := (mem_resK_iff p M _).1 (hres hmem)
  rw [residue_eq_iff] at hzr
  have hzr' : ‖(z : PadicAlgCl p) - (x - m0) / k‖ < 1 := hzr
  have hlt : ‖x - (m0 + k * (z : PadicAlgCl p))‖ < ‖x - m0‖ := by
    have e : x - (m0 + k * (z : PadicAlgCl p)) = -(k * ((z : PadicAlgCl p) - (x - m0) / k)) := by
      rw [mul_sub, mul_div_cancel₀ _ hk0]
      ring
    rw [e, norm_neg, norm_mul, hyk]
    calc ‖k‖ * ‖(z : PadicAlgCl p) - (x - m0) / k‖ < ‖k‖ * 1 :=
          mul_lt_mul_of_pos_left hzr' hkn
      _ = ‖k‖ := mul_one _
  exact absurd hlt (not_lt.2 (hmin _ (M.add_mem hm0 (M.mul_mem hk hz))))

theorem eq_Kn_of_norm (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hKL : K ≤ L) {n : ℕ} (hn : 0 < n)
    (hdeg : Module.finrank ℚ_[p] L = n * Module.finrank ℚ_[p] K)
    (h : ∀ x ∈ L, ∃ y ∈ K, ‖x‖ = ‖y‖) : L = Kn p K n := by
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have hL : FiniteDimensional ℚ_[p] L :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact Nat.mul_pos hn hd)
  obtain ⟨f, hf, hq, -⟩ := qK_le_pow_finrank p K hK hL hKL
  have hM : FiniteDimensional ℚ_[p] (Kn p K f) := finiteDimensional_Kn p K hK hf
  have hML : Kn p K f ≤ L := Kn_le_of_qK p K hK hL hKL (n := f) (m := 1) (by rw [mul_one]; exact hq)
  have hres : resK p L ≤ resK p (Kn p K f) := by
    have hfin : Finite (resK p L) := finite_resK p L hL
    have hsub : (resK p (Kn p K f) : Set (kbar p)) ⊆ (resK p L : Set (kbar p)) := resK_mono p hML
    have hcard : (resK p L : Set (kbar p)).ncard ≤ (resK p (Kn p K f) : Set (kbar p)).ncard := by
      have e1 : (resK p L : Set (kbar p)).ncard = qK p L := (Nat.card_coe_set_eq _).symm
      have e2 : (resK p (Kn p K f) : Set (kbar p)).ncard = qK p (Kn p K f) :=
        (Nat.card_coe_set_eq _).symm
      rw [e1, e2, hq, qK_Kn p K hK hf]
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
    intro c hc
    have : c ∈ (resK p (Kn p K f) : Set (kbar p)) := by rw [heq]; exact hc
    exact this
  have hLM : L = Kn p K f :=
    le_antisymm (le_of_resK_le_of_norm p hM hML hres
      (fun x hx => by
        obtain ⟨y, hy, hxy⟩ := h x hx
        exact ⟨y, le_Kn p K f hy, hxy⟩)) hML
  have hfn : f = n := by
    have h1 := finrank_Kn p K hK hf
    rw [← hLM, hdeg] at h1
    exact (Nat.eq_of_mul_eq_mul_right hd h1).symm
  rw [hLM, hfn]

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtD
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

namespace UnramifiedExtensions

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem qK_pow_sub_one_ne_zero (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    qK p K ^ n - 1 ≠ 0 := by
  have := Nat.one_lt_pow hn.ne' (one_lt_qK K hK)
  omega

theorem pow_apply_root {n : ℕ} {φ : GK p K}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → φ ζ = ζ ^ qK p K) (i : ℕ) :
    ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → (φ ^ i) ζ = ζ ^ (qK p K ^ i) := by
  induction i with
  | zero => intro ζ _; simp
  | succ i ih =>
    intro ζ hζ
    rw [pow_succ, AlgEquiv.mul_apply, h ζ hζ, map_pow, ih ζ hζ, ← pow_mul, pow_succ]

theorem eqOn_Kn_of_primitive {n : ℕ} (h0 : qK p K ^ n - 1 ≠ 0) {ζ₀ : PadicAlgCl p}
    (hζ₀ : IsPrimitiveRoot ζ₀ (qK p K ^ n - 1)) {σ τ : GK p K} (h : σ ζ₀ = τ ζ₀) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K n) : σ x = τ x := by
  have : NeZero (qK p K ^ n - 1) := ⟨h0⟩
  refine eqOn_Kn K (fun ζ hζ => ?_) hx
  obtain ⟨k, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  rw [map_pow, map_pow, h]

theorem pow_sub_one_dvd_iff {q : ℕ} (hq : 1 < q) {n : ℕ} (i : ℕ) :
    q ^ n - 1 ∣ q ^ i - 1 ↔ n ∣ i := by
  constructor
  · intro h
    have h1 := Nat.gcd_eq_left h
    rw [Nat.pow_sub_one_gcd_pow_sub_one] at h1
    have h2 : 1 ≤ q ^ Nat.gcd n i := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    have h4 : q ^ Nat.gcd n i = q ^ n := by omega
    have h5 := Nat.pow_right_injective (show 2 ≤ q by omega) h4
    exact Nat.gcd_eq_left_iff_dvd.1 h5
  · intro h
    exact Nat.pow_sub_one_dvd_pow_sub_one _ h

end UnramifiedExtensions

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isFrobOn_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (φ : GK p K) :
    IsFrobOn p K n φ ↔ ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → φ ζ = ζ ^ qK p K := by
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  have hq := one_lt_qK p K hK
  constructor
  · intro h ζ hζ
    by_contra hne
    have h1 := UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ
    have h2 := h ζ (mem_Kn_of_pow p K hζ) h1.le
    have h3 := norm_sub_eq_one_of_pow_eq_one p (UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn)
      (ζ := φ ζ) (ξ := ζ ^ qK p K) (by rw [← map_pow, hζ, map_one])
      (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]) hne
    rw [h3] at h2
    exact lt_irrefl _ h2
  · intro h x hx hx1
    have hex : ∃ ζ : PadicAlgCl p, φ ζ = ζ ^ qK p K ∧ ‖ζ‖ ≤ 1 ∧ ‖x - ζ‖ < 1 := by
      rcases lt_or_eq_of_le hx1 with h1 | h1
      · exact ⟨0, by rw [map_zero, zero_pow (by omega)], by simp, by simpa using h1⟩
      · obtain ⟨ζ, -, hζ, hxζ⟩ := exists_teichmuller p (Kn p K n) (finiteDimensional_Kn p K hK hn) hx h1
        rw [qK_Kn p K hK hn] at hζ
        exact ⟨ζ, h ζ hζ, (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le, hxζ⟩
    obtain ⟨ζ, h1, h2, h3⟩ := hex
    have h4 : UnramifiedExtensions.red x = UnramifiedExtensions.red ζ := (UnramifiedExtensions.red_eq_iff hx1 h2).2 h3
    have h5 : ‖φ x‖ ≤ 1 := by rw [norm_GK]; exact hx1
    have h6 : ‖x ^ qK p K‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx1
    rw [← UnramifiedExtensions.red_eq_iff h5 h6, ← UnramifiedExtensions.sigBar_red φ hx1, h4, UnramifiedExtensions.sigBar_red φ h2, h1,
      UnramifiedExtensions.red_pow h2, UnramifiedExtensions.red_pow hx1, h4]

theorem exists_isFrobOn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    ∃ φ : GK p K, IsFrobOn p K n φ := by
  classical
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  have hq := one_lt_qK p K hK
  have : NeZero (qK p K ^ n - 1) := ⟨hm0⟩
  obtain ⟨ζ₀, hζ₀⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hζ1 := hζ₀.pow_eq_one
  let E : IntermediateField K (PadicAlgCl p) := IntermediateField.extendScalars (le_Kn p K n)
  have hgal : IsGalois K E := isGalois_Kn p K hK hn
  have hfr : Module.finrank K E = n := finrank_extendScalars_Kn p K hK hn
  have hfd : FiniteDimensional K E := by
    change FiniteDimensional K (IntermediateField.extendScalars (le_Kn p K n))
    rw [extendScalars_Kn_eq_adjoin (p := p) (K := K) (n := n) hζ₀ hm0]
    exact IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hcard : Nat.card (E ≃ₐ[K] E) = n := by rw [IsGalois.card_aut_eq_finrank, hfr]
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (PadicAlgCl p)
  have hex : ∀ τ : E ≃ₐ[K] E, ∃ i : Fin n, ∃ σ : GK p K,
      AlgEquiv.restrictNormalHom E σ = τ ∧ σ ζ₀ = ζ₀ ^ (qK p K ^ (i : ℕ)) := by
    intro τ
    obtain ⟨σ, hσ⟩ := hsurj τ
    obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ1
    exact ⟨⟨i, hi⟩, σ, hσ, h⟩
  choose f g hg1 hg2 using hex
  have hinj : Function.Injective f := by
    intro τ1 τ2 h
    rw [← hg1 τ1, ← hg1 τ2]
    ext x
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
    exact UnramifiedExtensions.eqOn_Kn_of_primitive hm0 hζ₀ (by rw [hg2, hg2, h]) x.2
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_fin])
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨1 % n, Nat.mod_lt _ hn⟩
  refine ⟨g τ, (isFrobOn_iff p K hK hn _).2 ?_⟩
  have h0 : g τ ζ₀ = ζ₀ ^ qK p K := by
    rw [hg2, hτ]
    rcases Nat.lt_or_ge 1 n with h | h
    · simp only [Nat.mod_eq_of_lt h, pow_one]
    · obtain rfl : n = 1 := by omega
      have h1 := UnramifiedExtensions.pow_pow_succ_sub (q := qK p K) (n := 1) (by omega) hζ1
      simp only [Nat.mod_self, pow_zero, pow_one] at h1 ⊢
      exact h1.symm
  intro ζ hζ
  obtain ⟨k, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  rw [map_pow, h0, ← pow_mul, ← pow_mul, mul_comm]

theorem IsFrobOn.exists_pow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) (σ : GK p K) : ∃ i < n, ∀ x ∈ Kn p K n, σ x = (φ ^ i) x := by
  rw [isFrobOn_iff p K hK hn] at hφ
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  obtain ⟨ζ₀, hζ₀⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ₀.pow_eq_one
  refine ⟨i, hi, fun x hx => UnramifiedExtensions.eqOn_Kn_of_primitive hm0 hζ₀ ?_ hx⟩
  rw [h, UnramifiedExtensions.pow_apply_root hφ i ζ₀ hζ₀.pow_eq_one]

theorem IsFrobOn.pow_fixes_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) (i : ℕ) : (∀ x ∈ Kn p K n, (φ ^ i) x = x) ↔ n ∣ i := by
  rw [isFrobOn_iff p K hK hn] at hφ
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  have hq := one_lt_qK p K hK
  obtain ⟨ζ₀, hζ₀⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hζ1 := hζ₀.pow_eq_one
  have hζ0 : ζ₀ ≠ 0 := hζ₀.ne_zero hm0
  have h1 : 1 ≤ qK p K ^ i := Nat.one_le_pow _ _ (by omega)
  have key : (φ ^ i) ζ₀ = ζ₀ ↔ n ∣ i := by
    rw [UnramifiedExtensions.pow_apply_root hφ i ζ₀ hζ1, ← UnramifiedExtensions.pow_sub_one_dvd_iff hq, ← hζ₀.pow_eq_one_iff_dvd]
    have h2 : ζ₀ ^ (qK p K ^ i) = ζ₀ ^ (qK p K ^ i - 1) * ζ₀ := by
      rw [← pow_succ, Nat.sub_add_cancel h1]
    rw [h2]
    constructor
    · intro h
      exact mul_right_cancel₀ hζ0 (by rw [h, one_mul])
    · intro h
      rw [h, one_mul]
  rw [← key]
  constructor
  · intro h
    exact h ζ₀ (mem_Kn_of_pow p K hζ1)
  · intro h x hx
    exact UnramifiedExtensions.eqOn_Kn_of_primitive (τ := 1) hm0 hζ₀ h hx

theorem IsFrobOn.of_dvd (hK : FiniteDimensional ℚ_[p] K) {m n : ℕ} (h : m ∣ n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) : IsFrobOn p K m φ :=
  fun x hx hx1 => hφ x (Kn_mono p K hK h hx) hx1

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
