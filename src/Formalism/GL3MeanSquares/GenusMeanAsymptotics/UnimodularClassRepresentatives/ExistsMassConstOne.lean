module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormOneMkIff

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaStdOneNeZero
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace U3

open ExtendedPrimeIdeals EndomorphismScalars NormOneGroup

theorem absNorm_extP_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F))
    (k : ℕ) : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  rw [← absNorm_eq_card, map_pow, ThirdPropositionSlot.absNorm_extP hK hF, ← pow_mul]

theorem absNorm_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < Ideal.absNorm 𝔭 :=
  Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 (ne_bot_of_isMaximal h𝔭))

theorem akCount_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hvk : vd h L 𝔭 ≤ k) :
    akCount h L 𝔭 k = Ideal.absNorm 𝔭 ^ (2 * vd h L 𝔭) *
      normRepCount K (extP K 𝔭 ^ (k - vd h L 𝔭)) 1 1 := by
  obtain ⟨e, he⟩ := exists_isGen hL h1 h𝔭
  obtain ⟨n, hn⟩ := MeanB.exists_val hF hs hLi ⟨e, he.1⟩
  obtain ⟨hv, hv'⟩ := vd_spec hF hd h1 h𝔭 he hn
  generalize vd h L 𝔭 = v at hv hv' hvk ⊢
  have hq := absNorm_pos h𝔭
  have hfin : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := Nat.finite_of_card_ne_zero (by
    rw [absNorm_extP_pow hK hF]
    positivity)
  let π : (𝓞 K ⧸ extP K 𝔭 ^ k) →+* (𝓞 K ⧸ extP K 𝔭 ^ (k - v)) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.sub_le k v))
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have s1 : akCount h L 𝔭 k =
      Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} := by
    unfold akCount
    refine (Nat.card_congr (Equiv.subtypeEquiv
      (Equiv.ofBijective _ (endHom_bijective h𝔭 he k)) fun a => ?_)).symm
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Equiv.ofBijective_apply, endHom_mk, cond_iff hF hs hLi h𝔭 he hn hv hv' hvk b]
    exact normOne_mk_iff hF 𝔭 (k - v) b
  have s2 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (NormOne (extP K 𝔭 ^ (k - v)))
  have s3 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // True} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (fun _ => True)
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial),
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), absNorm_extP_pow hK hF,
    absNorm_extP_pow hK hF] at s3
  have s4 : Nat.card π.toAddMonoidHom.ker = Ideal.absNorm 𝔭 ^ (2 * v) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq (2 * (k - v)))
    rw [← s3, ← pow_add]
    congr 1
    omega
  rw [s1, s2, s4, card_normOne]

theorem alphaStd_one_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : alphaStd K 𝔭 1 ≠ 0 := by
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by
    have h0 := absNorm_pos h𝔭
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := mt Ideal.absNorm_eq_one_iff.1 h𝔭.ne_top
    exact_mod_cast (show 2 ≤ Ideal.absNorm 𝔭 by omega)
  have h3 : (Ideal.absNorm 𝔭 : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
  have h4 : 0 < (Ideal.absNorm 𝔭 : ℝ)⁻¹ := inv_pos.2 (by linarith)
  rw [ThirdPropositionSlot.alphaStd_one]
  unfold etaF
  split_ifs
  · nlinarith
  · nlinarith

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    alphaL h L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * alphaStd K 𝔭 1 := by
  have hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by exact_mod_cast (absNorm_pos h𝔭).ne'
  unfold alphaL
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop (vd h L 𝔭 + 1)] with k hk
  rw [akCount_eq hK hF hs hd hL hLi h1 h𝔭 (by omega), h1]
  push_cast
  rw [ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 (by omega), eq_div_iff (pow_ne_zero _ hq)]
  have e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (2 * vd h L 𝔭) * (Ideal.absNorm 𝔭 : ℝ) ^ (k - vd h L 𝔭) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (k * 1 ^ 2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    rw [one_pow, mul_one]
    omega
  linear_combination (-alphaStd K 𝔭 1) * e1

end U3

theorem localFactor_rank_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    lamP h L 𝔭 = 1 := by
  have hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by exact_mod_cast (U3.absNorm_pos h𝔭).ne'
  unfold lamP
  rw [U3.alphaL_eq hK hF hs hd hL hLi h1 h𝔭, h1, one_mul, mul_comm]
  exact div_self (mul_ne_zero (pow_ne_zero _ hq) (U3.alphaStd_one_ne_zero h𝔭))

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNeZeroOfIsLattice
open NumberField Module nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem exists_ne_zero_of_isLattice {A : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A) :
    ∃ a ∈ A, a ≠ 0 := by
  by_contra hne
  push Not at hne
  have h2 : Submodule.span K (A : Set K) = ⊥ := by
    rw [Submodule.span_eq_bot]; exact hne
  have h3 : (1 : K) ∈ Submodule.span K (A : Set K) := by
    rw [hA.span_eq_top]; exact Submodule.mem_top
  rw [h2, Submodule.mem_bot] at h3
  exact one_ne_zero h3

theorem span_eq_top_of_ne_zero {A : Submodule (𝓞 K) K} {a : K} (ha : a ∈ A) (h0 : a ≠ 0) :
    Submodule.span K (A : Set K) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = (x * a⁻¹) • a := by rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ha)

theorem isLattice_mul {A B : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A)
    (hB : Submodule.IsFullLattice K B) : Submodule.IsFullLattice K (A * B) := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  obtain ⟨b, hb, hb0⟩ := exists_ne_zero_of_isLattice hB
  have := Submodule.IsLattice.of_fg K (hA.toIsLattice.fg.mul hB.toIsLattice.fg)
  exact ⟨span_eq_top_of_ne_zero (Submodule.mul_mem_mul ha hb) (mul_ne_zero ha0 hb0)⟩

theorem exists_inv {A : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A) :
    ∃ A' : Submodule (𝓞 K) K, Submodule.IsFullLattice K A' ∧ A' * A = 1 := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨A, FractionalIdeal.isFractional_of_fg hA.toIsLattice.fg⟩
  have hI : I ≠ 0 := by
    intro h
    have h' : a ∈ (I : Submodule (𝓞 K) K) := ha
    rw [h, FractionalIdeal.coeToSubmodule_zero, Submodule.mem_bot] at h'
    exact ha0 h'
  have hmul : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * A = 1 := by
    have e := congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K))
      (inv_mul_cancel₀ hI)
    have e2 : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * (I : Submodule (𝓞 K) K) = 1 := by
      simpa only [FractionalIdeal.coeToSubmodule_mul, FractionalIdeal.coeToSubmodule_one] using e
    exact e2
  have := Submodule.IsLattice.of_fg K (FractionalIdeal.fg_of_isNoetherianRing le_rfl I⁻¹)
  refine ⟨_, ⟨?_⟩, hmul⟩
  have hne : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.bot_mul] at hmul
    have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.one_le.1 le_rfl
    rw [← hmul, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact span_eq_top_of_ne_zero hc hc0

def mulE (I J : Submodule (𝓞 K) K) (hJI : J * I = 1) :
    Submodule (𝓞 K) K ≃ Submodule (𝓞 K) K where
  toFun M := I * M
  invFun M := J * M
  left_inv M := by change J * (I * M) = M; rw [← mul_assoc, hJI, one_mul]
  right_inv M := by change I * (J * M) = M; rw [← mul_assoc, mul_comm I J, hJI, one_mul]

theorem gmap_mul (g : K ≃ₗ[K] K) (I M : Submodule (𝓞 K) K) : I * gmap g M = gmap g (I * M) := by
  have key : ∀ x y : K, g (x * y) = x * g y := fun x y => by
    simpa only [smul_eq_mul] using g.map_smul x y
  unfold gmap
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨i * m, Submodule.mul_mem_mul hi hm, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.mul_le.2 fun i hi m hm => ?_)
    rw [Submodule.mem_comap]
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
    exact Submodule.mul_mem_mul hi (Submodule.mem_map_of_mem hm)

theorem ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsMaximal) {s : 𝓞 K}
    (hs : s ∈ hcompl (K := K) p) : s ≠ 0 := by
  intro h0
  exact Formalism.HermitianLatticesTheory.genusBasic_hS (K := K) p hp s hs (by rw [h0]; exact p.zero_mem)

theorem loc_mul {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (I M : Submodule (𝓞 K) K) :
    I * loc (K := K) p M = loc (K := K) p (I * M) := by
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    have hy' : ∃ s ∈ hcompl (K := K) p, s • y ∈ M := hy
    obtain ⟨s, hs, hsy⟩ := hy'
    show ∃ s ∈ hcompl (K := K) p, s • (i * y) ∈ I * M
    refine ⟨s, hs, ?_⟩
    have e : s • (i * y) = i * (s • y) := by rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [e]
    exact Submodule.mul_mem_mul hi hsy
  · intro x hx
    have hx' : ∃ s ∈ hcompl (K := K) p, s • x ∈ I * M := hx
    obtain ⟨s, hs, hsx⟩ := hx'
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact ne_zero_of_mem_hcompl hp hs
    have hle : I * M ≤ (I * loc (K := K) p M).comap
        (LinearMap.mulLeft (𝓞 K) (algebraMap (𝓞 K) K s)⁻¹) := by
      refine Submodule.mul_le.2 fun i hi m hm => ?_
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      have e : (algebraMap (𝓞 K) K s)⁻¹ * (i * m) = i * ((algebraMap (𝓞 K) K s)⁻¹ * m) := by ring
      rw [e]
      refine Submodule.mul_mem_mul hi ?_
      show ∃ t ∈ hcompl (K := K) p, t • ((algebraMap (𝓞 K) K s)⁻¹ * m) ∈ M
      refine ⟨s, hs, ?_⟩
      rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
      exact hm
    have h2 := hle hsx
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul] at h2
    exact h2

theorem form_eq (h : K →ₗ⋆[K] K →ₗ[K] K) (x y : K) : h x y = star x * y * h 1 1 := by
  rw [show h x y = h (x • (1 : K)) (y • (1 : K)) by simp only [smul_eq_mul, mul_one],
    LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply]
  simp only [smul_eq_mul]
  ring

theorem mem_isom_iff {h : K →ₗ⋆[K] K →ₗ[K] K} (h1 : h 1 1 ≠ 0) (g : K ≃ₗ[K] K) :
    g ∈ isom h ↔ star (g 1) * g 1 = 1 := by
  have hg : ∀ x, g x = x * g 1 := fun x => by
    rw [show g x = g (x • (1 : K)) by rw [smul_eq_mul, mul_one], LinearEquiv.map_smul, smul_eq_mul]
  constructor
  · intro hm
    have hm' : ∀ x y, h (g x) (g y) = h x y := hm
    have e := hm' 1 1
    rw [form_eq h (g 1) (g 1)] at e
    exact mul_right_cancel₀ h1 (by rw [one_mul]; exact e)
  · intro he
    show ∀ x y, h (g x) (g y) = h x y
    intro x y
    rw [form_eq h (g x) (g y), form_eq h x y, hg x, hg y, star_mul']
    calc star x * star (g 1) * (y * g 1) * h 1 1 = star x * y * (star (g 1) * g 1) * h 1 1 := by ring
      _ = star x * y * h 1 1 := by rw [he, mul_one]

theorem mass_eq_of_lattices {h₁ h₂ : K →ₗ⋆[K] K →ₗ[K] K} (hn₁ : h₁ 1 1 ≠ 0) (hn₂ : h₂ 1 1 ≠ 0)
    {A B : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A) (hB : Submodule.IsFullLattice K B)
    (hex : ∃ s, IsClassReps h₁ A s) : mass h₂ B = mass h₁ A := by
  obtain ⟨A', hA', hA'A⟩ := exists_inv hA
  obtain ⟨B', hB', hB'B⟩ := exists_inv hB
  have hJC : (A * B') * (B * A') = 1 := by
    calc (A * B') * (B * A') = (A' * A) * (B' * B) := by ring
      _ = 1 := by rw [hA'A, hB'B, one_mul]
  have t1 : ∀ g : K ≃ₗ[K] K, (Equiv.refl (K ≃ₗ[K] K)) g ∈ isom h₂ ↔ g ∈ isom h₁ := fun g => by
    rw [Equiv.refl_apply, mem_isom_iff hn₂, mem_isom_iff hn₁]
  have t2 : ∀ (g : K ≃ₗ[K] K) (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (gmap g M) =
        gmap ((Equiv.refl (K ≃ₗ[K] K)) g) (mulE (B * A') (A * B') hJC M) := fun g M =>
    gmap_mul g (B * A') M
  have t3 : ∀ (p : Ideal (𝓞 K)), p.IsMaximal → ∀ (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (loc p M) = loc p (mulE (B * A') (A * B') hJC M) :=
    fun p hp M => loc_mul hp (B * A') M
  have t4 : ∀ (M : Submodule (𝓞 K) K),
      Submodule.IsFullLattice K (mulE (B * A') (A * B') hJC M) ↔ Submodule.IsFullLattice K M := by
    intro M
    change Submodule.IsFullLattice K (B * A' * M) ↔ Submodule.IsFullLattice K M
    constructor
    · intro hM
      have e := isLattice_mul (isLattice_mul hA hB') hM
      rwa [← mul_assoc, hJC, one_mul] at e
    · intro hM
      exact isLattice_mul (isLattice_mul hB hA') hM
  have hΦA : mulE (B * A') (A * B') hJC A = B := by
    show B * A' * A = B
    rw [mul_assoc, hA'A, mul_one]
  have he := (mass_transfer (mulE (B * A') (A * B') hJC) (Equiv.refl _) t1 t2 t3 t4 hex).2
  rw [hΦA] at he
  exact he

end Formalism.HermitianLattices.Ext.L3.RankOne
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (x := h x x)
  have hre : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hd x hx σ.toRingHom) Finset.univ_nonempty
  exact_mod_cast hre ▸ hpos

theorem exists_model [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (h1 : finrank K V = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) :
    ∃ (h' : K →ₗ⋆[K] K →ₗ[K] K) (A : Submodule (𝓞 K) K), h' 1 1 ≠ 0 ∧ Submodule.IsFullLattice K A ∧
      (∃ s, IsClassReps h' A s) ∧ mass h' A = mass h L := by
  let b := Module.finBasisOfFinrankEq K V h1
  let φ : V ≃ₗ[K] K := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)
  let h' : K →ₗ⋆[K] K →ₗ[K] K := (h.comp φ.symm.toLinearMap).compl₂ φ.symm.toLinearMap
  have hh' : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    simp [h']
  have htr := trace_pos hd
  obtain ⟨hex, -, -⟩ := Formalism.HermitianLatticesTheory.massBasic K V h hs htr L hL
  obtain ⟨hex', hm⟩ := mass_mapE φ hh' hex
  refine ⟨h', mapE φ L, ?_, isFullLattice_mapE φ hL, hex', hm⟩
  have h0 : φ.symm 1 ≠ 0 := by simp
  intro hz
  have := htr _ h0
  have hz' : h (φ.symm 1) (φ.symm 1) = 0 := by simpa [h'] using hz
  rw [hz', map_zero] at this
  exact lt_irrefl _ this

end RankOne

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_massConst_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := by
  obtain ⟨h₀, hh⟩ : ∃ h₀ : K →ₗ⋆[K] K →ₗ[K] K, ∀ x y, h₀ x y = star x * y :=
    ⟨LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
      (fun x y z => by simp [add_mul]) (fun a x y => by simp [smul_eq_mul, mul_assoc, starRingEnd_apply])
      (fun x y z => by simp [mul_add]) (fun a x y => by simp [smul_eq_mul, mul_left_comm]),
      fun _ _ => rfl⟩
  have hs₀ : h₀.IsSymm := by
    first
      | (intro x y; simp [hh, starRingEnd_apply, mul_comm])
      | (constructor; intro x y; simp [hh, starRingEnd_apply, mul_comm])
  have hd₀ : IsTotPosDef h₀ := by
    intro x hx φ
    have hx' : φ x ≠ 0 := (map_ne_zero φ).mpr hx
    have : φ (h₀ x x) = ((Complex.normSq (φ x) : ℝ) : ℂ) := by
      rw [hh, map_mul, hK.2.1 φ x, Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hx'
  have hn₀ : h₀ 1 1 ≠ 0 := by simp [hh]
  set L₀ : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
  have hL₀ : Submodule.IsFullLattice K L₀ :=
    { toIsLattice := Submodule.IsLattice.of_fg K (Submodule.fg_span_singleton _)
      span_eq_top := RankOne.span_eq_top_of_ne_zero (Submodule.subset_span rfl) one_ne_zero }
  obtain ⟨hex₀, -, hpos₀⟩ := Formalism.HermitianLatticesTheory.massBasic K K h₀ hs₀
    (RankOne.trace_pos hd₀) L₀ hL₀
  refine ⟨Formalism.HermitianLatticesTheory.mass h₀ L₀, hpos₀, ?_⟩
  intro V _ _ _ _ _ h L hs hd h1 hL hLi
  obtain ⟨h', A, hn', hA, -, hm⟩ := RankOne.exists_model hs hd h1 hL
  have hlam : lamG F h L = 1 := by
    unfold lamG
    exact (tprod_congr fun p => localFactor_rank_one hK hF hs hd hL hLi h1 p.2).trans tprod_one
  rw [hlam, mul_one, ← hm]
  exact RankOne.mass_eq_of_lattices hn₀ hn' hL₀ hA hex₀

end Formalism.HermitianLattices.Ext.L3
