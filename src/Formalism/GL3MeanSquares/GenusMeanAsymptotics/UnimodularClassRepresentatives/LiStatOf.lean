module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepRatioEqZero
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MulEqZeroIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocFSpanConsBasis

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiPin
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsTotPosDefOfSmul
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscrIdealSmulLeIff
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
theorem isIntegralLat_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (c : 𝓞 F) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (c : F) • h) L := by
  intro x hx y hy
  have h1 : algebraMap F K (c : F) ∈ (1 : Submodule (𝓞 K) K) :=
    Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 K) c, rfl⟩
  have h2 := Submodule.mul_mem_mul h1 (hLi x hx y hy)
  rw [one_mul] at h2
  exact h2

theorem akCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    akCount (algebraMap F K (c : F) • h) L 𝔭 k =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V ^ 2) * akCount h L 𝔭 (k - vF 𝔭 c) := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hL h𝔭
  obtain ⟨H, hH, _⟩ := LocF.exists_gram hLi b hbL
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.akCount_eq _ h𝔭 b hb hH', integralBasisSpans.akCount_eq h h𝔭 b hb hH, PinAA.akM_smul hK h𝔭 hc hk,
    Fintype.card_fin]

theorem nkCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (n : 𝓞 F) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V) * nkCount h L 𝔭 (k - vF 𝔭 c) n := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hL h𝔭
  obtain ⟨H, hH, _⟩ := LocF.exists_gram hLi b hbL
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.nkCount_eq _ h𝔭 b hb hH', integralBasisSpans.nkCount_eq h h𝔭 b hb hH, PinAA.nkM_smul hK h𝔭 hc n hk,
    Fintype.card_fin]

omit [NumberField K] [StarRing K] [Algebra F K] in
theorem pow_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} {j : ℕ} (hc : c ∉ 𝔭 ^ (j + 1))
    (m : ℕ) : c ^ m ∉ 𝔭 ^ (m * j + 1) := by
  induction m with
  | zero =>
    rw [pow_zero, zero_mul, zero_add, pow_one]
    exact fun e => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 e)
  | succ m ih =>
    rw [show (m + 1) * j + 1 = m * j + j + 1 by ring, pow_succ c]
    exact idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) ih hc

theorem gram_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 F) (x : Fin (finrank K V) → V) :
    (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V)) *
        (Matrix.of fun i j => h (x i) (x j)).det := by
  have e : (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)) =
      algebraMap F K (c : F) • Matrix.of fun i j => h (x i) (x j) := by
    ext i j
    rfl
  rw [e, Matrix.det_smul, Fintype.card_fin]
  congr 1
  simp only [map_pow]
  rfl

theorem discrIdeal_smul_le_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    (e : ℕ) :
    discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ (finrank K V * vF 𝔭 c + e) ↔
      discrIdeal h L ≤ extP K 𝔭 ^ e := by
  constructor
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    let d := c ^ finrank K V
    let v := finrank K V * vF 𝔭 c
    have hd : d ∉ 𝔭 ^ (v + 1) :=
      pow_notMem h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hc) (finrank K V)
    have hz : algebraMap (𝓞 F) (𝓞 K) d * z ∈ extP K 𝔭 ^ (v + e) := by
      apply hle
      exact Ideal.subset_span ⟨x, hx, by rw [gram_smul, map_mul, ez]⟩
    have hspan : extP K 𝔭 ^ v ≤
        Ideal.span {algebraMap (𝓞 F) (𝓞 K) d} ⊔ extP K 𝔭 ^ (v + e) := by
      have h := idealPowerSpanBounds.pow_le_span_sup h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hd (v + e)
      simpa only [extP, Ideal.map_pow, Ideal.map_sup, Ideal.map_span, Set.image_singleton] using
        (Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 K)) h)
    have hmul : extP K 𝔭 ^ v * Ideal.span {z} ≤ extP K 𝔭 ^ (v + e) := by
      refine (Ideal.mul_mono_left hspan).trans ?_
      rw [Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hz) Ideal.mul_le_left
    have hne : extP K 𝔭 ^ v ≠ 0 :=
      pow_ne_zero _ (idealPowerSpanBounds.map_ne_bot_of_isMaximal (K := K) h𝔭)
    have hdiv : extP K 𝔭 ^ v * extP K 𝔭 ^ e ∣ extP K 𝔭 ^ v * Ideal.span {z} := by
      rw [← pow_add]
      exact Ideal.dvd_iff_le.mpr hmul
    exact Ideal.dvd_span_singleton.mp ((mul_dvd_mul_iff_left hne).mp hdiv)
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi x hx
    have hz : z = algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) * g.det := by
      apply RingOfIntegers.coe_injective
      show algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K _
      rw [ez, gram_smul, map_mul, hdet]
    have h1 : g.det ∈ extP K 𝔭 ^ e := hle (Ideal.subset_span ⟨x, hx, hdet⟩)
    have h2 : algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) ∈ extP K 𝔭 ^ (finrank K V * vF 𝔭 c) := by
      rw [extP, ← Ideal.map_pow]
      apply Ideal.mem_map_of_mem
      rw [mul_comm, pow_mul]
      exact Ideal.pow_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 hc) _
    show z ∈ _
    rw [hz, pow_add]
    exact Ideal.mul_mem_mul h2 h1

theorem vd_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) :
    vd (algebraMap F K (c : F) • h) L 𝔭 = vd h L 𝔭 + finrank K V * vF 𝔭 c := by
  have hD : discrIdeal h L ≠ ⊥ := by
    obtain ⟨b, hbL, _⟩ := LocalSpans.exists_basis_locF hL h𝔭
    obtain ⟨g, _, hdet⟩ := LocF.exists_gram hLi b hbL
    intro hbot
    have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨b, hbL, hdet⟩
    rw [hbot, Ideal.mem_bot] at hmem
    apply LocF.gram_det_ne_zero h (LocF.aniso_of_totPosDef hd) b b.linearIndependent
    rw [← hdet, hmem, map_zero]
  have hE : extP K 𝔭 ≠ ⊤ := by
    intro e
    apply h𝔭.ne_top
    have h : Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (extP K 𝔭) = 𝔭 :=
      Ideal.comap_map_eq_self_of_faithfullyFlat 𝔭
    rw [e, Ideal.comap_top] at h
    exact h.symm
  have hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hD
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (extP K 𝔭) hE]
    refine le_iInf fun k => ?_
    obtain ⟨e, he, hke⟩ := hnb k
    exact he.trans (Ideal.pow_le_pow_right hke.le)
  have hmem : vd h L 𝔭 ∈ {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} :=
    Nat.sSup_mem ⟨0, by simp⟩ hb
  have hg : IsGreatest {e : ℕ | discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ e}
      (vd h L 𝔭 + finrank K V * vF 𝔭 c) := by
    constructor
    · rw [add_comm]
      exact (discrIdeal_smul_le_iff hLi h𝔭 hc _).2 hmem
    · intro e' he'
      by_cases hlt : e' ≤ finrank K V * vF 𝔭 c
      · omega
      · obtain ⟨e, rfl⟩ : ∃ e, e' = finrank K V * vF 𝔭 c + e := ⟨e' - finrank K V * vF 𝔭 c, by omega⟩
        have h1 : e ≤ vd h L 𝔭 := le_csSup hb ((discrIdeal_smul_le_iff hLi h𝔭 hc e).1 he')
        omega
  exact hg.csSup_eq

end Formalism.HermitianLattices.Ext.L3.PinA
end
end

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinD

section One

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [NumberField F] in
theorem star_cK (hF : IsFixF K F) (c : F) : star (algebraMap F K c) = algebraMap F K c :=
  (hF _).2 ⟨c, rfl⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K] in
theorem smul_form_apply (c : K) (h : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) : (c • h) x y = c * h x y := by
  rfl

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K]
  [NumberField F] in
theorem isSymm_of_smul (hF : IsFixF K F) {c : F} (hc : algebraMap F K c ≠ 0)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : (algebraMap F K c • h).IsSymm) : h.IsSymm := by
  refine ⟨fun x y => ?_⟩
  have hxy := hs.eq x y
  rw [smul_form_apply, smul_form_apply, map_mul] at hxy
  have hst : (starRingEnd K) (algebraMap F K c) = algebraMap F K c := star_cK hF c
  rw [hst] at hxy
  exact mul_left_cancel₀ hc hxy

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField F] in
theorem isTotPosDef_of_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {c : F}
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef (algebraMap F K c • h)) {x₀ : V}
    (h1 : h x₀ x₀ = 1) : IsTotPosDef h := by
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    simp at h1
  intro x hx φ
  have hreal : ∀ a : K, star a = a → (φ a).im = 0 := by
    intro a ha
    have := hK.2.1 φ a
    rw [ha] at this
    exact Complex.conj_eq_iff_im.1 this.symm
  have hc0 := hd x₀ hx0 φ
  rw [smul_form_apply, h1, mul_one] at hc0
  have hcx := hd x hx φ
  rw [smul_form_apply, map_mul] at hcx
  have hcr : (φ (algebraMap F K c)).im = 0 := hreal _ (star_cK hF c)
  rw [Complex.mul_re, hcr, zero_mul, sub_zero] at hcx
  exact pos_of_mul_pos_right hcx hc0.le

theorem alphaL_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) :
    alphaL (algebraMap F K (c : F) • h) L 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 1 + vF 𝔭 c ≤ k →
      (akCount (algebraMap F K (c : F) • h) L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.akCount_smul hK hF hs hd hL hLi h𝔭 hc (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := m) (by omega)]
    push_cast
    rw [show (m + vF 𝔭 c) * finrank K V ^ 2 = m * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      show 2 * vF 𝔭 c * finrank K V ^ 2 = vF 𝔭 c * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

theorem alphaN_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ≠ 0) :
    alphaN (algebraMap F K (c : F) • h) L 𝔭 (c * n) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 + vF 𝔭 c ≤ k →
      (nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) : ℝ) /
          (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) =
        (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.nkCount_smul hK hF hs hd hL hLi h𝔭 hc n (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭
        (localValuationFiltration.notMem_pow_vF h𝔭 hn) (k := m) (by omega)]
    push_cast
    have h2 : 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V - 1) + vF 𝔭 c := by
      have h3 : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
      calc 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V) := by ring
        _ = vF 𝔭 c * ((2 * finrank K V - 1) + 1) := by rw [← h3]
        _ = _ := by ring
    rw [h2, show (m + vF 𝔭 c) * (2 * finrank K V - 1) =
        m * (2 * finrank K V - 1) + vF 𝔭 c * (2 * finrank K V - 1) by ring, pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

end One

section Two

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isom_smul {c : K} (hc : c ≠ 0) (h : V →ₗ⋆[K] V →ₗ[K] K) :
    Formalism.HermitianLatticesTheory.isom (c • h) = Formalism.HermitianLatticesTheory.isom h := by
  ext g
  show (∀ x y, (c • h) (g x) (g y) = (c • h) x y) ↔ ∀ x y, h (g x) (g y) = h x y
  simp only [smul_form_apply, mul_right_inj' hc]

def unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) : VecSplit h h' where
  x₀ := S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := fun e => S.hx₀ (by rw [smul_form_apply, e, mul_zero])
  isom := fun a b => by
    have := S.isom a b
    rw [smul_form_apply, smul_form_apply] at this
    exact mul_left_cancel₀ hc this
  orth := fun a => by
    have := S.orth a
    rw [smul_form_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  cover := S.cover

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem fibLoc_unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 T = fibLoc (unscale hc S) L 𝔭 T := by
  simp only [fibLoc, isom_smul hc]
  rfl

theorem isLocReps_scale (hF : IsFixF K F) {c : 𝓞 F} (hc : algebraMap F K (c : F) ≠ 0)
    (S : VecSplit (algebraMap F K (c : F) • h) (algebraMap F K (c : F) • h'))
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')}
    (hr : IsLocReps (unscale hc S) L 𝔭 s) : IsLocReps S L 𝔭 s := by
  have hLi' := PinA.isIntegralLat_smul hLi c
  have hiso : Formalism.HermitianLatticesTheory.isom (algebraMap F K (c : F) • h') = Formalism.HermitianLatticesTheory.isom h' := isom_smul hc h'
  refine ⟨fun T hT => ?_, fun T hTl hTi hTf => ?_⟩
  · obtain ⟨h1, -, h3⟩ := hr.1 T hT
    rw [← fibLoc_unscale] at h3
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero S hL hLi' h3
    refine ⟨h1, ?_, h3⟩
    have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
    rwa [hC, h1] at this
  · rw [fibLoc_unscale hc] at hTf
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero (unscale hc S) hL hLi hTf
    have hTi' : IsIntegralAt 𝔭 h' T := by
      have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
      rwa [hC, hTl] at this
    rw [hiso]
    exact hr.2 T hTl hTi' hTf

theorem alphaL_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) :
    alphaL h L 𝔭 = alphaN h L 𝔭 1 * alphaL h' (S.cut L) 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hdim := S.finrank_add_one
  have hA := alphaL_pos hK hF hs hd hL hLi h𝔭
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 ^ (0 + 1) := by
    rw [zero_add, pow_one]; exact (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top
  have key : ∀ k, 2 * vd h L 𝔭 + 2 ≤ k → alphaN h L 𝔭 1 ≠ 0 ∧
      (akCount h' (S.cut L) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V' ^ 2) =
        alphaL h L 𝔭 / alphaN h L 𝔭 1 := by
    intro k hk
    have eA := firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := k) (by omega)
    have eB := firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 h1𝔭 (k := k) (by omega)
    have eS := PinB.akCount_split hK hF hs hd S h1 hL hLi hx h𝔭 hv (k := k) (by omega)
    rw [eS, Nat.cast_mul] at eA
    have hnk : (nkCount h L 𝔭 k 1 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_div] at eA
      linarith
    have hB : alphaN h L 𝔭 1 ≠ 0 := by
      rw [eB]; exact div_ne_zero hnk (pow_ne_zero _ hN)
    refine ⟨hB, ?_⟩
    rw [eA, eB, ← hdim]
    have e1 : k * (finrank K V' + 1) ^ 2 =
        k * (2 * (finrank K V' + 1) - 1) + k * finrank K V' ^ 2 := by
      have : 2 * (finrank K V' + 1) - 1 = 2 * finrank K V' + 1 := by omega
      rw [this]; ring
    rw [e1, pow_add]
    field_simp <;> ring
  obtain ⟨hB, -⟩ := key _ le_rfl
  have hl : alphaL h' (S.cut L) 𝔭 = alphaL h L 𝔭 / alphaN h L 𝔭 1 :=
    (tendsto_const_nhds.congr'
      (Filter.eventually_atTop.2 ⟨_, fun k hk => ((key k hk).2).symm⟩)).limUnder_eq
  rw [hl]
  field_simp

end Two

end Formalism.HermitianLattices.Ext.L3.PinD
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace PinD

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (n : 𝓞 F) (hn : n ≠ 0)
    (S : VecSplit (algebraMap F K (n : F) • h) (algebraMap F K (n : F) • h'))
    (hs' : (algebraMap F K (n : F) • h).IsSymm) (hd' : IsTotPosDef (algebraMap F K (n : F) • h))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hx : (algebraMap F K (n : F) • h) S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsFullLattice K L₀ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (n : F) • h) L₀ ∧
      repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n ≠ 0 ∧
      psiP S L₀ 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
        alphaStd K 𝔭 (finrank K V - 1) * repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero (algebraMap F K)).2 hnF
  set S₁ := unscale hc S with hS₁
  have hx1 : h S₁.x₀ S₁.x₀ = 1 := by
    have e := hx
    rw [smul_form_apply] at e
    exact mul_left_cancel₀ hc (e.trans (mul_one _).symm)
  have hs : h.IsSymm := isSymm_of_smul hF hc hs'
  have hd : IsTotPosDef h := isTotPosDef_of_smul hK hF hs hd' hx1
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 := fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have exists_full : ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsFullLattice K L₀ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧ S₁.x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
    open Cell LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans WCA in
    have aux {x₀ : V} {n : 𝓞 F} (hx : h x₀ x₀ = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n))
        (hn : n ∉ 𝔭) : ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsFullLattice K L₀ ∧
          Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧ x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
      let ι := algebraMap (𝓞 F) (𝓞 K)
      let κ := algebraMap (𝓞 K) K
      have hp := h𝔭.isPrime
      have hp0 := ne_bot h𝔭
      have han := LocF.aniso_of_totPosDef hd
      have κι_ne_zero {t : 𝓞 F} (ht : t ≠ 0) : κ (ι t) ≠ 0 := by
        intro h0
        apply ht
        have hι := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero κ).symm)
        exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (hι.trans (map_zero ι).symm)
      have hx0 : x₀ ≠ 0 := by
        rintro rfl
        rw [map_zero] at hx
        exact κι_ne_zero (ne_zero_of_notMem hn) hx.symm
      have hm : 0 < finrank K V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨x₀, hx0⟩
      obtain ⟨r, hr⟩ : ∃ r, finrank K V = r + 1 := ⟨finrank K V - 1, by omega⟩
      have symm0 {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
        have e : starRingEnd K (h x y) = h y x := by
          first
          | exact hs.eq x y
          | exact hs x y
        rw [hxy, map_zero] at e
        exact e.symm
    
      have form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (μ ν : K) (x y : V) :
          h (μ • x) (ν • y) = star μ * ν * h x y := by
        simp only [LinearMap.map_smulₛₗ₂, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply]
        ring
    
      have exists_normalise (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {h : V →ₗ⋆[K] V →ₗ[K] K}
          (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {e : V} (he : e ≠ 0) :
          ∃ μ : K, ∃ a : 𝓞 F, h (μ • e) (μ • e) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
        have hd0 : h e e ≠ 0 := fun h0 => he (han e h0)
        have hds : star (h e e) = h e e := by
          have e' : starRingEnd K (h e e) = h e e := by
            first
            | exact hs.eq e e
            | exact hs e e
          rwa [starRingEnd_apply] at e'
        obtain ⟨μ, -, hμs, a, ha, ha2⟩ := exists_scale_fixed hF h𝔭 hd0 hds
        exact ⟨μ, a, by rw [form_smul_smul, hμs, ha], ha2⟩
    
      have exists_pair (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
          {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {z e : V} {c a : 𝓞 F} (hze : h z e = 0)
          (hz : h z z = κ (ι c)) (he : h e e = κ (ι a)) (hc2 : c ∉ 𝔭 ^ 2) (ha2 : a ∉ 𝔭 ^ 2) (hcp : c ∈ 𝔭)
          (hap : a ∈ 𝔭) :
          ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧ b₂ ∉ 𝔭 ^ 2 ∧
            h w u = 0 ∧ ∀ v, h z v = 0 → h e v = 0 → h u v = 0 ∧ h w v = 0 := by
        have hez := symm0 hs hze
        obtain ⟨α, ν, hν, hW2, hW3⟩ := exists_alpha hK hF h𝔭 hcp hc2 hap ha2
        have hν' : star (κ α) * κ α = κ (ι ν) := by rw [← hν, map_mul]; rfl
        set W := c * ν + a with hW
        have hW0 : W ≠ 0 := fun h0 => hW3 (h0 ▸ zero_mem _)
        have hc0 : c ≠ 0 := fun h0 => hc2 (h0 ▸ zero_mem _)
        have ha0 : a ≠ 0 := fun h0 => ha2 (h0 ▸ zero_mem _)
        obtain ⟨μ₁, -, hμ₁s, b₁, hb₁, hb₁'⟩ := exists_scale (K := K) (r := 1) (k := 0) hF h𝔭
          (by simpa using hW2) (by simpa using hW3)
        obtain ⟨μ₂, -, hμ₂s, b₂, hb₂, hb₂'⟩ := exists_scale_int (K := K) hF h𝔭
          (mul_ne_zero (mul_ne_zero hc0 ha0) hW0)
        have hsι : ∀ t : 𝓞 F, star (κ (ι t)) = κ (ι t) := star_ι hF
        refine ⟨μ₁ • (κ α • z + e), μ₂ • ((-κ (ι a)) • z + (star (κ α) * κ (ι c)) • e), b₁, b₂,
          ?_, ?_, by simpa using hb₁', hb₂', ?_, fun v hzv hev => ⟨?_, ?_⟩⟩
        · rw [form_smul_smul, hμ₁s, ← hb₁]
          congr 1
          simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
            smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul]
          linear_combination κ (ι c) * hν'
        · rw [form_smul_smul, hμ₂s, ← hb₂]
          congr 1
          simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
            smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul, star_neg, star_star, hsι]
          linear_combination (κ (ι c) * κ (ι c) * κ (ι a)) * hν'
        · rw [form_smul_smul]
          simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
            smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, star_neg, star_mul', star_star, hsι]
          ring
        · simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
            smul_eq_mul, hzv, hev, mul_zero, add_zero]
        · simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
            smul_eq_mul, hzv, hev, mul_zero, add_zero]
    
      have κι_inj {a b : 𝓞 F} (hab : κ (ι a) = κ (ι b)) : a = b := by
        have e : ∀ c : 𝓞 F, κ (ι c) = algebraMap F K (c : F) := fun c => rfl
        rw [e, e] at hab
        exact RingOfIntegers.ext ((algebraMap F K).injective hab)
    
      have exists_family_local : ∀ r : ℕ, r + 1 ≤ finrank K V → ∃ (y : Fin r → V) (a : Fin r → 𝓞 F) (z : V) (c : 𝓞 F),
          (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ (∀ i, h z (y i) = 0) ∧
          (∀ i, h (y i) (y i) = κ (ι (a i))) ∧ h z z = κ (ι c) ∧ (∏ i, a i) ∉ 𝔭 ∧ c ∉ 𝔭 ^ 2 ∧
          (z = x₀ ∨ ∃ i, y i = x₀) := by
        have hp := h𝔭.isPrime
        intro r
        induction r with
        | zero =>
          intro _
          refine ⟨fun i => i.elim0, fun i => i.elim0, x₀, n, fun i => i.elim0, fun i => i.elim0,
            fun i => i.elim0, hx, ?_, fun hm => hn (Ideal.pow_le_self two_ne_zero hm), Or.inl rfl⟩
          rw [Finset.univ_eq_empty, Finset.prod_empty]
          exact fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
        | succ r ih =>
          intro hr
          obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ := ih (by omega)
          obtain ⟨e₀, he₀, hoe⟩ := GramDeterminantPositive.exists_ortho_ne_zero h (Fin.cons z y : Fin (r + 1) → V)
            (by omega)
          obtain ⟨μ, ae, hne, hae2⟩ := exists_normalise hF h𝔭 hs han he₀
          have hze : h z (μ • e₀) = 0 := by
            have := hoe 0
            rw [Fin.cons_zero] at this
            rw [map_smul, this, smul_zero]
          have hye : ∀ i, h (y i) (μ • e₀) = 0 := fun i => by
            have := hoe i.succ
            rw [Fin.cons_succ] at this
            rw [map_smul, this, smul_zero]
          set e := μ • e₀ with he
          have key : ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧
              b₂ ∉ 𝔭 ^ 2 ∧ h w u = 0 ∧ (∀ i, h u (y i) = 0 ∧ h w (y i) = 0) ∧
              (u = x₀ ∨ ∃ i, y i = x₀) := by
            by_cases hcp : c ∈ 𝔭
            · have hx₀' : ∃ i, y i = x₀ := by
                rcases hx₀ with rfl | h1
                · exact absurd hcp (by rw [κι_inj (hnz.symm.trans hx)]; exact hn)
                · exact h1
              by_cases hap : ae ∈ 𝔭
              · obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6⟩ :=
                  exists_pair hK hF h𝔭 hs hze hnz hne hc2 hae2 hcp hap
                exact ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5,
                  fun i => h6 _ (hzy i) (symm0 hs (hye i)), Or.inr hx₀'⟩
              · exact ⟨e, z, ae, c, hne, hnz, hap, hc2, hze,
                  fun i => ⟨symm0 hs (hye i), hzy i⟩, Or.inr hx₀'⟩
            · exact ⟨z, e, c, ae, hnz, hne, hcp, hae2, symm0 hs hze,
                fun i => ⟨hzy i, symm0 hs (hye i)⟩, hx₀⟩
          obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6, h7⟩ := key
          refine ⟨Fin.cons u y, Fin.cons b₁ a, w, b₂, ?_, ?_, ?_, h2, ?_, h4, Or.inr ?_⟩
          · intro i j
            refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
            · intro hij; exact absurd rfl hij
            · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact (h6 j).1
            · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (h6 i).1
            · intro hij
              rw [Fin.cons_succ, Fin.cons_succ]
              exact ho i j fun hh => hij (by rw [hh])
          · intro i
            refine Fin.cases ?_ (fun i => ?_) i
            · rw [Fin.cons_zero]; exact h5
            · rw [Fin.cons_succ]; exact (h6 i).2
          · intro i
            refine Fin.cases ?_ (fun i => ?_) i
            · rw [Fin.cons_zero, Fin.cons_zero]; exact h1
            · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
          · rw [Fin.prod_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            exact fun hm => (hp.mem_or_mem hm).elim h3 hprod
          · rcases h7 with rfl | ⟨i, hi⟩
            · exact ⟨0, by rw [Fin.cons_zero]⟩
            · exact ⟨i.succ, by rw [Fin.cons_succ]; exact hi⟩
      obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ :=
        exists_family_local r (by omega)
      have hof : ∀ i j, i ≠ j → h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) j) = 0 := by
        intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · intro hij; exact absurd rfl hij
        · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact hzy j
        · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (hzy i)
        · intro hij
          rw [Fin.cons_succ, Fin.cons_succ]
          exact ho i j fun hh => hij (by rw [hh])
      have hnf : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) =
          κ (ι ((Fin.cons c a : Fin (r + 1) → 𝓞 F) i)) := by
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [Fin.cons_zero, Fin.cons_zero]; exact hnz
        · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
      have hP : ∏ i, (Fin.cons c a : Fin (r + 1) → 𝓞 F) i ∉ 𝔭 ^ 2 := by
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hc2' : c ∉ 𝔭 ^ (1 + 1) := by simpa using hc2
        have hprod' : (∏ i, a i) ∉ 𝔭 ^ (0 + 1) := by simpa using hprod
        have := mul_notMem hp hp0 hc2' hprod'
        simpa using this
      have hne : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) ≠ 0 := by
        intro i
        rw [hnf]
        refine κι_ne_zero fun h0 => hP ?_
        rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
        exact zero_mem _
      obtain ⟨e, he⟩ := GramDeterminantPositive.exists_basis_of_ortho h _ hr hof hne
      refine ⟨spanO e, { toIsLattice := isLattice_spanO e, span_eq_top := ?_ },
        integral_spanO e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
          (fun i => by rw [he]; exact hnf i), ?_,
        vd_le_one_of_basis hr e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
          (fun i => by rw [he]; exact hnf i) hP⟩
      · change Submodule.span K (Submodule.span (𝓞 K) (Set.range e) : Set V) = ⊤
        rw [Submodule.span_span_of_tower, e.span_eq]
      · rcases hx₀ with rfl | ⟨i, hi⟩
        · exact Submodule.subset_span ⟨0, by rw [he, Fin.cons_zero]⟩
        · exact Submodule.subset_span ⟨i.succ, by rw [he, Fin.cons_succ, hi]⟩
    apply aux (n := 1)
    · simpa using hx1
    · exact h1𝔭
  obtain ⟨L₀, hLf, hLi, hxL, hvd⟩ := exists_full
  have hL : Submodule.IsLattice K L₀ := hLf.toIsLattice
  have hs₁' : h'.IsSymm := S₁.isSymm hs
  have hd₁' : IsTotPosDef h' := S₁.isTotPosDef hd
  have hsc' := S.isSymm hs'
  have hdc' := S.isTotPosDef hd'
  have hCf := StabilizerLattices.isFullLattice_cut S₁ hLf
  have hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h' (S₁.cut L₀) := Formalism.HermitianLattices.Ext.L3.UnimodularLocalization.isIntegralLat_cut S₁ hLi
  have hvdC : vd h' (S₁.cut L₀) 𝔭 = vd h L₀ 𝔭 := PinC.vd_cut hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭
  have hm := S₁.finrank_add_one
  have hLic := PinA.isIntegralLat_smul hLi n
  have hCic := PinA.isIntegralLat_smul hCi n
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have hb : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hb)
  have hsplit : alphaL h L₀ 𝔭 = alphaN h L₀ 𝔭 1 * alphaL h' (S₁.cut L₀) 𝔭 :=
    alphaL_split hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭 hvd
  have hαpos : 0 < alphaL h L₀ 𝔭 := alphaL_pos hK hF hs hd hLf hLi h𝔭
  have hαC : 0 < alphaL h' (S₁.cut L₀) 𝔭 := alphaL_pos hK hF hs₁' hd₁' hCf hCi h𝔭
  have hαN : alphaN h L₀ 𝔭 1 ≠ 0 := by
    intro h0
    rw [hsplit, h0, zero_mul] at hαpos
    exact lt_irrefl _ hαpos
  have hNsm : alphaN (algebraMap F K (n : F) • h) L₀ 𝔭 n =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 n * alphaN h L₀ 𝔭 1 := by
    have e := alphaN_smul hK hF hs hd hLf hLi h𝔭 hn hs' hd' (by omega) one_ne_zero
    rwa [mul_one] at e
  have hLsm := alphaL_smul hK hF hs hd hLf hLi h𝔭 hn hs' hd'
  have hvsm := PinA.vd_smul hK hF hs hd hLf hLi h𝔭 hn
  have hvT : vd (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      vd h' (S₁.cut L₀) 𝔭 + finrank K V' * vF 𝔭 n := by
    rw [vd_locF hK hF hsc' hdc' hCf.toIsLattice hCic h𝔭]
    exact PinA.vd_smul hK hF hs₁' hd₁' hCf hCi h𝔭 hn
  have hαT : alphaL (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 n * finrank K V' ^ 2) * alphaL h' (S₁.cut L₀) 𝔭 := by
    rw [← alphaL_smul hK hF hs₁' hd₁' hCf hCi h𝔭 hn hsc' hdc']
    unfold alphaL
    simp only [akCount_locF hF _ (S₁.cut L₀) 𝔭 h𝔭]
  have hrep : IsLocReps S₁ L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} :=
    PinC.isLocReps_cut hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭 hvd
  have hrep' : IsLocReps S L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} := isLocReps_scale hF hc S hL hLi h𝔭 hrep
  have hpsi : psiP S L₀ 𝔭 = lamP (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 := by
    rw [psiP_eq_sum hK hF hs' hd' S hL hLic h𝔭 hrep', Finset.sum_singleton, fibLoc_unscale hc,
      PinC.fibLoc_cut hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭 hvd]
    simp
  refine ⟨L₀, hLf, hLic, ?_, ?_⟩
  · unfold repRatio
    rw [hNsm, hLsm]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hN) (mul_ne_zero (pow_ne_zero _ hN) hαN))
      (mul_ne_zero (pow_ne_zero _ hN) hαpos.ne')
  · rw [hpsi]
    unfold lamP repRatio
    rw [hvT, hαT, hNsm, hLsm, hvsm, hsplit, hvdC, ← hm, Nat.add_sub_cancel]
    have hA := hαC.ne'
    field_simp
    ring

end PinD

theorem liPin : LIPin := by
  unfold LIPin
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S 𝔭 n hs hd h𝔭 hn hx
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero _).2 hnF
  obtain ⟨h₀, rfl⟩ : ∃ h₀ : V →ₗ⋆[K] V →ₗ[K] K, algebraMap F K (n : F) • h₀ = h :=
    ⟨(algebraMap F K (n : F))⁻¹ • h, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  obtain ⟨h₀', rfl⟩ : ∃ h₀' : V' →ₗ⋆[K] V' →ₗ[K] K, algebraMap F K (n : F) • h₀' = h' :=
    ⟨(algebraMap F K (n : F))⁻¹ • h', by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  exact PinD.core hK hF n hn S hs hd h𝔭 hx

end Formalism.HermitianLattices.Ext.L3
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem liStat_of (hR : LIRatio) (hP : LIPin) : LIStat := by
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S L 𝔭 n hs hd h𝔭 hn hx hL hLi
  obtain ⟨L₀, hL₀, hL₀i, hR0, hpin⟩ := hP K F hK hF V V' h h' S 𝔭 n hs hd h𝔭 hn hx
  have hrat := hR K F hK hF V V' h h' S L L₀ 𝔭 n hs hd h𝔭 hn hx hL hLi hL₀ hL₀i
  rw [hpin] at hrat
  have key : psiP S L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
      alphaStd K 𝔭 (finrank K V - 1) * repRatio h L 𝔭 n := by
    apply mul_right_cancel₀ hR0
    rw [hrat]
    ring
  rw [key, repRatio, Nat.mul_add, pow_add]
  ring

theorem liStat : LIStat := liStat_of liRatio liPin

end Formalism.HermitianLattices.Ext.L3
