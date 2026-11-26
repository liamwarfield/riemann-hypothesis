module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IntegralOfMemGenus
open NumberField Module
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallSum

open BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem repMass_eq_sum {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) {s : Finset (Submodule (𝓞 K) V)}
    (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) (t : K) :
    repMass h L t = ∑ M ∈ s, (repCount h M t : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
  classical
  have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨s, hsr⟩
  obtain ⟨sX, hsX, hX⟩ := StabilizerLattices.exists_pairReps hs hd hL t
  have e1 := StabilizerLattices.sum_pairs_eq_rep hs hd t hsr hsX hX
  have e2 := StabilizerLattices.sum_pairs_eq_rep hs hd t hex.choose_spec hsX hX
  simp only [repMass, dite_eq_left hex]
  rw [← e2, e1]

theorem integral_of_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {L M : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) : Formalism.HermitianLatticesTheory.IsIntegralLat h M := by
  exact Formalism.HermitianLatticesTheory.genusBasic_int (IsFractionRing.injective (𝓞 K) K)
    (fun r => Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range r) h L M hM.2 hLi

theorem exists_mem_boxSet (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M) {T : ℝ} {x : V}
    (hx : x ∈ M) (hx0 : x ≠ 0) (hxT : ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T) :
    ∃ n ∈ boxSet K F T, h x x = algebraMap F K (n : F) := by
  have hsym : star (h x x) = h x x := by
    rw [← starRingEnd_apply]
    exact hs.eq x x
  obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hMi x hx x hx)
  have hy' : star (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) K y := by rw [hy]; exact hsym
  obtain ⟨n, hn⟩ := QuadraticExtensionConjugation.exists_int_of_star_eq hF y hy'
  have hkey : h x x = algebraMap F K (n : F) := by
    rw [← hy, ← hn]
    rfl
  refine ⟨n, fun φ => ?_, hkey⟩
  rw [← hkey]
  exact ⟨hd x hx0 φ, hxT φ⟩

theorem ballCount_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M) {T : ℝ} (hT : 0 ≤ T) :
    ballCount h M T =
      1 + ∑ n ∈ (finite_boxSet hK hF T).toFinset, repCount h M (algebraMap F K (n : F)) := by
  classical
  let Fn : 𝓞 F → Finset V := fun n => (StabilizerLattices.finite_rep hd hM (algebraMap F K (n : F))).toFinset
  have hset : {x : V | x ∈ M ∧ ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T} =
      ↑(insert 0 ((finite_boxSet hK hF T).toFinset.biUnion Fn)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      Finset.mem_biUnion, Set.Finite.mem_toFinset, Fn]
    constructor
    · rintro ⟨hx, hxT⟩
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · obtain ⟨n, hn, he⟩ := exists_mem_boxSet hF hs hd hMi hx hx0 hxT
        exact Or.inr ⟨n, hn, hx, he⟩
    · rintro (rfl | ⟨n, hn, hx, he⟩)
      · exact ⟨M.zero_mem, fun φ => by simp [hT]⟩
      · exact ⟨hx, fun φ => by rw [he]; exact (hn φ).2⟩
  obtain ⟨φ0⟩ : Nonempty (K →+* ℂ) := inferInstance
  have h0 : (0 : V) ∉ (finite_boxSet hK hF T).toFinset.biUnion Fn := by
    simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, Fn, Set.mem_ofPred_eq, not_exists, not_and]
    intro n hn _ he
    have h1 := (hn φ0).1
    rw [← he] at h1
    simp at h1
  have hdisj : ∀ n ∈ (finite_boxSet hK hF T).toFinset, ∀ m ∈ (finite_boxSet hK hF T).toFinset,
      n ≠ m → Disjoint (Fn n) (Fn m) := by
    intro n _ m _ hnm
    rw [Finset.disjoint_left]
    intro x hxn hxm
    simp only [Fn, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hxn hxm
    apply hnm
    exact RingOfIntegers.ext ((algebraMap F K).injective (hxn.2.symm.trans hxm.2))
  unfold ballCount
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, hset, Set.ncard_coe_finset,
    Finset.card_insert_of_notMem h0, Finset.card_biUnion hdisj, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold repCount
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (StabilizerLattices.finite_rep hd hM _)]

private theorem repCount_zero_eq_one_of_isTotPosDef {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) (M : Submodule (𝓞 K) V) :
    repCount h M 0 = 1 := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  rw [repCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, M.zero_mem, by simp⟩, fun y => Subtype.ext ?_⟩
  by_contra hne
  have h1 := hd y.1 hne φ
  rw [y.2.2] at h1
  simp at h1

theorem sum_ballCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) {T : ℝ} (hT : 0 ≤ T) :
    ∑ M ∈ s, (ballCount h M T : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ) =
      Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F T, repMass h L (algebraMap F K (n : F)) := by
  classical
  have hmass : Formalism.HermitianLatticesTheory.mass h L = ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ := by
    have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨s, hsr⟩
    rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h L hex]
    have e1 := repMass_eq_sum hs hd hL hsr 0
    have e2 := repMass_eq_sum hs hd hL hex.choose_spec 0
    simp only [repCount_zero_eq_one_of_isTotPosDef hd, Nat.cast_one, one_div] at e1 e2
    rw [← e2, e1]
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_boxSet hK hF T), hmass]
  have hsplit : ∀ M ∈ s, (ballCount h M T : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ) =
      ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ + ∑ n ∈ (finite_boxSet hK hF T).toFinset,
        (repCount h M (algebraMap F K (n : F)) : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
    intro M hMs
    have hMg := hsr.1 M hMs
    rw [ballCount_eq hK hF hs hd hMg.1.toIsLattice (integral_of_mem_genus hs hL hLi hMg) hT]
    push_cast
    rw [add_div, one_div, Finset.sum_div]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun n _ => (repMass_eq_sum hs hd hL hsr _).symm

end Formalism.HermitianLattices.Ext.L3.BallSum
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormLeOfMemIdeal
open NumberField Module
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxCube

open BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem absNorm_le_of_mem_ideal {b : Ideal (𝓞 F)} {n : 𝓞 F} (hn : n ∈ b) (h0 : n ≠ 0) :
    (Ideal.absNorm b : ℝ) ≤ (Ideal.absNorm (Ideal.span {n}) : ℝ) := by
  have h1 : Ideal.absNorm b ∣ Ideal.absNorm (Ideal.span {n}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem b).2 hn)
  have h2 : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h0
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1

theorem absNorm_le_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {T : ℝ}
    {n : 𝓞 F} (hn : n ∈ boxSet K F T) (hb : n ∈ b) :
    (Ideal.absNorm b : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K :=
  (absNorm_le_of_mem_ideal hb (ne_zero_of_mem_boxSet hn)).trans (absNorm_le_of_mem hK hF hn)

theorem eq_of_close (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {δ : ℝ}
    (hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K ≤ (Ideal.absNorm b : ℝ)) {n n' : 𝓞 F} (hn : n ∈ b) (hn' : n' ∈ b)
    (hc : ∀ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n - rEmb w n'| < δ) : n = n' := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  by_contra hne
  have h0 : n - n' ≠ 0 := sub_ne_zero.2 hne
  have h1 := absNorm_le_of_mem_ideal (b.sub_mem hn hn') h0
  rw [absNorm_eq_prod] at h1
  have hne' : (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).Nonempty := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact ⟨⟨w, IsTotallyReal.isReal w⟩, Finset.mem_univ _⟩
  have h2 : ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w (n - n')| <
      ∏ _w : {w : InfinitePlace F // w.IsReal}, δ := by
    refine Finset.prod_lt_prod_of_nonempty₀ (fun w _ => ?_) (fun w _ => ?_) hne'
    · rw [abs_pos]
      intro h3
      apply h0
      have : (InfinitePlace.embedding_of_isReal w.2) ((n - n' : 𝓞 F) : F) = 0 := h3
      rw [map_eq_zero] at this
      exact RingOfIntegers.coe_injective (by simpa using this)
    · rw [map_sub]
      exact hc w
  rw [Finset.prod_const, Finset.card_univ, card_real hK hF] at h2
  linarith

theorem abs_sub_lt_of_floor_eq {δ a a' : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h : ⌊a / δ⌋₊ = ⌊a' / δ⌋₊) : |a - a'| < δ := by
  have h1 := Nat.floor_le (div_nonneg ha hδ.le)
  have h2 := Nat.lt_floor_add_one (a / δ)
  have h3 := Nat.floor_le (div_nonneg ha' hδ.le)
  have h4 := Nat.lt_floor_add_one (a' / δ)
  rw [h] at h1 h2
  have h5 : a / δ - a' / δ < 1 := by linarith
  have h6 : a' / δ - a / δ < 1 := by linarith
  rw [← sub_div, div_lt_one hδ] at h5 h6
  rw [abs_lt]
  constructor <;> linarith

theorem card_le_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {δ T : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K ≤ (Ideal.absNorm b : ℝ)) :
    Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} ≤ (⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K := by
  let W := {w : InfinitePlace F // w.IsReal}
  let g : {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} → (W → Fin (⌊T / δ⌋₊ + 1)) := fun n w =>
    ⟨⌊rEmb w n.1 / δ⌋₊, Nat.lt_succ_of_le (Nat.floor_le_floor
      (div_le_div_of_nonneg_right (((mem_boxSet_iff hK hF).1 n.2.1) w).2 hδ0.le))⟩
  have hg : Function.Injective g := by
    intro n n' h
    refine Subtype.ext (eq_of_close hK hF hδ n.2.2 n'.2.2 fun w => ?_)
    have h1 : ⌊rEmb w n.1 / δ⌋₊ = ⌊rEmb w n'.1 / δ⌋₊ := congrArg Fin.val (congrFun h w)
    exact abs_sub_lt_of_floor_eq hδ0 (((mem_boxSet_iff hK hF).1 n.2.1) w).1.le
      (((mem_boxSet_iff hK hF).1 n'.2.1) w).1.le h1
  have h1 := Nat.card_le_card_of_injective g hg
  have h2 : Nat.card (W → Fin (⌊T / δ⌋₊ + 1)) = (⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, card_real hK hF]
  rwa [h2] at h1

theorem fDeg_pos : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos

theorem card_box_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)}
    (hb : b ≠ ⊥) {T : ℝ} (hT0 : 0 ≤ T) :
    (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ) ≤
      2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm b : ℝ) := by
  have hf : Formalism.HermitianLatticesTheory.fDeg K ≠ 0 := (fDeg_pos (K := K)).ne'
  have hN : (0 : ℝ) < (Ideal.absNorm b : ℝ) := by
    have : Ideal.absNorm b ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.pos_of_ne_zero this
  by_cases he : IsEmpty {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b}
  · rw [Nat.card_of_isEmpty, Nat.cast_zero, ← mul_pow]
    positivity
  rw [not_isEmpty_iff] at he
  obtain ⟨n, hn, hnb⟩ := he
  have hT : 0 < T := by
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    exact (hn φ).1.trans_le (hn φ).2
  set δ : ℝ := (Ideal.absNorm b : ℝ) ^ ((Formalism.HermitianLatticesTheory.fDeg K : ℝ)⁻¹) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hN _
  have hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K = (Ideal.absNorm b : ℝ) := Real.rpow_inv_natCast_pow hN.le hf
  have hδT : δ ≤ T := by
    have := absNorm_le_pow hK hF hn hnb
    rw [← hδ] at this
    exact (pow_le_pow_iff_left₀ hδ0.le hT.le hf).1 this
  have h1 := card_le_pow hK hF (T := T) hδ0 hδ.le
  have h2 : ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T / δ := by
    have h3 := Nat.floor_le (div_nonneg hT.le hδ0.le)
    have h4 : 1 ≤ T / δ := (one_le_div hδ0).2 hδT
    push_cast
    rw [mul_div_assoc]
    linarith
  calc (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ)
      ≤ (((⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K := by push_cast; rfl
    _ ≤ (2 * T / δ) ^ Formalism.HermitianLatticesTheory.fDeg K := pow_le_pow_left₀ (by positivity) h2 _
    _ = _ := by rw [div_pow, mul_pow, hδ]

end Formalism.HermitianLattices.Ext.L3.BoxCube
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem sum_ballCount_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s)
    {T : ℝ} (hT : 0 ≤ T) :
    ∑ M ∈ s, (ballCount h M T : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ) =
      Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F T, repMass h L (algebraMap F K (n : F)) := by
  exact BallSum.sum_ballCount hK hF hs hd hL hLi hsr hT

theorem box_inter_eq_empty (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)}
    {T : ℝ} (hbT : T ^ Formalism.HermitianLatticesTheory.fDeg K < (Ideal.absNorm b : ℝ)) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b} = ∅ := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hn hb
  have := BoxCube.absNorm_le_pow hK hF hn hb
  linarith

end Formalism.HermitianLattices.Ext.L3
