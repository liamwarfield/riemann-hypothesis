module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairOmSumSameDatumLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFrameWeightSumSameDatumLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFrameWeightSumSameDatumLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem tsum_ite_le_sum_fibres {α β : Type*} (Q : α → Prop) (R : β → α → Prop) (f : α → ℝ≥0∞) (S : Finset β)
    [∀ a, Decidable (Q a)] [∀ p a, Decidable (R p a)]
    (h : ∀ a, Q a → ∃ p ∈ S, R p a) :
    (∑' a, if Q a then f a else 0) ≤ ∑ p ∈ S, ∑' a, if R p a then f a else 0 := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun a => ?_
  split_ifs with hq
  · obtain ⟨p, hp, hr⟩ := h a hq
    refine le_trans ?_ (Finset.single_le_sum (f := fun p => if R p a then f a else 0)
      (fun _ _ => zero_le) hp)
    simp [hr]
  · exact zero_le

theorem cf_nonneg_of_numberField (K : Type) [Field K] [NumberField K] : 0 ≤ cf K := by
  have h : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have := Real.logb_nonneg (b := 2) (by norm_num) h
  unfold cf
  linarith

theorem index_pair_bound {G D c X : ℝ} (k i b : ℕ) (hG : 0 < G) (hc : 0 ≤ c) (hX : 0 ≤ X)
    (h : G * (i : ℝ) ^ 2 * (b : ℝ) ^ 2 ≤ D) (hi : (i : ℝ) ≤ D) :
    ((i : ℝ) * b) ^ k * (i : ℝ) ^ c * X ≤ (D / G) ^ ((k : ℝ) / 2) * D ^ c * X := by
  have h0 : (0 : ℝ) ≤ (i : ℝ) * b := by positivity
  have h1 : ((i : ℝ) * b) ^ 2 ≤ D / G := by
    rw [le_div_iff₀ hG]; nlinarith
  have h2 : ((i : ℝ) * b) ^ k ≤ (D / G) ^ ((k : ℝ) / 2) := by
    calc ((i : ℝ) * b) ^ k = (((i : ℝ) * b) ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul h0, ← Real.rpow_natCast]
          congr 1; push_cast; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have h3 : (i : ℝ) ^ c ≤ D ^ c := Real.rpow_le_rpow (by positivity) hi hc
  have h4 : 0 ≤ (D / G) ^ ((k : ℝ) / 2) := le_trans (by positivity) h2
  gcongr

theorem omSum_sameDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, hG, hI, -, hGI, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hΛ
  have hG1 : (1 : ℝ) ≤ N.gI g Λ := by exact_mod_cast hG
  have hI1 : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast hI
  have hD : 1 ≤ N.Del := le_trans (by nlinarith) hGI
  have hnD : ∀ l, 0 ≤ N.nD l := fun l => by
    unfold NF.nD
    split_ifs
    · positivity
    · exact le_rfl
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => hnD l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hX : 0 ≤ (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) := by positivity
  set X := (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hXdef
  set S : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊N.Del⌋₊ ×ˢ Finset.Icc 1 ⌊N.Del⌋₊).filter
    (fun p => (N.gI g Λ : ℝ) * (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2 ≤ N.Del) with hS
  have hcard : (S.card : ℝ) ≤ N.Del ^ 2 := by
    have h1 : S.card ≤ ⌊N.Del⌋₊ * ⌊N.Del⌋₊ := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    have h2 : (⌊N.Del⌋₊ : ℝ) ≤ N.Del := Nat.floor_le (by linarith)
    calc (S.card : ℝ) ≤ (⌊N.Del⌋₊ : ℝ) * ⌊N.Del⌋₊ := by exact_mod_cast h1
      _ ≤ N.Del * N.Del := by gcongr
      _ = _ := by ring
  have hcover : ∀ Λ' : Submodule (𝓞 K) V, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' →
      ∃ p ∈ S, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2 := by
    rintro Λ' ⟨h1, h2⟩
    refine ⟨(N.iI g Λ', N.bI Λ'), ?_, h1, h2, rfl, rfl⟩
    obtain ⟨-, -, hI', hb, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ' hg h1
    have hb0 := (GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ' hg h1).1
    have hgg : N.gI g Λ' = N.gI g Λ := by
      unfold NF.gI flagPairDefinitePartLattice latLa
      rw [h2.1, h2.2.2]
    rw [hgg] at hb
    have hi1 : (1 : ℝ) ≤ N.iI g Λ' := by exact_mod_cast hI'
    have hb1 : (1 : ℝ) ≤ N.bI Λ' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
    have hi2 : (N.iI g Λ' : ℝ) ≤ (N.iI g Λ' : ℝ) ^ 2 := by nlinarith only [hi1]
    have hb2 : (N.bI Λ' : ℝ) ≤ (N.bI Λ' : ℝ) ^ 2 := by nlinarith only [hb1]
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hI', Nat.le_floor ?_⟩, Nat.one_le_iff_ne_zero.2 hb0, Nat.le_floor ?_⟩, hb⟩
    · refine le_trans ?_ hb
      calc (N.iI g Λ' : ℝ) = 1 * (N.iI g Λ' : ℝ) * 1 := by ring
        _ ≤ _ := by gcongr; linarith
    · refine le_trans ?_ hb
      calc (N.bI Λ' : ℝ) = 1 * 1 * (N.bI Λ' : ℝ) := by ring
        _ ≤ _ := by gcongr; linarith
  have hc := cf_nonneg_of_numberField K
  have hY : 0 ≤ (N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X := by
    have : 0 ≤ N.Del := by linarith
    positivity
  calc N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ')
      ≤ ∑ p ∈ S, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2) := by
        unfold NF.omSum
        exact @tsum_ite_le_sum_fibres _ _ _ _ _ S (fun _ => Classical.propDecidable _)
          (fun _ _ => Classical.propDecidable _) fun o ho => hcover _ ho
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X) := by
        refine Finset.sum_le_sum fun p hp => ?_
        refine (GlobalTheory.T.hermFramePair_omSum_same_datum_le K V H hK r N g Λ hg hΛ p.1 p.2).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        refine index_pair_bound _ _ _ (by linarith) hc hX hp.2 ?_
        exact le_trans (by exact_mod_cast hp.1.1.2) (Nat.floor_le (by linarith : 0 ≤ N.Del))
    _ = ENNReal.ofReal (S.card *
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hcard hY).trans (le_of_eq ?_))
        rw [Real.rpow_add (by linarith), Real.rpow_two]
        ring

end GlobalTheory.DegCnt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFrameWeightSumSameDatumLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFrame_weightSum_sameDatum_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegCnt.omSum_sameDat_le | exact GlobalTheory.DegCnt.omSum_sameDat_le | (intros; apply GlobalTheory.DegCnt.omSum_sameDat_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardInnerLatticesWithDefiniteTraceLeNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardInnerLatticesWithDefiniteTraceLeNorm
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.GlueZ

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem star_mem {t : K} (h : t ∈ (1 : Submodule (𝓞 K) K)) : star t ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 h
  have h1 : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) :=
    map_isIntegral_int (starRingEnd K) a.isIntegral_coe
  exact Submodule.mem_one.2 ⟨⟨_, h1⟩, rfl⟩

def Good (H : HermSpace K V) (S : Submodule K V) (z : V) (M : Submodule (𝓞 K) V) : Prop :=
  dual H M = M ∧ Submodule.span K (M : Set V) = S ∧ ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K)

variable {H : HermSpace K V} {S : Submodule K V} {z : V} {M : Submodule (𝓞 K) V}

theorem Good.z_mem (h : Good H S z M) : z ∈ M := by
  simpa using (h.2.2 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)

theorem Good.int (h : Good H S z M) {x y : V} (hx : x ∈ M) (hy : y ∈ M) :
    H.B x y ∈ (1 : Submodule (𝓞 K) K) :=
  ((mem_dual_iff H M x).1 (h.1.symm ▸ hx)).2 y hy

theorem Good.mem_S (h : Good H S z M) {x : V} (hx : x ∈ M) : x ∈ S :=
  h.2.1 ▸ Submodule.subset_span hx

theorem Good.mem_of (h : Good H S z M) {x : V} (hx : x ∈ S)
    (hB : ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ M :=
  h.1 ▸ (mem_dual_iff H M x).2 ⟨h.2.1.symm ▸ hx, hB⟩

theorem Good.exists_one (h : Good H S z M) (hz : H.B z z ≠ 0) : ∃ y ∈ M, H.B y z = 1 := by
  let J : Ideal (𝓞 K) :=
    (M.map ((H.B.flip z).restrictScalars (𝓞 K))).comap (Algebra.linearMap (𝓞 K) K)
  have hJ : ∀ a : 𝓞 K, a ∈ J ↔ ∃ y ∈ M, H.B y z = algebraMap (𝓞 K) K a := fun a => by
    simp [J]
  have hne : J ≠ ⊥ := by
    intro h0
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int h.z_mem h.z_mem)
    have : a ∈ J := (hJ a).2 ⟨z, h.z_mem, ha.symm⟩
    rw [h0, Ideal.mem_bot] at this
    exact hz (by rw [← ha, this, map_zero])
  have htop : J = ⊤ := by
    by_contra hJ1
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hne hJ1
    apply hx1
    rw [FractionalIdeal.mem_inv_iff (by simpa using hne)] at hx
    have h2 : star x • z ∈ M := by
      refine h.mem_of (S.smul_mem _ (h.mem_S h.z_mem)) fun y hy => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hy h.z_mem)
      have h3 := hx (algebraMap (𝓞 K) K a)
        (FractionalIdeal.mem_coeIdeal_of_mem _ ((hJ a).2 ⟨y, hy, ha.symm⟩))
      have h4 : x * algebraMap (𝓞 K) K a ∈ (1 : Submodule (𝓞 K) K) := by
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h3
        exact Submodule.mem_one.2 ⟨b, hb⟩
      have h5 := star_mem h4
      rw [ha, star_mul', H.herm] at h5
      simpa using h5
    have h6 := star_mem ((h.2.2 _).1 h2)
    rw [star_star] at h6
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h6
    exact (FractionalIdeal.mem_one_iff _).2 ⟨b, hb⟩
  obtain ⟨y, hy, e⟩ := (hJ 1).1 (htop ▸ Submodule.mem_top)
  exact ⟨y, hy, by rw [e, map_one]⟩

theorem Good.proj (h : Good H S z M) {y m : V} (hy : y ∈ M) (hy1 : H.B y z = 1) (hm : m ∈ M) :
    ∃ a : 𝓞 K, m - a • y ∈ M ∧ H.B (m - a • y) z = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hm h.z_mem)
  refine ⟨a, M.sub_mem hm (M.smul_mem a hy), ?_⟩
  rw [← algebraMap_smul K a y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hy1, ← ha]
  simp

theorem count (T : ℕ) (hT : T ≠ 0) (hz : H.B z z = -(T : K)) (M₁ : Submodule (𝓞 K) V) (h₁ : Good H S z M₁) :
    {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)}.encard ≤
      (T ^ Module.finrank ℚ K : ℕ) := by
  have hz0 : H.B z z ≠ 0 := by rw [hz]; simpa using hT
  obtain ⟨y₁, hy₁, e₁⟩ := h₁.exists_one hz0
  have e₁' : H.B z y₁ = 1 := by rw [← H.herm, e₁, star_one]
  set 𝓢 := {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)} with h𝓢
  have key : ∀ M : Submodule (𝓞 K) V, ∃ (y : V) (u : K) (a : 𝓞 K), M ∈ 𝓢 →
      y ∈ M ∧ H.B y z = 1 ∧ y + u • z ∈ M₁ ∧ algebraMap (𝓞 K) K a = 1 - u * T := by
    intro M
    by_cases hM : M ∈ 𝓢
    swap
    · exact ⟨0, 0, 0, fun h => absurd h hM⟩
    obtain ⟨y, hy, e⟩ := hM.1.exists_one hz0
    have hm : y + (-H.B y y₁) • z ∈ M₁ := by
      refine h₁.mem_of (S.add_mem (hM.1.mem_S hy) (S.smul_mem _ (h₁.mem_S h₁.z_mem))) fun m hm => ?_
      obtain ⟨a, ha, ha0⟩ := h₁.proj hy₁ e₁ hm
      have h2 := hM.1.int hy ((hM.2 _ ha0).2 ha)
      have h3 : H.B z (m - a • y₁) = 0 := by rw [← H.herm, ha0, star_zero]
      have h4 : m = (m - a • y₁) + (algebraMap (𝓞 K) K a) • y₁ := by rw [algebraMap_smul]; abel
      generalize m - a • y₁ = m₀ at h2 h3 h4
      rw [h4]
      simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h3, e₁',
        smul_eq_mul]
      convert h2 using 1
      ring
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h₁.int hm h₁.z_mem)
    refine ⟨y, -H.B y y₁, a, fun _ => ⟨hy, e, hm, ?_⟩⟩
    rw [ha, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, e, hz, smul_eq_mul]
    ring
  choose y u a hyu using key
  let I : Ideal (𝓞 K) := Ideal.span {(T : 𝓞 K)}
  have hle : ∀ M ∈ 𝓢, ∀ M' ∈ 𝓢, Ideal.Quotient.mk I (a M) = Ideal.Quotient.mk I (a M') → M ≤ M' := by
    intro M hM M' hM' e
    obtain ⟨p1, p2, p3, p4⟩ := hyu M hM
    obtain ⟨q1, q2, q3, q4⟩ := hyu M' hM'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e)
    have hb' : algebraMap (𝓞 K) K b = u M' - u M := by
      have := congrArg (algebraMap (𝓞 K) K) hb
      rw [map_sub, map_mul, map_natCast, p4, q4] at this
      have hT' : (T : K) ≠ 0 := by exact_mod_cast hT
      apply mul_right_cancel₀ hT'
      rw [this]; ring
    have h5 : y M - y M' ∈ M₁ := by
      have := M₁.add_mem (M₁.sub_mem p3 q3) (M₁.smul_mem b h₁.z_mem)
      rw [← algebraMap_smul K b z, hb', sub_smul] at this
      convert this using 1
      abel
    have h6 : H.B (y M - y M') z = 0 := by rw [map_sub, LinearMap.sub_apply, p2, q2, sub_self]
    have h7 : y M ∈ M' := by simpa using M'.add_mem ((hM'.2 _ h6).2 h5) q1
    intro m hm
    obtain ⟨c, hc, hc0⟩ := hM.1.proj p1 p2 hm
    simpa using M'.add_mem ((hM'.2 _ hc0).2 ((hM.2 _ hc0).1 hc)) (M'.smul_mem c h7)
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hT
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have h8 : 𝓢.encard ≤ (Set.univ : Set (𝓞 K ⧸ I)).encard :=
    Set.encard_le_encard_of_injOn (f := fun M => Ideal.Quotient.mk I (a M)) (fun _ _ => Set.mem_univ _)
      fun M hM M' hM' e => le_antisymm (hle M hM M' hM' e) (hle M' hM' M hM e.symm)
  refine h8.trans (le_of_eq ?_)
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem mem_lattice_zeroTorus {r : ℕ} (N : NF H r) (Λ : Submodule (𝓞 K) V) (y : V) (hy : H.B y N.F'.z = 0) :
    y ∈ latL N.F' N.F Λ ↔ y ∈ flagPairDefinitePartLattice N.F' N.F Λ := by
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have hc : star N.c ≠ 0 := by
    intro h0
    have := N.c_norm
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have e : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hy2 : H.B y N.F.z = 0 := by
    rw [e, LinearMap.map_smulₛₗ, smul_eq_mul] at hy
    exact (mul_eq_zero.1 hy).resolve_left hc
  have h1 : ∀ x ∈ N.F'.X ⊔ N.F.X, H.B y x = 0 := (mem_perp_iff H _ y).1 h.1
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hq
  simp [h1 p hp, hy, hy2, LinearMap.map_smulₛₗ]

end GlobalTheory.DegCnt.GlueZ

theorem GlobalTheory.DegCnt.GlueZ.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ((({L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.NT ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  have good : ∀ Λ', N.IsTerm g Λ' → GlueZ.Good H (uPerp N.F N.F') N.F'.z (latL N.F' N.F Λ') := fun Λ' h => by
    obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ' hg h
    exact ⟨h2.2, h2.1.2, h4⟩
  have hT : N.T ≠ 0 := by
    intro h0
    apply N.F'.hT
    rw [N.hT', h0, Nat.cast_zero]
  have hz : H.B N.F'.z N.F'.z = -(N.T : K) := N.hT' ▸ N.F'.zz
  have h1 := GlueZ.count N.T hT hz _ (good Λ hΛ)
  have h2 : {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧
      flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}.encard ≤ (N.T ^ Module.finrank ℚ K : ℕ) := by
    refine (Set.encard_le_encard ?_).trans h1
    rintro _ ⟨Λ', h, rfl, e⟩
    exact ⟨good Λ' h, fun y hy => by rw [GlueZ.mem_lattice_zeroTorus N Λ' y hy, GlueZ.mem_lattice_zeroTorus N Λ y hy, e]⟩
  haveI := hK.1
  have h3 : Module.finrank ℚ K = Formalism.HermitianLatticesTheory.fDeg K * 2 := by
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  refine (ENat.toENNReal_le.2 h2).trans (le_of_eq ?_)
  rw [NF.NT, ← pow_mul, ← h3, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardInnerLatticesWithDefiniteTraceLeNormStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_innerLattices_with_definite_trace_le_norm : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ((({L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.NT ^ 2) := by
  first | exact @GlobalTheory.DegCnt.GlueZ.main | exact GlobalTheory.DegCnt.GlueZ.main | (intros; apply GlobalTheory.DegCnt.GlueZ.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumWeightsInequivalentHermFrameTermsLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.FixedForm

theorem sum_le_orbit {G α ι : Type} [Group G] [MulAction G α] (Q : α → Prop) (w : α → ℝ≥0∞)
    (t : Finset ι) (x : ι → α) (hQ : ∀ i ∈ t, ∀ ρ : G, Q (ρ • x i) ∧ w (ρ • x i) = w (x i))
    (hd : ∀ i ∈ t, ∀ i' ∈ t, (∃ ρ : G, ρ • x i = x i') → i = i') :
    ∑ i ∈ t, w (x i) ≤ ∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0 := by
  let q : ι → MulAction.orbitRel.Quotient G α := fun i => Quotient.mk _ (x i)
  have hinj : ∀ i ∈ t, ∀ i' ∈ t, q i = q i' → i = i' := by
    intro i hi i' hi' h
    have h1 : (MulAction.orbitRel G α) (x i') (x i) := Quotient.exact h.symm
    rw [MulAction.orbitRel_apply] at h1
    exact hd i hi i' hi' h1
  have h1 : ∑ i ∈ t, w (x i) = ∑ o ∈ t.image q, if Q o.out then w o.out else 0 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 : (MulAction.orbitRel G α) (q i).out (x i) := Quotient.exact (Quotient.out_eq (q i))
    rw [MulAction.orbitRel_apply] at h2
    obtain ⟨ρ, hρ⟩ := h2
    have hρ' : ρ • x i = (q i).out := hρ
    rw [← hρ', if_pos (hQ i hi ρ).1, (hQ i hi ρ).2]
  rw [h1]
  exact ENNReal.sum_le_tsum _

theorem nD_nonneg {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r) (l : ℕ) :
    0 ≤ N.nD l := by
  unfold NF.nD
  split_ifs
  · positivity
  · exact le_rfl

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ₀ ι s Λ hg h0 hs hd
  set B : ℝ := (N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hB
  have hDel : 0 ≤ N.Del := nD_nonneg N _
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => nD_nonneg N l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hom := (GlobalTheory.DegAsm.WeightInf.main K V H hK r).1 N g
  let f : ι → Submodule (𝓞 K) V := fun i => latL N.F' N.F (Λ i)
  have hcard : ((s.image f).card : ℝ) ≤ N.NT ^ 2 := by
    have h1 := GlobalTheory.T.card_innerLattices_with_definite_trace_le_norm K V H hK r N g Λ₀ hg h0
    have h2 : ((s.image f : Finset _) : Set (Submodule (𝓞 K) V)) ⊆ {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ₀} := by
      intro L hL
      rw [Finset.mem_coe, Finset.mem_image] at hL
      obtain ⟨i, hi, rfl⟩ := hL
      exact ⟨Λ i, (hs i hi).1, rfl, (hs i hi).2.2.1⟩
    have h3 := (ENat.toENNReal_le.2 (Set.encard_le_encard h2)).trans h1
    rw [Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    exact h3
  have hfib : ∀ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) ≤ B := by
    intro L hL
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hL
    have h1 := GlobalTheory.T.hermFrame_weightSum_sameDatum_le K V H hK r N g (Λ i₀) hg (hs i₀ hi₀).1
    have hgI : N.gI g (Λ i₀) = N.gI g Λ₀ := by
      unfold NF.gI latLa flagPairDefinitePartLattice
      rw [(hs i₀ hi₀).2.1, (hs i₀ hi₀).2.2.2]
    rw [hgI, ← hB] at h1
    have h2 := sum_le_orbit (G := N.R) (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g (Λ i₀) Λ')
      (fun Λ' => ENNReal.ofReal (N.om Λ')) (s.filter fun i => f i = f i₀) Λ
      (by
        intro i hi ρ
        obtain ⟨hi, hfi⟩ := Finset.mem_filter.1 hi
        obtain ⟨a1, ⟨a2, a3, a4⟩, -⟩ := GlobalTheory.DegCnt.StabInv.main K V H hK r N g (Λ i) hg (hs i hi).1 ρ.1 ρ.2
        refine ⟨⟨a1, a2.trans ((hs i hi).2.1.trans (hs i₀ hi₀).2.1.symm), a3.trans hfi,
          a4.trans ((hs i hi).2.2.2.trans (hs i₀ hi₀).2.2.2.symm)⟩, ?_⟩
        exact congrArg ENNReal.ofReal ((hom (Λ i) hg (hs i hi).1).2 ρ.1 ρ.2))
      (by
        rintro i hi i' hi' ⟨ρ, hρ⟩
        exact hd i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1 ⟨ρ.1, ρ.2, hρ⟩)
    have h3 : ∑ i ∈ s with f i = f i₀, ENNReal.ofReal (N.om (Λ i)) ≤ ENNReal.ofReal B := by
      refine le_trans ?_ h1
      unfold NF.omSum
      convert h2
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi =>
      (hom (Λ i) hg (hs i (Finset.mem_filter.1 hi).1).1).1.le), ENNReal.ofReal_le_ofReal_iff hB0] at h3
    exact h3
  calc ∑ i ∈ s, N.om (Λ i) = ∑ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi) _).symm
    _ ≤ (s.image f).card • B := Finset.sum_le_card_nsmul _ _ _ hfib
    _ = ((s.image f).card : ℝ) * B := nsmul_eq_mul _ _
    _ ≤ N.NT ^ 2 * B := mul_le_mul_of_nonneg_right hcard hB0

end GlobalTheory.DegAsm.FixedForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumWeightsInequivalentHermFrameTermsLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_weights_inequivalent_hermFrameTerms_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegAsm.FixedForm.main | exact GlobalTheory.DegAsm.FixedForm.main | (intros; apply GlobalTheory.DegAsm.FixedForm.main <;> assumption)
end
