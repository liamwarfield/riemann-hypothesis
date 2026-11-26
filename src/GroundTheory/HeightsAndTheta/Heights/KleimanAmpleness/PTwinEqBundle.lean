module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqBundleLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open scoped Pointwise

variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]

section Local

variable (A : Subalgebra S Ω) {k : ℕ} (f c : Fin k → Ω)

theorem exists_sum_mul_pow_eq_one (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1)
    (n : ℕ) : ∃ d : Fin k → Ω, (∀ l, d l ∈ A) ∧ ∑ l, d l * f l ^ n = 1 := by
  let f' : Fin k → A := fun l => ⟨f l, hf l⟩
  have htop : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.span, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun l => ⟨c l, hc l⟩, Subtype.ext ?_⟩
    simpa [f'] using hs
  have h1 := Ideal.span_pow_eq_top _ htop n
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.span, Submodule.mem_span_range_iff_exists_fun] at h1
  obtain ⟨d, hd⟩ := h1
  refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
  have := congrArg Subtype.val hd
  simpa [f'] using this

theorem mem_of_forall_pow_mul_mem (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1)
    (P : Submodule A Ω) {z : Ω} (hz : ∀ l, ∃ m : ℕ, f l ^ m * z ∈ P) : z ∈ P := by
  choose m hm using hz
  obtain ⟨d, hd, hsum⟩ := exists_sum_mul_pow_eq_one A f c hf hc hs (Finset.univ.sup m)
  have key : z = ∑ l, (⟨d l * f l ^ (Finset.univ.sup m - m l), mul_mem (hd l) (pow_mem (hf l) _)⟩ : A) •
      (f l ^ m l * z) := by
    simp only [Subalgebra.smul_def, smul_eq_mul]
    calc z = (∑ l, d l * f l ^ Finset.univ.sup m) * z := by rw [hsum, one_mul]
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← pow_sub_mul_pow (f l) (Finset.le_sup (Finset.mem_univ l))]
        ring
  rw [key]
  exact sum_mem fun l _ => P.smul_mem _ (hm l)

theorem fg_and_invertible_of_frame (L : Submodule A Ω) (b : Fin k → Ω)
    (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1) (hb : ∀ l, b l ≠ 0)
    (hL : ∀ l e, (∃ n : ℕ, f l ^ n * e ∈ L) ↔ ∃ a : Ω, (∃ n : ℕ, f l ^ n * a ∈ A) ∧ e = a * b l) :
    L.FG ∧ ∃ L' : Submodule A Ω, L * L' = 1 := by
  have hgen : ∀ l, ∃ n : ℕ, f l ^ n * b l ∈ L := fun l =>
    (hL l (b l)).2 ⟨1, ⟨0, by rw [pow_zero, one_mul]; exact one_mem A⟩, (one_mul _).symm⟩
  choose n hn using hgen
  set g : Fin k → Ω := fun l => f l ^ n l * b l with hg
  have hloc : ∀ l, ∀ e ∈ L, ∃ a : Ω, (∃ m : ℕ, f l ^ m * a ∈ A) ∧ e = a * b l := fun l e he =>
    (hL l e).1 ⟨0, by rw [pow_zero, one_mul]; exact he⟩
  have hLG : L = Submodule.span A (Set.range g) := by
    apply le_antisymm
    · intro e he
      apply mem_of_forall_pow_mul_mem A f c hf hc hs
      intro l
      obtain ⟨a, ⟨m, hm⟩, rfl⟩ := hloc l e he
      refine ⟨m + n l, ?_⟩
      have : f l ^ (m + n l) * (a * b l) = (⟨f l ^ m * a, hm⟩ : A) • g l := by
        rw [Subalgebra.smul_def, smul_eq_mul, hg]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hn l
  refine ⟨hLG ▸ Submodule.fg_span (Set.finite_range g), 1 / L, le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro p hp q hq
    rw [mul_comm]
    exact (Submodule.mem_div_iff_forall_mul_mem.1 hq) p hp
  · rw [Submodule.one_le]
    apply mem_of_forall_pow_mul_mem A f c hf hc hs
    intro l
    have hbd : ∀ s, ∃ m : ℕ, f l ^ m * (g s / b l) ∈ A := by
      intro s
      obtain ⟨a, ⟨m, hm⟩, hgs⟩ := hloc l (g s) (hn s)
      refine ⟨m, ?_⟩
      rw [hgs, mul_div_assoc, div_self (hb l), mul_one]
      exact hm
    choose M hM using hbd
    set K := Finset.univ.sup M with hK
    have hy : f l ^ K / b l ∈ 1 / L := by
      rw [Submodule.mem_div_iff_forall_mul_mem]
      intro e he
      rw [hLG] at he
      induction he using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨s, rfl⟩ := hz
        rw [Submodule.mem_one]
        refine ⟨⟨f l ^ (K - M s) * (f l ^ M s * (g s / b l)), mul_mem (pow_mem (hf l) _) (hM s)⟩, ?_⟩
        change f l ^ (K - M s) * (f l ^ M s * (g s / b l)) = f l ^ K / b l * g s
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ s))]
        ring
      | zero => rw [mul_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
      | smul a u _ hu =>
        have : f l ^ K / b l * (a • u) = a • (f l ^ K / b l * u) := by
          rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul]
          ring
        rw [this]
        exact Submodule.smul_mem _ a hu
    refine ⟨n l + K, ?_⟩
    have : f l ^ (n l + K) * 1 = g l * (f l ^ K / b l) := by
      rw [hg, mul_one, pow_add]
      field_simp [hb l]
    rw [this]
    exact Submodule.mul_mem_mul (hn l) hy

end Local

section Lift

variable {A B : Subalgebra S Ω}

theorem span_span_of_le (hAB : A ≤ B) (T : Set Ω) :
    Submodule.span B (Submodule.span A T : Set Ω) = Submodule.span B T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul a u _ hu => exact Submodule.smul_mem _ (⟨a, hAB a.2⟩ : B) hu
  · exact Submodule.span_mono Submodule.subset_span

theorem fg_span_of_le (hAB : A ≤ B) {L : Submodule A Ω} (hL : L.FG) :
    (Submodule.span B (L : Set Ω)).FG := by
  obtain ⟨T, rfl⟩ := hL
  rw [span_span_of_le hAB]
  exact Submodule.fg_span T.finite_toSet

theorem mul_span_eq_one_of_le (hAB : A ≤ B) {L L' : Submodule A Ω} (h : L * L' = 1) :
    Submodule.span B (L : Set Ω) * Submodule.span B (L' : Set Ω) = 1 := by
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, hp, q, hq, rfl⟩
    have hpq : p * q ∈ L * L' := Submodule.mul_mem_mul hp hq
    rw [h, Submodule.mem_one] at hpq
    obtain ⟨a, ha⟩ := hpq
    exact Submodule.mem_one.2 ⟨⟨a, hAB a.2⟩, ha⟩
  · rw [Submodule.one_le]
    have h1 : (1 : Ω) ∈ L * L' := h ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
    rw [Submodule.mul_eq_span_mul_set] at h1
    exact (span_span_of_le hAB ((L : Set Ω) * (L' : Set Ω))).le (Submodule.subset_span h1)

end Lift

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

noncomputable section

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem div_mem_chartRing_of_mem (I : Kleiman.Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1)
    (j : Fin (N + 1)) : x j / x i ∈ Kleiman.chartRing S x I :=
  ⟨X j, X i, 1, Kleiman.X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩

section First

variable (Q : Kleiman.LineBundle S x)

end First

section Second

variable (Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x)

def latSub {i : Fin (N + 1)} (h : x i ≠ 0) :
    Submodule (Kleiman.chartRing S x (Kleiman.singleChart h)) Ω where
  carrier := Q'.lat i
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a e he := Q'.stable i a (by rw [chartRing.equiv S x h]; exact a.2) e he

theorem coe_latSub {i : Fin (N + 1)} (h : x i ≠ 0) : (latSub Q' h : Set Ω) = (Q'.lat i : Set Ω) := rfl

def subOf (I : Kleiman.Chart x) : Submodule (Kleiman.chartRing S x I) Ω :=
  Submodule.span _ (⋃ i ∈ I.1, (Q'.lat i : Set Ω))

theorem subOf_eq {I : Kleiman.Chart x} {i : Fin (N + 1)} (hi : i ∈ I.1) :
    subOf Q' I = Submodule.span _ (Q'.lat i : Set Ω) := by
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  apply le_antisymm
  · rw [subOf, Submodule.span_le]
    intro e he
    obtain ⟨j, hj, he⟩ := Set.mem_iUnion₂.1 he
    have hxj : x j ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hj)
    obtain ⟨m, hm⟩ := Q'.overlap j i hxj hxi e he
    have hr : (x i / x j) ^ m ∈ Kleiman.chartRing S x I := pow_mem (div_mem_chartRing_of_mem I hj i) m
    have hc : x i / x j * (x j / x i) = 1 := by field_simp
    have key : e = (⟨_, hr⟩ : Kleiman.chartRing S x I) • ((x j / x i) ^ m • e) := by
      rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_pow, hc, one_pow, one_mul]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
  · exact Submodule.span_mono fun e he => Set.mem_iUnion₂.2 ⟨i, hi, he⟩

theorem subOf_mono (I J : Kleiman.Chart x) (h : I.1 ⊆ J.1) (y : Ω) (hy : y ∈ subOf Q' I) :
    y ∈ subOf Q' J := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.1 hz
    exact Submodule.subset_span (Set.mem_iUnion₂.2 ⟨i, h hi, hz⟩)
  | zero => exact zero_mem _
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul a z _ hz => exact Submodule.smul_mem _ (Kleiman.chartIncl h a) hz

theorem subOf_mem_iff (I J : Kleiman.Chart x) (h : I.1 ⊆ J.1) (y : Ω) :
    y ∈ subOf Q' J ↔
      ∃ a : Kleiman.chartRing S x I, IsUnit (Kleiman.chartIncl h a) ∧ (a : Ω) • y ∈ subOf Q' I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, hj, hz⟩ := Set.mem_iUnion₂.1 hz
      have hxj : x j ≠ 0 := (Kleiman.mem_support x).1 (J.2.2 hj)
      obtain ⟨m, hm⟩ := Q'.overlap j i hxj hxi z hz
      refine ⟨⟨(x j / x i) ^ m, pow_mem (div_mem_chartRing_of_mem I hi j) m⟩, ?_, ?_⟩
      · rw [isUnit_iff_exists_inv]
        refine ⟨⟨(x i / x j) ^ m, pow_mem (div_mem_chartRing_of_mem J hj i) m⟩, Subtype.ext ?_⟩
        change (x j / x i) ^ m * (x i / x j) ^ m = 1
        have hc : x j / x i * (x i / x j) = 1 := by field_simp
        rw [← mul_pow, hc, one_pow]
      · rw [subOf_eq Q' hi]
        exact Submodule.subset_span hm
    | zero => exact ⟨1, by simp, by rw [smul_zero]; exact zero_mem _⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, hau⟩ := hu
      obtain ⟨b, hb, hbv⟩ := hv
      refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
      have : ((a * b : Kleiman.chartRing S x I) : Ω) • (u + v) = b • ((a : Ω) • u) + a • ((b : Ω) • v) := by
        simp only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact add_mem (Submodule.smul_mem _ b hau) (Submodule.smul_mem _ a hbv)
    | smul c z _ hz =>
      obtain ⟨a, ha, haz⟩ := hz
      obtain ⟨a', ha', hc⟩ := Kleiman.exists_isUnit_mul_mem h c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have : ((a' * a : Kleiman.chartRing S x I) : Ω) • (c • z) =
          (⟨(a' : Ω) * c, hc⟩ : Kleiman.chartRing S x I) • ((a : Ω) • z) := by
        simp only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ haz
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hay' := subOf_mono Q' I J h _ hay
    have hinv : ((↑u⁻¹ : Kleiman.chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy' : y = (↑u⁻¹ : Kleiman.chartRing S x J) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, ← mul_smul, hinv, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ hay'

theorem latSub_fg_invertible {i : Fin (N + 1)} (h : x i ≠ 0) :
    (latSub Q' h).FG ∧ ∃ L' : Submodule (Kleiman.chartRing S x (Kleiman.singleChart h)) Ω,
      latSub Q' h * L' = 1 := by
  obtain ⟨k, f, c, hf, hc, hs, hb⟩ := Q'.frame i h
  have hA : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i = Kleiman.chartRing S x (Kleiman.singleChart h) :=
    chartRing.equiv S x h
  simp only [hA] at hf hc hb
  choose b hbli _ hiff using hb
  refine fg_and_invertible_of_frame _ f c (latSub Q' h) (fun l => b l 0) hf hc hs
    (fun l => linearIndependent_unique_iff.1 (hbli l)) (fun l e => ?_)
  have := hiff l e
  simp only [Fin.sum_univ_one, smul_eq_mul] at this
  constructor
  · intro hn
    obtain ⟨a, ha, he⟩ := this.1 hn
    exact ⟨a 0, ha 0, he⟩
  · rintro ⟨a, ha, he⟩
    exact this.2 ⟨fun _ => a, fun _ => ha, he⟩

theorem subOf_fg (I : Kleiman.Chart x) : (subOf Q' I).FG := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  have hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I :=
    Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)
  rw [subOf_eq Q' hi]
  exact fg_span_of_le hle (latSub_fg_invertible Q' hxi).1

theorem subOf_invertible (I : Kleiman.Chart x) :
    ∃ L' : Submodule (Kleiman.chartRing S x I) Ω, subOf Q' I * L' = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  have hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I :=
    Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)
  obtain ⟨L', hL'⟩ := (latSub_fg_invertible Q' hxi).2
  have key := mul_span_eq_one_of_le (B := Kleiman.chartRing S x I) hle hL'
  rw [coe_latSub] at key
  refine ⟨Submodule.span (Kleiman.chartRing S x I) (L' : Set Ω), ?_⟩
  rw [subOf_eq Q' hi]
  exact key

def ofSecond : Kleiman.LineBundle S x where
  sub := subOf Q'
  mono := subOf_mono Q'
  mem_iff := subOf_mem_iff Q'
  fg I := subOf_fg Q' I
  invertible I := subOf_invertible Q' I

end Second

end

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
