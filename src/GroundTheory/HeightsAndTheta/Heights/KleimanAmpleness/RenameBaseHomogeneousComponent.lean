module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RenameBaseHomogeneousComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

section

variable {k : Type} [Field k] {N m : ℕ}

theorem weight_mapDomain_base (e : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (graphIdx N m))
        (Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e) =
      Sum.elim (fun _ => e.degree) (fun _ => 0) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  funext c
  rw [← sum_block_eq_blockWeight]
  rcases c with ⟨⟩ | ⟨⟩
  · simp only [Sum.elim_inl]
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_congr rfl fun a _ => Finsupp.mapDomain_apply_of_injective hinj e a
  · simp only [Sum.elim_inr]
    refine Finset.sum_eq_zero fun b _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨a, ha⟩
    cases (Sigma.mk.inj ha).1

theorem rename_base_homogeneousComponent (d : ℕ) (f : Kleiman.Poly k N) :
    rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (homogeneousComponent d f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) (Sum.elim (fun _ => d) (fun _ => 0))
        (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  ext e'
  rw [coeff_weightedHomogeneousComponent]
  by_cases he : ∃ e, Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e = e'
  · obtain ⟨e, rfl⟩ := he
    rw [coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj, coeff_homogeneousComponent,
      weight_mapDomain_base]
    by_cases hd : e.degree = d
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (congrFun h (Sum.inl ()))]
  · push Not at he
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    · rfl

end

theorem CurveComap.proof (hR : SectionRatio.Statement) (hD : RatioDim.Statement) : CurveComap.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle e
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.relevant (Sum.inr ())
  have hdim := hD k N m W hW.isPrime hW.multiHomog j hj fun b => by
    obtain ⟨d, f, g, -, -, h1, h2⟩ := hR k N Ω x Q n m s hx hgen W hW hle j b hj
    exact ⟨f, g, h1, h2⟩
  have hsub : Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) e ↔
      ringKrullDim (Kleiman.Poly k N ⧸
          W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) =
        ((e + 1 : ℕ) : WithBot ℕ∞) := by
    refine ⟨fun h => h.dim, fun h => ⟨Ideal.comap_isPrime _ _, fun f hf d => ?_, ?_, ?_, h⟩⟩
    · rw [Ideal.mem_comap] at hf ⊢
      rw [rename_base_homogeneousComponent]
      exact hW.multiHomog _ hf _
    · rw [← comap_mIdealOver_graph (S := k) x s]
      exact Ideal.comap_mono hle
    · obtain ⟨i, hi⟩ := hW.relevant (Sum.inl ())
      have hXi : rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i : Kleiman.Poly k N) =
          X ⟨baseBlock, i⟩ := rename_X _ _
      exact ⟨i, by rw [Ideal.mem_comap, hXi]; exact hi⟩
  rw [hsub, FieldNumbers.CutRegular.relDim_eq_natCast_iff, hdim, Fintype.card_sum, Fintype.card_unit]
  generalize ringKrullDim (Kleiman.Poly k N ⧸
    W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) = D
  induction D using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add]
    exact iff_of_false (WithBot.bot_ne_natCast _) (WithBot.bot_ne_natCast _)
  | coe t =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_inj,
      WithBot.coe_inj]
    induction t using ENat.recTopCoe with
    | top => exact iff_of_false (by rw [top_add]; exact ENat.top_ne_natCast _) (ENat.top_ne_natCast _)
    | coe t =>
      norm_cast
      omega

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SpanSecsMemLocInSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

section Local

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem spanSecs_mem_locIn_self {A : Subalgebra F Ω} {p : Ideal A} [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  mem_locIn.mpr ⟨⟨a, ha⟩, 1, one_not_mem_of_prime hp, by simp⟩

theorem spanSecs_mul_step {B : Subalgebra F Ω} {q : Ideal B} [hq : q.IsPrime] {T : Set Ω} {u g : Ω}
    (hg : g ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (hu : ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * (g * u) ∈ Submodule.span B T := by
  obtain ⟨b, hb, hbu⟩ := hu
  obtain ⟨a, b', hb', rfl⟩ := mem_locIn.mp hg
  refine ⟨b' * b, fun h => (hq.mem_or_mem h).elim hb' hb, ?_⟩
  have h0 := coe_ne_zero_of_not_mem hb'
  have e : ((b' * b : B) : Ω) * ((a : Ω) / b' * u) = a • ((b : Ω) * u) := by
    rw [Subalgebra.smul_def, smul_eq_mul, Subalgebra.coe_mul]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ hbu

theorem spanSecs_exists_mul_mem (B C : Subalgebra F Ω) (q : Ideal B) [hq : q.IsPrime]
    (hC : ∀ a ∈ C, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (T : Set Ω) {u : Ω} (hu : u ∈ Submodule.span C T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T := by
  induction hu using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_not_mem_of_prime hq, by simpa using Submodule.subset_span hz⟩
  | zero => exact ⟨1, one_not_mem_of_prime hq, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨b₁, hb₁, h₁⟩ := hz
    obtain ⟨b₂, hb₂, h₂⟩ := hw
    refine ⟨b₁ * b₂, fun h => (hq.mem_or_mem h).elim hb₁ hb₂, ?_⟩
    have e : ((b₁ * b₂ : B) : Ω) * (z + w) = b₂ • ((b₁ : Ω) * z) + b₁ • ((b₂ : Ω) * w) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, Subalgebra.coe_mul]
      ring
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul a z _ hz =>
    rw [Subalgebra.smul_def, smul_eq_mul]
    exact spanSecs_mul_step (hC _ a.2) hz

theorem spanSecs_mem_of_local (B : Subalgebra F Ω) (T : Set Ω) (u : Ω)
    (h : ∀ q : Ideal B, q.IsMaximal → ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    u ∈ Submodule.span B T := by
  let J : Ideal B := (Submodule.span B T).comap (LinearMap.toSpanSingleton B Ω u)
  have hJ : ∀ b : B, b ∈ J ↔ (b : Ω) * u ∈ Submodule.span B T := fun b => Iff.rfl
  by_cases hJt : J = ⊤
  · have h1 : (1 : B) ∈ J := hJt ▸ Submodule.mem_top
    simpa using (hJ 1).mp h1
  · obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal J hJt
    obtain ⟨b, hb, hbu⟩ := h q hq
    exact absurd (hJq ((hJ b).mpr hbu)) hb

end Local

theorem SpanSecs.proof : SpanSecs.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod T d s
  have hxv : ∀ i, x i = y ⟨k₀, e.symm i⟩ := fun i => by rw [hx]; rfl

  let B : ι k₀ → Subalgebra F Ω := fun i' =>
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => i')
  have hB : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), Kleiman.chartRing F x (Kleiman.singleChart hi) = B (e.symm i) := by
    intro i hi
    rw [← chartRingOver_oneBlock_eq_chartRing (S := F) x (fun _ => i) hi]
    unfold B chartRingOver
    congr 1
    ext z
    constructor
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e.symm l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩

  have hBc : ∀ c : ∀ k, ι k, B (c k₀) ≤ chartRingOver F y c := by
    intro c
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨_, l⟩, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨k₀, l⟩, rfl⟩
  constructor
  · intro hs c hc
    have hi : x (e (c k₀)) ≠ 0 := by rw [hxv, Equiv.symm_apply_apply]; exact hc k₀
    set A := Kleiman.chartRing F x (Kleiman.singleChart hi) with hA
    have hAc : A ≤ chartRingOver F y c := by
      rw [hA, hB, Equiv.symm_apply_apply]; exact hBc c
    have hs' := Submodule.mem_iInf _ |>.mp hs (Kleiman.singleChart hi)
    rw [Submodule.restrictScalars_mem,
      Kleiman.twistMod_eq_span d _ (Finset.mem_singleton_self (e (c k₀)))] at hs'
    have hv : y ⟨k₀, c k₀⟩ = x (e (c k₀)) := by rw [hxv, Equiv.symm_apply_apply]
    rw [hv]
    refine Submodule.mul_induction_on hs' ?_ ?_
    · intro m hm n hn
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
      have e1 : m * (a • x (e (c k₀)) ^ d) * x (e (c k₀)) ^ (-d) = (⟨a, hAc a.2⟩ : chartRingOver F y c) • m := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, zpow_neg]
        field_simp
      rw [e1]
      exact Submodule.smul_mem _ _ (span_subset_span hAc T hm)
    · intro a b ha hb
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  · intro h
    refine Submodule.mem_iInf _ |>.mpr fun I => ?_
    rw [Submodule.restrictScalars_mem]
    obtain ⟨i, hiI⟩ := I.2.1
    have hi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hiI)
    rw [Kleiman.twistMod_eq_span d I hiI]
    have hle : Kleiman.chartRing F x (Kleiman.singleChart hi) ≤ Kleiman.chartRing F x I :=
      Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hiI)

    suffices key : s * x i ^ (-d) ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.singleChart hi)) T by
      have e1 : s = s * x i ^ (-d) * x i ^ d := by
        rw [zpow_neg, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero d hi), mul_one]
      rw [e1]
      exact Submodule.mul_mem_mul (span_subset_span hle T key) (Submodule.subset_span rfl)
    rw [hB i hi]
    have hxi' : y ⟨k₀, e.symm i⟩ ≠ 0 := by rw [← hxv]; exact hi
    refine spanSecs_mem_of_local _ T _ fun q hq => ?_
    have := hq.isPrime

    have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q ∈
        IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) :=
      ⟨fun _ => e.symm i, fun _ => hxi', q, hq.isPrime, rfl⟩
    rw [← hmod.2] at hz
    obtain ⟨c, hc, p, hp, hzp⟩ := hz
    have := hp
    have hCz : ∀ a ∈ chartRingOver F y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      intro a ha
      rw [hzp]
      exact spanSecs_mem_locIn_self ha

    set w := y ⟨k₀, c k₀⟩ with hw
    set v := y ⟨k₀, e.symm i⟩ with hvdef
    have hw0 : w ≠ 0 := hc k₀
    have h1 : w / v ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      spanSecs_mem_locIn_self (Algebra.subset_adjoin ⟨⟨(), c k₀⟩, rfl⟩)
    have h2 : v / w ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      hCz _ (Algebra.subset_adjoin ⟨⟨k₀, e.symm i⟩, rfl⟩)
    have hg : (w / v) ^ d ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
      · rw [zpow_natCast]; exact pow_mem h1 n
      · rw [zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem h2 n
    have e2 : s * x i ^ (-d) = (w / v) ^ d * (s * w ^ (-d)) := by
      rw [hxv, ← hvdef, div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [e2]
    exact spanSecs_mul_step hg (spanSecs_exists_mul_mem _ _ q hCz T (h c hc))

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowOfMemCellSec
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver cellMon)

namespace RowSecGlue

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [Algebra S Ω]

def ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_ratioPt_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (R : MRingOver S ι) :
    aeval (ratioPt y c) R ∈ chartRingOver S y c := by
  rw [chartRingOver, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨R, rfl⟩

theorem aeval_eq_ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {F : MRingOver S ι} {d : K → ℕ} (hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F d) :
    aeval y F = aeval (ratioPt y c) F * ∏ k, y ⟨k, c k⟩ ^ d k := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  simp only [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have h1 : ∀ p : (Σ k, ι k), y p ^ μ p = ratioPt y c p ^ μ p * y ⟨p.1, c p.1⟩ ^ μ p := by
    intro p
    rw [ratioPt, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hc p.1))]
  have h2 : ∏ p : (Σ k, ι k), y ⟨p.1, c p.1⟩ ^ μ p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hF μ hμ k]
  rw [Finset.prod_congr rfl fun p _ => h1 p, Finset.prod_mul_distrib, h2]
  ring

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_mul_eq_pow (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (J : Finset (Fin (N + 1))) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {t : MRingOver S ι}
    (ht : t ∈ cellMon S (baseCell k₀ e J fun k => {c k})) :
    ∃ (n : ℕ) (w : Ω), w ∈ chartRingOver S y c ∧
      w * aeval (ratioPt y c) t = (∏ j ∈ J, ratioPt y c ⟨k₀, e.symm j⟩) ^ n := by
  have hone : ∀ k, ratioPt y c ⟨k, c k⟩ = 1 := fun k => div_self (hc k)
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map] at hi
      rcases hi with rfl | ⟨j, hj, rfl⟩
      · exact ⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩
      · refine ⟨1, ∏ j' ∈ J.erase j, ratioPt y c ⟨k, e.symm j'⟩,
          prod_mem fun j' _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k, e.symm j'⟩), ?_⟩
        rw [aeval_X, pow_one]
        exact Finset.prod_erase_mul J (fun j' => ratioPt y c ⟨k, e.symm j'⟩) hj
    · rw [Function.update_of_ne hk, Finset.mem_singleton] at hi
      subst hi
      exact ⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul f g _ _ h₁ h₂ =>
    obtain ⟨n₁, w₁, hw₁, e₁⟩ := h₁
    obtain ⟨n₂, w₂, hw₂, e₂⟩ := h₂
    exact ⟨n₁ + n₂, w₁ * w₂, mul_mem hw₁ hw₂, by rw [map_mul, pow_add, ← e₁, ← e₂]; ring⟩

theorem prod_zpow_neg (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) (k₀ : K) (γ : K → ℤ) (m : ℕ) :
    ∏ k, Y k ^ (-(γ + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) = (∏ k, Y k ^ γ k)⁻¹ * (Y k₀ ^ m)⁻¹ := by
  have h : ∀ k, Y k ^ (-(γ + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (Y k ^ γ k)⁻¹ * (Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k))⁻¹ := by
    intro k
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_add, zpow_add₀ (hY k), zpow_neg, zpow_neg,
      IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  have h2 : ∏ k, Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k) = Y k₀ ^ m := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [Pi.single_apply, hk])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [Finset.prod_congr rfl fun k _ => h k, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_inv_distrib, h2]

theorem exists_pow_of_mem_cellSec (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ)
    (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {z : Ω}
    (hz : z ∈ cellSec S y γ (baseCell k₀ e J.1 fun k => {c k})) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Kleiman.xProd J ^ n * z *
      ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) ∈ chartRingOver S y c := by
  have hJ : ∀ j ∈ J.1, y ⟨k₀, e.symm j⟩ ≠ 0 := fun j hj => (Kleiman.mem_support _).mp (J.2.2 hj)
  have hmeet : CellMeets y (baseCell k₀ e J.1 fun k => {c k}) := by
    intro k i hi
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map] at hi
      rcases hi with rfl | ⟨j, hj, rfl⟩
      · exact hc k
      · exact hJ j hj
    · rw [Function.update_of_ne hk, Finset.mem_singleton] at hi
      subst hi; exact hc k
  unfold cellSec at hz
  rw [if_pos hmeet] at hz
  set u := ratioPt y c with hu
  set xJ := ∏ j ∈ J.1, u ⟨k₀, e.symm j⟩ with hxJdef
  have hxJ : xJ ∈ chartRingOver S y c :=
    prod_mem fun j _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k₀, e.symm j⟩)
  have hxJ0 : xJ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj => div_ne_zero (hJ j hj) (hc k₀)
  have hX : Kleiman.xProd J = xJ * y ⟨k₀, c k₀⟩ ^ J.1.card := by
    rw [Kleiman.xProd, hxJdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hu, ratioPt, Function.comp, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    rw [div_mul_cancel₀ _ (hc k₀)]
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, t, a', ht, hta, hγ, hg, rfl⟩ := hz
    obtain ⟨n₀, w, hw, hwt⟩ := exists_mul_eq_pow y k₀ e J.1 c hc ht
    refine ⟨n₀, fun n hn => ?_⟩
    have ht0 : aeval u t ≠ 0 := fun h0 => pow_ne_zero n₀ hxJ0 (by rw [← hwt, h0, mul_zero])
    have hg' := aeval_eq_ratioPt y c hc hg
    have ht' := aeval_eq_ratioPt y c hc hta
    have hexp : ∏ k, y ⟨k, c k⟩ ^ (γ k + a' k).toNat = (∏ k, y ⟨k, c k⟩ ^ γ k) * ∏ k, y ⟨k, c k⟩ ^ a' k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, Int.toNat_of_nonneg (hγ k), zpow_add₀ (hc k), zpow_natCast]
    have hW : (∏ k, y ⟨k, c k⟩ ^ γ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hA : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    rw [← hu] at hg' ht'
    have hn' : xJ ^ n = xJ ^ (n - n₀) * (w * aeval u t) := by
      rw [hwt, ← pow_add, Nat.sub_add_cancel hn]
    have key : Kleiman.xProd J ^ n * (aeval y g / aeval y t) *
        ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
        xJ ^ (n - n₀) * w * aeval u g := by
      rw [prod_zpow_neg (fun k => y ⟨k, c k⟩) hc k₀ γ, hX, mul_pow, hn', hg', ht', hexp, pow_mul]
      have hp : y ⟨k₀, c k₀⟩ ^ (J.1.card * n) * (y ⟨k₀, c k₀⟩)⁻¹ ^ (J.1.card * n) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (hc k₀), one_pow]
      field_simp
      linear_combination (w * aeval u g) * hp
    rw [key]
    exact mul_mem (mul_mem (pow_mem hxJ _) hw) (aeval_ratioPt_mem y c g)
  | zero => exact ⟨0, fun n _ => by simp⟩
  | add z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨n₁, h₁⟩ := h₁
    obtain ⟨n₂, h₂⟩ := h₂
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    have := add_mem (h₁ n (le_of_max_le_left hn)) (h₂ n (le_of_max_le_right hn))
    rwa [← add_mul, ← mul_add] at this
  | smul r z _ h =>
    obtain ⟨n₀, h⟩ := h
    refine ⟨n₀, fun n hn => ?_⟩
    have e1 : Kleiman.xProd J ^ n * (r • z) *
        ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
        algebraMap S Ω r * (Kleiman.xProd J ^ n * z *
          ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) := by
      rw [Algebra.smul_def]; ring
    rw [e1]
    exact mul_mem (Subalgebra.algebraMap_mem _ r) (h n hn)

end RowSecGlue

theorem RowSecGlue.proof : RowSecGlue.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J a h
  have hc : ∀ c : ∀ k, ι k, ∃ n₀ : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ n ≥ n₀, Kleiman.xProd J ^ n * a *
      ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) ∈ chartRingOver S y c := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n₀, h'⟩ := RowSecGlue.exists_pow_of_mem_cellSec y k₀ e γ J c hc (h c hc)
      exact ⟨n₀, fun _ => h'⟩
    · exact ⟨0, fun h' => absurd h' hc⟩
  choose n₀ hn₀ using hc
  refine ⟨Finset.univ.sup n₀, ?_⟩
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c hc'
  exact hn₀ c hc' _ (Finset.le_sup (Finset.mem_univ c))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Charts

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

theorem prod_zpow_add_baseDeg (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (δ : K → ℤ) (m : ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * y ⟨k₀, c k₀⟩ ^ (-m) := by
  have hterm : ∀ k, y ⟨k, c k⟩ ^ (-(δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      y ⟨k, c k⟩ ^ (-δ k) * (if k = k₀ then y ⟨k, c k⟩ ^ (-m) else 1) := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, IndefiniteRowSideFullHecke.Kleiman2.baseDeg, smul_eq_mul]
    by_cases hk : k = k₀
    · subst hk
      rw [Pi.single_eq_same, if_pos rfl, mul_one, neg_add, zpow_add₀ (hc _)]
    · rw [Pi.single_eq_of_ne hk, if_neg hk, mul_zero, add_zero, mul_one]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib, Finset.prod_ite_eq',
    if_pos (Finset.mem_univ _)]

def baseRatio (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) : Ω :=
  Kleiman.xProd I * (y ⟨k₀, c k₀⟩ ^ I.1.card)⁻¹


omit [Fintype K] [DecidableEq K] in
theorem baseRatio_mem (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) :
    baseRatio y k₀ I c ∈ chartRingOver S y c := by
  have h : baseRatio y k₀ I c = ∏ i ∈ I.1, y ⟨k₀, e.symm i⟩ / y ⟨k₀, c k₀⟩ := by
    rw [Finset.prod_div_distrib, Finset.prod_const, div_eq_mul_inv]
    rfl
  rw [h]
  exact prod_mem fun i _ => Algebra.subset_adjoin ⟨⟨k₀, e.symm i⟩, rfl⟩

theorem mem_chartSecOver_iff (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (t : Ω) :
    t ∈ chartSecOver S y k₀ e δ I ↔ ∃ n : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * (t * ∏ k, y ⟨k, c k⟩ ^ (-δ k)) ∈ chartRingOver S y c := by
  simp only [chartSecOver, Set.mem_ofPred_eq]
  refine exists_congr fun n => ?_
  rw [mem_secOver_iff_charts]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [prod_zpow_add_baseDeg y k₀ c hc]
  have h : Kleiman.xProd I ^ n * t * ((∏ k, y ⟨k, c k⟩ ^ (-δ k)) *
      y ⟨k₀, c k₀⟩ ^ (-(((n * I.1.card : ℕ) : ℤ)))) =
      baseRatio y k₀ I c ^ n * (t * ∏ k, y ⟨k, c k⟩ ^ (-δ k)) := by
    rw [zpow_neg, zpow_natCast, baseRatio, mul_pow, inv_pow, ← pow_mul, mul_comm I.1.card n]
    ring
  rw [h]


omit [DecidableEq K] in
theorem exists_forall_baseRatio [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ}
    {e : ι k₀ ≃ Fin (N + 1)} (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (w : (∀ k, ι k) → Ω)
    (h : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∃ n : ℕ, baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c) :
    ∃ n : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c := by
  have hev : ∀ c : ∀ k, ι k, ∀ᶠ n : ℕ in Filter.atTop, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n₀, hn₀⟩ := h c hc
      refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn _ => ?_⟩
      have hsplit : baseRatio y k₀ I c ^ n * w c =
          baseRatio y k₀ I c ^ (n - n₀) * (baseRatio y k₀ I c ^ n₀ * w c) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
      rw [hsplit]
      exact mul_mem (pow_mem (baseRatio_mem y k₀ I c) _) hn₀
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' hc
  exact (Filter.eventually_all.mpr hev).exists

theorem prod_zpow_mem_secOver (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℤ) (hδ : ∀ k, 0 ≤ δ k) :
    ∏ k, y ⟨k, c k⟩ ^ δ k ∈ secOver S y δ := by
  rw [mem_secOver_iff_charts]
  intro c' _
  rw [← Finset.prod_mul_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (hδ k)
  have h : y ⟨k, c k⟩ ^ δ k * y ⟨k, c' k⟩ ^ (-δ k) = (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ m := by
    rw [hm, zpow_neg, zpow_natCast, zpow_natCast, div_pow, div_eq_mul_inv]
  rw [h]
  refine pow_mem ?_ m
  exact Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩

end Charts

theorem ChartSecMul.proof (h₁ : BundleOfDeg.Statement) : ChartSecMul.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ N e hM γ β I
  have hsub : ∀ δ : K → ℤ, ∃ Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
      (Q.sub I : Set Ω) = chartSecOver S y k₀ e δ I := by
    intro δ
    obtain ⟨Q, hQ⟩ := h₁ S K ι Ω y k₀ N e hM δ
    refine ⟨Q, Set.ext fun t => ?_⟩
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hQ]
  choose Q hQ using hsub
  have hmemP : ∀ δ t, t ∈ (Q δ).sub I ↔ t ∈ chartSecOver S y k₀ e δ I := fun δ t =>
    Set.ext_iff.mp (hQ δ) t

  have hmul : ∀ a b c : K → ℤ, a + b = c → (Q a).sub I * (Q b).sub I ≤ (Q c).sub I := by
    rintro a b _ rfl
    rw [Submodule.mul_le]
    intro g hg f hf
    rw [hmemP, mem_chartSecOver_iff] at hg hf ⊢
    obtain ⟨n₁, hn₁⟩ := hg
    obtain ⟨n₂, hn₂⟩ := hf
    refine ⟨n₁ + n₂, fun c hc => ?_⟩
    have hY : ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k) =
        (∏ k, y ⟨k, c k⟩ ^ (-a k)) * ∏ k, y ⟨k, c k⟩ ^ (-b k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, neg_add, zpow_add₀ (hc k)]
    have hsplit : baseRatio y k₀ I c ^ (n₁ + n₂) * (g * f * ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k)) =
        (baseRatio y k₀ I c ^ n₁ * (g * ∏ k, y ⟨k, c k⟩ ^ (-a k))) *
          (baseRatio y k₀ I c ^ n₂ * (f * ∏ k, y ⟨k, c k⟩ ^ (-b k))) := by
      rw [hY, pow_add]
      ring
    rw [hsplit]
    exact mul_mem (hn₁ c hc) (hn₂ c hc)

  have hA : ∀ a : Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I, (a : Ω) ∈ (Q 0).sub I := by
    intro a
    have h1 : (1 : Ω) ∈ (Q 0).sub I := by
      refine (hmemP 0 1).mpr (mem_chartSecOver_of_mem S y k₀ e 0 I ?_)
      rw [mem_secOver_iff_charts]
      intro c _
      simp
    have := ((Q 0).sub I).smul_mem a h1
    rwa [Kleiman.chartRing_smul_def, mul_one] at this

  have hinv : ∀ δ : K → ℤ, (∀ k, 0 ≤ δ k) → 1 ≤ (Q δ).sub I * (Q (-δ)).sub I := by
    intro δ hδ
    obtain ⟨Q', hQ'⟩ := (Q δ).invertible I
    rw [← hQ']
    refine mul_le_mul_right (fun z hz => ?_) _
    rw [hmemP, mem_chartSecOver_iff]
    refine exists_forall_baseRatio y k₀ I _ fun c hc => ?_
    have hyc : (∏ k, y ⟨k, c k⟩ ^ δ k) ∈ (Q δ).sub I :=
      (hmemP δ _).mpr (mem_chartSecOver_of_mem S y k₀ e δ I (prod_zpow_mem_secOver y c δ hδ))
    have hw : z * ∏ k, y ⟨k, c k⟩ ^ δ k ∈ (1 : Submodule (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) Ω) := by
      rw [← hQ', mul_comm z]
      exact Submodule.mul_mem_mul hyc hz
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hw
    obtain ⟨n, hn⟩ := (mem_chartSecOver_iff y k₀ e 0 I _).mp ((hmemP 0 _).mp (hA a))
    refine ⟨n, ?_⟩
    have he : z * ∏ k, y ⟨k, c k⟩ ^ (-(-δ) k) = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ (-(0 : K → ℤ) k) := by
      simp only [Pi.neg_apply, neg_neg, Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
      exact ha.symm
    rw [he]
    exact hn c hc
  have hshift : ∀ ε δ : K → ℤ, (∀ k, 0 ≤ δ k) →
      (Q ε).sub I ≤ (Q (ε + δ)).sub I * (Q (-δ)).sub I := by
    intro ε δ hδ
    calc (Q ε).sub I = (Q ε).sub I * 1 := (mul_one _).symm
      _ ≤ (Q ε).sub I * ((Q δ).sub I * (Q (-δ)).sub I) := mul_le_mul_right (hinv δ hδ) _
      _ = (Q ε).sub I * (Q δ).sub I * (Q (-δ)).sub I := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_left (hmul _ _ _ rfl) _
  have hshift' : ∀ ε δ : K → ℤ, (∀ k, 0 ≤ δ k) →
      (Q ε).sub I ≤ (Q (ε - δ)).sub I * (Q δ).sub I := by
    intro ε δ hδ
    calc (Q ε).sub I = (Q ε).sub I * 1 := (mul_one _).symm
      _ ≤ (Q ε).sub I * ((Q δ).sub I * (Q (-δ)).sub I) := mul_le_mul_right (hinv δ hδ) _
      _ = (Q ε).sub I * (Q (-δ)).sub I * (Q δ).sub I := by rw [mul_comm ((Q δ).sub I), mul_assoc]
      _ ≤ _ := mul_le_mul_left (hmul _ _ _ (sub_eq_add_neg ε δ).symm) _

  have hbp : ∀ k, 0 ≤ (fun k => max (β k) 0) k := fun k => le_max_right _ _
  have hbm : ∀ k, 0 ≤ (fun k => max (-β k) 0) k := fun k => le_max_right _ _
  have hγ : γ + β + (fun k => max (-β k) 0) - (fun k => max (β k) 0) = γ := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [max_def, max_def]
    split_ifs <;> omega
  have hβ : (fun k => max (β k) 0) + -(fun k => max (-β k) 0) = β := by
    funext k
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [max_def, max_def]
    split_ifs <;> omega
  have hle : (Q (γ + β)).sub I ≤ (Q γ).sub I * (Q β).sub I := by
    calc (Q (γ + β)).sub I
        ≤ (Q (γ + β + fun k => max (-β k) 0)).sub I * (Q (-fun k => max (-β k) 0)).sub I :=
          hshift _ _ hbm
      _ ≤ (Q (γ + β + (fun k => max (-β k) 0) - fun k => max (β k) 0)).sub I *
            (Q fun k => max (β k) 0).sub I * (Q (-fun k => max (-β k) 0)).sub I :=
          mul_le_mul_left (hshift' _ _ hbp) _
      _ = (Q γ).sub I * ((Q fun k => max (β k) 0).sub I * (Q (-fun k => max (-β k) 0)).sub I) := by
          rw [hγ, mul_assoc]
      _ ≤ (Q γ).sub I * (Q β).sub I := mul_le_mul_right (hmul _ _ _ hβ) _
  have heq : (Q γ).sub I * (Q β).sub I = (Q (γ + β)).sub I := le_antisymm (hmul _ _ _ rfl) hle
  rw [← hQ γ, ← hQ β, ← Submodule.mul_eq_span_mul_set, heq, hQ]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeetsBaseCell
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] [Algebra S Ω]

theorem cellSec_mono [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) {I I' : ∀ k, Finset (ι k)} (h : ∀ k, I k ⊆ I' k)
    (hI' : CellMeets y I') : cellSec S y γ I ≤ cellSec S y γ I' := by
  classical
  unfold cellSec
  rw [if_pos hI']
  split_ifs with hI
  · refine Submodule.span_mono ?_
    rintro z ⟨g, t, a, ht, hta, hγ, hg, rfl⟩
    refine ⟨g, t, a, ?_, hta, hγ, hg, rfl⟩
    refine Submonoid.closure_mono ?_ ht
    rintro f ⟨k, i, hi, rfl⟩
    exact ⟨k, i, h k hi, rfl⟩
  · exact bot_le

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem subset_baseCell (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1)))
    (I : ∀ k, Finset (ι k)) (k : K) : I k ⊆ baseCell k₀ e J I k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self]; exact Finset.subset_union_left
  · rw [Function.update_of_ne hk]

theorem baseCell_mono (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {J J' : Finset (Fin (N + 1))}
    {I I' : ∀ k, Finset (ι k)} (hJ : J ⊆ J') (hI : ∀ k, I k ⊆ I' k) (k : K) :
    baseCell k₀ e J I k ⊆ baseCell k₀ e J' I' k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self, Function.update_self]
    exact Finset.union_subset_union (hI k) (Finset.map_subset_map.mpr hJ)
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]; exact hI k

theorem cellMeets_baseCell (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) :
    CellMeets y (baseCell k₀ e J.1 I) := by
  intro k i hi
  unfold baseCell at hi
  by_cases hk : k = k₀
  · subst hk
    rw [Function.update_self, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hI k i hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact (Kleiman.mem_support _).mp (J.2.2 hj)
  · rw [Function.update_of_ne hk] at hi; exact hI k i hi

theorem ModelCechRefine.proof (hC : CechContract.Statement) (hR : ModelRowExact.Statement)
    (hD : DoubleCech.Statement) : ModelCechRefine.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ T hT n
  have hM0 : ∀ (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, ¬ CellMeets y I →
      cellSec F y γ (baseCell k₀ e J.1 I) = ⊥ := fun J I hI => by
    unfold cellSec
    rw [if_neg fun h => hI fun k i hi => h k i (subset_baseCell k₀ e J.1 I k hi)]
  have hMJ : ∀ (J J' : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, J.1 ⊆ J'.1 →
      cellSec F y γ (baseCell k₀ e J.1 I) ≤ cellSec F y γ (baseCell k₀ e J'.1 I) := fun J J' I h => by
    by_cases hI : CellMeets y I
    · exact cellSec_mono y γ (baseCell_mono k₀ e h fun _ => subset_rfl) (cellMeets_baseCell y k₀ e J' hI)
    · rw [hM0 J I hI]; exact bot_le
  refine (hD F K ι Ω y N _ T (cellSec F y γ) (fun J I => cellSec F y γ (baseCell k₀ e J.1 I)) hM.1 ?_
    (fun I hI => by unfold cellSec; rw [if_neg hI]) hM0 hMJ
    (fun J I I' h hI' => cellSec_mono y γ (baseCell_mono k₀ e subset_rfl h) (cellMeets_baseCell y k₀ e J hI'))
    ?_ ?_ n)
  · obtain ⟨i, hi⟩ := hM.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  · intro I hne hI
    obtain ⟨i, hi⟩ := hne k₀
    have hx : (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (e i) ≠ 0 := by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hI k₀ i hi
    let J₀ : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) :=
      ⟨{e i}, Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr ((Kleiman.mem_support _).mpr hx)⟩
    have hadd : ∀ J : Finset (Fin (N + 1)), baseCell k₀ e ({e i} ∪ J) I = baseCell k₀ e J I := by
      intro J
      unfold baseCell
      congr 1
      rw [Finset.map_union, ← Finset.union_assoc, Finset.map_singleton]
      congr 1
      exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (by simpa using hi))
    have h₀ : baseCell k₀ e J₀.1 I = I := by
      have := hadd ∅
      rw [Finset.union_empty] at this
      rw [show J₀.1 = {e i} from rfl, this]
      unfold baseCell
      simp
    have := hC F Ω N _ (fun J => cellSec F y γ (baseCell k₀ e J.1 I)) J₀ (Finset.card_singleton _)
      (fun J J' h => hMJ J J' I h) (fun J J' h => by
        show cellSec F y γ (baseCell k₀ e J'.1 I) = _
        rw [h]; exact congrArg _ (hadd J.1))
    simpa only [h₀] using this
  · intro J
    have h := hR F K ι Ω y k₀ N e hM γ J
    rwa [← hT J, ← Submodule.coe_restrictScalars F, Submodule.span_eq] at h

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
