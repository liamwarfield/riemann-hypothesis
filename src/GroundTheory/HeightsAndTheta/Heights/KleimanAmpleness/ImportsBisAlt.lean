module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisSide

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelPoint.proof (hgen : BlockGenOfModel.Statement) (htr : BlockGenTransfer.Statement)
    (hmod : ModelOfBlockGen.Statement) : ModelPoint.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ hy K' _ _ y' hy' hle
  exact hmod F K ι K' y' k₀ hy' (htr F K ι Ω y k₀ (hgen F K ι Ω y k₀ hy) K' y' hy' hle)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartRingBlockVecIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver mConeMapOver)

theorem ne_zero_of_mIdealOver_le {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω Ω' : Type} [Field Ω]
    [Field Ω'] [Algebra S Ω] [Algebra S Ω'] {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → Ω'}
    (h : mIdealOver S y ≤ mIdealOver S y') (p : Σ k, ι k) (hp : y' p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hmem : (X p : MvPolynomial (Σ k, ι k) S) ∈ mIdealOver S y := by
    simp [mIdealOver, RingHom.mem_ker, mConeMapOver, h0]
  have h' := h hmem
  simpa [mIdealOver, RingHom.mem_ker, mConeMapOver] using h'

theorem mem_chartRing_blockVec_iff {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra S Ω] (z : (Σ k, ι k) → Ω) (k₀ : K) (j : ι k₀) (u : Ω) :
    u ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec z k₀)) (fun _ => j) ↔
      ∃ P : MvPolynomial (Σ _ : Unit, ι k₀) S,
        aeval (fun v : (Σ _ : Unit, ι k₀) => z ⟨k₀, v.2⟩ / z ⟨k₀, j⟩) P = u := by
  unfold chartRingOver
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]
  rfl

theorem aeval_rename_blockRatio {S : Type} [CommRing S] {K : Type} {ι : K → Type} {L : Type} [Field L]
    [Algebra S L] (z : (Σ k, ι k) → L) (k₀ : K) (c : ∀ k, ι k) (P : MvPolynomial (Σ _ : Unit, ι k₀) S) :
    aeval (fun p => z p / z ⟨p.1, c p.1⟩)
        (rename (fun v : (Σ _ : Unit, ι k₀) => (⟨k₀, v.2⟩ : Σ k, ι k)) P) =
      aeval (fun v : (Σ _ : Unit, ι k₀) => z ⟨k₀, v.2⟩ / z ⟨k₀, c k₀⟩) P := by
  rw [aeval_rename]
  rfl

theorem BlockGenTransfer.proof (hk : ChartKernel.Statement) : BlockGenTransfer.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ hB Ω' _ _ y' hne hle j hj k
  have hy := ne_zero_of_mIdealOver_le hle
  obtain ⟨c, hck₀, hc⟩ : ∃ c : ∀ k, ι k, c k₀ = j ∧ ∀ k, y' ⟨k, c k⟩ ≠ 0 := by
    choose c₀ hc₀ using hne
    refine ⟨Function.update c₀ k₀ j, Function.update_self _ _ _, fun k' => ?_⟩
    by_cases h : k' = k₀
    · cases h
      rw [Function.update_self]
      exact hj
    · rw [Function.update_of_ne h]
      exact hc₀ k'
  have hb₀ : y ⟨k, c k⟩ ≠ 0 := hy _ (hc k)
  obtain ⟨w, hw, hsum⟩ := hB j (hy _ hj) k
  choose P hP using fun a b => (mem_chartRing_blockVec_iff y k₀ j _).1 (hw a b)
  let φ : (Σ _ : Unit, ι k₀) → (Σ k, ι k) := fun v => ⟨k₀, v.2⟩
  have hR1 : ∀ a b, aeval (fun p => y p / y ⟨p.1, c p.1⟩)
      (X ⟨k, a⟩ * rename φ (P (c k) b) - rename φ (P a b)) = 0 := by
    intro a b
    simp only [map_sub, map_mul, aeval_X, φ, aeval_rename_blockRatio, hck₀, hP]
    field_simp
    ring
  have hR2 : aeval (fun p => y p / y ⟨p.1, c p.1⟩)
      (∑ b, X ⟨k, b⟩ * rename φ (P (c k) b) - 1) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_one, aeval_X, φ, aeval_rename_blockRatio, hck₀, hP]
    rw [sub_eq_zero, ← hsum]
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp
  refine ⟨fun b => aeval (fun v : (Σ _ : Unit, ι k₀) => y' ⟨k₀, v.2⟩ / y' ⟨k₀, j⟩) (P (c k) b) / y' ⟨k, c k⟩,
    fun a b => ?_, ?_⟩
  · have h1 := hk S K ι Ω y Ω' y' hle c hc _ (hR1 a b)
    simp only [map_sub, map_mul, aeval_X, φ, aeval_rename_blockRatio, hck₀, sub_eq_zero] at h1
    rw [mem_chartRing_blockVec_iff]
    refine ⟨P a b, ?_⟩
    rw [← h1]
    ring
  · have h2 := hk S K ι Ω y Ω' y' hle c hc _ hR2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_one, aeval_X, φ, aeval_rename_blockRatio, hck₀,
      sub_eq_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts)

theorem BlockGenOfModel.proof : BlockGenOfModel.Statement := by
  classical
  intro S _ K ι _ Ω _ _ y k₀ hmod j hj k
  set x := IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) with hx
  set A := chartRingOver S x (fun _ => j) with hA

  let D : Set A := {d | ∃ b, y ⟨k, b⟩ ≠ 0 ∧ ∀ a, (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b⟩) ∈ A}
  have hI : (Submodule.span A D : Ideal A) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal _ hne
    have hqp : q.IsPrime := hq.isPrime
    have hsame : modelPts S y = modelPts S x := hmod.2
    have hmem : locIn A q ∈ modelPts S x := ⟨fun _ => j, fun _ => hj, q, hqp, rfl⟩
    rw [← hsame] at hmem
    obtain ⟨c, hc, p, hp, hEq⟩ := hmem
    have hr : ∀ a, y ⟨k, a⟩ / y ⟨k, c k⟩ ∈ locIn A q := by
      intro a
      rw [hEq]
      exact (mem_locIn_chart_iff y c p).mpr
        ⟨⟨_, Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩⟩, 1, Ideal.one_notMem p, by simp⟩
    choose nn dd hdd hnd using fun a => (mem_locIn_chart_iff x (fun _ => j) q).mp (hr a)
    have hdq : (∏ a, dd a) ∉ q := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨a, -, ha⟩
      exact hdd a ha
    apply hdq
    apply hIq
    apply Submodule.subset_span
    refine ⟨c k, hc k, fun a => ?_⟩
    rw [hnd a]
    have hda : (dd a : Ω) ≠ 0 := coe_ne_zero_of_notMem x (fun _ => j) q (hdd a)
    have e : ((∏ a', dd a' : A) : Ω) * ((nn a : Ω) / dd a) =
        (nn a : Ω) * ∏ a' ∈ Finset.univ.erase a, (dd a' : Ω) := by
      rw [SubmonoidClass.coe_finsetProd, ← Finset.mul_prod_erase Finset.univ (fun a' => (dd a' : Ω))
        (Finset.mem_univ a)]
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _ (nn a).2 (Subalgebra.prod_mem _ fun i _ => (dd i).2)

  have key : ∀ t ∈ (Submodule.span A D : Ideal A), ∃ w : ι k → Ω,
      (∀ a b, y ⟨k, a⟩ * w b ∈ A) ∧ ∑ b, y ⟨k, b⟩ * w b = (t : Ω) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨b, hb, hdb⟩ := hd
      refine ⟨Pi.single b ((d : Ω) / y ⟨k, b⟩), fun a b' => ?_, ?_⟩
      · by_cases h : b' = b
        · subst h
          simp only [Pi.single_eq_same]
          have e : y ⟨k, a⟩ * ((d : Ω) / y ⟨k, b'⟩) = (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b'⟩) := by ring
          rw [e]
          exact hdb a
        · simp only [Pi.single_eq_of_ne h, mul_zero]
          exact Subalgebra.zero_mem _
      · simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        field_simp
    | zero => exact ⟨0, fun _ _ => by simp, by simp⟩
    | add s t _ _ hs ht =>
      obtain ⟨w, hw, hws⟩ := hs
      obtain ⟨w', hw', hwt⟩ := ht
      refine ⟨w + w', fun a b => ?_, ?_⟩
      · rw [Pi.add_apply, mul_add]
        exact Subalgebra.add_mem _ (hw a b) (hw' a b)
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hws, hwt]
        push_cast
        ring
    | smul r t _ ht =>
      obtain ⟨w, hw, hwt⟩ := ht
      refine ⟨fun b => (r : Ω) * w b, fun a b => ?_, ?_⟩
      · have e : y ⟨k, a⟩ * ((r : Ω) * w b) = (r : Ω) * (y ⟨k, a⟩ * w b) := by ring
        rw [e]
        exact Subalgebra.mul_mem _ r.2 (hw a b)
      · rw [smul_eq_mul, Subalgebra.coe_mul, ← hwt, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
  obtain ⟨w, hw, hsum⟩ := key 1 (by rw [hI]; exact Submodule.mem_top)
  exact ⟨w, hw, by rw [hsum]; simp⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ProdNotMemPrimeOfForall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

section Between

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem prod_notMem_prime_of_forall {K : Type} [Fintype K] {A : Subalgebra S Ω} {p : Ideal A} (hp : p.IsPrime)
    (f : K → Ω) (hf : ∀ k, f k ∈ A) (hnot : ∀ k, (⟨f k, hf k⟩ : A) ∉ p) :
    (⟨∏ k, f k, prod_mem fun k _ => hf k⟩ : A) ∉ p := by
  have := hp
  have h : (⟨∏ k, f k, prod_mem fun k _ => hf k⟩ : A) = ∏ k, (⟨f k, hf k⟩ : A) :=
    Subtype.ext (by simp)
  rw [h, Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hnot k hk

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem blockRing_between (y : (Σ k, ι k) → Ω) (k₀ : K) (j : ι k₀) (c : ∀ k, ι k) (hcj : c k₀ = j)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (w : ∀ k, ι k → Ω)
    (hw : ∀ k a b, y ⟨k, a⟩ * w k b ∈
      chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j))
    (b : ∀ k, ι k) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j) ≤ chartRingOver S y c ∧
      chartRingOver S y c ≤ powMulMem _ (∏ k, y ⟨k, c k⟩ * w k (b k)) (prod_mem fun k _ => hw k (c k) (b k)) := by
  subst hcj
  refine ⟨?_, ?_⟩
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨⟨⟩, i⟩, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, a⟩, rfl⟩
    refine ⟨1, ?_⟩
    have hk := hc k
    have h : (∏ k', y ⟨k', c k'⟩ * w k' (b k')) ^ 1 * (y ⟨k, a⟩ / y ⟨k, c k⟩) =
        y ⟨k, a⟩ * w k (b k) * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ * w k' (b k') := by
      rw [pow_one, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
      field_simp
    rw [h]
    exact Subalgebra.mul_mem _ (hw k a (b k)) (prod_mem fun k' _ => hw k' (c k') (b k'))

end Between

theorem ModelOfBlockGen.proof : ModelOfBlockGen.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ hy hBG
  refine ⟨hy, ?_⟩
  show IndefiniteRowSideFullHecke.Kleiman2.modelPts S y = IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))
  ext z
  constructor
  · rintro ⟨c, hc, P, hP, rfl⟩
    choose w hw hsum using hBG (c k₀) (hc k₀)
    have hAc : ∀ k b, y ⟨k, c k⟩ * w k b ∈ chartRingOver S y c := fun k b =>
      (blockRing_between y k₀ (c k₀) c rfl hc w hw c).1 (hw k (c k) b)
    have hb : ∀ k, ∃ b, (⟨_, hAc k b⟩ : chartRingOver S y c) ∉ P := by
      intro k
      by_contra h
      push Not at h
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      have hk := hc k
      have h1 : (1 : chartRingOver S y c) = ∑ b, (⟨y ⟨k, b⟩ / y ⟨k, c k⟩,
          Algebra.subset_adjoin ⟨⟨k, b⟩, rfl⟩⟩ : chartRingOver S y c) * ⟨_, hAc k b⟩ := by
        apply Subtype.ext
        simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
        rw [← hsum k]
        refine Finset.sum_congr rfl fun b _ => ?_
        field_simp
      rw [h1]
      exact Ideal.sum_mem _ fun b _ => P.mul_mem_left _ (h b)
    choose b hb using hb
    obtain ⟨hAB, hle⟩ := blockRing_between y k₀ (c k₀) c rfl hc w hw b
    have heP := prod_notMem_prime_of_forall hP (fun k => y ⟨k, c k⟩ * w k (b k)) (fun k => hAc k (b k)) hb
    have hP' : (P.comap (Subalgebra.inclusion hAB)).IsPrime := Ideal.comap_isPrime _ _
    exact ⟨fun _ => c k₀, fun _ => hc k₀, _, hP',
      locIn_eq_of_le_powMulMem hAB (prod_mem fun k _ => hw k (c k) (b k)) hle P hP heP⟩
  · rintro ⟨c₀, hc₀, p, hp, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, c₀ = fun _ => j := ⟨c₀ (), funext fun _ => rfl⟩
    have hj : y ⟨k₀, j⟩ ≠ 0 := hc₀ ()
    choose w hw hsum using hBG j hj
    let A := chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j)
    have hd : ∀ k, ∃ d, (⟨_, hw k d d⟩ : A) ∉ p := by
      intro k
      by_contra h
      push Not at h
      apply hp.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : A) = ∑ b, (⟨_, hw k b b⟩ : A) := by
        apply Subtype.ext
        simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum]
        exact (hsum k).symm
      rw [h1]
      exact Ideal.sum_mem _ fun b _ => h b
    choose d hd using hd
    obtain ⟨b₀, hb₀⟩ : ∃ b, (⟨_, hw k₀ j b⟩ : A) ∉ p := by
      by_contra h
      push Not at h
      apply hp.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : A) = ∑ b, (⟨y ⟨k₀, b⟩ / y ⟨k₀, j⟩, Algebra.subset_adjoin ⟨⟨(), b⟩, rfl⟩⟩ : A) *
          ⟨_, hw k₀ j b⟩ := by
        apply Subtype.ext
        simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
        rw [← hsum k₀]
        refine Finset.sum_congr rfl fun b _ => ?_
        field_simp
      rw [h1]
      exact Ideal.sum_mem _ fun b _ => p.mul_mem_left _ (h b)
    let c : ∀ k, ι k := Function.update d k₀ j
    let b : ∀ k, ι k := Function.update d k₀ b₀
    have hcb : ∀ k, (⟨_, hw k (c k) (b k)⟩ : A) ∉ p := by
      intro k
      by_cases hk : k = k₀
      · subst k
        have h : (⟨_, hw k₀ (c k₀) (b k₀)⟩ : A) = ⟨_, hw k₀ j b₀⟩ := Subtype.ext (by simp [c, b])
        rw [h]
        exact hb₀
      · have h : (⟨_, hw k (c k) (b k)⟩ : A) = ⟨_, hw k (d k) (d k)⟩ :=
          Subtype.ext (by simp [c, b, Function.update_of_ne hk])
        rw [h]
        exact hd k
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      apply hcb k
      have h : (⟨_, hw k (c k) (b k)⟩ : A) = 0 := Subtype.ext (by simp [h0])
      rw [h]
      exact p.zero_mem
    obtain ⟨hAB, hle⟩ := blockRing_between y k₀ j c (by simp [c]) hc w hw b
    have hep := prod_notMem_prime_of_forall hp (fun k => y ⟨k, c k⟩ * w k (b k)) (fun k => hw k (c k) (b k)) hcb
    obtain ⟨P, hP, hPeq⟩ := exists_isPrime_locIn_eq hAB _ hle p hp hep
    exact ⟨c, hc, P, hP, hPeq.symm⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
