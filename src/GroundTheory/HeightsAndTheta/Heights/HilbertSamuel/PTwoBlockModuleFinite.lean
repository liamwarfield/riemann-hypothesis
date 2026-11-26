module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCycleExpand
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.TwoLeKrullDimOfRelevantPrime
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace TwoBlockModuleFinite

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem cone_X (x x' : Ix κ → Ω) (p : Σ k, FinTwoTypeFamily κ k) :
    mConeMap (pair x x') (X p : MRing (FinTwoTypeFamily κ)) = MvPolynomial.C (pair x x' p) * X p.1 :=
  aeval_X _ _

theorem cone_num (x x' : Ix κ → Ω) (l : Ix κ → ℤ) :
    mConeMap (pair x x') (twoBlockNum l) = MvPolynomial.C (∑ j, (l j : Ω) * x' j) * X 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [twoBlockNum, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨⟨⟩, j⟩ := j
  rw [cone_X]
  simp [mConeMap, pair, mul_assoc]

theorem coneMap_firstBlock_linearForm (x x' : Ix κ → Ω) (n : Ix κ → ℤ) :
    mConeMap (pair x x') (∑ i : Ix κ, MvPolynomial.C (n i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ))) =
      MvPolynomial.C (∑ i, (n i : Ω) * x i) * X 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨⟩, i⟩ := i
  rw [cone_X]
  simp [mConeMap, pair, mul_assoc]

theorem mem_twoBlockIdeal (x x' : Ix κ → Ω) (f : MRing (FinTwoTypeFamily κ)) :
    f ∈ twoBlockIdeal x x' ↔ mConeMap (pair x x') f = 0 :=
  RingHom.mem_ker

theorem le_of_add_one_le' {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    have h' : ((b + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
    rw [WithBot.coe_le_coe] at h'
    change ((b : ℕ∞) : WithBot ℕ∞) ≤ (((n : ℕ) : ℕ∞) : WithBot ℕ∞)
    rw [WithBot.coe_le_coe]
    induction b using ENat.recTopCoe with
    | top => exact absurd h' (by simp)
    | coe m =>
      have : m + 1 ≤ n + 1 := by exact_mod_cast h'
      exact_mod_cast (by omega : m ≤ n)

end TwoBlockModuleFinite


open TwoBlockModuleFinite in
theorem TwoBlockModuleFinite.proof : TwoBlockModuleFinite.Statement := by
  classical
  have hA := CoordArithOfFnField.proof
  have hF := TwoBlockFnField.proof
  intro D Ω _ _ κ _ x B c l hx hli hB hspan hxc
  obtain ⟨hFp, -⟩ := hF Ω κ x B hB
  set x' := matAct B x with hx'def
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx
  have hxc0 : x ⟨(), c⟩ ≠ 0 := hli.ne_zero _
  have hx'0 : ∃ j, x' ⟨(), j⟩ ≠ 0 := by
    by_contra h
    push Not at h
    apply hxc0
    rw [hxc]
    exact Finset.sum_eq_zero fun j _ => by
      obtain ⟨⟨⟩, j⟩ := j
      rw [h j, mul_zero]
  obtain ⟨i₁, hi₁⟩ := hx'0
  have hpA : IsArithVar (twoBlockIdeal x x') (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x x') (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨c, by simpa [pair] using hxc0⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  obtain ⟨S, hS, hPS⟩ := hpA.2.1.2.1

  have hL : ∀ i : κ, ∃ L : Ix κ → ℤ, x ⟨(), i⟩ = ∑ j, (L j : Ω) * x' j := by
    intro i
    have hmem : x ⟨(), i⟩ ∈ Submodule.span ℤ (Set.range x') := hspan (Submodule.subset_span ⟨_, rfl⟩)
    obtain ⟨L, hL⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
    exact ⟨L, by rw [← hL]; simp [zsmul_eq_mul]⟩
  choose L hL using hL

  set N : ℕ := ∏ p : Ix κ × Ix κ, (B p.1 p.2).den with hN
  have hN0 : 0 < N := Finset.prod_pos fun p _ => (B p.1 p.2).den_pos
  have hn : ∀ j i, ∃ z : ℤ, (z : ℚ) = N * B j i := by
    intro j i
    obtain ⟨M, hM⟩ : (B j i).den ∣ N :=
      Finset.dvd_prod_of_mem (fun p : Ix κ × Ix κ => (B p.1 p.2).den) (Finset.mem_univ (j, i))
    refine ⟨M * (B j i).num, ?_⟩
    rw [hM]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose n hn using hn
  have hNx' : ∀ j : κ, (N : Ω) * x' ⟨(), j⟩ = ∑ i, (n ⟨(), j⟩ i : Ω) * x i := by
    intro j
    simp only [hx'def, matAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    congr 1
    have h := congrArg (fun q : ℚ => (q : Ω)) (hn ⟨(), j⟩ i)
    push_cast at h
    rw [h]
  have hPO : twoBlockIdeal x x' ≤ twoBlockMOuter x x' c := le_sup_left
  have hPI : twoBlockIdeal x x' ≤ twoBlockMInner x x' l := le_sup_left
  have hgO : ∀ j : κ, twoBlockDen c * X ⟨1, j⟩ ∈ twoBlockMOuter x x' c := fun j =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
  have hgI : ∀ i : κ, twoBlockNum l * X ⟨0, i⟩ ∈ twoBlockMInner x x' l := fun i =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hlx : ∑ j, (l j : Ω) * x' j = x ⟨(), c⟩ := hxc.symm
  refine ⟨?_, ?_, ?_, ⟨N, hN0, ?_⟩, ?_⟩
  ·
    refine ⟨S ∪ Set.range fun j : κ => twoBlockDen c * X ⟨1, j⟩, ?_, ?_⟩
    · rintro f (hf | ⟨j, rfl⟩)
      · exact hS f hf
      · exact ⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (TwoBlockCycleExpand.isMultiHomog_twoBlockDen c)
          (ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X _)⟩
    · rw [twoBlockMOuter, hPS, Ideal.span_union]
  ·
    refine ⟨S ∪ Set.range fun i : κ => twoBlockNum l * X ⟨0, i⟩, ?_, ?_⟩
    · rintro f (hf | ⟨i, rfl⟩)
      · exact hS f hf
      · exact ⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (TwoBlockCycleExpand.isMultiHomog_twoBlockNum l)
          (ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X _)⟩
    · rw [twoBlockMInner, hPS, Ideal.span_union]
  ·
    rw [twoBlockMInner, sup_le_iff]
    refine ⟨hPO, Ideal.span_le.mpr ?_⟩
    rintro _ ⟨i, rfl⟩
    have hd : twoBlockNum l * X ⟨0, i⟩ - twoBlockDen c * twoBlockNum (L i) ∈ twoBlockIdeal x x' := by
      rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, cone_num, cone_num, twoBlockDen, cone_X, cone_X, hlx,
        ← hL i]
      simp [pair]
      ring
    have hs : twoBlockDen c * twoBlockNum (L i) ∈ twoBlockMOuter x x' c := by
      rw [twoBlockNum, Finset.mul_sum]
      exact Ideal.sum_mem _ fun j _ => by
        rw [mul_left_comm]
        exact Ideal.mul_mem_left _ _ (hgO j.2)
    have h := Ideal.add_mem _ (hPO hd) hs
    rwa [sub_add_cancel] at h
  ·
    intro f hf
    rw [twoBlockMOuter, Submodule.mem_sup] at hf
    obtain ⟨p, hp, s, hs, rfl⟩ := hf
    rw [mul_add]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hPI hp)) ?_
    induction hs using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      have hd : (N : MRing (FinTwoTypeFamily κ)) * (twoBlockDen c * X ⟨1, j⟩) -
          twoBlockNum l * ∑ i : Ix κ, MvPolynomial.C (n ⟨(), j⟩ i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ)) ∈
            twoBlockIdeal x x' := by
        rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, map_mul, map_natCast, cone_num, coneMap_firstBlock_linearForm, twoBlockDen, cone_X,
          cone_X, hlx, ← hNx' j]
        simp [pair]
        ring
      have hs : twoBlockNum l * ∑ i : Ix κ, MvPolynomial.C (n ⟨(), j⟩ i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ)) ∈
          twoBlockMInner x x' l := by
        rw [Finset.mul_sum]
        exact Ideal.sum_mem _ fun i _ => by
          rw [mul_left_comm]
          exact Ideal.mul_mem_left _ _ (hgI i.2)
      have h := Ideal.add_mem _ (hPI hd) hs
      rwa [sub_add_cancel] at h
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Ideal.add_mem _ ha hb
    | smul r a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ ha
  ·
    intro W hW hIW _
    have : (twoBlockIdeal x x').IsPrime := hpA.2.1.1
    have := hW
    have hlt : twoBlockIdeal x x' < W := by
      refine lt_of_le_of_ne (hPI.trans hIW) fun h => ?_
      have hm : twoBlockNum l * X ⟨0, c⟩ ∈ twoBlockIdeal x x' := by
        rw [h]
        exact hIW (hgI c)
      rw [mem_twoBlockIdeal, map_mul, cone_num, cone_X, hlx] at hm
      simp [pair, hxc0] at hm
    have h := krullDim_quotient_add_one_le hlt
    rw [hpA.2.2.2, Fintype.card_fin, show D + 1 + 2 = D + 2 + 1 by omega] at h
    rw [Fintype.card_fin]
    exact le_of_add_one_le' h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockModuleCycleAlt

section General

variable {K : Type} {ι : K → Type} {τ : Type}

theorem mem_minimalPrimes_iff_of {R : Type*} [CommRing R] {J J' W : Ideal R} (hJ : J ≤ J')
    (key : ∀ Q : Ideal R, Q.IsPrime → Q ≤ W → J ≤ Q → J' ≤ Q) :
    W ∈ J.minimalPrimes ↔ W ∈ J'.minimalPrimes := by
  constructor
  · intro h
    exact ⟨⟨h.1.1, key W h.1.1 le_rfl h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, hJ.trans hQ.2⟩ hQW⟩
  · intro h
    exact ⟨⟨h.1.1, hJ.trans h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, key Q hQ.1 hQW hQ.2⟩ hQW⟩

theorem sup_range_le {R : Type*} [CommRing R] (P : Ideal R) (s : R) (v : τ → R) :
    P ⊔ Ideal.span (Set.range fun j => s * v j) ≤ P ⊔ Ideal.span {s} := by
  refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

theorem mul_mem_sup_range {R : Type*} [CommRing R] {P : Ideal R} {s : R} {v : τ → R} (i : τ) {y : R}
    (hy : y ∈ P ⊔ Ideal.span {s}) : v i * y ∈ P ⊔ Ideal.span (Set.range fun j => s * v j) := by
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [mul_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hp)) (Ideal.mem_sup_right ?_)
  have e : v i * (t * s) = t * (s * v i) := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem multAt_sup_range_eq {P W : Ideal (MRing ι)} {s : MRing ι} {v : τ → MRing ι} (hW : W.IsPrime) {i : τ}
    (hi : v i ∉ W) : multAt (P ⊔ Ideal.span (Set.range fun j => s * v j)) W = multAt (P ⊔ Ideal.span {s}) W := by
  have := hW
  unfold multAt
  rw [dite_eq_left hW, dite_eq_left hW, GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedQuot_eq_of_mul_le
    (sup_range_le P s v) hi (fun y hy => mul_mem_sup_range i hy)]

theorem multAt_eq_zero_of_not_le {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by
  have := hW
  unfold multAt
  rw [dite_eq_left hW, Module.length_eq_zero_iff.mpr
    (GroundTheory.Heights₂.Heights.NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]
  rfl

theorem log_charOf_of_horizontal {W : Ideal (MRing ι)} (h : IsHorizontal W) : Real.log (charOf W) = 0 := by
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 :=
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mp h
  simp [charOf, hg]


open Classical in
theorem vert_weight_eq (W : Ideal (MRing ι)) (g : ℤ) :
    (if IsHorizontal W then 0 else (g : ℝ) * Real.log (charOf W)) = Real.log (charOf W) * g := by
  split_ifs with h
  · rw [log_charOf_of_horizontal h, zero_mul]
  · ring

end General

section TwoBlock

variable {Ω : Type} [Field Ω] {κ : Type}

theorem mem_twoBlockIdeal {x x' : Ix κ → Ω} {f : MRing (FinTwoTypeFamily κ)} :
    f ∈ twoBlockIdeal x x' ↔ mConeMap (ι := FinTwoTypeFamily κ) (pair x x') f = 0 :=
  RingHom.mem_ker

theorem mConeMap_X_zero (x x' : Ix κ → Ω) (i : κ) :
    mConeMap (ι := FinTwoTypeFamily κ) (pair x x') (X ⟨0, i⟩) = MvPolynomial.C (x ⟨(), i⟩) * MvPolynomial.X 0 := by
  simp [mConeMap, pair]

theorem mConeMap_num [Fintype κ] (x x' : Ix κ → Ω) (l : Ix κ → ℤ) :
    mConeMap (ι := FinTwoTypeFamily κ) (pair x x') (twoBlockNum l) =
      MvPolynomial.C (∑ j, (l j : Ω) * x' j) * MvPolynomial.X 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [twoBlockNum, mConeMap, pair, Finset.sum_mul, mul_assoc, map_sum]

theorem rel_mem [Fintype κ] (x x' : Ix κ → Ω) (c : κ) (l m : Ix κ → ℤ) (i : κ)
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * x' j) (hm : x ⟨(), i⟩ = ∑ j, (m j : Ω) * x' j) :
    X ⟨0, i⟩ * twoBlockNum l - twoBlockDen c * twoBlockNum m ∈ twoBlockIdeal x x' := by
  rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, mConeMap_num, mConeMap_num, twoBlockDen,
    mConeMap_X_zero, mConeMap_X_zero, ← hl, ← hm]
  ring

end TwoBlock

end TwoBlockModuleCycleAlt


open TwoBlockModuleCycleAlt in
theorem TwoBlockModuleCycle.proof : TwoBlockModuleCycle.Statement := by
  classical
  intro D Ω _ _ κ _ x B c l hX hx hB hsp hl e

  obtain ⟨hFp, -⟩ := TwoBlockFnField.proof Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hX
  have hxc : x ⟨(), c⟩ ≠ 0 := hx.ne_zero _
  have hx0 : x ≠ 0 := fun h => hxc (by rw [h]; rfl)
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0
  have hpA : IsArithVar (twoBlockIdeal x (matAct B x)) (D + 1) :=
    CoordArithOfFnField.proof Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  have hPp : (twoBlockIdeal x (matAct B x)).IsPrime := hpA.2.1.1
  have hdim := hpA.2.2.2

  have hnumP : twoBlockNum l ∉ twoBlockIdeal x (matAct B x) := by
    rw [mem_twoBlockIdeal, mConeMap_num, ← hl]
    simp [hxc]

  have hm : ∀ i : κ, ∃ m : Ix κ → ℤ, x ⟨(), i⟩ = ∑ j, (m j : Ω) * matAct B x j := by
    intro i
    have h := hsp (Submodule.subset_span ⟨⟨(), i⟩, rfl⟩)
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
    exact ⟨m, by rw [← hm]; simp [zsmul_eq_mul]⟩
  choose m hm using hm

  have hden_num : ∀ Q : Ideal (MRing (FinTwoTypeFamily κ)), Q.IsPrime → twoBlockIdeal x (matAct B x) ≤ Q →
      (∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q) → twoBlockDen c ∈ Q → twoBlockNum l ∈ Q := by
    rintro Q hQ hPQ ⟨i, hi⟩ hd
    have h1 := hPQ (rel_mem x (matAct B x) c l (m i) i hl (hm i))
    have h2 : X ⟨0, i⟩ * twoBlockNum l ∈ Q := by
      have e : X ⟨0, i⟩ * twoBlockNum l =
          (X ⟨0, i⟩ * twoBlockNum l - twoBlockDen c * twoBlockNum (m i)) + twoBlockDen c * twoBlockNum (m i) := by
        ring
      rw [e]
      exact Q.add_mem h1 (Q.mul_mem_right _ hd)
    exact (hQ.mem_or_mem h2).resolve_left hi

  have hmin : ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W →
      (W ∈ (twoBlockMInner x (matAct B x) l).minimalPrimes ↔
        W ∈ (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}).minimalPrimes) := by
    intro W hrel
    refine mem_minimalPrimes_iff_of (sup_range_le _ _ _) fun Q hQ hQW hJQ => ?_
    obtain ⟨i, hi⟩ := hrel 0
    have hiQ : (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q := fun h => hi (hQW h)
    have hn : twoBlockNum l * X ⟨0, i⟩ ∈ Q :=
      hJQ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    exact sup_le (le_sup_left.trans hJQ)
      ((Ideal.span_singleton_le_iff_mem _).mpr ((hQ.mem_or_mem hn).resolve_right hiQ))
  have hT : topComps (twoBlockMInner x (matAct B x) l) D = divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) := by
    ext W
    constructor
    · rintro ⟨hW, hrel, -⟩
      exact ⟨(hmin W hrel).mp hW, hrel⟩
    · rintro ⟨hW, hrel⟩
      exact ⟨(hmin W hrel).mpr hW, hrel, dim_of_minimal hnumP hW hdim⟩

  have hsub : divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) ⊆
      divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) := by
    rintro W ⟨hW, hrel⟩
    have hWp : W.IsPrime := hW.1.1
    have hPW : twoBlockIdeal x (matAct B x) ≤ W := le_sup_left.trans hW.1.2
    have hdW : twoBlockDen c ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnW := hden_num W hWp hPW (hrel 0) hdW
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hnW))
    have hQeq : Q = W := ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_le_of_mem_minimalPrimes hPp hW hQ.1.1
      (le_sup_left.trans hQ.1.2) (hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) hnumP hQW
    exact ⟨hQeq ▸ hQ, hrel⟩

  have hback : ∀ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l), twoBlockDen c ∈ W →
      W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) := by
    rintro W ⟨hW, hrel⟩ hdW
    refine ⟨⟨⟨hW.1.1, sup_le (le_sup_left.trans hW.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hdW)⟩,
      fun Q hQ hQW => hW.2 ⟨hQ.1, ?_⟩ hQW⟩, hrel⟩
    have hPQ := le_sup_left.trans hQ.2
    have hrQ : ∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q := by
      obtain ⟨i, hi⟩ := hrel 0
      exact ⟨i, fun h => hi (hQW h)⟩
    exact sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr
      (hden_num Q hQ.1 hPQ hrQ (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))))

  rw [hT]
  unfold twoBlockVert vertCycleNum
  have hfin := divSupp_finite (twoBlockIdeal x (matAct B x)) (twoBlockNum l)
  have hden_sum :
      ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c),
          (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) *
            (if IsHorizontal W then 0 else (geoNum D W e : ℝ) * Real.log (charOf W)) =
        ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l),
          (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) *
            (if IsHorizontal W then 0 else (geoNum D W e : ℝ) * Real.log (charOf W)) := by
    refine finsum_mem_inter_support_eq' _ _ _ fun W hW => ⟨fun h => hsub h, fun h => hback W h ?_⟩
    by_contra hd
    apply hW
    show (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) * _ = 0
    rw [multAt_eq_zero_of_not_le h.1.1.1 fun hle =>
      hd (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))]
    simp
  rw [hden_sum, ← finsum_mem_sub_distrib _ _ hfin]
  refine finsum_mem_congr rfl fun W hW => ?_
  obtain ⟨i, hi⟩ := hW.2 0
  obtain ⟨j, hj⟩ := hW.2 1
  have h1 : multAt (twoBlockMInner x (matAct B x) l) W =
      multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}) W :=
    multAt_sup_range_eq (s := twoBlockNum l) (v := fun i : κ => (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hi
  have h2 : multAt (twoBlockMOuter x (matAct B x) c) W =
      multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W :=
    multAt_sup_range_eq (s := twoBlockDen c) (v := fun j : κ => (X ⟨1, j⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hj
  rw [h1, h2, vert_weight_eq]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphDeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGraphDeg

theorem isMultiHomog_blockForms {K : Type} [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type}
    (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (q : Σ k, GlobalTheory κ k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (blockForms k₀ M q) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk, Sigma.ext_iff]

theorem x'_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} [Fintype K₂]
    {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}
    (G : GenFibre (inrV (ι := ι) (ι₂ := ι₂)) (graphIdeal P g)) (k : K) (i : ι k)
    (hi : (X ⟨k, i⟩ : MRing ι) ∉ P) : G.x' ⟨Sum.inl k, i⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl k, i⟩ : MRing (Sum.elim ι ι₂)) ∈ graphIdeal P g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  exact hi (Ideal.Quotient.eq_zero_iff_mem.1 (MvPolynomial.C_eq_zero.1 h1))

end BlockGraphDeg


open BlockGraphDeg in
theorem BlockGraphDeg.proof (hGr : GraphStatement) (hImg : BlockGraphImage.Statement)
    (hEx : GenFibreExistsStatement) (hDim : FibreDimStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCR : Inter.ChartRankAdjoin.Statement) (hRat : BlockGraphFibreRatio.Statement) :
    BlockGraphDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hy hB hx hI
  have hImage := hImg K ι Ω κ y k₀ M N x hI
  have hIm : IsArithVar (imageZ (inrV (ι := ι) (ι₂ := GlobalTheory κ))
      (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (D + 1) := by
    rw [hImage]
    exact hx

  have hnv : ∀ u : Unit, ∃ j, blockForms k₀ M ⟨u, j⟩ ∉ mCoordIdeal y := by
    intro u
    obtain ⟨j, hj⟩ := hIm.2.1.2.2 u
    refine ⟨j, fun hm => hj ?_⟩
    rw [imageZ, Ideal.mem_comap]
    change rename inrV (X ⟨u, j⟩) ∈ _
    rw [rename_X, graphIdeal, RingHom.mem_ker, inrV, graphMap, eval₂Hom_X']
    change C (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨u, j⟩)) * X u = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero, zero_mul]
  have hΓ := (hGr K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) hy
    (isMultiHomog_blockForms k₀ M) hnv).1
  obtain ⟨G⟩ := hEx Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) isBlockMap_inr hΓ
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr)
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm

  choose c hc using hy.2.1.2.2
  let ch : (k : FibreBlock (Sum.inr : Unit → K ⊕ Unit)) → fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k := fun
    | ⟨Sum.inl k, _⟩ => c k
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(k | u), h⟩
    · exact x'_ne_zero G k (c k) (hc k)
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := hCR (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr) G.Φ G.Φ'
    (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit),
      fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(k | u), h⟩, i⟩, rfl⟩
    · exact IntermediateField.mem_bot.2 (hRat D K ι Ω κ y k₀ M N x hy hB hI G k i (c k) (x'_ne_zero G k (c k) (hc k)))
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionInterpIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem locDens_resPot_interp (d : HSMDatum D Ω κ) {m₁ : ConeMetric ℂ (Ix κ)} (hm₁ : IsSmoothMetric m₁)
    (t : ℝ) (j : Fin d.R.A.n) {y : Fin D → ℂ} (hy : y ∈ (d.R.A.chart j).target) :
    locDens d.R.A (fun _ => resPot d (interp d.m m₁ t)) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y := by
  let x0 := (d.R.A.chart j).symm y
  let γ : (Fin D → ℂ) → Ix κ → ℂ := fun y' => d.R.lift x0 ((d.R.A.chart j).symm y')
  have hV : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U x0)
  have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ≠ 0 := by
    filter_upwards [hV.mem_nhds ⟨hy, d.R.mem_U x0⟩] with y' hy'
    exact ⟨differentiableAt_pi.2 fun p => (d.R.holo x0 p j y' hy').differentiableAt,
      gaamix_ne_zero_of_mcPts (d.R.mem x0 _ hy'.2)⟩
  have hL : locDens d.R.A (fun _ => resPot d (interp d.m m₁ t)) j y =
      maDensity (fun k y' => purePot (interp d.m m₁ t) D k (γ y')) y := rfl
  have hR : ∀ i, locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y =
      maDensity (fun k y' => mixPot d.m m₁ D i k (γ y')) y := by
    intro i
    have e : (fun (k : Fin D) (y' : Fin D → ℂ) =>
        (if k.val < i then resPot d m₁ else resPot d d.m).φ x0 ((d.R.A.chart j).symm y')) =
        fun k y' => mixPot d.m m₁ D i k (γ y') := by
      funext k y'
      by_cases hk : k.val < i
      · simp only [hk, if_true, mixPot]
        rfl
      · simp only [hk, if_false, mixPot]
        rfl
    show ReciprocityTheory.AnForm.maDens _ y = _
    rw [e]
    rfl
  rw [hL, gbamix_maDensity_interp d.smooth hm₁ t hγ]
  exact Finset.sum_congr rfl fun i _ => by rw [hR i]

theorem mInt_resPot_interp (d : HSMDatum D Ω κ) {m₁ : ConeMetric ℂ (Ix κ)} (hm₁ : IsSmoothMetric m₁)
    (t : ℝ) :
    mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) (fun y => logRatio d.m m₁ (resPt d y)) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m)
          (fun y => logRatio d.m m₁ (resPt d y)) := by
  have hg : Continuous (fun y => logRatio d.m m₁ (resPt d y)) :=
    continuous_logRatio_resPt d d.smooth hm₁
  have hΦ : ∀ (i : ℕ) (k : Fin D),
      IsPotential d.R.A (if k.val < i then resPot d m₁ else resPot d d.m) := by
    intro i k
    split_ifs
    · exact isPotential_resPot d hm₁
    · exact isPotential_resPot d d.smooth
  unfold mInt
  by_cases hP : Nonempty (ChartPartition d.R.A)
  · simp only [dif_pos hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((d.R.A.chart j).symm y) * logRatio d.m m₁ (resPt d ((d.R.A.chart j).symm y)) *
            locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y))
        (volume.restrict (d.R.A.chart j).target) := fun i _ =>
      (integrableOn_weight d.R.A hP.some _ _ (mIntegrableCont d.R.A _ (hΦ i) _ hg) j).const_mul _
    calc _ = ∫ y in (d.R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((d.R.A.chart j).symm y) *
              logRatio d.m m₁ (resPt d ((d.R.A.chart j).symm y)) *
              locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y) := by
          refine setIntegral_congr_fun (d.R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_resPot_interp d hm₁ t j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dif_neg hP, mul_zero, Finset.sum_const_zero]

namespace ResolutionInterpIntegral

theorem proof : ResolutionInterpIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  unfold resMetricInt
  simp only [mInt_resPot_interp d hm₁]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end ResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

namespace ResolutionDegree

theorem hessC_congr {n : ℕ} {φ ψ : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]

theorem maDens_congr {n : ℕ} {φ ψ : Fin n → (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : (fun k => ReciprocityTheory.AnForm.hessC (φ k) z) = fun k => ReciprocityTheory.AnForm.hessC (ψ k) z :=
    funext fun k => hessC_congr (h k)
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH]

theorem mInt_congr_of_locDens {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Ψ : Fin e → LocPot X} (h : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Ψ j y)
    (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [h j y hy]
  · rfl

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem smooth_logRatio_resPt (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) :
    d.R.A.Smooth (fun y => logRatio m₀ m₁ (resPt d y)) := fun j => by
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y),
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _), ⟨hy.1, d.R.mem_U _⟩, ?_⟩
  have hsm : ContDiffOn ℝ ∞
      (fun y' => logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y')))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y)) :=
    (gbamix_smooth_logRatio h₀ h₁).comp (resLift_contDiffOn d _ j)
      fun y' hy' => gaamix_ne_zero_of_mcPts (d.R.mem _ _ hy'.2)
  refine (hsm.mono Set.inter_subset_right).congr fun y' hy' => ?_
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2.2⟩
  change logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')) = _
  rw [hcy]
  exact gbamix_logRatio_deg (m₀ := m₀) (m₁ := m₁) c _ hc

theorem mInt_resPot_eq (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)} (g : d.R.X → ℝ) :
    mInt d.R.A (fun _ => resPot d m₁) g =
      mInt d.R.A (fun _ => resPot d m₀ + LocPot.ofFun (fun y => logRatio m₀ m₁ (resPt d y))) g := by
  refine mInt_congr_of_locDens _ (fun j y hy => ?_) g
  unfold locDens
  refine maDens_congr fun _ => ?_
  have hmem : (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y) ∈ 𝓝 y :=
    ((d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _)).mem_nhds ⟨hy, d.R.mem_U _⟩
  filter_upwards [hmem] with y' hy'
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2⟩
  have hz := gaamix_ne_zero_of_mcPts (d.R.mem ((d.R.A.chart j).symm y) _ hy'.2)
  have h₀ := m₀.pos _ hz
  have h₁ := m₁.pos _ hz
  change Real.log (m₁.ρ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) =
    Real.log (m₀.ρ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) +
      logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y'))
  rw [hcy, gbamix_logRatio_deg (m₀ := m₀) (m₁ := m₁) c
    (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y')) hc,
    logRatio, Real.log_div h₁.ne' h₀.ne']
  ring

theorem mass_eq (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) :
    mInt d.R.A (fun _ => resPot d m₁) (fun _ => 1) = mInt d.R.A (fun _ => resPot d m₀) (fun _ => 1) := by
  rw [mInt_resPot_eq d (m₀ := m₀)]
  exact massIndep d.R.A (fun _ => resPot d m₀) (fun _ y => logRatio m₀ m₁ (resPt d y))
    (fun _ => isPotential_resPot d h₀) (fun _ => smooth_logRatio_resPt d h₀ h₁)

theorem mass_pullFS (hPM : ProjFSMass.Statement) (d : HSMDatum D Ω κ) {e : Fin (D + 1) → Ix κ}
    {m₀ : ConeMetric ℂ (Ix κ)} (hfr : IsProjFrame d.x e) (h₀ : IsSmoothMetric m₀) (hFS : IsPullFS d.x e m₀) :
    mInt d.R.A (fun _ => resPot d m₀) (fun _ => 1) = (projDeg d.x e : ℝ) := by
  obtain ⟨Ψ, hΨ, hmass⟩ := hPM D Ω κ d.x e m₀ hfr hFS
  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory κ) := HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  have hA : IsSmoothHerm A := contDiffOn_const
  have hlog : logNorm A 1 = fun _ => (1 : ℝ) := by
    funext z
    simp [A, logNorm, HermLine.ofWeight]
  have hsec : IsSectionOn (coordIdeal ℤ d.x) A 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro a ha k
      rw [support_one] at ha
      simp only [Finset.mem_singleton] at ha
      simp [ha]
    · exact (Ideal.ne_top_iff_one _).1 d.arith.2.1.1.ne_top
  have key := AnResBridge.bridge d.R Ψ (fun _ => HermLine.ofCone m₀) A 1 d.arith hΨ
    (fun _ => gbamix_smoothHerm_ofCone h₀) hA hsec
  rw [hlog] at key
  rw [← hmass]
  exact key.symm

end ResolutionDegree

theorem ResolutionDegree.proof (hPF : PullFSExtension.Statement) (hPM : ProjFSMass.Statement) :
    ResolutionDegree.Statement := by
  intro D Ω _ _ κ _ d e m hfr hm
  obtain ⟨m₀, h₀, -, -, hFS⟩ := hPF D Ω κ d.x e hfr
  rw [ResolutionDegree.mass_eq d h₀ hm]
  exact ResolutionDegree.mass_pullFS hPM d hfr h₀ hFS

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
