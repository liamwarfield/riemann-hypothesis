module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCharacterBound
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchPowerSumAtRootsOfUnity
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFrobeniusCharacterFormula
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralVandermondeMul
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurAtRootsOfUnity
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.POtherFactorFormula
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSameFactorBound
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.RestAt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagHomogeneousComponentMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem FlagHomogeneousComponentMul.proof : FlagHomogeneousComponentMul.Statement := by
  intro σ P G k n hP
  exact HomogeneousComponentMul.proof σ ℚ P G k n hP

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestKSumBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

theorem RestKSumBound.proof : RestKSumBound.Statement := by
  intro p X N hp hX hXp
  obtain ⟨hsum, htsum, hexp⟩ := ExponentialTail.intersectionNumber_baseChange p X hp hX hXp
  set g : ℕ → ℝ := fun j => 2 * (p ^ (j + 2))⁻¹ * X ^ (j + 1) / ((j + 2).factorial : ℝ) with hg
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hre : ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) =
      ∑ j ∈ Finset.range (N + 1 - 2), g j := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg]
    simp only
    rw [show 2 + j = j + 2 from Nat.add_comm 2 j, show j + 2 - 1 = j + 1 by omega]
  have hnn : ∀ j, 0 ≤ g j := fun j => by rw [hg]; positivity
  rw [hre]
  calc ∑ j ∈ Finset.range (N + 1 - 2), g j ≤ ∑' j, g j :=
        hsum.sum_le_tsum _ fun j _ => hnn j
    _ ≤ Real.exp (3 / 8) * X / p ^ 2 := htsum
    _ ≤ 1.5 * X / p ^ 2 := hexp

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestBound.proof (h₁ : RestPrimeBound.Statement) (h₂ : RestBoundOfPrimeBound.Statement) :
    RestBound.Statement := by
  intro f r a c B₀ hf hr ha hB
  refine ⟨(h₁ f r a c B₀ hf hr ha hB).1, ?_⟩
  intro Q hQ s e he P
  exact h₂ f r a c B₀ hf hr ha hB Q s e
    (fun p hp hpB => (h₁ f r a c B₀ hf hr ha hB).2 Q hQ s e he p hp hpB) P

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPrimeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestPrimeBound.proof (h₁ : RestPrimeBoundOfFactor.Statement)
    (h₂ : SameFactorBound.Statement) (h₃ : OtherFactorBound.Statement) :
    RestPrimeBound.Statement := by
  intro f r a c B₀ hf hr ha hB
  obtain ⟨_, hQex, hsame⟩ := h₂ f r a c hf hr ha
  obtain ⟨_, _, hother⟩ := h₃ f r a c hf hr ha
  refine ⟨hQex, ?_⟩
  intro Q hQ s e he p hp hBp
  refine h₁ f r a c B₀ hf hr ha hB Q ?_ s e he p hp hBp
  intro k hk2 hkN τ τ'
  by_cases h : τ' = τ
  · subst h
    exact hsame Q hQ k hk2 hkN τ'
  · exact (hother Q hQ k hk2 hkN τ τ' h).2

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.POtherFactorBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem OtherFactorBound.add_le_mul_add_one {r a : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a) :
    r + a ≤ r * a + 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  nlinarith [Nat.zero_le (r' * a')]

theorem OtherFactorBound.coeff_bound (hS : SchurSignCoefficient.Statement)
    (hH : HookSumBound.Statement) (r a k : ℕ) (c : SmallBlock) (hk1 : 1 ≤ k) (hkN : k ≤ r + a)
    (S : MvPolynomial (Fin (r + a)) ℚ)
    (hSeq : powerSumHom (r + a) S =
      ∑ nu ∈ partitionsOf r k,
        C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
          aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu)) :
    |S.coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
  set e := Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1 with he
  have hs : c.sign = 1 ∨ c.sign = -1 := by cases c <;> simp [SmallBlock.sign]
  have hex : ∀ nu : Fin r → ℕ, ∃ T : MvPolynomial (Fin (r + a)) ℚ, nu ∈ partitionsOf r k →
      powerSumHom (r + a) T = aeval (fun i : Fin (r + a) => C c.sign * X i)
          (schur (Fin (r + a)) nu) ∧
        AddMonoidAlgebra.coeff T e = c.sign ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0 := by
    intro nu
    by_cases hnu : nu ∈ partitionsOf r k
    · have hmem := hnu
      simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hmem
      obtain ⟨T, hT1, hT2⟩ := hS (r + a) r k hk1 hkN nu c.sign hs
        (fun i j hij => hmem.2 i j hij) hmem.1
      exact ⟨T, fun _ => ⟨hT1, hT2⟩⟩
    · exact ⟨0, fun h => absurd h hnu⟩
  choose T hT using hex
  have hSsum : S = ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * T nu := by
    apply Flag.powerSumHom_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hSeq, map_sum]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [map_mul, (hT nu hnu).1]
    congr 1
    simp [powerSumHom]
  have hterm : ∀ nu ∈ partitionsOf r k,
      |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| =
        (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) else 0) / k := by
    intro nu hnu
    rw [(hT nu hnu).2, abs_mul, abs_mul, abs_pow]
    have habs : |c.sign| = 1 := by rcases hs with h | h <;> simp [h]
    rw [habs, one_pow, one_mul, Nat.abs_cast]
    split_ifs
    · rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]; ring
    · simp
  calc |S.coeff e|
      = |∑ nu ∈ partitionsOf r k,
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| := by
        rw [hSsum, coeff_sum]
        simp only [coeff_C_mul]
    _ ≤ ∑ nu ∈ partitionsOf r k,
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = (∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)|) / k := by
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_filter]
        simp only [Nat.abs_cast]
    _ ≤ (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
        gcongr
        exact hH r a k (fun nu => ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)) hk1
          (fun nu _ => by simp)

theorem OtherFactorBound.proof (hO : OtherFactorFormula.Statement)
    (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    OtherFactorBound.Statement := by
  intro f r a c hf hr ha
  have hP : (0 : ℚ) < numStandardTable (rectangle r a) := by exact_mod_cast hR r a
  have hkey := OtherFactorBound.add_le_mul_add_one hr ha
  refine ⟨?_, hD f r a c, ?_⟩
  · obtain ⟨C₀, hC₀, hJ, -⟩ := hF f r a c hf hr ha
    rw [hJ]
    have h1 : ((f * (r * a)).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    have := hP.ne'
    simp_all
  intro Q hQ k hk2 hkN τ τ' hne
  have hk1 : k - 1 ≤ r * a := by omega
  refine ⟨fun h => absurd h (by omega), ?_⟩
  have hf2 : 2 ≤ f := by
    by_contra h
    have : f = 1 := by omega
    subst this
    exact hne (Subsingleton.elim _ _)
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hO f r a c hf2 hr ha
  obtain ⟨S, hSeq, hTk⟩ := hT Q hQ k hk2 hkN τ τ' hne
  have hcoef := OtherFactorBound.coeff_bound hS hH r a k c (by omega) hkN S hSeq
  have hchi := hB r (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    (fun _ _ _ => le_rfl) (by
      intro q hq
      simp only [List.mem_cons, List.mem_replicate] at hq
      omega)
  rw [hTk, hJ]
  set y := AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)
  set z := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
  set P : ℚ := (numStandardTable (rectangle r a) : ℚ) with hPdef
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have hg : g + 2 - 2 = g := by omega
  rw [hg]

  set n1 := r * a with hn1
  set n := (g + 2) * n1 with hn
  have hD1 : ((n1 + k).factorial : ℚ) =
      (Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial n1 k
    rw [← this]; push_cast; ring
  have hA : (n1.factorial : ℚ) =
      ((n1 - (k - 1)).factorial : ℚ) * (n1.descFactorial (k - 1) : ℚ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hk1).symm
  have hM : ((n + 1).factorial : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hdesc : (0 : ℚ) < n1.descFactorial (k - 1) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hk1
  have hchoose : (0 : ℚ) < Nat.choose (n1 + k) k := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hBpos : (0 : ℚ) < (n1 - (k - 1)).factorial := by positivity
  have hKpos : (0 : ℚ) < k.factorial := by positivity
  have hnpos : (0 : ℚ) < n.factorial := by positivity
  have hkpos : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)

  have hstep : |C₀ * k * ((n + 1).factorial : ℚ) /
        (((n1 + k).factorial : ℚ) * ((n1 - (k - 1)).factorial : ℚ) *
          ((n1).factorial : ℚ) ^ g) * P ^ g * z * y| ≤
      ((n + 1 : ℕ) : ℚ) * |C₀ * (n.factorial : ℚ) / ((n1).factorial : ℚ) ^ (g + 2) * P ^ (g + 2)| *
        ((n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)) / (k.factorial : ℚ) := by
    rw [hD1, hM]
    have hApos : (0 : ℚ) < n1.factorial := by positivity
    simp only [abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_pos hP]
    have hX1 : 0 ≤ |C₀| * (k : ℚ) * (((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ)) /
        ((Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) *
          ((n1 - (k - 1)).factorial : ℚ) * (n1.factorial : ℚ) ^ g) * P ^ g := by positivity
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hchi hX1) hcoef (abs_nonneg _)
      (by positivity)).trans (le_of_eq ?_)
    field_simp
    rw [hA]
    ring
  refine hstep.trans ?_

  have hX : (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1) ≤ restX r a ^ (k - 1) := by
    have h1 : (n1.descFactorial (k - 1) : ℚ) ≤ (n1 : ℚ) ^ (k - 1) := by
      exact_mod_cast Nat.descFactorial_le_pow n1 (k - 1)
    have h2 : (2 * (n1 : ℚ)) ≤ restX r a := by
      simp only [restX, hn1]; push_cast; nlinarith [(Nat.cast_nonneg (r + a : ℕ) : (0 : ℚ) ≤ _)]
    calc (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)
        ≤ (n1 : ℚ) ^ (k - 1) * 2 ^ (k - 1) := by gcongr
      _ = (2 * (n1 : ℚ)) ^ (k - 1) := by ring
      _ ≤ restX r a ^ (k - 1) := by gcongr
  have hpos1 : 0 ≤ ((n + 1 : ℕ) : ℚ) := by positivity
  gcongr

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneousDecomposition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem RestPolynomialHomogeneousDecomposition.proof (h1 : CoinvAboveTop.Statement)
    (h2 : RestPolynomialHomogeneous.Statement) :
    RestPolynomialHomogeneousDecomposition.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, hF⟩ := h1 ℚ f (r + a) (topDegree f (r + a) + 1) (restPolynomial f r a c)
    (h2 f r a c) (by unfold Coinv.coinvTop topDegree; omega)
  exact ⟨Q, hF, hQ⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialDecomposes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

theorem RestPolynomialDecomposes.proof (h1 : RestPolynomialHomogeneousDecomposition.Statement) :
    RestPolynomialDecomposes.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, -⟩ := h1 f r a c
  exact ⟨Q, hQ⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchurSignCoefficient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchurSignCoefficient.coeff_aeval_diagonal {N : ℕ} (c : Fin N → ℚ)
    (P : MvPolynomial (Fin N) ℚ) (e : Fin N →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun i : Fin N => C (c i) * X i) P) e = (∏ i, c i ^ e i) * AddMonoidAlgebra.coeff P e := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hmon : aeval (fun i : Fin N => C (c i) * X i) (monomial u a) =
        monomial u (a * ∏ i, c i ^ u i) := by
      rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
        Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, algebraMap_eq, C_mul, ← C_pow, ← map_prod]
      ring
    rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with hue
    · subst hue; ring
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem SchurSignCoefficient.aeval_smul_powerSumHom (N : ℕ) (s : ℚ)
    (S : MvPolynomial (Fin N) ℚ) :
    aeval (fun i : Fin N => C s * X i) (powerSumHom N S) =
      powerSumHom N (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S) := by
  have key : (aeval (fun i : Fin N => C s * X i)).comp (powerSumHom N) =
      (powerSumHom N).comp (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, powerSumHom, aeval_X, map_mul, aeval_C, algebraMap_eq, psum,
      map_sum, map_pow, mul_pow, Finset.mul_sum]
  exact DFunLike.congr_fun key S

theorem SchurSignCoefficient.proof (h : SchurPowerSumCoefficient.Statement) :
    SchurSignCoefficient.Statement := by
  intro N r k hk1 hkN nu s _ hnu hsum
  obtain ⟨S₀, hS₀, hc₀⟩ := h N r k hk1 hkN nu hnu hsum
  refine ⟨aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S₀, ?_, ?_⟩
  · rw [← SchurSignCoefficient.aeval_smul_powerSumHom, hS₀]
  · rw [SchurSignCoefficient.coeff_aeval_diagonal, hc₀]
    congr 1
    rw [Finset.prod_eq_single (⟨k - 1, by omega⟩ : Fin N)]
    · rw [Finsupp.single_eq_same, pow_one]
      congr 1
      simp only
      omega
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg (Ne.symm hb), pow_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTablePos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem numStandardTable_pos {m : ℕ} (lam : Fin m → ℕ) : 0 < numStandardTable lam := by
  classical
  let t : Finset (Fin m ×ₗ ℕ) := (youngCells lam).map (toLex : Fin m × ℕ ≃ _).toEmbedding
  have ht : t.card = (youngCells lam).card := Finset.card_map _
  let e : Fin (youngCells lam).card ≃o t := t.orderIsoOfFin ht
  let g : youngCells lam ≃ t :=
    Equiv.subtypeEquiv toLex fun p => by simp [t]
  let T : youngCells lam ≃ Fin (youngCells lam).card := g.trans e.symm.toEquiv
  have hT : ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q := by
    intro p q h1 h2
    apply e.symm.monotone
    show toLex p.1 ≤ toLex q.1
    exact Prod.Lex.toLex_mono ⟨h1, h2⟩
  have : Nonempty {T : youngCells lam ≃ Fin (youngCells lam).card //
      ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q} := ⟨⟨T, hT⟩⟩
  exact Nat.card_pos

theorem RectangleTablePos.intersectionNumber_baseChange : RectangleTablePos.Statement :=
  fun r a => numStandardTable_pos (rectangle r a)

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookSumBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem exists_hookShape_of_isHook {r k : ℕ} (hk : 1 ≤ k) (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (hhook : ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) :
    ∃ l, l < r ∧ l < k ∧ nu = hookShape r k l := by
  set g : ℕ → ℕ := fun j => if h : j < r then nu ⟨j, h⟩ else 0 with hg
  have hgnu : ∀ i : Fin r, g i = nu i := fun i => by simp [hg, i.isLt]
  have hsumg : ∑ j ∈ range r, g j = k := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [hgnu]
    exact hsum
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      simp at hsumg
      omega
    · exact h
  have hanti_g : ∀ i j, i ≤ j → g j ≤ g i := by
    intro i j hij
    by_cases hj : j < r
    · have hi : i < r := lt_of_le_of_lt hij hj
      simp only [hg, dif_pos hj, dif_pos hi]
      exact hanti (show (⟨i, hi⟩ : Fin r) ≤ ⟨j, hj⟩ from hij)
    · simp [hg, dif_neg hj]
  have hle1 : ∀ j, 1 ≤ j → g j ≤ 1 := by
    intro j hj
    by_cases h : j < r
    · simp only [hg, dif_pos h]
      exact hhook ⟨j, h⟩ (by simp only; omega)
    · simp [hg, dif_neg h]
  have hsplit : g 0 + ∑ j ∈ Ico 1 r, g j = k := by
    rw [← Finset.sum_eq_sum_Ico_succ_bot hr, ← Finset.range_eq_Ico]
    exact hsumg
  set t := ∑ j ∈ Ico 1 r, g j with ht
  have hrow : ∀ i, 1 ≤ i → i < r → g i = if i ≤ t then 1 else 0 := by
    intro i hi1 hir
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle1 i hi1) with h0 | h1
    · have hz : ∀ j ∈ Ico i r, g j = 0 := fun j hj => by
        have := hanti_g i j (mem_Ico.mp hj).1
        omega
      have hti : t ≤ i - 1 := by
        rw [ht, ← Finset.sum_Ico_consecutive g hi1 hir.le, Finset.sum_eq_zero hz, add_zero]
        calc ∑ j ∈ Ico 1 i, g j ≤ ∑ j ∈ Ico 1 i, 1 :=
              Finset.sum_le_sum fun j hj => hle1 j (mem_Ico.mp hj).1
          _ = i - 1 := by simp
      rw [h0, if_neg (by omega)]
    · have ho : ∀ j ∈ Ico 1 (i + 1), g j = 1 := fun j hj => by
        have h2 := hanti_g j i (by have := (mem_Ico.mp hj).2; omega)
        have h3 := hle1 j (mem_Ico.mp hj).1
        omega
      have hit : i ≤ t := by
        rw [ht, ← Finset.sum_Ico_consecutive g (show 1 ≤ i + 1 by omega)
          (show i + 1 ≤ r by omega), Finset.sum_congr rfl ho]
        simp
      rw [h1, if_pos hit]
  have htr : t < r := by
    have : t ≤ r - 1 := by
      calc t ≤ ∑ j ∈ Ico 1 r, 1 := Finset.sum_le_sum fun j hj => hle1 j (mem_Ico.mp hj).1
        _ = r - 1 := by simp
    omega
  have hg0 : 1 ≤ g 0 := by
    by_contra h
    have hz : ∀ j, g j = 0 := fun j => by
      have := hanti_g 0 j (Nat.zero_le j)
      omega
    simp [hz] at hsumg
    omega
  refine ⟨t, htr, by omega, ?_⟩
  funext i
  rw [← hgnu i]
  unfold hookShape
  by_cases hi0 : (i : ℕ) = 0
  · rw [if_pos hi0, hi0]
    omega
  · rw [if_neg hi0, hrow i (by omega) i.isLt]

theorem HookSumBound.proof (hC : LemmaC.Statement) (hH : HookTableauCount.Statement) :
    HookSumBound.Statement := by
  intro r a k b hk hb
  have hB0 : (0 : ℚ) ≤ (Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a) := by
    positivity
  have hterm : ∀ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      |b nu| ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) *
        (numStandardTable nu : ℚ) := by
    intro nu hnu
    have hmem := (Finset.mem_filter.mp hnu).1
    have h := Finset.mem_filter.mp hmem
    have hsum : ∑ i, nu i = k := Finset.Nat.mem_antidiagonalTuple.mp h.1
    have hc := hC r a nu (fun i j hij => h.2 i j hij)
    rw [hsum] at hc
    calc |b nu| ≤ numStandardTable (fun i => a + nu i) := hb nu hmem
      _ ≤ _ := by exact_mod_cast hc
  have himg : (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) ⊆
      (range (min r k)).image (hookShape r k) := by
    intro nu hnu
    obtain ⟨hmem, hhook⟩ := Finset.mem_filter.mp hnu
    have h := Finset.mem_filter.mp hmem
    obtain ⟨l, hlr, hlk, rfl⟩ := exists_hookShape_of_isHook hk nu (fun i j hij => h.2 i j hij)
      (Finset.Nat.mem_antidiagonalTuple.mp h.1) hhook
    exact Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr (lt_min hlr hlk), rfl⟩
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hhooks : ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      (numStandardTable nu : ℚ) ≤ 2 ^ (k - 1) := by
    calc _ ≤ ∑ nu ∈ (range (min r k)).image (hookShape r k), (numStandardTable nu : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity
      _ ≤ ∑ l ∈ range (min r k), (numStandardTable (hookShape r k l) : ℚ) :=
          Finset.sum_image_le_of_nonneg fun _ _ => by positivity
      _ = ∑ l ∈ range (min r k), ((k - 1).choose l : ℚ) := by
          refine Finset.sum_congr rfl fun l hl => ?_
          have hl' := lt_min_iff.mp (Finset.mem_range.mp hl)
          rw [hH r k l hl'.2 hl'.1]
      _ ≤ ∑ l ∈ range k, ((k - 1).choose l : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right _ _))
            fun _ _ _ => by positivity
      _ = 2 ^ (k - 1) := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          rw [Nat.add_sub_cancel]
          exact_mod_cast Nat.sum_range_choose n
  calc _ ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) * 2 ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hhooks hB0
    _ = _ := by ring

end GroundTheory.Heights₂.Heights.RestTerms
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem CoinvStepReduction.full : CoinvStepReduction.Statement :=
  CoinvStepReduction.proof

theorem CoinvMonomialReduction.full : CoinvMonomialReduction.Statement :=
  CoinvMonomialReduction.proof CoinvStepReduction.full

theorem CoinvPolynomialReduction.full : CoinvPolynomialReduction.Statement :=
  CoinvPolynomialReduction.proof CoinvMonomialReduction.full

theorem CoinvIdealRepresentation.full : CoinvIdealRepresentation.Statement :=
  CoinvIdealRepresentation.proof

theorem HomogeneousComponentMul.full : HomogeneousComponentMul.Statement :=
  HomogeneousComponentMul.proof

theorem CoinvIdealComponent.full : CoinvIdealComponent.Statement :=
  CoinvIdealComponent.proof CoinvIdealRepresentation.full HomogeneousComponentMul.full

theorem CoinvStaircaseDegree.full : CoinvStaircaseDegree.Statement :=
  CoinvStaircaseDegree.proof

theorem CoinvStaircaseComponent.full : CoinvStaircaseComponent.Statement :=
  CoinvStaircaseComponent.proof CoinvStaircaseDegree.full

theorem FlagCoeffBlockPermute.full : FlagCoeffBlockPermute.Statement :=
  FlagCoeffBlockPermute.proof

theorem FlagAltCoeffInjective.full : FlagAltCoeffInjective.Statement :=
  FlagAltCoeffInjective.proof FlagCoeffBlockPermute.full

theorem FlagInjSumBound.full : FlagInjSumBound.Statement :=
  FlagInjSumBound.proof

theorem FlagStaircaseOrbit.full : FlagStaircaseOrbit.Statement :=
  FlagStaircaseOrbit.proof

theorem FlagVandermondeHomogeneous.full : FlagVandermondeHomogeneous.Statement :=
  FlagVandermondeHomogeneous.proof

theorem FlagAltTopDegree.full : FlagAltTopDegree.Statement :=
  FlagAltTopDegree.proof FlagCoeffBlockPermute.full FlagAltCoeffInjective.full FlagInjSumBound.full FlagStaircaseOrbit.full FlagVandermondeHomogeneous.full

theorem FlagAntisymHomogeneous.full : FlagAntisymHomogeneous.Statement :=
  FlagAntisymHomogeneous.proof

theorem FlagIntegralPermute.full : FlagIntegralPermute.Statement :=
  FlagIntegralPermute.proof FlagCoeffBlockPermute.full

theorem FlagIntegralAntisymmetrize.full : FlagIntegralAntisymmetrize.Statement :=
  FlagIntegralAntisymmetrize.proof FlagIntegralPermute.full

theorem FlagIntegralTopComponent.full : FlagIntegralTopComponent.Statement :=
  FlagIntegralTopComponent.proof FlagVandermondeHomogeneous.full

theorem FlagHomogeneousComponentMul.full : FlagHomogeneousComponentMul.Statement :=
  FlagHomogeneousComponentMul.proof

theorem FlagIntegralVandermondeMul.full : FlagIntegralVandermondeMul.Statement :=
  FlagIntegralVandermondeMul.proof FlagIntegralTopComponent.full FlagHomogeneousComponentMul.full FlagVandermondeHomogeneous.full

theorem FlagIntegralViaQuotient.full : FlagIntegralViaQuotient.Statement :=
  FlagIntegralViaQuotient.proof FlagIntegralAntisymmetrize.full FlagIntegralVandermondeMul.full

theorem FlagIntegralTopDegree.full : FlagIntegralTopDegree.Statement :=
  FlagIntegralTopDegree.proof FlagAltTopDegree.full FlagAntisymHomogeneous.full FlagIntegralViaQuotient.full

theorem FlagIntegralVandermondePos.full : FlagIntegralVandermondePos.Statement :=
  FlagIntegralVandermondePos.proof

theorem FlagSwapDivisible.full : FlagSwapDivisible.Statement :=
  FlagSwapDivisible.proof

theorem FlagDiffPrime.full : FlagDiffPrime.Statement :=
  FlagDiffPrime.proof

theorem FlagDiffNotDvd.full : FlagDiffNotDvd.Statement :=
  FlagDiffNotDvd.proof

theorem FlagProdPrimesDvd.full : FlagProdPrimesDvd.Statement :=
  FlagProdPrimesDvd.proof

theorem FlagVandermondeDvd.full : FlagVandermondeDvd.Statement :=
  FlagVandermondeDvd.proof FlagSwapDivisible.full FlagDiffPrime.full FlagDiffNotDvd.full FlagProdPrimesDvd.full

theorem FlagDividedDifferencePoly.full : FlagDividedDifferencePoly.Statement :=
  FlagDividedDifferencePoly.proof FlagVandermondeDvd.full

theorem FlagSymmetricMulAntisym.full : FlagSymmetricMulAntisym.Statement :=
  FlagSymmetricMulAntisym.proof

theorem FlagPowerSumSymmetric.full : FlagPowerSumSymmetric.Statement :=
  FlagPowerSumSymmetric.proof

theorem FlagAntisymDecomposition.full : FlagAntisymDecomposition.Statement :=
  FlagAntisymDecomposition.proof FlagSymmetricMulAntisym.full FlagPowerSumSymmetric.full

theorem FlagQuotientHomogeneous.full : FlagQuotientHomogeneous.Statement :=
  FlagQuotientHomogeneous.proof

theorem FlagRestrictHomogeneous.full : FlagRestrictHomogeneous.Statement :=
  FlagRestrictHomogeneous.proof

theorem FlagRestrictSymmetric.full : FlagRestrictSymmetric.Statement :=
  FlagRestrictSymmetric.proof

theorem FlagRestrictPowerSum.full : FlagRestrictPowerSum.Statement :=
  FlagRestrictPowerSum.proof

theorem FlagRestrictDecomposition.full : FlagRestrictDecomposition.Statement :=
  FlagRestrictDecomposition.proof FlagRestrictPowerSum.full

theorem FlagPowerSumPreimage.full : FlagPowerSumPreimage.Statement :=
  FlagPowerSumPreimage.proof

theorem FlagRestrictConstantCoeff.full : FlagRestrictConstantCoeff.Statement :=
  FlagRestrictConstantCoeff.proof

theorem LemmaA.full : LemmaA.Statement :=
  LemmaA.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full FlagDividedDifferencePoly.full FlagAntisymDecomposition.full FlagVandermondeHomogeneous.full FlagAntisymHomogeneous.full FlagQuotientHomogeneous.full FlagRestrictHomogeneous.full FlagRestrictSymmetric.full FlagRestrictDecomposition.full FlagPowerSumPreimage.full FlagRestrictConstantCoeff.full FlagIntegralViaQuotient.full

theorem SchAevalSignedRename.full : SchAevalSignedRename.Statement :=
  SchAevalSignedRename.proof

theorem SchAntisymmetrizePlace.full : SchAntisymmetrizePlace.Statement :=
  SchAntisymmetrizePlace.proof

theorem SchAlternantHomogeneous.full : SchAlternantHomogeneous.Statement :=
  SchAlternantHomogeneous.proof

theorem SchSmallBlockProduct.full : SchSmallBlockProduct.Statement :=
  SchSmallBlockProduct.proof SchAevalSignedRename.full SchAlternantHomogeneous.full

theorem SchAlternantRenamePlace.full : SchAlternantRenamePlace.Statement :=
  SchAlternantRenamePlace.proof

theorem SchConcatExponent.full : SchConcatExponent.Statement :=
  SchConcatExponent.proof

theorem SchConcatAlternant.full : SchConcatAlternant.Statement :=
  SchConcatAlternant.proof SchAlternantRenamePlace.full SchConcatExponent.full

theorem SchConcatAlternantZero.full : SchConcatAlternantZero.Statement :=
  SchConcatAlternantZero.proof

theorem SchBlockVandermondeOne.full : SchBlockVandermondeOne.Statement :=
  SchBlockVandermondeOne.proof

theorem SchSchurHomogeneous.full : SchSchurHomogeneous.Statement :=
  SchSchurHomogeneous.proof

theorem LemmaB.full : LemmaB.Statement :=
  LemmaB.proof SchAevalSignedRename.full SchAntisymmetrizePlace.full SchSmallBlockProduct.full SchConcatAlternant.full SchConcatAlternantZero.full SchBlockVandermondeOne.full SchSchurHomogeneous.full

theorem CombCardYoungCells.full : CombCardYoungCells.Statement :=
  CombCardYoungCells.proof

theorem CombTableauRowCount.full : CombTableauRowCount.Statement :=
  CombTableauRowCount.proof

theorem CombTableauRowPrefix.full : CombTableauRowPrefix.Statement :=
  CombTableauRowPrefix.proof

theorem CombTableauRowLattice.full : CombTableauRowLattice.Statement :=
  CombTableauRowLattice.proof

theorem CombYoungRowCard.full : CombYoungRowCard.Statement :=
  CombYoungRowCard.proof

theorem CombWordOfTableau.full : CombWordOfTableau.Statement :=
  CombWordOfTableau.proof CombTableauRowCount.full CombTableauRowPrefix.full CombTableauRowLattice.full CombYoungRowCard.full

theorem CombCellOfWordMem.full : CombCellOfWordMem.Statement :=
  CombCellOfWordMem.proof

theorem CombCellOfWordInj.full : CombCellOfWordInj.Statement :=
  CombCellOfWordInj.proof

theorem CombCellOfWordMono.full : CombCellOfWordMono.Statement :=
  CombCellOfWordMono.proof

theorem CombTableauOfWord.full : CombTableauOfWord.Statement :=
  CombTableauOfWord.proof CombCellOfWordMem.full CombCellOfWordInj.full CombCellOfWordMono.full

theorem CombTableEqWords.full : CombTableEqWords.Statement :=
  CombTableEqWords.proof CombCardYoungCells.full CombWordOfTableau.full CombTableauOfWord.full

theorem CombCfUpdateZero.full : CombCfUpdateZero.Statement :=
  CombCfUpdateZero.proof

theorem CombCfAtStair.full : CombCfAtStair.Statement :=
  CombCfAtStair.proof CombCfUpdateZero.full

theorem CombCfMonomialPsumOne.full : CombCfMonomialPsumOne.Statement :=
  CombCfMonomialPsumOne.proof

theorem CombDetDescFactorial.full : CombDetDescFactorial.Statement :=
  CombDetDescFactorial.proof

theorem CombCfVandermondePsumOne.full : CombCfVandermondePsumOne.Statement :=
  CombCfVandermondePsumOne.proof CombCfMonomialPsumOne.full CombDetDescFactorial.full

theorem FrobeniusDimensionFormula.full : FrobeniusDimensionFormula.Statement :=
  FrobeniusDimensionFormula.proof CombTableEqWords.full CombCfAtStair.full CombCfVandermondePsumOne.full

theorem LemmaC.full : LemmaC.Statement :=
  LemmaC.proof FrobeniusDimensionFormula.full

theorem SchPowerSumHomWeighted.full : SchPowerSumHomWeighted.Statement :=
  SchPowerSumHomWeighted.proof

theorem SchWeightedPreimage.full : SchWeightedPreimage.Statement :=
  SchWeightedPreimage.proof SchPowerSumHomWeighted.full

theorem SchPowerSumAtRootsOfUnity.full : SchPowerSumAtRootsOfUnity.Statement :=
  SchPowerSumAtRootsOfUnity.proof

theorem SchEvalPowerSumHom.full : SchEvalPowerSumHom.Statement :=
  SchEvalPowerSumHom.proof SchPowerSumAtRootsOfUnity.full

theorem SchSchurRowsToK.full : SchSchurRowsToK.Statement :=
  SchSchurRowsToK.proof

theorem SchProdOneSubRootsOfUnity.full : SchProdOneSubRootsOfUnity.Statement :=
  SchProdOneSubRootsOfUnity.proof

theorem SchCompleteGenerating.full : SchCompleteGenerating.Statement :=
  SchCompleteGenerating.proof

theorem SchCompleteAtRootsOfUnity.full : SchCompleteAtRootsOfUnity.Statement :=
  SchCompleteAtRootsOfUnity.proof SchProdOneSubRootsOfUnity.full SchCompleteGenerating.full

theorem SchSchurEvalMatrix.full : SchSchurEvalMatrix.Statement :=
  SchSchurEvalMatrix.proof SchCompleteAtRootsOfUnity.full

theorem SchRootOfUnityBialternant.full : SchRootOfUnityBialternant.Statement :=
  SchRootOfUnityBialternant.proof SchSchurEvalMatrix.full

theorem SchRootOfUnityRowsPerm.full : SchRootOfUnityRowsPerm.Statement :=
  SchRootOfUnityRowsPerm.proof

theorem SchRootOfUnityRowsEq.full : SchRootOfUnityRowsEq.Statement :=
  SchRootOfUnityRowsEq.proof

theorem SchHookResidues.full : SchHookResidues.Statement :=
  SchHookResidues.proof

theorem SchResidueCount.full : SchResidueCount.Statement :=
  SchResidueCount.proof

theorem SchNonHookResidues.full : SchNonHookResidues.Statement :=
  SchNonHookResidues.proof SchResidueCount.full

theorem SchRootOfUnityVandermondeNe.full : SchRootOfUnityVandermondeNe.Statement :=
  SchRootOfUnityVandermondeNe.proof

theorem SchJTMatrixDetAtRoots.full : SchJTMatrixDetAtRoots.Statement :=
  SchJTMatrixDetAtRoots.proof SchRootOfUnityBialternant.full SchRootOfUnityRowsPerm.full SchRootOfUnityRowsEq.full SchHookResidues.full SchNonHookResidues.full SchRootOfUnityVandermondeNe.full

theorem SchSchurAtRootsOfUnity.full : SchSchurAtRootsOfUnity.Statement :=
  SchSchurAtRootsOfUnity.proof SchSchurRowsToK.full SchSchurEvalMatrix.full SchJTMatrixDetAtRoots.full

theorem SchurPowerSumCoefficient.full : SchurPowerSumCoefficient.Statement :=
  SchurPowerSumCoefficient.proof SchWeightedPreimage.full SchEvalPowerSumHom.full SchSchurHomogeneous.full SchSchurAtRootsOfUnity.full

theorem SchStrictAntiSplit.full : SchStrictAntiSplit.Statement :=
  SchStrictAntiSplit.proof

theorem SchAltPartitionExpansion.full : SchAltPartitionExpansion.Statement :=
  SchAltPartitionExpansion.proof SchStrictAntiSplit.full

theorem FrobeniusCharacterFormula.full : FrobeniusCharacterFormula.Statement :=
  FrobeniusCharacterFormula.proof SchAltPartitionExpansion.full

theorem CombSortLe.full : CombSortLe.Statement :=
  CombSortLe.proof

theorem CombSortShift.full : CombSortShift.Statement :=
  Comb.CombSortShift.proof CombSortLe.full

theorem CombSortShiftDistinct.full : CombSortShiftDistinct.Statement :=
  CombSortShiftDistinct.proof

theorem CombPcntAppend.full : CombPcntAppend.Statement :=
  CombPcntAppend.proof

theorem CombExtendWord.full : CombExtendWord.Statement :=
  CombExtendWord.proof CombPcntAppend.full

theorem CombStripSum.full : CombStripSum.Statement :=
  CombStripSum.proof CombCfAtStair.full CombSortShift.full CombSortShiftDistinct.full CombExtendWord.full

theorem CombCfBound.full : CombCfBound.Statement :=
  CombCfBound.proof CombCfAtStair.full CombSortShift.full CombStripSum.full

theorem CharacterBound.full : CharacterBound.Statement :=
  CharacterBound.proof CombTableEqWords.full CombCfBound.full

theorem CharacterAtIdentity.full : CharacterAtIdentity.Statement :=
  CharacterAtIdentity.proof CombTableEqWords.full CombCfAtStair.full

theorem CoinvAboveTop.full : CoinvAboveTop.Statement :=
  CoinvAboveTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full

theorem VandermondeOfHomogeneous.full : VandermondeOfHomogeneous.Statement :=
  VandermondeOfHomogeneous.proof

theorem RestPolynomialHomogeneous.full : RestPolynomialHomogeneous.Statement :=
  RestPolynomialHomogeneous.proof VandermondeOfHomogeneous.full

theorem RestPolynomialHomogeneousDecomposition.full : RestPolynomialHomogeneousDecomposition.Statement :=
  RestPolynomialHomogeneousDecomposition.proof CoinvAboveTop.full RestPolynomialHomogeneous.full

theorem RestPolynomialDecomposes.full : RestPolynomialDecomposes.Statement :=
  RestPolynomialDecomposes.proof RestPolynomialHomogeneousDecomposition.full

theorem SameFactorFormula.full : SameFactorFormula.Statement :=
  SameFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

theorem SchurSignCoefficient.full : SchurSignCoefficient.Statement :=
  SchurSignCoefficient.proof SchurPowerSumCoefficient.full

theorem HookTableauCount.full : HookTableauCount.Statement :=
  HookTableauCount.proof FrobeniusDimensionFormula.full

theorem HookSumBound.full : HookSumBound.Statement :=
  HookSumBound.proof LemmaC.full HookTableauCount.full

theorem SameFactorBound.full : SameFactorBound.Statement :=
  SameFactorBound.proof SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

theorem OtherFactorFormula.full : OtherFactorFormula.Statement :=
  OtherFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

theorem OtherFactorBound.full : OtherFactorBound.Statement :=
  OtherFactorBound.proof OtherFactorFormula.full SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

theorem RestInnerTsumBound.full : RestInnerTsumBound.Statement :=
  RestInnerTsumBound.proof

theorem RestKSumBound.full : RestKSumBound.Statement :=
  RestKSumBound.proof

theorem RestPrimeBoundOfFactor.full : RestPrimeBoundOfFactor.Statement :=
  RestPrimeBoundOfFactor.proof RestInnerTsumBound.full RestKSumBound.full

theorem RestPrimeBound.full : RestPrimeBound.Statement :=
  RestPrimeBound.proof RestPrimeBoundOfFactor.full SameFactorBound.full OtherFactorBound.full

theorem RestBoundOfPrimeBound.full : RestBoundOfPrimeBound.Statement :=
  RestBoundOfPrimeBound.proof

theorem RestBound.full : RestBound.Statement :=
  RestBound.proof RestPrimeBound.full RestBoundOfPrimeBound.full

end RestTerms

end GroundTheory.Heights₂.Heights
