module

public import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.FrRevInj
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TensZeroRight
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestPlOf

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ProdRangeZmod
section -- merged from Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.PlMonPsiExpPAdd
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks

section LevP

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def psiExpP (a : TL J nL r × Fin r →₀ ℕ) : TV n' (m + 1) →₀ ℕ :=
  a.sum fun v e => Finsupp.single (plVar Fr hk nL v.1 v.2) (lowP Fr p v.1 * e)

def PsiP : MvPolynomial (TL J nL r × Fin r) (KK O) →ₐ[KK O] MvPolynomial (TV n' (m + 1)) (KK O) :=
  aeval fun v => X (plVar Fr hk nL v.1 v.2) ^ lowP Fr p v.1

theorem PsiP_monomial (a : TL J nL r × Fin r →₀ ℕ) (c : KK O) :
    PsiP (O := O) Fr p hk nL (monomial a c) = monomial (psiExpP Fr p hk nL a) c := by
  unfold PsiP psiExpP
  rw [aeval_monomial, monomial_finsupp_sum_index, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun v _ => ?_
  rw [← pow_mul, X_pow_eq_monomial]

variable {Fr nL}

theorem plVar_inj {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) {x x' : TL J nL r} {a a' : Fin r}
    (h : plVar Fr hk nL x a = plVar Fr hk nL x' a') : x = x' ∧ a = a' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Formalism.MainNotions.TestSideWords.plVar] at h1 h2
  exact ⟨dg_inj hV hr hJ hnL h1, Fin.castAdd_injective r K (Fin.cast_injective _ h2)⟩

theorem psiExpP_apply {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (a : TL J nL r × Fin r →₀ ℕ) (x : TL J nL r) (a' : Fin r) :
    psiExpP Fr p hk nL a (plVar Fr hk nL x a') = lowP Fr p x * a (x, a') := by
  unfold psiExpP
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single (x, a')]
  · rw [Finsupp.single_eq_same]
  · intro v _ hv
    rw [Finsupp.single_apply, if_neg]
    intro h
    obtain ⟨e1, e2⟩ := plVar_inj hk hV hr hJ hnL h
    exact hv (Prod.ext e1 e2)
  · intro _
    rw [mul_zero, Finsupp.single_zero, Finsupp.zero_apply]

theorem plMon_psiExpP_add {L₁ N₁ : ℕ} (hp : 0 < p) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (a : TL J nL r × Fin r →₀ ℕ) (c : TV n' (m + 1) →₀ ℕ) :
    plMon Fr p hk nL (psiExpP Fr p hk nL a + c) = plMon Fr p hk nL c + a := by
  ext ⟨x, a'⟩
  have hP : 0 < lowP Fr p x := pow_pos hp _
  simp only [plMon, Finsupp.coe_equivFunOnFinite_symm, Finsupp.add_apply]
  rw [psiExpP_apply p hk hV hr hJ hnL, Nat.mul_add_div hP, add_comm]

theorem levelAtPrime_character_mul {L₁ N₁ : ℕ} (hp : 0 < p) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (H : MvPolynomial (TL J nL r × Fin r) (KK O))
    (c : TV n' (m + 1) →₀ ℕ) :
    levP Fr p hk nL (PsiP (O := O) Fr p hk nL H * monomial c 1) = monomial (plMon Fr p hk nL c) 1 * H := by
  induction H using MvPolynomial.induction_on' with
  | monomial a k =>
    rw [PsiP_monomial, monomial_mul, T5.monomialSubstitution_monomial, plMon_psiExpP_add p hk hp hV hr hJ hnL, monomial_mul, mul_one,
      one_mul]
  | add F G hF hG => rw [map_add (f := _), add_mul, T5.monomialSubstitution_add, hF, hG, mul_add]

end LevP

end Formalism.MainNotions.NormalSetCounting
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.NormalSetCounting
  Formalism.MainNotions.TraceSpectra

theorem restSpec : RestSpec := Formalism.MainNotions.NormalSetCounting.restSpec

theorem prod_range_zmod {M : Type*} [CommMonoid M] (J : ℕ) [NeZero J] (f : ℕ → M) :
    ∏ i ∈ Finset.range J, f i = ∏ j : ZMod J, f j.val := by
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by have := NeZero.ne J; omega⟩
  exact (Fin.prod_univ_eq_prod_range f (n + 1)).symm

theorem seg_PsiP (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) {J : ℕ}
    [NeZero J] (Dt : SignedChainData p O r J) (hJ : J = Fr.J) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) (hA : A ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)}) :
    MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) (phSeg O K p Fr (segZ j) (plEmb O r K A))) =
      PsiP (O := O) Fr p hk Dt.nL (Dt.ph (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) A))) := by
  have hsp := Formalism.MainNotions.NormalSetCounting.restSpec n' r Fr L₁ N₁ hV J Dt.nL hnL j
  obtain ⟨-, hper, hmono, hgap, -⟩ := hV
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  rw [MvPolynomial.supported_eq_adjoin_X] at hA
  induction hA using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨y, a⟩, hy, rfl⟩ := hx
    have hy' : y ∈ Fr.letters (segZ j) := hy
    simp only [plEmb, phSeg, chi, rename_X, aeval_X, map_pow, map_X, if_pos hy']
    rcases hsp y hy' with ⟨l, rfl, hml⟩ | ⟨mm, rfl, hml⟩ | ⟨mm, rfl, hml⟩
    · rw [hml]
      simp only [SignedChainData.ph, PsiP, aeval_X]
      rfl
    · rw [hml]
      simp only [SignedChainData.ph, PsiP, aeval_X]
      rfl
    · rw [hml]
      simp only [SignedChainData.ph, PsiP, aeval_X, map_pow, ← pow_mul, SignedChainData.P]
      obtain ⟨s, hs, hsh⟩ := Formalism.MainNotions.Proposition5Numerics.DdG.shift Fr hper hJ (j - 1)
      simp only [sub_add_cancel] at hsh
      have hA1 : ∀ k, Fr.fr (segZ (j - 1)) k = Fr.fr (segZ j - 1) k + s := fun k => (hsh k).1
      have hA2 : ∀ k, Fr.fr (segZ (j - 1) + 1) k = Fr.fr (segZ j) k + s := fun k => (hsh k).2
      have e1 : plVar Fr hk Dt.nL (⟨j - 1, Sum.inr mm⟩ : TL J Dt.nL r) a =
          castV hk (posOf n' (Fr.fr (segZ j - 1) (r - 1 - mm.val)), Fin.castAdd K a) := by
        show (posOf n' (Fr.fr (segZ (j - 1)) (r - 1 - mm.val)), Fin.cast hk.symm (Fin.castAdd K a)) = _
        rw [hA1]
        rcases hs with rfl | rfl
        · rw [add_zero]
          rfl
        · rw [Formalism.MainNotions.Proposition5Numerics.DdG.posOf_add_n]
          rfl
      have e2 : lowP Fr p (⟨j - 1, Sum.inr mm⟩ : TL J Dt.nL r) * p ^ Dt.gP (j - 1) mm =
          p ^ Fr.dist (segZ j) (Fr.fr (segZ j - 1) (r - 1 - mm.val)) := by
        show p ^ Fr.dist (segZ (j - 1)) (Fr.fr (segZ (j - 1)) (r - 1 - mm.val)) * p ^ Dt.gP (j - 1) mm = _
        rw [← pow_add, hgP]
        congr 1
        simp only [Frames.dist, hA1, hA2]
        have h1 := Formalism.MainNotions.Proposition5Numerics.DdG.fr_le Fr hmono (segZ j - 1) (Nat.sub_le (r - 1) mm.val) (by omega)
        have h2 := hgap (segZ j - 1)
        simp only [sub_add_cancel] at h2
        have h3 := Formalism.MainNotions.Proposition5Numerics.DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (r - 1)) (by omega)
        omega
      rw [e1, e2]
  | algebraMap c =>
    simp only [MvPolynomial.algebraMap_eq, MvPolynomial.algHom_C, map_C]
  | add x y _ _ hx hy =>
    simp only [map_add (f := _)]
    rw [hx, hy]
  | mul x y _ _ hx hy =>
    simp only [map_mul]
    rw [hx, hy]

theorem restTr : RestTr := by
  unfold RestTr
  intro p _ n' r K m _ _ _ O _ _ _ hk Fr L₁ N₁ hV hn' J _ Dt hT A hA l hl ga hPE
  obtain ⟨hJ, hnL, hsgn, hgP, -, -⟩ := hT
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  refine ⟨?_, ?_⟩
  · have hseg : ∀ j : ZMod J,
        MvPolynomial.map (algebraMap O (KK O))
          (rename (castV hk) (phSeg O K p Fr ((j.val : ℕ) : ℤ) (plEmb O r K (A ((j.val : ℕ) : ℤ))))) =
        PsiP (O := O) Fr p hk Dt.nL
          (Dt.ph (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j))))) := by
      intro j
      have hj : j.val < Fr.J := by
        rw [← hJ]
        exact ZMod.val_lt j
      exact seg_PsiP p O hk Fr L₁ N₁ hV Dt hJ hnL hgP j (A (segZ j)) (hA j.val hj)
    have hz : zPl p O hk Fr A l ga =
        PsiP (O := O) Fr p hk Dt.nL (∏ j : ZMod J,
          Dt.ph (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j))))) *
        monomial (l.mapDomain (castV hk) + ga) 1 := by
      unfold zPl
      simp only [map_mul, map_prod, rename_monomial, map_monomial, map_one]
      rw [mul_assoc, monomial_mul, one_mul, ← hJ, prod_range_zmod J]
      congr 1
      exact Finset.prod_congr rfl (fun j _ => hseg j)
    rw [hz, Formalism.MainNotions.NormalSetCounting.levelAtPrime_character_mul p hk hp hV hr hJ hnL]
  · intro j ll a hs
    have hs' := hsgn j ll
    rw [hs] at hs'
    have hodd : ¬ Even (llPos Fr (segZ j) ll.val) := of_decide_eq_false hs'.symm
    have hll : ll.val < (Fr.LLset (segZ j)).card := by
      rw [← hnL]
      exact ll.isLt
    have hmem := Formalism.MainNotions.Proposition5Numerics.DdG.llPos_mem Fr (segZ j) ll.val hll
    obtain ⟨hlet, hW⟩ := Formalism.MainNotions.Proposition5Numerics.LL_sub_letters hV hr (segZ j) _ hmem
    have hlab := hl (segZ j) _ hlet hW (Fin.castAdd K a)
    have hinj : Function.Injective (castV (n' := n') hk) := by
      intro v w h
      simp only [castV, Prod.mk.injEq] at h
      exact Prod.ext h.1 (Fin.ext (by simpa using congrArg Fin.val h.2))
    have hpv : plVar Fr hk Dt.nL (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) a =
        castV hk (posOf n' (llPos Fr (segZ j) ll.val), Fin.castAdd K a) := rfl
    have hgz : ga (plVar Fr hk Dt.nL (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) a) = 0 := by
      by_contra hne
      have hev : Even (posOf n' (llPos Fr (segZ j) ll.val)).val := (hPE _ hne).2
      apply hodd
      have hn0 : (n' : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n'
      have hnn : 0 ≤ llPos Fr (segZ j) ll.val % (n' : ℤ) := Int.emod_nonneg _ hn0
      have hlt : llPos Fr (segZ j) ll.val % (n' : ℤ) < n' :=
        Int.emod_lt_of_pos _ (by exact_mod_cast NeZero.pos n')
      have hv : ((posOf n' (llPos Fr (segZ j) ll.val)).val : ℤ) = llPos Fr (segZ j) ll.val % (n' : ℤ) := by
        show (((llPos Fr (segZ j) ll.val % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = _
        have hlt' : (llPos Fr (segZ j) ll.val % (n' : ℤ)).toNat < n' := by omega
        rw [Nat.mod_eq_of_lt hlt', Int.toNat_of_nonneg hnn]
      have h2 : (2 : ℤ) ∣ n' := by exact_mod_cast (even_iff_two_dvd.mp hn')
      rw [Int.even_iff, ← Int.emod_emod_of_dvd _ h2, ← hv]
      exact Int.even_iff.mp (Int.even_coe_nat _ |>.mpr hev)
    show (l.mapDomain (castV hk) + ga) (plVar Fr hk Dt.nL (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) a) /
      lowP Fr p (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) = 0
    rw [Finsupp.add_apply, hgz, add_zero, hpv, Finsupp.mapDomain_apply_of_injective hinj]
    exact Nat.div_eq_of_lt hlab

end Formalism.MainNotions.PairMembershipBlocks
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.MultidegSingle
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.TraceSpectra
open Formalism.MainNotions.G.WittFrameLocaliserOrders

namespace LkD

section MD

variable {ι : Type*} {n : ℕ}

theorem multideg_add (a b : ι × Fin n →₀ ℕ) (x : ι) : multideg (a + b) x = multideg a x + multideg b x := by
  simp [multideg, Finset.sum_add_distrib]

theorem multideg_zero (x : ι) : multideg (0 : ι × Fin n →₀ ℕ) x = 0 := by
  simp [multideg]

theorem multideg_smul (k : ℕ) (a : ι × Fin n →₀ ℕ) (x : ι) : multideg (k • a) x = k * multideg a x := by
  simp [multideg, Finset.mul_sum]

theorem multideg_single (v : ι × Fin n) (k : ℕ) (x : ι) :
    multideg (Finsupp.single v k) x = if v.1 = x then k else 0 := by
  unfold multideg
  by_cases h : v.1 = x
  · rw [if_pos h, Finset.sum_eq_single v.2]
    · have hv : v = (x, v.2) := by
        obtain ⟨v1, v2⟩ := v
        simp only at h
        rw [h]
      rw [Finsupp.single_apply, if_pos hv]
    · intro c _ hc
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hc (congrArg Prod.snd e).symm
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro c _
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact h (congrArg Prod.fst e)

end MD

theorem ne_pred {J : ℕ} (hJ : 2 ≤ J) (j : ZMod J) : j ≠ j - 1 := by
  intro h
  haveI : Fact (1 < J) := ⟨by omega⟩
  have h1 : (1 : ZMod J) = 0 := by linear_combination h
  exact one_ne_zero h1

section Phi

variable {p : ℕ} {n' r : ℕ} [NeZero n'] [NeZero r] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)

theorem ph_ll (j : ZMod J) (l : Fin (Dt.nL j)) (a : Fin r) :
    Dt.ph (X (ML.ll j l, a)) = monomial (Finsupp.single ((⟨j, Sum.inl l⟩ : TL J Dt.nL r), a) 1) 1 := by
  rw [SignedChainData.ph, aeval_X]
  rfl

theorem ph_lab (j : ZMod J) (m : Fin r) (a : Fin r) :
    Dt.ph (X (ML.lab j m, a)) = monomial (Finsupp.single ((⟨j, Sum.inr m⟩ : TL J Dt.nL r), a) 1) 1 := by
  rw [SignedChainData.ph, aeval_X]
  rfl

theorem ph_wc (j : ZMod J) (m : Fin r) (a : Fin r) :
    Dt.ph (X (ML.wc j m, a)) = monomial (Finsupp.single ((⟨j, Sum.inr m⟩ : TL J Dt.nL r), a) (Dt.P j m)) 1 := by
  rw [SignedChainData.ph, aeval_X]
  exact X_pow_eq_monomial

theorem PhiJ_X (j : ZMod J) (v : ℤ × Fin r) (hv : v.1 ∈ Fr.letters (segZ j)) :
    PhiJ Fr Dt j (X v) = Dt.ph (X (mlOf Fr Dt.nL j v.1, v.2)) := by
  rw [PhiJ, AlgHom.comp_apply, chi, aeval_X, if_pos hv]

theorem PhiJ_X_mon (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (hJ : 2 ≤ J) (j : ZMod J)
    (v : ℤ × Fin r) (hv : v.1 ∈ Fr.letters (segZ j)) :
    ∃ e : TL J Dt.nL r × Fin r →₀ ℕ, PhiJ Fr Dt j (X v) = monomial e 1 ∧
      ∀ m' : Fin r, multideg e ⟨j - 1, Sum.inr m'⟩ =
        Dt.P (j - 1) m' * (if v.1 = Fr.fr (segZ j - 1) (r - 1 - m'.val) then 1 else 0) := by
  have hne := ne_pred hJ j
  have hr : 1 ≤ r := NeZero.one_le
  rw [PhiJ_X Dt j v hv]
  have hord := hV.2.2.2.1 (segZ j - 1)
  rw [sub_add_cancel] at hord
  rcases Formalism.MainNotions.NormalSetCounting.restSpec n' r Fr L₁ N₁ hV J Dt.nL hnL j v.1 hv with ⟨l, hy, hml⟩ | ⟨m, hy, hml⟩ | ⟨m, hy, hml⟩
  · rw [hml]
    refine ⟨_, ph_ll Dt j l v.2, fun m' => ?_⟩
    rw [multideg_single, if_neg (fun h => hne (congrArg Sigma.fst h)), if_neg, mul_zero]
    intro h
    have h1 := (Formalism.MainNotions.NormalSetCounting.ll_between hnL j l).1
    have h2 := frame_entry_le_last Fr L₁ N₁ hV (segZ j - 1) (r - 1 - m'.val) (by omega)
    omega
  · rw [hml]
    refine ⟨_, ph_lab Dt j m v.2, fun m' => ?_⟩
    rw [multideg_single, if_neg (fun h => hne (congrArg Sigma.fst h)), if_neg, mul_zero]
    intro h
    have h1 := frame_row_monotone Fr L₁ N₁ hV (segZ j) (r - 1 - m.val) (by omega)
    have h2 := frame_entry_le_last Fr L₁ N₁ hV (segZ j - 1) (r - 1 - m'.val) (by omega)
    omega
  · rw [hml]
    refine ⟨_, ph_wc Dt (j - 1) m v.2, fun m' => ?_⟩
    rw [multideg_single]
    by_cases hmm : m = m'
    · subst hmm
      rw [if_pos rfl, if_pos hy, mul_one]
    · rw [if_neg, if_neg, mul_zero]
      · intro h
        rw [hy] at h
        exact hmm (Formalism.MainNotions.NormalSetCounting.fr_rev_inj hV _ h)
      · intro h
        have h3 := eq_of_heq (Sigma.mk.inj_iff.1 h).2
        exact hmm (Sum.inr.inj h3)

theorem PhiJ_monomial (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (hJ : 2 ≤ J) (j : ZMod J)
    (μ : ℤ × Fin r →₀ ℕ) : (∀ v ∈ μ.support, v.1 ∈ Fr.letters (segZ j)) →
    ∃ ν : TL J Dt.nL r × Fin r →₀ ℕ, (∀ c : KK O, PhiJ Fr Dt j (monomial μ c) = monomial ν c) ∧
      ∀ m' : Fin r, multideg ν ⟨j - 1, Sum.inr m'⟩ =
        Dt.P (j - 1) m' * multideg μ (Fr.fr (segZ j - 1) (r - 1 - m'.val)) := by
  induction μ using Finsupp.induction_linear with
  | zero =>
    intro _
    refine ⟨0, fun c => ?_, fun m' => by rw [multideg_zero, multideg_zero, mul_zero]⟩
    exact MvPolynomial.algHom_C _ c
  | add f g hf hg =>
    intro h
    obtain ⟨ν1, a1, b1⟩ := hf (fun v hv => h v (by
      rw [Finsupp.mem_support_iff] at hv ⊢
      rw [Finsupp.add_apply]
      omega))
    obtain ⟨ν2, a2, b2⟩ := hg (fun v hv => h v (by
      rw [Finsupp.mem_support_iff] at hv ⊢
      rw [Finsupp.add_apply]
      omega))
    refine ⟨ν1 + ν2, fun c => ?_, fun m' => ?_⟩
    · have e : (monomial (f + g) c : MvPolynomial (ℤ × Fin r) (KK O)) = monomial f c * monomial g 1 := by
        rw [monomial_mul, mul_one]
      rw [e, map_mul, a1, a2, monomial_mul, mul_one]
    · rw [multideg_add, multideg_add, b1, b2, mul_add]
  | single v k =>
    intro h
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨0, fun c => ?_, fun m' => by rw [Finsupp.single_zero, multideg_zero, multideg_zero, mul_zero]⟩
      rw [Finsupp.single_zero]
      exact MvPolynomial.algHom_C _ c
    · have hv : v.1 ∈ Fr.letters (segZ j) := h v (by rw [Finsupp.mem_support_iff, Finsupp.single_eq_same]; exact hk0)
      obtain ⟨e, he, hm⟩ := PhiJ_X_mon Dt hV hnL hJ j v hv
      refine ⟨k • e, fun c => ?_, fun m' => ?_⟩
      · have e1 : (monomial (Finsupp.single v k) c : MvPolynomial (ℤ × Fin r) (KK O)) = C c * X v ^ k := by
          rw [X_pow_eq_monomial, C_mul_monomial, mul_one]
        rw [e1, map_mul, map_pow, he, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, monomial_pow, one_pow,
          C_mul_monomial, mul_one]
      · rw [multideg_smul, hm, multideg_single]
        split_ifs <;> ring

end Phi

end LkD

theorem lkDeg : LkDeg := by
  intro p _ n' r _ _ O _ _ _ Fr L₁ N₁ hV J _ Dt hS hJ j F hF δ hδ ν hν m'
  have hFs := congrArg (PhiJ Fr Dt j) F.as_sum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hFs
  rw [hFs] at hν
  obtain ⟨μ, hμ, hν'⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hν)
  obtain ⟨ν0, a0, b0⟩ := LkD.PhiJ_monomial Dt hV hS.2.1 hJ j μ (fun v hv =>
    (mem_supported.1 hF) (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨μ, hμ, hv⟩)))
  rw [a0] at hν'
  have := support_monomial_subset hν'
  rw [Finset.mem_singleton] at this
  rw [this, b0, hδ μ hμ]

theorem lkVars : LkVars := by
  intro p n' r _ _ O _ _ _ Fr J _ Dt j
  let s : Set (TL J Dt.nL r × Fin r) :=
    {v | (∃ l, v.1 = ⟨j, Sum.inl l⟩) ∨ ∃ (j' : ZMod J) (m' : Fin r), v.1 = ⟨j', Sum.inr m'⟩}
  have hmon : ∀ (x : TL J Dt.nL r × Fin r) (k : ℕ), x ∈ s →
      (monomial (Finsupp.single x k) (1 : KK O)) ∈ supported (KK O) s := by
    intro x k hx
    rw [← X_pow_eq_monomial]
    refine Subalgebra.pow_mem _ ?_ _
    rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hx)
  have hX : ∀ u : ℤ × Fin r, PhiJ Fr Dt j (X u) ∈ supported (KK O) s := by
    intro u
    unfold PhiJ chi
    rw [AlgHom.comp_apply, aeval_X]
    split_ifs with hu
    · unfold mlOf
      split_ifs with h1 h2 h3
      · rw [LkD.ph_ll]; exact hmon _ _ (Or.inl ⟨_, rfl⟩)
      · rw [LkD.ph_lab]; exact hmon _ _ (Or.inr ⟨_, _, rfl⟩)
      · rw [LkD.ph_wc]; exact hmon _ _ (Or.inr ⟨_, _, rfl⟩)
      · rw [LkD.ph_lab]; exact hmon _ _ (Or.inr ⟨_, _, rfl⟩)
    · rw [map_zero]; exact Subalgebra.zero_mem _
  have hall : ∀ F : MvPolynomial (ℤ × Fin r) (KK O), PhiJ Fr Dt j F ∈ supported (KK O) s := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.algHom_C]; exact Subalgebra.algebraMap_mem _ a
    | add f g hf hg => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hf hg
    | mul_X f u hf => rw [map_mul]; exact Subalgebra.mul_mem _ hf (hX u)
  intro F v hv
  exact (mem_supported.1 (hall F)) (Finset.mem_coe.2 hv)

end Formalism.MainNotions.PairMembershipBlocks
end
end
