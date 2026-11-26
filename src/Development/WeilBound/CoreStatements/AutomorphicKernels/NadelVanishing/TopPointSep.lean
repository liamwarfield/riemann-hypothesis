module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingTwoPointsAmpleStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingPairsOfPrincipalisation
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationClosed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointSeparationPairOfPrincipalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KollarTwoPointSeparationOfNadelVanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBig
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBig
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBig
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KodairaNefBig

theorem isAffine_of_dim_zero {X : Scheme.{0}} [IsIntegral X] (h : topologicalKrullDim X = 0) :
    IsAffine X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU' : U = ⊤ := eq_top_iff.2 fun x _ => by
    rw [GlobalTheory.FlagQ.eq_genericPoint_of_krullDim_zero h x]; exact hmem
  subst hU'
  haveI : IsAffine (⊤ : X.Opens) := hU
  exact IsAffine.of_isIso X.topIso.inv

theorem prod_le {d : ℕ} (q : ℤ) (hq : 1 ≤ q) (n : Fin (d + 1) → Fin 2 → ℤ)
    (h0 : ∀ j, 0 ≤ n 0 j ∧ n 0 j ≤ 2) (hs : ∀ (i : Fin d) j, 0 ≤ n i.succ j ∧ n i.succ j ≤ q)
    (a : Fin (d + 1) → Fin 2) : ∏ i, n i (a i) ≤ 2 * q ^ d := by
  rw [Fin.prod_univ_succ]
  have hp : ∏ i : Fin d, n i.succ (a i.succ) ≤ ∏ _i : Fin d, q :=
    Finset.prod_le_prod₀ (fun i _ => (hs i _).1) fun i _ => (hs i _).2
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  exact mul_le_mul (h0 _).2 hp (Finset.prod_nonneg fun i _ => (hs i _).1) (by norm_num)

end GlobalTheory.KodairaNefBig


open GlobalTheory.KodairaNefBig in
theorem GlobalTheory.exists_ample_add_eff_of_isNef_isBig : GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N : LB X) (hN : N.IsLB), IsNef ℂ N → IsBig ℂ N → ∃ (a : ℕ) (A : LB X) (hA : A.IsLB) (E₀ : CartierDiv X), 0 < a ∧ IsAmpleLB A ∧ E₀.Eff ∧ a • cls N hN = cls A hA + cls (toLB E₀) (isLB_toLB E₀) := by
  intro hNN X _ _ p hp N hN hnef hbig
  letI := algebraΓOfHom p
  have hp' : IsProjOver (strHom ℂ (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨D, hD, -⟩ := hbig.growth
  cases D with
  | zero =>
    have := isAffine_of_dim_zero (X := X) (by simpa using hD)
    refine ⟨1, N, hN, 0, one_pos, isAmpleLB_of_isAffine hN, CartierDiv.eff_zero, ?_⟩
    rw [one_smul, ← toPic_apply, map_zero, add_zero]
  | succ d =>
    have := isNoetherian_of_isProjOver hp
    have hV := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom ℂ X) (GlobalTheory.structureModule X)
      hp' (d := d + 1) (by rw [QCoh.suppDim_structureModule]; exact hD.le)
    let P : Fin 2 → LB X := ![N, A]
    have hPn : ∀ j, IsNef ℂ (P j) := fun j => by
      fin_cases j
      exacts [hnef, hA.isNef]
    have hP : ∀ j, (P j).IsLB := fun j => (hPn j).isLB
    have hI : ∀ a : Fin (d + 1) → Fin 2, 0 ≤ interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
      fun a => hNN.1.interNum_nonneg hp' hD fun i => hPn (a i)
    set S : ℤ := ∑ a : Fin (d + 1) → Fin 2, interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => hI a
    have hT : 0 < topSelfIntersection ℂ N (d + 1) := (hNN.2.2.isBig_iff hp' hD hnef).1 hbig
    set q : ℕ := 2 * (d + 1) * S.toNat + 1 with hqdef
    have hqS : (q : ℤ) = 2 * (d + 1) * S + 1 := by
      rw [hqdef]; push_cast [Int.toNat_of_nonneg hS0]; ring
    have hq1 : (1 : ℤ) ≤ q := by rw [hqS]; nlinarith
    let L : LB X := tens A (lbPow N q)
    have hL : IsAmpleLB L := IsAmpleLB.tens_of_isNef hNN ℂ X p hp A _ hA (hnef.pow hA q)
    let B : LB X := lbPow A 2
    have hB : IsAmpleLB B := (isAmpleLB_pow_iff hA.isLB (by norm_num)).2 hA
    let M : LB X := tens (lbPow N q) (dual A)
    have hM : M.IsLB := isLB_tens (isLB_lbPow hN q) (isLB_dual hA.isLB)
    have hclsL : cls L hL.isLB = (q : ℤ) • cls N hN + cls A hA.isLB := by
      rw [cls_tens hA.isLB (isLB_lbPow hN q), cls_lbPow hN, natCast_zsmul, add_comm]
    have hclsB : cls B hB.isLB = (2 : ℤ) • cls A hA.isLB := by
      rw [cls_lbPow hA.isLB]; norm_cast
    have hclsM : cls M hM = (q : ℤ) • cls N hN - cls A hA.isLB := by
      rw [cls_tens (isLB_lbPow hN q) (isLB_dual hA.isLB), cls_lbPow hN, cls_dual hA.isLB,
        natCast_zsmul, sub_eq_add_neg]
    have e : cls L hL.isLB = cls M hM + cls B hB.isLB := by
      rw [hclsL, hclsM, hclsB]; abel

    have e₁ := hV.interNum_of_cls_eq_sum hP (Q := fun _ => L) (fun _ => hL.isLB)
      (fun _ => ![(q : ℤ), 1]) (fun _ => by
        rw [Fin.sum_univ_two, hclsL]
        simp [P])
    have hlow : (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) ≤ topSelfIntersection ℂ L (d + 1) := by
      rw [topSelf_def ℂ L, e₁]
      have hnn : ∀ a : Fin (d + 1) → Fin 2,
          0 ≤ (∏ i, (![(q : ℤ), 1] : Fin 2 → ℤ) (a i)) * interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
        fun a => mul_nonneg (Finset.prod_nonneg fun i _ => by
          rcases Fin.exists_fin_two.1 ⟨a i, rfl⟩ with h | h <;> rw [h] <;> simp <;> omega) (hI a)
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun a _ => hnn a)
        (Finset.mem_univ (fun _ => (0 : Fin 2))))
      simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl

    let n : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![0, 2] (fun _ => ![(q : ℤ), 1])
    have e₂ := hV.interNum_of_cls_eq_sum hP (Q := Fin.cons B (fun _ : Fin d => L))
      (Fin.cases hB.isLB fun _ => hL.isLB) n (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_zero, n]
          rw [hclsB]
          simp [P]
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_succ, n]
          rw [hclsL]
          simp [P])
    have hup : interNum ℂ (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
        ≤ 2 * (q : ℤ) ^ d * S := by
      rw [e₂, hSdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (hI a)
      refine prod_le (q : ℤ) hq1 n (fun j => ?_) (fun i j => ?_) a
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n]
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n] <;> omega
    have hineq : ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
        (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection ℂ L (d + 1) := by
      have hqd : (0 : ℤ) < (q : ℤ) ^ d := pow_pos (by omega) d
      have hd1 : (0 : ℤ) ≤ (d : ℤ) + 1 := by positivity
      calc ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
            (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
          ≤ ((d : ℤ) + 1) * (2 * (q : ℤ) ^ d * S) := mul_le_mul_of_nonneg_left hup hd1
        _ = (q : ℤ) ^ d * (2 * (d + 1) * S) := by ring
        _ < (q : ℤ) ^ d * q := mul_lt_mul_of_pos_left (by rw [hqS]; omega) hqd
        _ = (q : ℤ) ^ (d + 1) * 1 := by ring
        _ ≤ (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        _ ≤ topSelfIntersection ℂ L (d + 1) := hlow
    obtain ⟨r, hr, hs⟩ := exists_hasNonzeroSec_pow_of_ample_sub_ample ℂ X hp' d hD.le L B M hL hB hM
      e hineq
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    refine ⟨q * r, lbPow A r, isLB_lbPow hA.isLB r, divOfSec (isLB_lbPow hM r) s hs,
      Nat.mul_pos (Nat.succ_pos _) hr, (isAmpleLB_pow_iff hA.isLB hr).2 hA,
      eff_divOfSec_of_sec _ s hs, ?_⟩
    rw [← toPic_apply, (presents_divOfRatSec _ (isRatSec_ratOfSec s hs)).toPic_eq,
      cls_lbPow hA.isLB, cls_lbPow hM, hclsM]
    first
      | module
      | (simp only [← natCast_zsmul, smul_sub, smul_smul, Nat.cast_mul]; rw [mul_comm (r : ℤ)]; abel)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBigStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_add_effective_of_nef_big : GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N : LB X) (hN : N.IsLB), IsNef ℂ N → IsBig ℂ N → ∃ (a : ℕ) (A : LB X) (hA : A.IsLB) (E₀ : CartierDiv X), 0 < a ∧ IsAmpleLB A ∧ E₀.Eff ∧ a • cls N hN = cls A hA + cls (toLB E₀) (isLB_toLB E₀) := by
  first | exact @GlobalTheory.exists_ample_add_eff_of_isNef_isBig | exact GlobalTheory.exists_ample_add_eff_of_isNef_isBig | (intros; apply GlobalTheory.exists_ample_add_eff_of_isNef_isBig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBig
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.NefBigSep

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H N A B : LB X} {Z : Closeds X}

theorem deg_of_cls_eq (hZ : IsCompleteCurve k Z) (hH : IsAmpleLB H) (hN : N.IsLB) (hA : A.IsLB)
    (hB : B.IsLB) (a b : ℕ) (e : cls N hN = a • cls A hA + b • cls B hB) :
    interNumRed k Z ![N] = a * interNumRed k Z ![A] + b * interNumRed k Z ![B] := by
  rw [hZ.interNumRed_of_cls_eq_add hH hN (isLB_lbPow hA a) (isLB_lbPow hB b)
    (by rw [cls_lbPow hA, cls_lbPow hB, e]), hZ.interNumRed_lbPow hH hA,
    hZ.interNumRed_lbPow hH hB]

theorem exists_budget (ρ S c : ℚ) (a : ℕ) (hρ : 0 < ρ) (hS : S < ρ) (hS0 : 0 ≤ S) (hc : 0 < c) :
    ∃ q m' : ℕ, 0 < m' ∧ (q : ℚ) = ρ * m' ∧ a < q ∧ 1 / (m' : ℚ) ≤ c ∧ (m' : ℚ) * S < q - a := by
  have hd : (0 : ℚ) < ρ.den := by exact_mod_cast ρ.den_pos
  have hu : (0 : ℤ) ≤ ρ.num := (Rat.num_pos.2 hρ).le
  have hρ' : ((ρ.num.toNat : ℕ) : ℚ) = ρ * ρ.den := by
    rw [show ((ρ.num.toNat : ℕ) : ℚ) = ((ρ.num.toNat : ℤ) : ℚ) from rfl, Int.toNat_of_nonneg hu]
    exact (Rat.mul_den_eq_num ρ).symm
  have hgap : 0 < (ρ.den : ℚ) * (ρ - S) := mul_pos hd (sub_pos.2 hS)
  obtain ⟨t, ht⟩ := exists_nat_gt (max (1 / c) (a / ((ρ.den : ℚ) * (ρ - S))))
  have ht1 : 1 / c < t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht2 : a / ((ρ.den : ℚ) * (ρ - S)) < t := lt_of_le_of_lt (le_max_right _ _) ht
  have htpos : (0 : ℚ) < t := lt_trans (by positivity) ht1
  have ht2' : (a : ℚ) < t * ((ρ.den : ℚ) * (ρ - S)) := by
    rw [div_lt_iff₀ hgap] at ht2; linarith
  refine ⟨ρ.num.toNat * t, ρ.den * t, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos ρ.den_pos (by exact_mod_cast htpos)
  · push_cast; rw [hρ']; ring
  · have : (a : ℚ) < ((ρ.num.toNat * t : ℕ) : ℚ) := by
      push_cast; rw [hρ']; nlinarith [mul_nonneg (mul_nonneg hd.le htpos.le) hS0]
    exact_mod_cast this
  · push_cast
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at ht1
    have : (1 : ℚ) ≤ ρ.den := by exact_mod_cast ρ.den_pos
    nlinarith
  · push_cast; rw [hρ']; nlinarith

end GlobalTheory.NefBigSep

namespace GlobalTheory.NefBigSep

theorem separate_nef_big : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsNef ℂ N → IsBig ℂ N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → 0 < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hPr hNad hNef X _ _ _ p n hp hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hG hNn hNb
    hcurve hx₁ hx₂ hne hh hz hsum hρ
  letI := algebraΓOfHom p
  obtain ⟨a, A, hA, E₀, ha, hAmp, hE₀, hcls⟩ :=
    GlobalTheory.T.exists_ample_add_effective_of_nef_big hNef X p hp N hNn.isLB hNn hNb
  obtain ⟨c, hc, hkltc⟩ := GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor hPr X p n hp hdim Δ m G (qWeil E₀ 1) hm hG hklt
    ⟨1, E₀, one_pos, hE₀, rfl⟩
  have hS0 : 0 ≤ ∑ e ∈ Finset.Icc 1 n, h e := Finset.sum_nonneg fun e _ => (hh e).le
  obtain ⟨q, m', hm', hq, haq, hmc, hbud⟩ := exists_budget ρ _ c a hρ hsum hS0 hc
  have hNp := isLB_lbPow hNn.isLB (q - a)
  have hN'lb := isLB_tens hA hNp
  have hclsN' : cls _ hN'lb = cls A hA + (q - a) • cls N hNn.isLB := by
    rw [cls_tens hA hNp, cls_lbPow hNn.isLB]
  have hN'amp : IsAmpleLB (tens A (lbPow N (q - a))) :=
    IsAmpleLB.tens_of_isNef hNef ℂ X p hp A _ hAmp (hNn.pow hAmp _)
  have hqa : (0 : ℚ) < q - a := sub_pos.2 (by exact_mod_cast haq)
  have hqa' : (((q - a : ℕ) : ℚ)) = q - a := by rw [Nat.cast_sub haq.le]
  have hB : qWeil E₀ m' = (1 / (m' : ℚ)) • qWeil E₀ 1 := by
    funext z; simp [qWeil]; ring
  refine GlobalTheory.T.exists_section_separating_two_points_ample hPr hNad hNef X p n hp hdim M (Δ + qWeil E₀ m') (m * m') (m' • G + m • E₀)
    (tens A (lbPow N (q - a))) (1 / (m' : ℚ)) (fun e => h e / ((q : ℚ) - a)) x₁ x₂ hM
    (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', E₀, hm', hE₀, rfl⟩) ?_ (Nat.mul_pos hm hm')
    (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G E₀ hm hm' hG) hN'amp ?_ hx₁ hx₂ hne
    (fun e => div_pos (hh e) hqa) ?_ ?_
  · intro y
    rw [hB]
    exact (GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hdim Δ (qWeil E₀ 1) (1 / (m' : ℚ)) c y
      ⟨1, E₀, one_pos, hE₀, rfl⟩ hmc).1 (hkltc y)
  · intro C hC
    have h1 := hcurve C hC
    have dN' := deg_of_cls_eq hC hAmp hN'lb hA hNn.isLB 1 (q - a) (by rw [hclsN', one_nsmul])
    have dK := hC.interNumRed_of_cls_eq_add hAmp (isLB_lbPow hNn.isLB a) hA (isLB_toLB E₀)
      (by rw [cls_lbPow hNn.isLB, hcls])
    rw [hC.interNumRed_lbPow hAmp hNn.isLB] at dK
    have dG := deg_of_cls_eq hC hAmp (isLB_toLB (m' • G + m • E₀)) (isLB_toLB G) (isLB_toLB E₀)
      m' m (by rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add (f := _), map_nsmul, map_nsmul])
    rw [h1, dN', dG]
    have dK' : (a : ℚ) * interNumRed ℂ C ![N] = interNumRed ℂ C ![A] + interNumRed ℂ C ![toLB E₀] := by
      exact_mod_cast dK
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hm0' : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
    push_cast
    rw [hqa']
    field_simp
    linear_combination (m : ℚ) * dK' - (m : ℚ) * (interNumRed ℂ C ![N] : ℚ) * hq
  · intro z e hze he hdz
    have hmix := mixExp_interNumRed hNef ℂ X p hp N A (tens A (lbPow N (q - a))) hNn.isLB hA hN'lb
      (q - a) 1 (Closeds.closure {z}) e hNn hAmp.isNef (by rw [hclsN', one_nsmul, add_comm])
      (by rw [Closeds.coe_closure]; exact hdz)
    have key : ((q : ℚ) - a) ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)
        ≤ (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => tens A (lbPow N (q - a)) : ℤ) := by
      have := (Int.cast_le (R := ℚ)).2 hmix
      push_cast at this
      rwa [hqa'] at this
    have h0 := hz z e hze he hdz
    have e1 : h e ^ e * ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ) : ℚ) =
        (h e / ((q : ℚ) - a)) ^ e * (((q : ℚ) - a) ^ e *
          (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) := by
      rw [div_pow]; field_simp
    calc 2 * (e : ℚ) ^ e < _ := h0
      _ = _ := e1
      _ ≤ _ := mul_le_mul_of_nonneg_left key (pow_nonneg (div_pos (hh e) hqa).le _)
  · rw [← Finset.sum_div, div_lt_div_iff₀ hqa (by exact_mod_cast hm')]
    linarith

end GlobalTheory.NefBigSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBigStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separate_two_points_nef_big : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsNef ℂ N → IsBig ℂ N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → 0 < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  first | exact @GlobalTheory.NefBigSep.separate_nef_big | exact GlobalTheory.NefBigSep.separate_nef_big | (intros; apply GlobalTheory.NefBigSep.separate_nef_big <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInduction
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_rat_budget_term (r : ℕ) (hr : 0 < r) (e : ℕ) (he : e ≠ 0) (c : ℝ) (hc : 0 < c) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) ∧
      ∀ t : ℤ, c ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heR : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hapos : 0 < ((r : ℝ) * c) ^ e := by positivity
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = ⌊((r : ℝ) * c) ^ e⌋ + 1 := ⟨_, rfl⟩
  have hTa : ((r : ℝ) * c) ^ e < (T : ℝ) := by
    rw [hT]; push_cast; exact Int.lt_floor_add_one _
  have hTpos : (0 : ℝ) < T := hapos.trans hTa
  have hupos : 0 < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by positivity
  have hue : ((2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c)) ^ e = 2 * (e : ℝ) ^ e / ((r : ℝ) * c) ^ e := by
    rw [div_pow, mul_pow, one_div, Real.rpow_inv_natCast_pow (by norm_num) he]
  have hv0 : 0 ≤ (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) := by positivity
  have hve : ((2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹)) ^ e = 2 * (e : ℝ) ^ e / T :=
    Real.rpow_inv_natCast_pow (by positivity) he
  have hvu : (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by
    rw [← pow_lt_pow_iff_left₀ hv0 hupos.le he, hve, hue]
    exact div_lt_div_of_pos_left (by positivity) hapos hTa
  obtain ⟨q, hvq, hqu⟩ := exists_rat_btwn hvu
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt hv0 hvq
  refine ⟨q, by exact_mod_cast hq0, hqu, ?_⟩
  intro t ht
  have hct : c ^ e * (r : ℝ) ^ e < t := (lt_div_iff₀ (by positivity)).1 ht
  have hat : ((r : ℝ) * c) ^ e < t := by
    calc ((r : ℝ) * c) ^ e = c ^ e * (r : ℝ) ^ e := by rw [mul_pow, mul_comm]
      _ < t := hct
  have hTt : (T : ℝ) ≤ t := by
    have h1 := Int.floor_lt.2 hat
    have : T ≤ t := by omega
    exact_mod_cast this
  have key : 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * t := by
    have h1 := pow_lt_pow_left₀ hvq hv0 he
    rw [hve, div_lt_iff₀ hTpos] at h1
    calc 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * T := h1
      _ ≤ (q : ℝ) ^ e * t := mul_le_mul_of_nonneg_left hTt (by positivity)
  exact_mod_cast key

theorem exists_rat_budgets : ∀ (n r : ℕ) (c : ℕ → ℝ), 0 < r → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
    ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 →
    ∃ (h : ℕ → ℚ), (∀ e, 0 < h e) ∧ ∑ e ∈ Finset.Icc 1 n, h e < 1 / (r : ℚ) ∧
      ∀ e ∈ Finset.Icc 1 n, ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e →
        2 * (e : ℚ) ^ e < h e ^ e * t := by
  intro n r c hr hc hsum
  have hex : ∀ e, ∃ q : ℚ, 0 < q ∧ (e ∈ Finset.Icc 1 n →
      (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) ∧
      ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t) := by
    intro e
    by_cases he : e ∈ Finset.Icc 1 n
    · have he0 : e ≠ 0 := by
        have := (Finset.mem_Icc.1 he).1
        omega
      obtain ⟨q, hq0, hqu, hqt⟩ := exists_rat_budget_term r hr e he0 (c e) (hc e he)
      exact ⟨q, hq0, fun _ => ⟨hqu, hqt⟩⟩
    · exact ⟨1, one_pos, fun h => absurd h he⟩
  choose h hpos hprop using hex
  refine ⟨h, hpos, ?_, fun e he => (hprop e he).2⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hR : ∑ e ∈ Finset.Icc 1 n, (h e : ℝ) < 1 / (r : ℝ) := by
    rcases (Finset.Icc 1 n).eq_empty_or_nonempty with hE | hE
    · rw [hE, Finset.sum_empty]; positivity
    · calc ∑ e ∈ Finset.Icc 1 n, (h e : ℝ)
          < ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) :=
            Finset.sum_lt_sum_of_nonempty hE (fun e he => (hprop e he).1)
        _ = 1 / (r : ℝ) * ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by ring
        _ ≤ 1 / (r : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 / (r : ℝ) := mul_one _
  have hR' : ((∑ e ∈ Finset.Icc 1 n, h e : ℚ) : ℝ) < ((1 / (r : ℚ) : ℚ) : ℝ) := by
    push_cast; exact hR
  exact Rat.cast_lt.mp hR'

end GlobalTheory.PairStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInductionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_budgets_twoPointInduction : ∀ (n r : ℕ) (c : ℕ → ℝ), 0 < r → (∀ e ∈ Finset.Icc 1 n, 0 < c e) → ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 → ∃ (h : ℕ → ℚ), (∀ e, 0 < h e) ∧ ∑ e ∈ Finset.Icc 1 n, h e < 1 / (r : ℚ) ∧ ∀ e ∈ Finset.Icc 1 n, ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < h e ^ e * t := by
  first | exact @GlobalTheory.PairStep.exists_rat_budgets | exact GlobalTheory.PairStep.exists_rat_budgets | (intros; apply GlobalTheory.PairStep.exists_rat_budgets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KollarTwoPointSeparationOfNadelVanishing
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem pointSeparationPair_of_vanishing :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics →
      GlobalTheory.Published.PointSeparationPair := by
  intro hP hV hN X _ _ _ p n hproj hdim M Δ m G r N₀ x₁ x₂ c hM hΔ hklt hm hG hr hnef hbig hC
    h₁ h₂ hx hc hZ hs
  letI := algebraΓOfHom p
  obtain ⟨h, hpos, hsum, hh⟩ := GlobalTheory.T.exists_rational_budgets_twoPointInduction n r c hr hc hs
  have hr' : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
  refine GlobalTheory.T.separate_two_points_nef_big hP hV hN X p n hproj hdim M Δ m G N₀ (1 / (r : ℚ)) h x₁ x₂ hM hΔ hklt hm hG
    hnef hbig ?_ h₁ h₂ hx hpos ?_ hsum (by positivity)
  · intro C hCc
    rw [hC C hCc]
    ring
  · intro z e hz he hze
    have hle : e ≤ n := by
      have h1 := topologicalKrullDim_subspace_le X (closure ({z} : Set X))
      rw [hze, hdim] at h1
      exact_mod_cast h1
    have hmem : x₁ ∈ Closeds.closure ({z} : Set X) ∨ x₂ ∈ Closeds.closure ({z} : Set X) := by
      rcases hz with hz | hz
      · exact Or.inl (specializes_iff_mem_closure.1 hz)
      · exact Or.inr (specializes_iff_mem_closure.1 hz)
    have hZ' := hZ (Closeds.closure ({z} : Set X)) e isIrreducible_singleton.closure hmem he hze
    exact hh e (Finset.mem_Icc.2 ⟨he, hle⟩) _ hZ'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KollarTwoPointSeparationOfNadelVanishingStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kollarTwoPointSeparation_of_nadelVanishing : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.PointSeparationPair := by
  first | exact @GlobalTheory.pointSeparationPair_of_vanishing | exact GlobalTheory.pointSeparationPair_of_vanishing | (intros; apply GlobalTheory.pointSeparationPair_of_vanishing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingPairsOfPrincipalisationStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nadel_vanishing_pairs_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair := by
  first | exact @GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | exact GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | (intros; apply GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleNumericalTheoremsProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nefLineBundleNumericalTheorems_proof : GlobalTheory.Published.NefNumerics := by
  first | exact @GlobalTheory.nefNumerics_outright | exact GlobalTheory.nefNumerics_outright | (intros; apply GlobalTheory.nefNumerics_outright <;> assumption)
end

theorem GlobalTheory.pointSeparationPair_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.PointSeparationPair := fun hP =>
  GlobalTheory.T.kollarTwoPointSeparation_of_nadelVanishing hP (GlobalTheory.T.nadel_vanishing_pairs_of_principalisation hP) GlobalTheory.T.nefLineBundleNumericalTheorems_proof
end

namespace NadelVanishingSeparation.NSI

theorem pointSeparationPair : GlobalTheory.Published.PointSeparationPair :=
  GlobalTheory.pointSeparationPair_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

end NadelVanishingSeparation.NSI
