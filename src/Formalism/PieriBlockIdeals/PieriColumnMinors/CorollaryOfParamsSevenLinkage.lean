module

public import Formalism.PieriBlockIdeals.HidaLatticeInclusionAtCoarseWeightBound
public import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RealOfSkeleton
public import Formalism.PieriBlockIdeals.PieriColumnMinors.IrreducibleGeneration

@[expose] public section

section -- merged from Formalism.PieriBlockIdeals.LemmaDGradedOfPieriReal
namespace Formalism.CohomologicalDescent.ColumnMinorsFromPieri

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

def ColumnsRealOfPieriReal : Prop := LR.PieriReal → LR.ColumnsReal

end Formalism.CohomologicalDescent.ColumnMinorsFromPieri
end

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsLinkage
section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.ColumnsPieriSkeleton
section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.LemmaDSkeletonFour
section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.PermutationWeightInvariant
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lc_c_filter_succ {A : Type*} [AddCommMonoid A] {n : ℕ} (f : Fin n → A) (l : ℕ) (hl : l < n) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l + 1), f i =
      f ⟨l, hl⟩ + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), f i := by
  have hfil : (Finset.univ.filter (fun i : Fin n => i.val < l + 1)) =
      insert (⟨l, hl⟩ : Fin n) (Finset.univ.filter (fun i : Fin n => i.val < l)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hfil, Finset.sum_insert (by simp)]

theorem lc_c_filter_zero {A : Type*} [AddCommMonoid A] {n : ℕ} (f : Fin n → A) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < 0), f i = 0 := by
  have : (Finset.univ.filter (fun i : Fin n => i.val < 0)) = ∅ := by
    ext i; simp
  rw [this, Finset.sum_empty]

theorem lc_c_casVal_step {q : ℕ} (κ : Fin q → ℕ) (r : Fin q) :
    casVal (κ + Pi.single r 1) - casVal κ - (q : ℤ) = 2 * ((κ r : ℤ) - (r.val : ℤ)) := by
  have h2 := casimir_content_holds q (fun b => (κ b : ℤ)) r
  unfold casVal
  simp only [Pi.add_apply, Pi.single_apply, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact h2

theorem lc_c_casVal_path {q n : ℕ} (lam2 : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q) (h0 : κ 0 = lam2)
    (hs : ∀ j : Fin n, κ (j.val + 1) = κ j.val + Pi.single (ρ j) 1) : ∀ l ≤ n,
    casVal (κ l) = casVal lam2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), (2 * cseq κ ρ i + (q : ℤ)) := by
  intro l
  induction l with
  | zero => intro _; rw [lc_c_filter_zero, add_zero, h0]
  | succ l ih =>
    intro hl
    have hl' : l < n := hl
    rw [lc_c_filter_succ _ l hl']
    have h1 := lc_c_casVal_step (κ l) (ρ ⟨l, hl'⟩)
    have h2 := hs ⟨l, hl'⟩
    simp only at h2
    rw [← h2] at h1
    have h3 := ih hl'.le
    simp only [cseq] at h3 ⊢
    linarith

theorem lc_c_eig {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {A T : Module.End K V} (h : Commute T A)
    {z : V} {a : K} (hz : A z = a • z) : A (T z) = a • T z := by
  have := LinearMap.congr_fun h.eq z
  simp only [Module.End.mul_apply] at this
  rw [← this, hz, map_smul]

theorem lc_c_Dpart0 {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P]
    {n : ℕ} (EM : R → R → Module.End k M) (b b' : R) :
    (Dpart k EM 0 b b' : Module.End k (Tens R P M n)) = onM k (EM b b') := by
  simp [Dpart]

theorem commute_casimir_zero {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P]
    [Fintype R] {n : ℕ} (EM : R → R → Module.End k M) (T : Module.End k (Tens R P M n))
    (h0 : ∀ a b, Commute T (onM k (EM a b))) : Commute T (Cas k EM 0) := by
  unfold Cas
  simp only [lc_c_Dpart0]
  exact Commute.sum_right _ _ _ fun b _ => Commute.sum_right _ _ _ fun b' _ => (h0 _ _).mul_right (h0 _ _)

theorem casimir_from_x : CasFromX := by
  intro K P M q _ _ _ _ EM n lam2 c z hz l
  induction l with
  | zero =>
    intro _
    rw [lc_c_filter_zero, add_zero]
    exact hz.1
  | succ l ih =>
    intro hl
    have hl' : l < n := hl
    have h1 := congrArg (fun T : Module.End K (Tens (Fin q) P M n) => T z)
      (casimir_jucys_murphy_holds K (Fin q) P M EM n ⟨l, hl'⟩)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      Fintype.card_fin] at h1
    rw [lc_c_filter_succ _ l hl']
    rw [ih hl'.le, hz.2 ⟨l, hl'⟩, ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, smul_smul, ← add_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem weight_iff_condition : WtIff := by
  intro K P M q _ _ _ _ _ EM n lam2 κ ρ h0 hs z
  constructor
  · intro hz
    refine ⟨?_, fun j => ?_⟩
    · have := hz 0 (Nat.zero_le _)
      rwa [h0] at this
    · exact (path_eigen_holds K P M q EM n κ ρ hs z hz).1 j
  · intro hz j hj
    rw [casimir_from_x K P M q EM n lam2 _ z hz j hj, lc_c_casVal_path lam2 κ ρ h0 hs j hj]

theorem permutation_weight_invariant : PermXWt := by
  intro K P M q _ _ _ _ EM n lam2 c z σ hz
  refine ⟨?_, fun j => ?_⟩
  · exact lc_c_eig (commute_casimir_zero EM _ fun a b => permFirst_commute_onModule K σ _) hz.1
  · exact lc_c_eig (commute_jucysMurphy_of_commute K EM _ (fun a b => permFirst_commute_onModule K σ _)
      (fun i a b => permFirst_commute_unitSecond K σ i a b) j) (hz.2 j)

theorem to_symmetric_y_x : ToSymYX := by
  intro K R P M _ _ _ _ _ _ _ n σ z
  rw [← toSym_perm_eq (k := K) (permX K σ⁻¹ z) σ]
  congr 1
  funext g
  simp [permTensor_apply_comp, permFirst_apply, permSecond_apply]

theorem lc_c_ss {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ} (a b : Fin n) :
    (permY k (Equiv.swap a b) * permY k (Equiv.swap a b) : Module.End k (Tens R P M n)) = 1 := by
  rw [← permOnTensor_mul, Equiv.swap_mul_self, permSecond_one]

theorem exchange' : Exchange := by
  intro K P M q _ _ _ _ _ EM n lam2 c z j hj hz hne
  set j' : Fin n := ⟨j.val + 1, hj⟩ with hj'
  set s : Module.End K (Tens (Fin q) P M n) := permY K (Equiv.swap j j') with hs
  have hH := hecke_relations_hold K (Fin q) P M EM n j hj
  have h1 : s * xJM K EM j = xJM K EM j' * s - 1 := hH.1
  have hss : s * s = 1 := lc_c_ss j j'
  have h2 : xJM K EM j * s = s * xJM K EM j' - 1 := by
    calc xJM K EM j * s = (s * s) * xJM K EM j * s := by rw [hss, one_mul]
      _ = s * (s * xJM K EM j) * s := by simp only [mul_assoc]
      _ = s * (xJM K EM j' * s - 1) * s := by rw [h1]
      _ = s * xJM K EM j' * (s * s) - s * s := by noncomm_ring
      _ = s * xJM K EM j' - 1 := by rw [hss, mul_one]
  have e1 : xJM K EM j' (s z) = ((c j : ℤ) : K) • s z + z := by
    have := LinearMap.congr_fun h1 z
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this
    rw [hz.2 j, map_smul] at this
    rw [this]; abel
  have e2 : xJM K EM j (s z) = ((c j' : ℤ) : K) • s z - z := by
    have := LinearMap.congr_fun h2 z
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this
    rw [hz.2 j', map_smul] at this
    exact this
  have hd : (((c j - c j' : ℤ) : ℤ) : K) ≠ 0 := Int.cast_ne_zero.2 (sub_ne_zero.2 hne)
  set b : K := (((c j - c j' : ℤ) : ℤ) : K)⁻¹ with hbdef
  have hb : b * (((c j : ℤ) : K) - ((c j' : ℤ) : K)) = 1 := by
    rw [← Int.cast_sub]; exact inv_mul_cancel₀ hd
  have hjj' : j ≠ j' := by
    intro e; have := congrArg Fin.val e; simp [hj'] at this
  refine ⟨?_, fun l => ?_⟩
  · rw [map_add (f := _), map_smul, hz.1, lc_c_eig (commute_casimir_zero EM s fun a b => permSecond_commute_onModule K _ _) hz.1]
    module
  · by_cases hl : l = j
    · subst hl
      rw [Function.comp_apply, Equiv.swap_apply_left, map_add (f := _), map_smul, e2, hz.2 l]
      have e : b * ((c l : ℤ) : K) - 1 = ((c j' : ℤ) : K) * b := by linear_combination hb
      calc _ = ((c j' : ℤ) : K) • s z + (b * ((c l : ℤ) : K) - 1) • z := by module
        _ = _ := by rw [e]; module
    · by_cases hl' : l = j'
      · rw [hl', Function.comp_apply, Equiv.swap_apply_right, map_add (f := _), map_smul, e1, hz.2 j']
        have e : 1 + b * ((c j' : ℤ) : K) = ((c j : ℤ) : K) * b := by linear_combination (-1 : K) * hb
        calc _ = ((c j : ℤ) : K) • s z + (1 + b * ((c j' : ℤ) : K)) • z := by module
          _ = _ := by rw [e]; module
      · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hl hl', map_add (f := _), map_smul, hz.2 l,
          lc_c_eig (hH.2 l hl hl') (hz.2 l)]
        module

theorem good_swap_exists : GoodSwap := by
  intro K P M q _ _ _ _ _ _ EM n lam2 c j hj hd hgood z hz
  have hne : c j ≠ c ⟨j.val + 1, hj⟩ := by intro e; rw [e] at hd; omega
  have hz' := exchange' K P M q EM n lam2 c z j hj hz hne
  set j' : Fin n := ⟨j.val + 1, hj⟩ with hj'
  set s : Module.End K (Tens (Fin q) P M n) := permY K (Equiv.swap j j') with hs
  set b : K := (((c j - c j' : ℤ) : ℤ) : K)⁻¹ with hbdef
  set z' := s z + b • z with hz'def
  have hss : s * s = 1 := lc_c_ss j j'
  have t1 : toSym K z' = 0 := hgood z' hz'
  have t2 : toSym K (s z') = 0 := by
    rw [hs, to_symmetric_y_x K (Fin q) P M n (Equiv.swap j j') z']
    exact hgood _ (permutation_weight_invariant K P M q EM n lam2 _ z' _ hz')
  have hssz : s (s z) = z := by
    have := LinearMap.congr_fun hss z
    simpa using this
  have e : s z' - b • z' = (1 - b * b) • z := by
    rw [hz'def, map_add (f := _), map_smul, hssz]
    module
  have t3 : (1 - b * b) • toSym K z = 0 := by
    rw [← map_smul, ← e, map_sub, map_smul, t1, t2]; simp
  have hD : (((c j - c j' : ℤ) : ℤ) : K) ≠ 0 := Int.cast_ne_zero.2 (sub_ne_zero.2 hne)
  have hb : b * (((c j - c j' : ℤ) : ℤ) : K) = 1 := inv_mul_cancel₀ hD
  have hbb : 1 - b * b ≠ 0 := by
    intro h0
    have h1 : (((c j - c j' : ℤ) : ℤ) : K) * (((c j - c j' : ℤ) : ℤ) : K) = 1 := by
      linear_combination ((((c j - c j' : ℤ) : ℤ) : K) * (((c j - c j' : ℤ) : ℤ) : K)) * h0 +
        (b * (((c j - c j' : ℤ) : ℤ) : K) + 1) * hb
    have h2 : (c j - c j') * (c j - c j') = 1 := by exact_mod_cast h1
    nlinarith
  exact (smul_eq_zero.1 t3).resolve_left hbb

theorem NoWt_of (h : NoTuple) : NoWt := by
  intro K P M q _ _ _ _ _ EM n lam2 hp c z hz hc
  let TT : Set (Fin (n + 1) → K) := {t | ∃ (tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q),
    IsPath n lam2 tau κ ρ ∧ ∀ j : Fin (n + 1), t j = ((casVal (κ j.val) : ℤ) : K)}
  let E : Set (Tens (Fin q) P M n) := ⋃ tau : Fin q → ℕ, {z | ∃ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q),
    IsPath n lam2 tau κ ρ ∧ ∀ j ≤ n, Cas K EM j z = ((casVal (κ j) : ℤ) : K) • z}
  have hE : Submodule.span K E = ⊤ := by
    rw [← hp, Submodule.span_iUnion]; rfl
  let T0 : ℕ → ℤ := fun l => casVal lam2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), (2 * c i + (q : ℤ))
  refine h K (Tens (Fin q) P M n) (Fin (n + 1)) (fun j => Cas K EM j.val) TT E ?_ z (by rw [hE]; trivial)
    (fun j => ((T0 j.val : ℤ) : K)) ?_ ?_
  · intro e he
    obtain ⟨tau, κ, ρ, hpath, hcas⟩ := Set.mem_iUnion.1 he
    exact ⟨fun j => ((casVal (κ j.val) : ℤ) : K), ⟨tau, κ, ρ, hpath, fun _ => rfl⟩,
      fun j => hcas j.val (Nat.lt_succ_iff.1 j.2)⟩
  · rintro ⟨tau, κ, ρ, hpath, ht⟩
    apply hc
    refine ⟨tau, κ, ρ, hpath, ?_⟩
    have hT : ∀ l ≤ n, T0 l = casVal (κ l) := by
      intro l hl
      have : ((T0 l : ℤ) : K) = ((casVal (κ l) : ℤ) : K) := ht ⟨l, Nat.lt_succ_iff.2 hl⟩
      exact Int.cast_injective this
    funext i
    have a1 := hT i.val i.2.le
    have a2 := hT (i.val + 1) i.2
    rw [lc_c_casVal_path lam2 κ ρ hpath.start hpath.step _ i.2.le] at a1
    rw [lc_c_casVal_path lam2 κ ρ hpath.start hpath.step _ i.2] at a2
    simp only [T0] at a1 a2
    rw [lc_c_filter_succ _ i.val i.2, lc_c_filter_succ _ i.val i.2] at a2
    simp only [Fin.eta] at a2
    linarith
  · intro j
    exact casimir_from_x K P M q EM n lam2 c z hz j.val (Nat.lt_succ_iff.1 j.2)

theorem AntiStep_of (h : NoTuple) : AntiStep := by
  intro K P M q _ _ _ _ _ EM n lam2 hp c z j hj hz hc hn
  have hne : c j ≠ c ⟨j.val + 1, hj⟩ := by rw [hc]; omega
  have hz' := exchange' K P M q EM n lam2 c z j hj hz hne
  have h0 := NoWt_of h K P M q EM n lam2 hp _ _ hz' hn
  have h1 : c j - c ⟨j.val + 1, hj⟩ = 1 := by rw [hc]; ring
  rw [h1] at h0
  simp only [Int.cast_one, inv_one, one_smul] at h0
  exact eq_neg_of_add_eq_zero_left h0

end Formalism.CohomologicalDescent.LC
end

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.MeasureSwapInvariant
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem no_bad_tuple : NoTuple := by
  intro K V J _ _ _ T TT E hE v hv t0 ht0 hv0
  classical
  choose! tt htt1 htt2 using hE
  obtain ⟨f, t, htE, -, hsum⟩ := (Submodule.mem_span_iff_exists_finset_subset).1 hv
  clear hv
  induction t using Finset.induction_on generalizing f v with
  | empty => simpa using hsum.symm
  | insert e0 t' he0 ih =>
    have he0E : e0 ∈ E := htE (by simp)
    have hne : tt e0 ≠ t0 := fun h => ht0 (h ▸ htt1 e0 he0E)
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have h1 : (t0 j - tt e0 j) • v = ∑ a ∈ t', (f a * (tt a j - tt e0 j)) • a := by
      have h3 : T j v - tt e0 j • v = ∑ a ∈ insert e0 t', f a • (T j a - tt e0 j • a) := by
        rw [← hsum]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intros
        rw [smul_comm]
      rw [sub_smul, ← hv0 j, h3, Finset.sum_insert he0, htt2 e0 he0E j, sub_self, smul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro a ha
      rw [htt2 a (htE (by simp [ha])) j, ← sub_smul, smul_smul]
    have h2 := ih ((t0 j - tt e0 j) • v) (fun i => by rw [map_smul, hv0 i, smul_comm])
      (fun a => f a * (tt a j - tt e0 j)) (fun a ha => htE (by simp at ha ⊢; exact Or.inr ha)) h1.symm
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hj))

theorem measure_swap_invariant : MeasSwap := by
  intro n col j hj hlt
  set b : Fin n := ⟨j.val + 1, hj⟩ with hb
  have hjb : j ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [hb] at this
  have hsplit : ∀ F : Fin n → ℕ, ∑ l, F l = F j + (F b + ∑ l ∈ (Finset.univ.erase j).erase b, F l) := by
    intro F
    rw [Finset.add_sum_erase _ F (by simp [hjb.symm]), Finset.add_sum_erase _ F (by simp)]
  unfold meas
  rw [hsplit, hsplit (fun l => (n - l.val) * col l)]
  have hrest : ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * (col ∘ Equiv.swap j b) l =
      ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * col l := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hl.2 hl.1]
  rw [hrest]
  simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  obtain ⟨w, hw⟩ : ∃ w, n - b.val = w := ⟨_, rfl⟩
  have hw' : n - j.val = w + 1 := by
    have : b.val = j.val + 1 := rfl
    omega
  rw [hw, hw']
  nlinarith

theorem ColumnsFromPieri_of (hSwap : SwapPath) (hSame : SameCol) (hMeas : MeasSwap) (hMono : MonoRun)
    (hWt : WtIff) (hGood : GoodSwap) (hAntiStep : AntiStep) (hAnti : Anti) : ColumnsFromPieri := by
  intro K P M q _ _ _ _ _ _ EM n lam2 hp tau ⟨b, j0, hj0, hcol⟩ z hz
  have key : ∀ N : ℕ, ∀ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
      meas (colSeq κ ρ) = N → ∀ z : Tens (Fin q) P M n, IsWt K EM lam2 (cseq κ ρ) z → toSym K z = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro κ ρ hpath hN z hz
      by_cases hdesc : ∃ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ ⟨j.val + 1, hj⟩ < colSeq κ ρ j
      · obtain ⟨j, hj, hlt⟩ := hdesc
        obtain ⟨h2, κ', hpath', hc', hcol'⟩ := hSwap q n lam2 tau κ ρ hpath j hj hlt
        refine hGood K P M q EM n lam2 (cseq κ ρ) j hj h2 ?_ z hz
        intro z' hz'
        rw [← hc'] at hz'
        refine ih _ ?_ κ' _ hpath' rfl z' hz'
        rw [hcol', ← hN]
        exact hMeas n _ j hj hlt
      · push Not at hdesc
        obtain ⟨i, hi, hrun⟩ := hMono q n lam2 tau κ ρ hpath hdesc (Fintype.card P) j0 hcol
        refine hAnti K (Fin q) P M n i hi z ?_
        intro j hj h1 h2
        have hc : colSeq κ ρ ⟨j.val + 1, hj⟩ = colSeq κ ρ j := by
          rw [hrun j h1 (by omega), hrun ⟨j.val + 1, hj⟩ (by simp only []; omega) (by simp only []; omega)]
        obtain ⟨ha, hb⟩ := hSame q n lam2 tau κ ρ hpath j hj hc
        exact hAntiStep K P M q EM n lam2 hp _ z j hj hz ha hb
  have hle : PathSpace K (P := P) EM n lam2 tau ≤ LinearMap.ker (toSym K) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨κ, ρ, hpath, hy⟩
    exact LinearMap.mem_ker.2 (key _ κ ρ hpath rfl y ((hWt K P M q EM n lam2 κ ρ hpath.start hpath.step y).1 hy))
  exact LinearMap.mem_ker.1 (hle hz)

end Formalism.CohomologicalDescent.LC
end

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.AntitoneShapes
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lcb_transp {K R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] {n : ℕ} (i p : ℕ) (u : Tens R P M n)
    (h : ∀ (j : Fin n) (hj : j.val + 1 < n), i ≤ j.val → j.val < i + p →
      permY K (Equiv.swap j ⟨j.val + 1, hj⟩) u = - u) :
    ∀ (d : ℕ) (a b : Fin n), i ≤ a.val → b.val = a.val + d + 1 → b.val ≤ i + p →
      permY K (Equiv.swap a b) u = - u := by
  intro d
  induction d with
  | zero =>
    intro a b ha hb hbp
    have hj : a.val + 1 < n := by have := b.isLt; omega
    have hb' : b = ⟨a.val + 1, hj⟩ := Fin.ext (by simpa using hb)
    rw [hb']; exact h a hj ha (by omega)
  | succ d ih =>
    intro a b ha hb hbp
    have hc : a.val + d + 1 < n := by have := b.isLt; omega
    have hcb : (⟨a.val + d + 1, hc⟩ : Fin n).val + 1 < n := by have := b.isLt; simp only; omega
    have hb' : b = ⟨(⟨a.val + d + 1, hc⟩ : Fin n).val + 1, hcb⟩ := Fin.ext (by simp only; omega)
    have h1 : permY K (Equiv.swap a ⟨a.val + d + 1, hc⟩) u = - u := ih a ⟨a.val + d + 1, hc⟩ ha rfl (by simp only; omega)
    have h2 : permY K (Equiv.swap ⟨a.val + d + 1, hc⟩ b) u = - u := by
      rw [hb']; exact h ⟨a.val + d + 1, hc⟩ hcb (by simp only; omega) (by simp only; omega)
    have hac : a ≠ ⟨a.val + d + 1, hc⟩ := by
      intro e; have := congrArg Fin.val e; simp only at this; omega
    have hab : a ≠ b := by
      intro e; have := congrArg Fin.val e; omega
    have e : Equiv.swap a b = Equiv.swap ⟨a.val + d + 1, hc⟩ b * Equiv.swap a ⟨a.val + d + 1, hc⟩ *
        Equiv.swap ⟨a.val + d + 1, hc⟩ b := by
      rw [Equiv.swap_mul_swap_mul_swap hac hab, Equiv.swap_comm]
    rw [e, permOnTensor_mul, permOnTensor_mul]
    simp only [Module.End.mul_apply, h1, h2, map_neg, neg_neg]

theorem antitone_shapes : Anti := by
  intro K R P M _ _ _ _ _ _ _ _ n i hi u h
  classical
  have htr := lcb_transp (K := K) i (Fintype.card P) u h
  have hex : ∀ x : Fin n → P, ∃ ab : Fin n × Fin n, i ≤ ab.1.val ∧ ab.1.val < ab.2.val ∧
      ab.2.val ≤ i + Fintype.card P ∧ x ab.1 = x ab.2 := by
    intro x
    have hcard : Fintype.card P < Fintype.card (Fin (Fintype.card P + 1)) := by simp
    obtain ⟨s, t, hst, hx⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun s : Fin (Fintype.card P + 1) => x ⟨i + s.val, by have := s.isLt; omega⟩) hcard
    have hs := s.isLt
    have ht := t.isLt
    have hst' : s.val ≠ t.val := fun e => hst (Fin.ext e)
    rcases lt_or_gt_of_ne hst' with hlt | hlt
    · exact ⟨(⟨i + s.val, by omega⟩, ⟨i + t.val, by omega⟩), by simp only; omega, by simp only; omega,
        by simp only; omega, hx⟩
    · exact ⟨(⟨i + t.val, by omega⟩, ⟨i + s.val, by omega⟩), by simp only; omega, by simp only; omega,
        by simp only; omega, hx.symm⟩
  choose pr hpr using hex
  funext m
  rw [toSym_apply_sum_fiber]
  let xs : (Fin n → R × P) → Fin n → P := fun g s => (g s).2
  let inv : (Fin n → R × P) → (Fin n → R × P) := fun g => g ∘ Equiv.swap (pr (xs g)).1 (pr (xs g)).2
  have hxs : ∀ g, xs (inv g) = xs g := by
    intro g; funext s
    obtain ⟨_, _, _, h4⟩ := hpr (xs g)
    show (g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).2 = (g s).2
    by_cases hs1 : s = (pr (xs g)).1
    · rw [hs1, Equiv.swap_apply_left]; exact h4.symm
    · by_cases hs2 : s = (pr (xs g)).2
      · rw [hs2, Equiv.swap_apply_right]; exact h4
      · rw [Equiv.swap_apply_of_ne_of_ne hs1 hs2]
  have hu : ∀ g, u g + u (inv g) = 0 := by
    intro g
    obtain ⟨h1, h2, h3, h4⟩ := hpr (xs g)
    have key := congrFun (htr ((pr (xs g)).2.val - (pr (xs g)).1.val - 1) (pr (xs g)).1 (pr (xs g)).2 h1
      (by omega) h3) g
    rw [permSecond_apply] at key
    have e : (fun s => ((g (Equiv.swap (pr (xs g)).1 (pr (xs g)).2 s)).1, (g s).2)) = inv g := by
      funext s
      have := congrFun (hxs g) s
      exact Prod.ext rfl this.symm
    rw [e] at key
    rw [key]; simp
  show _ = (0 : M)
  refine Finset.sum_involution (fun g _ => inv g) ?_ ?_ ?_ ?_
  · intro g _; exact hu g
  · intro g _ hne heq
    apply hne
    have h0 := hu g
    rw [heq] at h0
    have h2 : (2 : K) • u g = 0 := by rw [two_smul]; exact h0
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    show cont (g ∘ _) = m
    rw [content_comp_perm_eq]; exact hg
  · intro g _
    show (inv g) ∘ Equiv.swap (pr (xs (inv g))).1 (pr (xs (inv g))).2 = g
    rw [hxs g]
    funext s
    simp [inv]

theorem lcb_mono {n : ℕ} (col : Fin n → ℕ) (h : ∀ (j : Fin n) (hj : j.val + 1 < n), col j ≤ col ⟨j.val + 1, hj⟩) :
    ∀ (d : ℕ) (a b : Fin n), b.val = a.val + d → col a ≤ col b := by
  intro d
  induction d with
  | zero => intro a b hb; have : a = b := Fin.ext (by omega); rw [this]
  | succ d ih =>
    intro a b hb
    have hc : a.val + d < n := by have := b.isLt; omega
    have hc' : (⟨a.val + d, hc⟩ : Fin n).val + 1 < n := by have := b.isLt; simp only; omega
    have hb' : b = ⟨(⟨a.val + d, hc⟩ : Fin n).val + 1, hc'⟩ := Fin.ext (by simp only; omega)
    calc col a ≤ col ⟨a.val + d, hc⟩ := ih a _ rfl
      _ ≤ col b := by rw [hb']; exact h _ hc'

theorem lcb_ivt {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (hp : IsPath n lam2 tau κ ρ) (a : Fin q) (j0 : ℕ) (h0 : lam2 a ≤ j0) :
    ∀ m ≤ n, j0 < κ m a → ∃ l : Fin n, ρ l = a ∧ κ l.val a = j0 := by
  intro m
  induction m with
  | zero => intro _ h; rw [hp.start] at h; omega
  | succ m ih =>
    intro hm h
    by_cases h' : j0 < κ m a
    · exact ih (by omega) h'
    · have hs := hp.step ⟨m, by omega⟩
      have hs' : κ (m + 1) a = κ m a + (Pi.single (ρ ⟨m, by omega⟩) 1 : Fin q → ℕ) a := by
        have := congrFun hs a; simpa using this
      by_cases hr : ρ ⟨m, by omega⟩ = a
      · refine ⟨⟨m, by omega⟩, hr, ?_⟩
        rw [hr, Pi.single_eq_same] at hs'
        simp only; omega
      · rw [Pi.single_eq_of_ne (Ne.symm hr)] at hs'
        omega

theorem monotone_run : MonoRun := by
  intro q n lam2 tau κ ρ hp hmono p j0 hlen
  classical
  unfold LD.colLen at hlen
  set S : Finset (Fin n) := Finset.univ.filter (fun l => colSeq κ ρ l = j0) with hS
  have hmem : ∀ l, l ∈ S ↔ colSeq κ ρ l = j0 := by
    intro l; simp [hS]
  have hsub : (Finset.univ.filter fun a : Fin q => lam2 a ≤ j0 ∧ j0 < tau a) ⊆ S.image ρ := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨l, hl1, hl2⟩ := lcb_ivt hp a j0 ha.1 n le_rfl (by rw [hp.stop]; exact ha.2)
    refine Finset.mem_image.mpr ⟨l, ?_, hl1⟩
    rw [hmem]
    unfold colSeq
    rw [hl1]; exact hl2
  have hcard : p < S.card := by
    calc p < _ := hlen
      _ ≤ (S.image ρ).card := Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hi : colSeq κ ρ (S.min' hne) = j0 := (hmem _).mp (Finset.min'_mem S hne)
  have hi' : colSeq κ ρ (S.max' hne) = j0 := (hmem _).mp (Finset.max'_mem S hne)
  have hIcc : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := fun l hl =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le S l hl, Finset.le_max' S l hl⟩
  have hc2 : S.card ≤ (S.max' hne).val + 1 - (S.min' hne).val := by
    have := Finset.card_le_card hIcc
    rwa [Fin.card_Icc] at this
  refine ⟨(S.min' hne).val, by have := (S.max' hne).isLt; omega, fun l h1 h2 => ?_⟩
  have m1 := lcb_mono _ hmono (l.val - (S.min' hne).val) (S.min' hne) l (by omega)
  have m2 := lcb_mono _ hmono ((S.max' hne).val - l.val) l (S.max' hne) (by omega)
  omega

end Formalism.CohomologicalDescent.LC
end

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.PathEqOfContentSequence
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lca_content_lt {q : ℕ} (κ : Fin q → ℕ) (h : Antitone κ) {a b : Fin q} (hab : a < b) :
    (κ b : ℤ) - (b.val : ℤ) < (κ a : ℤ) - (a.val : ℤ) := by
  have h1 : κ b ≤ κ a := h hab.le
  have h2 : a.val < b.val := hab
  omega

theorem lca_content_inj {q : ℕ} (κ : Fin q → ℕ) (h : Antitone κ) {a b : Fin q}
    (e : (κ a : ℤ) - (a.val : ℤ) = (κ b : ℤ) - (b.val : ℤ)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lca_content_lt κ h hab; omega
  · exact hab
  · have := lca_content_lt κ h hab; omega

theorem path_eq_of_content_sequence {q n : ℕ} {lam2 tau tau' : Fin q → ℕ} {κ κ' : ℕ → Fin q → ℕ} {ρ ρ' : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (H' : IsPath n lam2 tau' κ' ρ') (m : ℕ) (hm : m ≤ n)
    (hc : ∀ j : Fin n, j.val < m → cseq κ ρ j = cseq κ' ρ' j) : ∀ l ≤ m, κ l = κ' l := by
  intro l
  induction l with
  | zero => intro _; rw [H.start, H'.start]
  | succ l ih =>
    intro hl
    have e := ih (by omega)
    have hln : l < n := by omega
    have h1 := hc ⟨l, hln⟩ (by show l < m; omega)
    have h2 := H.step ⟨l, hln⟩
    have h3 := H'.step ⟨l, hln⟩
    dsimp only [cseq] at h1 h2 h3
    rw [← e] at h1 h3
    have h4 : ρ ⟨l, hln⟩ = ρ' ⟨l, hln⟩ := lca_content_inj (κ l) (H.dom l (by omega)) h1
    rw [h2, h3, h4]

theorem lca_single_ne {q : ℕ} {r a : Fin q} (h : a ≠ r) (A : Fin q → ℕ) :
    (A + Pi.single r 1 : Fin q → ℕ) a = A a := by
  simp [Pi.single_apply, h]

theorem lca_single_eq {q : ℕ} (r : Fin q) (A : Fin q → ℕ) :
    (A + Pi.single r 1 : Fin q → ℕ) r = A r + 1 := by simp

theorem lca_rows_lt {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (hle : colSeq κ ρ j' ≤ colSeq κ ρ j) :
    ρ j < ρ j' ∧ colSeq κ ρ j' = κ j.val (ρ j') := by
  have hjn := j'.isLt
  have s1 := H.step j
  have d1 := H.dom (j.val + 1) (by omega)
  have hle' : κ (j.val + 1) (ρ j') ≤ κ j.val (ρ j) := by
    have := hle; unfold colSeq at this; rwa [hv] at this
  have hlt : ρ j < ρ j' := by
    by_contra hcon
    have hcon : ρ j' ≤ ρ j := not_lt.mp hcon
    have h3 := d1 hcon
    rw [s1] at h3 hle'
    rw [lca_single_eq] at h3
    omega
  refine ⟨hlt, ?_⟩
  unfold colSeq; rw [hv, s1, lca_single_ne hlt.ne']

theorem lca_swap {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (hlt : colSeq κ ρ j' < colSeq κ ρ j) :
    2 ≤ cseq κ ρ j - cseq κ ρ j' ∧
      ∃ κ' : ℕ → Fin q → ℕ, IsPath n lam2 tau κ' (ρ ∘ Equiv.swap j j') ∧
        cseq κ' (ρ ∘ Equiv.swap j j') = cseq κ ρ ∘ Equiv.swap j j' ∧
        colSeq κ' (ρ ∘ Equiv.swap j j') = colSeq κ ρ ∘ Equiv.swap j j' := by
  obtain ⟨hr, hc⟩ := lca_rows_lt H j j' hv hlt.le
  have hjn := j'.isLt
  have s1 := H.step j
  have s2 := H.step j'
  rw [hv] at s2
  have d0 := H.dom j.val (by omega)
  have d2 := H.dom (j.val + 1 + 1) (by omega)
  have hA : κ j.val (ρ j') < κ j.val (ρ j) := by rw [← hc]; exact hlt
  have hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ) := by
    have := hc; unfold colSeq at this; unfold cseq; rw [this]
  have hr' : (ρ j).val < (ρ j').val := hr
  refine ⟨by rw [hc']; unfold cseq; omega, ?_⟩
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℕ → Fin q → ℕ,
      ∀ l, κ' l = if l = j.val + 1 then κ j.val + Pi.single (ρ j') 1 else κ l := ⟨_, fun _ => rfl⟩
  have k1 : κ' (j.val + 1) = κ j.val + Pi.single (ρ j') 1 := by rw [hκ', if_pos rfl]
  have k2 : ∀ l, l ≠ j.val + 1 → κ' l = κ l := fun l h => by rw [hκ', if_neg h]
  have anti : Antitone (κ j.val + Pi.single (ρ j') 1) := by
    intro a b hab
    by_cases hb : b = ρ j'
    · by_cases ha : a = ρ j'
      · rw [ha, hb]
      · rw [hb, lca_single_eq, lca_single_ne ha]
        have hab' : a < ρ j' := lt_of_le_of_ne (hb ▸ hab) ha
        by_cases har : a ≤ ρ j
        · have := d0 har; omega
        · have har : ρ j < a := not_le.mp har
          have h5 := d2 hab'.le
          rw [s2, s1] at h5
          rw [lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha, lca_single_ne har.ne'] at h5
          exact h5
    · rw [lca_single_ne hb]
      calc κ j.val b ≤ κ j.val a := d0 hab
        _ ≤ (κ j.val + Pi.single (ρ j') 1 : Fin q → ℕ) a := by simp [Pi.add_apply]
  have hcol : colSeq κ' (ρ ∘ Equiv.swap j j') = colSeq κ ρ ∘ Equiv.swap j j' := by
    funext l
    by_cases h1 : l = j
    · rw [h1]
      simp only [colSeq, Function.comp, Equiv.swap_apply_left]
      rw [k2 j.val (by omega), hv, s1, lca_single_ne hr.ne']
    · by_cases h2 : l = j'
      · rw [h2]
        simp only [colSeq, Function.comp, Equiv.swap_apply_right]
        rw [hv, k1, lca_single_ne hr.ne]
      · have h4 : l.val ≠ j.val + 1 := fun h => h2 (Fin.ext (h.trans hv.symm))
        simp only [colSeq, Function.comp]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ h4]
  refine ⟨κ', ⟨?_, ?_, ?_, ?_⟩, ?_, hcol⟩
  · rw [k2 0 (by omega), H.start]
  · intro l
    by_cases h1 : l = j
    · rw [h1]
      simp only [Function.comp, Equiv.swap_apply_left]
      rw [k1, k2 j.val (by omega)]
    · by_cases h2 : l = j'
      · rw [h2]
        simp only [Function.comp, Equiv.swap_apply_right]
        rw [hv, k1, k2 (j.val + 1 + 1) (by omega), s2, s1]
        exact add_right_comm _ _ _
      · have h3 : l.val ≠ j.val := fun h => h1 (Fin.ext h)
        have h4 : l.val ≠ j.val + 1 := fun h => h2 (Fin.ext (h.trans hv.symm))
        simp only [Function.comp]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ (by omega), k2 _ h4]
        exact H.step l
  · rw [k2 n (by omega), H.stop]
  · intro l hl
    by_cases h : l = j.val + 1
    · rw [h, k1]; exact anti
    · rw [k2 l h]; exact H.dom l hl
  · funext l
    have := congrFun hcol l
    simp only [colSeq, cseq, Function.comp] at this ⊢
    rw [this]

theorem swap_path_exists : SwapPath := by
  intro q n lam2 tau κ ρ H j hj hlt
  exact lca_swap H j ⟨j.val + 1, hj⟩ rfl hlt

theorem lca_same {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (heq : colSeq κ ρ j' = colSeq κ ρ j) :
    cseq κ ρ j' = cseq κ ρ j - 1 ∧ ¬ IsContentSeq lam2 (cseq κ ρ ∘ Equiv.swap j j') := by
  obtain ⟨hr, hc⟩ := lca_rows_lt H j j' hv heq.le
  have hjn := j'.isLt
  have s1 := H.step j
  have s2 := H.step j'
  rw [hv] at s2
  have d0 := H.dom j.val (by omega)
  have d2 := H.dom (j.val + 1 + 1) (by omega)
  have hA : κ j.val (ρ j') = κ j.val (ρ j) := by rw [← hc]; exact heq
  have hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ) := by
    have := hc; unfold colSeq at this; unfold cseq; rw [this]
  have hr' : (ρ j).val < (ρ j').val := hr
  constructor
  · have hrow : (ρ j').val = (ρ j).val + 1 := by
      by_contra hcon
      have hq := (ρ j').isLt
      obtain ⟨a, ha⟩ : ∃ a : Fin q, a.val = (ρ j).val + 1 := ⟨⟨(ρ j).val + 1, by omega⟩, rfl⟩
      have ha1 : ρ j < a := by show (ρ j).val < a.val; omega
      have ha2 : a < ρ j' := by show a.val < (ρ j').val; omega
      have h5 := d2 ha2.le
      rw [s2, s1] at h5
      rw [lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha2.ne, lca_single_ne ha1.ne'] at h5
      have h6 := d0 ha1.le
      omega
    rw [hc']; unfold cseq; omega
  · rintro ⟨tau', κ', ρ', H', hcs⟩
    have hpre : ∀ i : Fin n, i.val < j.val → cseq κ ρ i = cseq κ' ρ' i := by
      intro i hi
      have h := congrFun hcs i
      have h1 : i ≠ j := fun h => by rw [h] at hi; omega
      have h2 : i ≠ j' := fun h => by rw [h] at hi; omega
      simp only [Function.comp] at h
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at h
      exact h.symm
    have e : κ j.val = κ' j.val := path_eq_of_content_sequence H H' j.val (by omega) hpre j.val le_rfl
    have h1 := congrFun hcs j
    simp only [Function.comp, Equiv.swap_apply_left] at h1
    rw [hc'] at h1
    unfold cseq at h1
    rw [← e] at h1
    have h2 : ρ' j = ρ j' := lca_content_inj _ d0 h1
    have h3 := H'.dom (j.val + 1) (by omega) hr.le
    rw [H'.step j, ← e, h2, lca_single_eq, lca_single_ne hr.ne] at h3
    omega

theorem same_column : SameCol := by
  intro q n lam2 tau κ ρ H j hj heq
  exact lca_same H j ⟨j.val + 1, hj⟩ rfl heq

end Formalism.CohomologicalDescent.LC
end

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem antitone_increment : AntiStep := AntiStep_of no_bad_tuple

theorem columns_from_pieri : ColumnsFromPieri :=
  ColumnsFromPieri_of swap_path_exists same_column measure_swap_invariant monotone_run weight_iff_condition good_swap_exists
    antitone_increment antitone_shapes

end Formalism.CohomologicalDescent.LC
end

namespace Formalism.CohomologicalDescent.ColumnMinorsFromPieri

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem columns_real_of_pieri_real : ColumnsRealOfPieriReal := by
  intro hP p q w lam2 hanti hle n tau hcol z hz
  exact Formalism.CohomologicalDescent.LC.columns_from_pieri ℚ (Fin p) _ q _ n lam2 (hP p q w lam2 hanti hle n) tau
    (by simpa using hcol) z hz

end Formalism.CohomologicalDescent.ColumnMinorsFromPieri
end

namespace Formalism.CohomologicalDescent.Down

theorem hG : LD.LemmaDGraded :=
  LR.real_of_pieri LPR.pieri_real_form (ColumnMinorsFromPieri.columns_real_of_pieri_real LPR.pieri_real_form)

theorem inclusion_w_real_holds : InclWReal := ShortWeightBounds.inclusion_w_real_holds hG

end Formalism.CohomologicalDescent.Down
end

namespace Formalism.CohomologicalDescent.Down7

private lemma cShort6_le_cCoarse (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) :
    Formalism.CohomologicalDescent.ShortWeightBounds.cShort6 l k j t q h N' ecl xm xp mB I ≤
      Formalism.CohomologicalDescent.UnitNormBounds.cCoarse l k j t q h N' ecl xm xp mB I := by
  unfold Formalism.CohomologicalDescent.ShortWeightBounds.cShort6 Formalism.CohomologicalDescent.UnitNormBounds.cCoarse
  have e : ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6) =
      ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1)) +
        ((q : ℝ) + 2 * (j : ℝ)) * 6 := by ring
  have hq : (0 : ℝ) ≤ ((q : ℝ) + 2 * (j : ℝ)) * 6 := by positivity
  linarith

private lemma JW_le_coarseWeightBound {ι : Type} [Fintype ι] [DecidableEq ι] (W : Formalism.CohomologicalDescent.ShortWeightBounds.Wts ι)
    (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (l : ℕ) : W.JW P l ≤ W.coarseWeightBound P l := by
  unfold Formalism.CohomologicalDescent.ShortWeightBounds.Wts.JW Formalism.CohomologicalDescent.ShortWeightBounds.Wts.coarseWeightBound
  apply Finset.sum_le_sum
  intro τ _
  unfold Formalism.CohomologicalDescent.DepthNonnegative.cTau Formalism.CohomologicalDescent.ShortWeightBounds.cFloorShort6 Formalism.CohomologicalDescent.DepthNonnegative.cFloorCoarse
  split_ifs
  · exact min_le_min_left _ (Nat.floor_mono (cShort6_le_cCoarse _ _ _ _ _ _ _ _ _ _ _ _))
  · exact le_rfl

private lemma pow_smul_mem_mono' {T M S : Type*} [Monoid T] [MulAction T M] [Membership M S]
    (a : T) (s : S) {J J' : ℕ} (hJ : J ≤ J') (h : ∀ y : M, a ^ J • y ∈ s) :
    ∀ y : M, a ^ J' • y ∈ s := by
  intro y
  have hy := h (a ^ (J' - J) • y)
  rwa [smul_smul, ← pow_add, Nat.add_sub_cancel' hJ] at hy

private lemma Incl_mono {ι : Type} [DecidableEq ι] {N : ℕ} {lam : ι → ℕ → ℕ}
    (X : Formalism.CohomologicalDescent.ShortWeightBounds.HidaSetting ι N lam) (l J J' : ℕ) (h : X.Incl l J) (hJ : J ≤ J') :
    X.Incl l J' := by
  unfold Formalism.CohomologicalDescent.ShortWeightBounds.HidaSetting.Incl Formalism.CohomologicalDescent.DepthNonnegative.TopIncl at h ⊢
  exact pow_smul_mem_mono' _ _ hJ h

theorem inclusion_w_seven_real_holds : HidaLatticeInclusionAtCoarseWeightBound := by
  intro P hP hL ι _ _ W hW l X hl hu hlJ hin
  obtain ⟨h1, h2⟩ := Formalism.CohomologicalDescent.Down.inclusion_w_real_holds P hP hL ι W hW l X hl hu hlJ hin
  exact ⟨Incl_mono X l _ _ h1 (JW_le_coarseWeightBound W P l), le_trans h2 (JW_le_coarseWeightBound W P l)⟩

end Formalism.CohomologicalDescent.Down7
