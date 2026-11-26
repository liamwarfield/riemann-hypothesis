module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchPowerSumAtRootsOfUnity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchPowerSumAtRootsOfUnity.rootOfUnity_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) : IsPrimitiveRoot (rootOfUnity k) k := by
  simpa [rootOfUnity] using Complex.isPrimitiveRoot_exp k (by omega)

theorem SchPowerSumAtRootsOfUnity.proof : SchPowerSumAtRootsOfUnity.Statement := by
  intro N k j hk hkN hj
  have hprim := SchPowerSumAtRootsOfUnity.rootOfUnity_isPrimitiveRoot hk
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [psum, map_sum, map_pow, aeval_X]
  have hsum : ∑ i : Fin N, rootOfUnityPoint N k i ^ j =
      ∑ i ∈ range k, (rootOfUnity k ^ j) ^ i := by
    unfold rootOfUnityPoint
    rw [Fin.sum_univ_eq_sum_range (fun i => (if i < k then rootOfUnity k ^ i else 0) ^ j) N,
      ← Finset.sum_range_add_sum_Ico _ hkN]
    rw [Finset.sum_eq_zero (s := Ico k N) (fun i hi => by
      simp only [Finset.mem_Ico] at hi
      simp [show ¬ i < k by omega, zero_pow (show j ≠ 0 by omega)]), add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [hi, ← pow_mul, mul_comm]
  rw [hsum]
  split_ifs with hd
  · have h1 : rootOfUnity k ^ j = 1 := (hprim.pow_eq_one_iff_dvd j).2 hd
    simp [h1]
  · have h1 : rootOfUnity k ^ j ≠ 1 := fun h => hd ((hprim.pow_eq_one_iff_dvd j).1 h)
    have h2 : (rootOfUnity k ^ j) ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchStrictAntiSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchStrictAntiSplit.add_gap_le {r : ℕ} {d : Fin r → ℕ} (hd : StrictAnti d) :
    ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k → d j + k ≤ d i :=
  _root_.UpperTheory.Reformulated.B.Yoa4.add_gap_le hd

theorem SchStrictAntiSplit.sum_staircase (r : ℕ) :
    ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, Finset.sum_range_reflect (fun i => i) r,
    Finset.sum_range_id]

theorem SchStrictAntiSplit.proof : SchStrictAntiSplit.Statement := by
  intro r n d hd hsum
  have hlow : ∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i := by
    intro i
    have hr : 0 < r := Fin.pos i
    have h := SchStrictAntiSplit.add_gap_le hd (r - 1 - (i : ℕ)) i ⟨r - 1, by omega⟩
      (by simp; omega)
    omega
  refine ⟨hlow, ?_⟩
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  refine ⟨?_, ?_⟩
  · have hadd : ∑ i : Fin r, (d i - (r - 1 - (i : ℕ))) + ∑ i : Fin r, (r - 1 - (i : ℕ)) =
        ∑ i : Fin r, d i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlow i)
    rw [SchStrictAntiSplit.sum_staircase] at hadd
    omega
  · intro i j hij
    have h := SchStrictAntiSplit.add_gap_le hd ((j : ℕ) - i) i j (by omega)
    have := hlow i
    have := hlow j
    have : (i : ℕ) ≤ j := hij
    have : (j : ℕ) < r := j.isLt
    show d j - (r - 1 - (j : ℕ)) ≤ d i - (r - 1 - (i : ℕ))
    omega

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchJTMatrixDetAtRoots
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchJTMatrixDetAtRoots.proof (h1 : SchRootOfUnityBialternant.Statement)
    (h2 : SchRootOfUnityRowsPerm.Statement) (h3 : SchRootOfUnityRowsEq.Statement)
    (h4 : SchHookResidues.Statement) (h5 : SchNonHookResidues.Statement)
    (h6 : SchRootOfUnityVandermondeNe.Statement) : SchJTMatrixDetAtRoots.Statement := by
  intro k nu hk hanti hsum
  have hV := h6 k hk
  have hB := h1 k nu hk

  have hstair : (Matrix.of fun i j : Fin k =>
      rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det =
      vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := by
    rw [← Schur.det_pow_staircase_eq_vandermondeOf (fun j : Fin k => rootOfUnity k ^ (j : ℕ))]
    congr 1
    ext i j
    simp [Matrix.of_apply, pow_mul]
  split_ifs with hhook
  · obtain ⟨π, hres, hsign⟩ := h4 k nu hk hanti hsum hhook
    have hP := h2 k (fun i => nu i + (k - 1 - (i : ℕ))) π hk hres
    rw [hstair] at hP
    have hP' : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := hP
    rw [hB] at hP'
    have := mul_right_cancel₀ hV hP'
    rw [this, hsign]
    push_cast
    rfl
  · obtain ⟨i, i', hne, hres⟩ := h5 k nu hk hanti hsum hhook
    have hZ : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det = 0 :=
      h3 k (fun i => nu i + (k - 1 - (i : ℕ))) i i' hne hres
    rw [hB] at hZ
    exact (mul_eq_zero.mp hZ).resolve_right hV

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagInjSumBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem FlagInjSumBound.finset_sum_bound (S : Finset ℕ) :
    ∑ i ∈ Finset.range S.card, i ≤ ∑ x ∈ S, x ∧
      (∑ x ∈ S, x = ∑ i ∈ Finset.range S.card, i → S ⊆ Finset.range S.card) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S' hlt ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hm : m ∉ S' := fun h => lt_irrefl m (hlt m h)
    have hsub : S' ⊆ Finset.range m := fun x hx => Finset.mem_range.2 (hlt x hx)
    have hcard : S'.card ≤ m := by simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hm, Finset.sum_range_succ, Finset.sum_insert hm]
    refine ⟨by omega, fun heq => ?_⟩
    have hmeq : m = S'.card := by omega
    have hS' := ih₂ (by omega)
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_range.2 (by omega)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hS' hx)))

theorem FlagInjSumBound.proof : FlagInjSumBound.Statement := by
  intro N g hg
  classical
  set S := Finset.univ.image g with hSdef
  have hcard : S.card = N := by
    rw [hSdef, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i, g i = ∑ x ∈ S, x := by
    rw [hSdef, Finset.sum_image (fun i _ j _ h => hg h)]
  obtain ⟨h₁, h₂⟩ := FlagInjSumBound.finset_sum_bound S
  rw [hcard, Finset.sum_range_id] at h₁ h₂
  rw [hsum]
  refine ⟨h₁, fun heq i => ?_⟩
  have hi : g i ∈ S := Finset.mem_image_of_mem g (Finset.mem_univ i)
  exact Finset.mem_range.1 (h₂ heq hi)

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralPermute
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralPermute.proof (h1 : FlagCoeffBlockPermute.Statement) :
    FlagIntegralPermute.Statement := by
  classical
  intro f N w H
  let e : Fin f × Fin N ≃ Fin f × Fin N := Equiv.prodShear (Equiv.refl _) w
  have hcomp : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) =
        Finsupp.equivMapDomain e.symm α := by
    intro α; ext p; simp [Finsupp.equivMapDomain_apply, e, Equiv.prodShear]
  have hH : ∀ α, AddMonoidAlgebra.coeff (blockPermute f N w H) α = AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) := by
    intro α; rw [h1, hcomp]
  have hD : ∀ α, AddMonoidAlgebra.coeff (blockVandermonde f N) (Finsupp.equivMapDomain e.symm α) =
      blockSign f N w * AddMonoidAlgebra.coeff (blockVandermonde f N) α := by
    intro α
    rw [← hcomp, ← h1, Flag.blockPermute_blockVandermonde, coeff_smul, smul_eq_mul]
  have hs2 : blockSign f N w * blockSign f N w = 1 := Flag.blockSign_mul_self f N w
  have hs0 : blockSign f N w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hs2; exact zero_ne_one hs2
  have hfac : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivMapDomain e.symm α).prod (fun _ n => (n.factorial : ℚ)) =
        α.prod (fun _ n => (n.factorial : ℚ)) := by
    intro α; rw [Finsupp.prod_equivMapDomain]
  unfold flagIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Finsupp.domCongr e.symm).toEquiv (fun α => ?_) (fun α _ => ?_)
  · simp only [MvPolynomial.mem_support_iff, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
      Finsupp.domCongr_apply, hD]
    exact ⟨fun h => mul_ne_zero hs0 h, fun h h' => h (by rw [h', mul_zero])⟩
  · simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.domCongr_apply, hH, hD, hfac]
    linear_combination (-(AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) *
      AddMonoidAlgebra.coeff (blockVandermonde f N) α * α.prod (fun _ n => (n.factorial : ℚ)))) * hs2

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAlternantRenamePlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

noncomputable section

theorem rename_alternant_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (v : ι → ℕ) :
    rename e (alternant v) = alternant (v ∘ e.symm) := by
  unfold alternant
  rw [AlgHom.map_det, ← Matrix.det_submatrix_equiv_self e
    (Matrix.of fun p p' : κ => (X p : MvPolynomial κ ℚ) ^ (v ∘ e.symm) p')]
  congr 1
  ext i i'
  simp [Matrix.map_apply, Matrix.submatrix_apply]

def smallBlockEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv := by
    intro x
    cases c <;> rcases x with i | j <;> simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv := by
    intro p
    cases c <;> simp only [smallBlockOf] <;> split_ifs with h <;>
      apply Fin.ext <;> simp [smallBlockPlace, yIndex, zIndex] <;> omega

theorem SchAlternantRenamePlace.proof : SchAlternantRenamePlace.Statement := by
  intro r a c v
  have hg : smallBlockPlace r a c =
      (fun p : Fin (r + a) => ((0 : Fin 1), p)) ∘ smallBlockEquiv r a c := by
    funext x
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hs : (smallBlockEquiv r a c).symm = smallBlockOf r a c := rfl
  rw [hg, ← rename_rename]
  congr 1
  rw [rename_alternant_equiv, hs]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchProdOneSubRootsOfUnity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Polynomial Finset

theorem SchProdOneSubRootsOfUnity.proof : SchProdOneSubRootsOfUnity.Statement := by
  intro k hk
  have hk0 : 0 < k := hk
  have : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk0⟩
  have hζ : IsPrimitiveRoot (rootOfUnity k) k := by
    unfold rootOfUnity
    exact Complex.isPrimitiveRoot_exp k (Nat.pos_iff_ne_zero.mp hk0)
  set p : ℂ[X] := ∏ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X) with hp
  set q : ℂ[X] := 1 - X ^ k with hq
  have hpdeg : p.natDegree ≤ k := by
    have h1 : ∀ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X).natDegree ≤ 1 := fun i _ => by
      compute_degree
    refine (natDegree_prod_le _ _).trans ((sum_le_sum h1).trans ?_)
    simp
  have hqdeg : q.natDegree ≤ k := by
    rw [hq]; compute_degree
  have hdeg : (p - q).degree < #(insert (0 : ℂ) (nthRootsFinset k (1 : ℂ))) := by
    rw [card_insert_of_notMem (by simp [mem_nthRootsFinset hk0, zero_pow hk0.ne']),
      hζ.card_nthRootsFinset]
    refine (degree_le_of_natDegree_le ((natDegree_sub_le _ _).trans (max_le hpdeg hqdeg))).trans_lt ?_
    exact_mod_cast Nat.lt_succ_self k
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ hdeg fun x hx => ?_
  rcases mem_insert.mp hx with rfl | hx
  · simp [hp, hq, eval_prod, zero_pow hk0.ne']
  · have hxk : x ^ k = 1 := (mem_nthRootsFinset hk0 _).mp hx
    have hinv : x⁻¹ ^ k = 1 := by rw [inv_pow, hxk, inv_one]
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hinv
    have hx0 : x ≠ 0 := by
      rintro rfl; simp [zero_pow hk0.ne'] at hxk
    have hzero : p.eval x = 0 := by
      rw [hp, eval_prod]
      refine prod_eq_zero (mem_range.mpr hi) ?_
      simp [hi', inv_mul_cancel₀ hx0]
    rw [hzero, hq]
    simp [hxk]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchCompleteGenerating
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace SchCompleteGenerating

theorem coeff_prod_geomSeries_eval {N : ℕ} (y : Fin N → ℂ) (n : ℕ) :
    PowerSeries.coeff n (∏ i : Fin N, Schur.geomSeries (y i)) =
      aeval y (hsymm (Fin N) ℚ n) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PowerSeries.coeff_prod, Schur.hsymm_eq_sum_finsuppAntidiag, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Schur.geomSeries, PowerSeries.coeff_mk, map_prod]

theorem coe_prod_one_sub {N : ℕ} (y : Fin N → ℂ) :
    ((∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp

theorem prod_one_sub_mul_prod_geomSeries {N : ℕ} (y : Fin N → ℂ) :
    (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      ∏ i : Fin N, Schur.geomSeries (y i) = 1 := by
  rw [← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm, Schur.geomSeries_mul]

theorem proof : Statement := by
  intro N y d
  have key := congrArg (PowerSeries.coeff d) (prod_one_sub_mul_prod_geomSeries y)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      PowerSeries.coeff b (∏ i : Fin N, Schur.geomSeries (y i))), PowerSeries.coeff_one] at key
  simp only [coeff_prod_geomSeries_eval, ← coe_prod_one_sub, Polynomial.coeff_coe] at key
  exact key

end SchCompleteGenerating

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAltCoeffInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagAltCoeffInjective.proof (h1 : FlagCoeffBlockPermute.Statement) :
    FlagAltCoeffInjective.Statement := by
  classical
  intro f N P α hP hc τ i j hij
  simp only at hij
  by_contra hne
  let w : Fin f → Equiv.Perm (Fin N) := Function.update 1 τ (Equiv.swap i j)
  have hsign : blockSign f N w = -1 := by
    unfold blockSign
    rw [Finset.prod_eq_single τ]
    · simp [w, Equiv.Perm.sign_swap hne]
    · intro b _ hb
      simp [w, Function.update_of_ne hb]
    · simp
  have hα : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α := by
    ext ⟨σ, k⟩
    change α (σ, w σ k) = α (σ, k)
    by_cases hσ : σ = τ
    · subst hσ
      simp only [w, Function.update_self]
      rcases eq_or_ne k i with rfl | hki
      · rw [Equiv.swap_apply_left]; exact hij.symm
      · rcases eq_or_ne k j with rfl | hkj
        · rw [Equiv.swap_apply_right]; exact hij
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    · simp [w, Function.update_of_ne hσ]
  have key := h1 f N w P α
  rw [hα, hP w, hsign, coeff_smul] at key
  have : AddMonoidAlgebra.coeff P α = 0 := by
    have h2 : (2 : ℚ) * AddMonoidAlgebra.coeff P α = 0 := by
      rw [smul_eq_mul] at key
      linarith
    simpa using h2
  exact hc this

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagPowerSumPreimage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ l ∈ Finset.Icc 1 N, g l = ∑ i : Fin N, g (i.val + 1) := by
  have hI : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1)), hI, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  exact Finset.sum_congr rfl (fun i _ => by rw [add_comm])

theorem FlagPowerSumPreimage.proof : FlagPowerSumPreimage.Statement := by
  intro N T hT
  choose Sf hSf using fun l => Flag.exists_powerSumHom_eq (hT l)
  refine ⟨∑ i : Fin N, X i * Sf (i.val + 1), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [sum_Icc_one_eq_sum_fin N (fun l => psum (Fin N) ℚ l * T l), map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_mul, hSf]
      simp [powerSumHom]
  · intro k hk1 hkN
    set j : Fin N := ⟨k - 1, by omega⟩ with hj
    rw [coeff_sum, Finset.sum_eq_single j]
    · rw [coeff_X_mul', if_pos (by simp), tsub_self, ← constantCoeff_eq,
        ← Flag.constantCoeff_powerSumHom, hSf]
      have : j.val + 1 = k := by simp [hj]; omega
      rw [this]
    · intro i _ hij
      rw [coeff_X_mul', if_neg]
      simp only [Finsupp.mem_support_iff, ne_eq]
      rw [Finsupp.single_apply, if_neg (fun h => hij h.symm)]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem LemmaA.proof (h1 : FlagIntegralTopDegree.Statement)
    (h2 : FlagIntegralVandermondePos.Statement) (h3 : FlagDividedDifferencePoly.Statement)
    (h4 : FlagAntisymDecomposition.Statement) (h5 : FlagVandermondeHomogeneous.Statement)
    (h6 : FlagAntisymHomogeneous.Statement) (h7 : FlagQuotientHomogeneous.Statement)
    (h8 : FlagRestrictHomogeneous.Statement) (h9 : FlagRestrictSymmetric.Statement)
    (h10 : FlagRestrictDecomposition.Statement) (h11 : FlagPowerSumPreimage.Statement)
    (h12 : FlagRestrictConstantCoeff.Statement) (h13 : FlagIntegralViaQuotient.Statement) :
    LemmaA.Statement := by
  intro f N
  refine ⟨flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f, ?_, ?_, ?_⟩
  · exact div_ne_zero (h2 f N).ne' (pow_ne_zero _ (Nat.cast_ne_zero.mpr N.factorial_ne_zero))
  · exact fun H hH => h1 f N H hH
  intro F Q hF k hk1 hkN τ G hG
  choose R hR hRsym using fun l σ => h3 f N (G * Q l σ)
  set P : RootRing f N := ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ
    with hPdef
  have hanti : antisymmetrize f N (G * F) = blockVandermonde f N * P := h4 f N F G Q R hF hR
  refine ⟨P, ?_, ?_, ?_⟩
  · have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) _)).mpr
        (Flag.blockVandermonde_ne_zero f N)
    rw [dividedDifference, hanti, map_mul, mul_div_cancel_left₀ _ hΔ]
  · intro hFh
    have hGF : (G * F).IsHomogeneous (topDegree f N + k) := by
      have := hG.mul hFh
      rwa [show k - 1 + (topDegree f N + 1) = topDegree f N + k by omega] at this
    have hA := h6 f N (G * F) _ hGF
    rw [hanti] at hA
    exact h8 f N τ P k (h7 _ _ _ _ _ (Flag.blockVandermonde_ne_zero f N) (h5 f N) hA)
  · obtain ⟨S, hS, hScoeff⟩ := h11 N (fun l => restrictToBlock f N τ (R l τ))
      (fun l => h9 f N τ (R l τ) (hRsym l τ))
    refine ⟨S, ?_, ?_⟩
    · rw [hS, hPdef, h10]
    · rw [hScoeff k hk1 hkN, h12, h13 f N _ _ (hR k τ)]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAntisymmetrizePlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def smallBlockPlaceEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv x := by
    cases c <;> rcases x with i | j <;>
      simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv p := by
    cases c
    · by_cases h : (p : ℕ) < a
      · simp [smallBlockPlace, smallBlockOf, zIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inl, yIndex]
        ext; simp; omega
    · by_cases h : (p : ℕ) < r
      · simp [smallBlockPlace, smallBlockOf, yIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inr, zIndex]
        ext; simp; omega

theorem smallBlockPlace_eq (r a : ℕ) (c : SmallBlock) (x : Fin r ⊕ Fin a) :
    smallBlockPlace r a c x = (0, smallBlockPlaceEquiv r a c x) := by
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem SchAntisymmetrizePlace.proof : SchAntisymmetrizePlace.Statement := by
  intro r a c Q
  set e := smallBlockPlaceEquiv r a c with he
  unfold antisymmetrize antisym
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv ((Equiv.funUnique (Fin 1) _).trans e.symm.permCongr) _ _ ?_
  intro w
  simp only [Equiv.trans_apply, Equiv.funUnique_apply]
  rw [AlgHom.map_smul_of_tower, blockPermute, rename_rename, rename_rename]
  have hs : blockSign 1 (r + a) w = ((Equiv.Perm.sign (e.symm.permCongr (w 0)) : ℤ) : ℚ) := by
    rw [Equiv.Perm.sign_permCongr, blockSign, Fintype.prod_unique]
    rfl
  rw [hs]
  congr 3
  funext x
  simp [smallBlockPlace_eq, ← he]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchNonHookResidues
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem sum_fin_staircase (k : ℕ) : ∑ i : Fin k, (k - 1 - (i : ℕ)) = k * (k - 1) / 2 := by
  have h := Finset.sum_range_reflect (fun i : ℕ => i) k
  rw [Fin.sum_univ_eq_sum_range (fun i => k - 1 - i) k, h, Finset.sum_range_id]

theorem SchNonHookResidues.proof (h1 : SchResidueCount.Statement) :
    SchNonHookResidues.Statement := by
  intro k nu hk hanti hsum hnot
  push Not at hnot
  obtain ⟨j, hj0, hj2⟩ := hnot
  have hk2 : 2 ≤ k := by have := j.isLt; omega
  by_contra hcon
  push Not at hcon
  set l : Fin k → ℕ := fun i => nu i + (k - 1 - (i : ℕ)) with hl
  have hinj : Function.Injective (fun i => l i % k) := by
    intro a b hab
    by_contra hne
    exact hcon a b hne hab
  have hle : ∀ i, nu i ≤ k := fun i =>
    hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hlt : ∀ i, l i < 2 * k := by
    intro i
    have := hle i
    have := i.isLt
    simp only [hl]
    omega
  have hcount := h1 k l hlt hinj
  have hsumL : ∑ i, l i = k + k * (k - 1) / 2 := by
    simp only [hl, Finset.sum_add_distrib, hsum, sum_fin_staircase]
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have h1le : nu j ≤ nu i1 := hanti (show i1 ≤ j by rw [Fin.le_iff_val_le_val]; simp [i1]; omega)
  have h0le : nu i1 ≤ nu i0 := hanti (show i0 ≤ i1 by rw [Fin.le_iff_val_le_val]; simp [i0, i1])
  have hsub : ({i0, i1} : Finset (Fin k)) ⊆ univ.filter fun i => k ≤ l i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hv0 : (i0 : ℕ) = 0 := rfl
    have hv1 : (i1 : ℕ) = 1 := rfl
    rcases hx with rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hl, hv0, hv1] <;> omega
  have hcard : 2 ≤ (univ.filter fun i => k ≤ l i).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (by simp [i0, i1, Fin.ext_iff])] at this
  have hmul := Nat.mul_le_mul_left k hcard
  omega

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchCompleteAtRootsOfUnity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem prod_one_sub_rootOfUnityPoint (h1 : SchProdOneSubRootsOfUnity.Statement) {N k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ) := by
  let f : ℕ → Polynomial ℂ := fun i =>
    1 - Polynomial.C (if i < k then rootOfUnity k ^ i else 0) * Polynomial.X
  calc ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X)
      = ∏ i ∈ range N, f i := Fin.prod_univ_eq_prod_range f N
    _ = ∏ i ∈ range k, f i := by
        refine (prod_subset (range_subset_range.2 hkN) fun i _ hik => ?_).symm
        have : ¬ i < k := fun h => hik (mem_range.2 h)
        simp [f, this]
    _ = ∏ i ∈ range k, (1 - Polynomial.C (rootOfUnity k ^ i) * Polynomial.X) :=
        prod_congr rfl fun i hi => by simp [f, mem_range.1 hi]
    _ = 1 - Polynomial.X ^ k := h1 k hk

theorem SchCompleteAtRootsOfUnity.proof (h1 : SchProdOneSubRootsOfUnity.Statement)
    (h2 : SchCompleteGenerating.Statement) : SchCompleteAtRootsOfUnity.Statement := by
  intro N k d hk hkN
  let H : ℕ → ℂ := fun n => aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ n)
  have hrec : ∀ n, H n - (if k ≤ n then H (n - k) else 0) = if n = 0 then 1 else 0 := by
    intro n
    have e := h2 N (rootOfUnityPoint N k) n
    rw [prod_one_sub_rootOfUnityPoint h1 hk hkN] at e
    rw [← e]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow, sub_mul,
      sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
    simp [H]
  show H d = _
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have e := hrec d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [if_neg (by omega), sub_zero, if_pos rfl] at e
      rw [e, if_pos (dvd_zero k)]
    · by_cases hkd : k ≤ d
      · rw [if_pos hkd, if_neg (show d ≠ 0 by omega), sub_eq_zero, ih (d - k) (by omega)] at e
        have hdvd : k ∣ d - k ↔ k ∣ d := by
          conv_rhs => rw [show d = d - k + k by omega]
          exact (Nat.dvd_add_self_right).symm
        rw [e]
        exact if_congr hdvd rfl rfl
      · rw [if_neg hkd, if_neg (show d ≠ 0 by omega), sub_zero] at e
        rw [e, if_neg]
        exact fun h => hkd (Nat.le_of_dvd hd h)

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSmallBlockProduct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchSmallBlockProduct.sum_fin_staircase (r : ℕ) : ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r,
    Finset.sum_range_reflect (fun i => i) r, Finset.sum_range_id]

theorem SchSmallBlockProduct.vandermondeOf_X_comp {m : ℕ} {κ : Type*} (g : Fin m → κ) :
    vandermondeOf (fun i => (X (g i) : MvPolynomial κ ℚ)) =
      rename g (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) := by
  simp [vandermondeOf, map_prod, map_sub, rename_X]

theorem SchSmallBlockProduct.vandermondeOf_X_eq_alternant (m : ℕ) :
    vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun j : Fin m => m - 1 - (j : ℕ)) := by
  rw [← Schur.det_pow_staircase_eq_vandermondeOf, alternant, ← Matrix.det_transpose]
  rfl

theorem SchSmallBlockProduct.schur_mul_vandermondeOf_eq_alternant {m : ℕ} (lam : Fin m → ℕ) :
    schur (Fin m) lam * vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun i : Fin m => lam i + (m - 1 - (i : ℕ))) := by
  rw [← Schur.det_pow_add_staircase_eq, alternant, ← Matrix.det_transpose]
  rfl

theorem SchSmallBlockProduct.proof (h1 : SchAevalSignedRename.Statement)
    (h2 : SchAlternantHomogeneous.Statement) : SchSmallBlockProduct.Statement := by
  intro r a c lam
  set e : Fin r → ℕ := fun i => lam i + (r - 1 - (i : ℕ)) with he
  have hy : yRoot 1 r a c 0 = fun i => C c.sign * (X (yIndex 1 r a c 0 i) : RootRing 1 (r + a)) :=
    rfl
  have hz : zRoot 1 r a c 0 = fun i => (X (zIndex 1 r a c 0 i) : RootRing 1 (r + a)) := rfl

  have hVy : vandermondeOf (yRoot 1 r a c 0) =
      aeval (yRoot 1 r a c 0) (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))) := by
    simp [vandermondeOf, map_prod, map_sub]

  have hdeg : ∑ i, e i = ∑ i, lam i + r * (r - 1) / 2 := by
    rw [he, Finset.sum_add_distrib, SchSmallBlockProduct.sum_fin_staircase]
  have hA : aeval (yRoot 1 r a c 0) (alternant e) =
      C (c.sign ^ (∑ i, lam i + r * (r - 1) / 2)) * rename (yIndex 1 r a c 0) (alternant e) := by
    rw [hy, ← hdeg]
    exact h1 (Fin r) (Fin 1 × Fin (r + a)) c.sign (yIndex 1 r a c 0) _ (alternant e) (h2 (Fin r) e)
  have hVz : vandermondeOf (zRoot 1 r a c 0) =
      rename (zIndex 1 r a c 0) (alternant fun j : Fin a => a - 1 - (j : ℕ)) := by
    rw [hz, SchSmallBlockProduct.vandermondeOf_X_comp, SchSmallBlockProduct.vandermondeOf_X_eq_alternant]
  have hplace_l : smallBlockPlace r a c ∘ Sum.inl = yIndex 1 r a c 0 := rfl
  have hplace_r : smallBlockPlace r a c ∘ Sum.inr = zIndex 1 r a c 0 := rfl
  rw [hVy, ← map_mul, SchSmallBlockProduct.schur_mul_vandermondeOf_eq_alternant, hA, hVz, map_mul, rename_rename,
    rename_rename, hplace_l, hplace_r, mul_assoc]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem antisymmetrize_C_mul (f N : ℕ) (k : ℚ) (H : RootRing f N) :
    antisymmetrize f N (C k * H) = C k * antisymmetrize f N H := by
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [blockPermute]

theorem blockVandermonde_ne_zero (f N : ℕ) : blockVandermonde f N ≠ 0 := by
  unfold blockVandermonde vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr ?_
  intro h
  have h' := X_injective h
  simp only [Prod.mk.injEq, true_and] at h'
  exact (ne_of_lt (Finset.mem_Ioi.mp hj)) h'

theorem LemmaB.proof (h1 : SchAevalSignedRename.Statement) (h2 : SchAntisymmetrizePlace.Statement)
    (h3 : SchSmallBlockProduct.Statement) (h4 : SchConcatAlternant.Statement)
    (h5 : SchConcatAlternantZero.Statement) (h6 : SchBlockVandermondeOne.Statement)
    (h7 : SchSchurHomogeneous.Statement) : LemmaB.Statement := by
  intro r a c
  obtain ⟨s, hs, hconc⟩ := h4 r a c
  have hsgn : ∀ n : ℕ, c.sign ^ n = 1 ∨ c.sign ^ n = -1 := by
    intro n
    cases c <;> simp [SmallBlock.sign, neg_one_pow_eq_or]
  refine ⟨s * ((r.factorial : ℚ) * a.factorial) * c.sign ^ (r * (r - 1) / 2 + r * a), ?_, ?_⟩
  · rcases hs with rfl | rfl <;> rcases hsgn (r * (r - 1) / 2 + r * a) with h | h <;>
      rw [h] <;> first | (left; ring1) | (right; ring1)
  intro lam hlam
  have hV : algebraMap (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
      (blockVandermonde 1 (r + a)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (blockVandermonde_ne_zero 1 (r + a))
  unfold dividedDifference
  rw [h3, antisymmetrize_C_mul, h2, KAlt.antisym_rename_mul_rename, map_smul]
  split_ifs with hcont
  · rw [hconc lam hcont, div_eq_iff hV, ← map_mul]
    congr 1
    have hA := h1 (Fin (r + a)) (Fin 1 × Fin (r + a)) c.sign (fun i => ((0 : Fin 1), i))
      (∑ i, (lam i - a)) (schur (Fin (r + a)) (fun i : Fin r => lam i - a))
      (h7 (Fin (r + a)) r (fun i : Fin r => lam i - a))
    have hsum : ∑ i, lam i = ∑ i, (lam i - a) + r * a := by
      rw [show r * a = ∑ _i : Fin r, a by simp, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (hcont i)).symm
    rw [hA, h6, map_mul, hsum, smul_eq_C_mul]
    simp only [map_mul, map_pow, map_natCast]
    ring
  · rw [h5 r a lam hlam hcont, map_zero, smul_zero, mul_zero, map_zero, zero_div]

end

end GroundTheory.Heights₂.Heights.RestTerms
end
