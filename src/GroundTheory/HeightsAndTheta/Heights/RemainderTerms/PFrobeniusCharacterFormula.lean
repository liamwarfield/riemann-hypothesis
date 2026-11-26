module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFrobeniusCharacterFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem vandermondeOf_X_fin_ne_zero (r : ℕ) :
    vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) ≠ 0 := by
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
  refine sub_ne_zero.mpr fun h => hij ?_
  exact X_injective (R := ℚ) h

theorem vandermondeOf_X_isHomogeneous (r : ℕ) :
    (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))).IsHomogeneous
      (r * (r - 1) / 2) := by
  have h := IsHomogeneous.prod (σ := Fin r) (R := ℚ) Finset.univ
    (fun i : Fin r => ∏ j ∈ Finset.Ioi i, ((X i : MvPolynomial (Fin r) ℚ) - X j))
    (fun i => ∑ _j ∈ Finset.Ioi i, 1)
    (fun i _ => IsHomogeneous.prod _ _ _ fun j _ =>
      (isHomogeneous_X ℚ i).sub (isHomogeneous_X ℚ j))
  have hdeg : ∑ i : Fin r, ∑ _j ∈ Finset.Ioi i, (1 : ℕ) = r * (r - 1) / 2 := by
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, ← Finset.sum_range_id]
    exact Finset.sum_range_reflect (fun i => i) r
  rw [hdeg] at h
  exact h

theorem psum_isHomogeneous (σ : Type*) [Fintype σ] (q : ℕ) :
    (psum σ ℚ q).IsHomogeneous q := by
  unfold psum
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i q

theorem FrobeniusCharacterFormula.proof (h1 : SchAltPartitionExpansion.Statement) :
    FrobeniusCharacterFormula.Statement := by
  intro r q m _hq
  set V := vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) with hVdef
  set S := psum (Fin r) ℚ q * psum (Fin r) ℚ 1 ^ m with hSdef
  have hprod : ((q :: List.replicate m 1).map fun k => psum (Fin r) ℚ k).prod = S := by
    simp [S, List.map_replicate, List.prod_replicate]
  have halt : Comb.IsAlt (V * S) := by
    have := Comb.isAlt_vandermonde_mul_prod (m := r) (q :: List.replicate m 1)
    rwa [hprod] at this
  have hhom : (V * S).IsHomogeneous (r * (r - 1) / 2 + (q + m)) := by
    have h := (vandermondeOf_X_isHomogeneous r).mul
      ((psum_isHomogeneous (Fin r) q).mul ((psum_isHomogeneous (Fin r) 1).pow m))
    rwa [one_mul] at h
  have hexp := h1 r (q + m) (V * S) halt hhom
  apply mul_left_cancel₀ (vandermondeOf_X_fin_ne_zero r)
  rw [Finset.mul_sum]
  refine hexp.trans (Finset.sum_congr rfl fun lam _ => ?_)
  simp only [symmetricGroupCharacter, hprod]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagSwapDivisible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagSwapDivisible.dvd_sub_substitute {R σ : Type} [CommRing R] [DecidableEq σ] (a b : σ)
    (Q : MvPolynomial σ R) :
    (X a - X b : MvPolynomial σ R) ∣
      Q - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p k hp =>
    rw [map_mul, aeval_X]
    have hk : (X a - X b : MvPolynomial σ R) ∣
        X k - (if k = a then (X b : MvPolynomial σ R) else X k) := by
      split_ifs with h
      · subst h; exact dvd_rfl
      · simp
    have e : p * X k - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
          (if k = a then (X b : MvPolynomial σ R) else X k) =
        (p - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p) * X k +
          aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
            (X k - (if k = a then (X b : MvPolynomial σ R) else X k)) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)

theorem FlagSwapDivisible.proof : FlagSwapDivisible.Statement := by
  intro σ _ P a b hab hP
  set g : σ → MvPolynomial σ ℚ := fun v => if v = a then X b else X v with hg
  have hswap : g ∘ Equiv.swap a b = g := by
    funext v
    simp only [Function.comp_apply, hg]
    rcases eq_or_ne v a with rfl | hva
    · simp [Equiv.swap_apply_left, hab.symm]
    · rcases eq_or_ne v b with rfl | hvb
      · simp [Equiv.swap_apply_right, hva]
      · simp [Equiv.swap_apply_of_ne_of_ne hva hvb, hva]
  have hzero : aeval g P = 0 := by
    have h1 : aeval g P = -aeval g P := by
      calc aeval g P = aeval (g ∘ Equiv.swap a b) P := by rw [hswap]
        _ = aeval g (rename (Equiv.swap a b) P) := (aeval_rename _ _ _).symm
        _ = -aeval g P := by rw [hP, map_neg]
    have h2 : aeval g P + aeval g P = 0 := by
      nth_rewrite 2 [h1]; exact add_neg_cancel _
    have h3 : (2 : MvPolynomial σ ℚ) * aeval g P = 0 := by rw [two_mul]; exact h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hd := FlagSwapDivisible.dvd_sub_substitute a b P
  rw [← hg, hzero, sub_zero] at hd
  exact hd

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAltTopDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem FlagAltTopDegree.proof (h1 : FlagCoeffBlockPermute.Statement)
    (h2 : FlagAltCoeffInjective.Statement) (h3 : FlagInjSumBound.Statement)
    (h4 : FlagStaircaseOrbit.Statement) (h5 : FlagVandermondeHomogeneous.Statement) :
    FlagAltTopDegree.Statement := by
  intro f N P hP hhom

  have key : ∀ (R : RootRing f N) (β : Fin f × Fin N →₀ ℕ), IsBlockAlternating f N R →
      R.IsHomogeneous (topDegree f N) → AddMonoidAlgebra.coeff R β ≠ 0 →
      (∀ τ, Function.Injective fun i : Fin N => β (τ, i)) ∧ ∀ τ i, β (τ, i) < N := by
    intro R β hR hRh hβ
    have hinj := h2 f N R β hR hβ
    refine ⟨hinj, ?_⟩
    have hdeg : β.degree = topDegree f N := by
      by_contra hne; exact hβ (hRh.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, topDegree] at hdeg
    set K := N * (N - 1) / 2
    have hge : ∀ τ, K ≤ ∑ i, β (τ, i) := fun τ => (h3 N _ (hinj τ)).1
    have hsplit : ∑ τ : Fin f, ∑ i, β (τ, i) =
        ∑ _τ : Fin f, K + ∑ τ : Fin f, (∑ i, β (τ, i) - K) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => (Nat.add_sub_of_le (hge τ)).symm
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hdeg] at hsplit
    have hz : ∑ τ : Fin f, (∑ i, β (τ, i) - K) = 0 := by omega
    intro τ i
    have hτ := (Finset.sum_eq_zero_iff.mp hz) τ (Finset.mem_univ _)
    exact (h3 N _ (hinj τ)).2 (le_antisymm (by omega) (hge τ)) i
  have hΔ := isBlockAlternating_blockVandermonde f N
  obtain ⟨α₁, hα₁⟩ := MvPolynomial.ne_zero_iff.mp (Flag.blockVandermonde_ne_zero f N)
  set e : ℚ := AddMonoidAlgebra.coeff P α₁ / AddMonoidAlgebra.coeff (blockVandermonde f N) α₁
  set Q := P - C e * blockVandermonde f N with hQ
  have hQalt : IsBlockAlternating f N Q := by
    intro w
    simp only [hQ, map_sub, map_mul, algHom_C, hP w, hΔ w, smul_sub, mul_smul_comm,
      MvPolynomial.algebraMap_eq]
  have hQhom : Q.IsHomogeneous (topDegree f N) := hhom.sub ((h5 f N).C_mul e)
  have hQα₁ : AddMonoidAlgebra.coeff Q α₁ = 0 := by
    simp only [hQ, coeff_sub, coeff_C_mul, e]
    field_simp
    ring
  have hQ0 : Q = 0 := by
    by_contra hne
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hne
    obtain ⟨hinjα, hltα⟩ := key Q α hQalt hQhom hα
    obtain ⟨hinj₁, hlt₁⟩ := key _ α₁ hΔ (h5 f N) hα₁
    obtain ⟨w, hw⟩ := h4 f N α α₁ hltα hlt₁ hinjα hinj₁
    have hα₁eq : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α₁ := by
      ext p; simp [hw]
    have hc := h1 f N w Q α
    rw [hα₁eq, hQα₁, hQalt w, coeff_smul, smul_eq_mul] at hc
    have hs : blockSign f N w ≠ 0 := by
      intro h0; have := Flag.blockSign_mul_self f N w; rw [h0, zero_mul] at this; exact zero_ne_one this
    exact hα ((mul_eq_zero.mp hc).resolve_left hs)
  exact ⟨e, sub_eq_zero.mp hQ0⟩

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDiffPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

namespace FlagDiffPrime

variable {σ : Type} [DecidableEq σ]

def collapse (a b : σ) : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
  aeval fun i => if i = a then X b else X i

theorem collapse_X_sub (a b : σ) : collapse a b (X a - X b : MvPolynomial σ ℚ) = 0 := by
  simp [collapse]

theorem dvd_sub_collapse (a b : σ) (Q : MvPolynomial σ ℚ) :
    (X a - X b : MvPolynomial σ ℚ) ∣ Q - collapse a b Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [collapse]
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul]
    have e : p * X i - collapse a b p * collapse a b (X i) =
        (p - collapse a b p) * X i + collapse a b p * (X i - collapse a b (X i)) := by ring
    rw [e]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    by_cases h : i = a
    · rw [h]; simp [collapse]
    · simp [collapse, h]

theorem collapse_eq_zero_of_dvd (a b : σ) {P : MvPolynomial σ ℚ}
    (h : (X a - X b : MvPolynomial σ ℚ) ∣ P) : collapse a b P = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, collapse_X_sub, zero_mul]

theorem dvd_of_collapse_eq_zero (a b : σ) {P : MvPolynomial σ ℚ}
    (h : collapse a b P = 0) : (X a - X b : MvPolynomial σ ℚ) ∣ P := by
  simpa [h] using dvd_sub_collapse a b P

theorem proof : FlagDiffPrime.Statement := by
  intro σ _ a b hab
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_ne_zero]
    exact fun h => hab (X_injective h)
  · intro hu
    have hu' := hu.map (collapse a b)
    rw [collapse_X_sub] at hu'
    exact not_isUnit_zero hu'
  · intro A B h
    have h0 := collapse_eq_zero_of_dvd a b h
    rw [map_mul, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Or.inl (dvd_of_collapse_eq_zero a b h0)
    · exact Or.inr (dvd_of_collapse_eq_zero a b h0)

end FlagDiffPrime

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchEvalPowerSumHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchEvalPowerSumHom.eq_single_of_dvd {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (e : Fin N →₀ ℕ) (hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = k)
    (hd : ∀ i ∈ e.support, k ∣ (i : ℕ) + 1) :
    e = Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1 := by
  have hsum : ∑ i ∈ e.support, e i * ((i : ℕ) + 1) = k := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] at hw
    exact hw
  obtain ⟨j, hj⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hsum
    omega
  have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hjk : k ≤ (j : ℕ) + 1 := Nat.le_of_dvd (by omega) (hd j hj)
  rw [← Finset.add_sum_erase _ _ hj] at hsum
  have hmul : k ≤ e j * ((j : ℕ) + 1) := le_trans hjk (Nat.le_mul_of_pos_left _ hej)
  have hrest : ∑ i ∈ e.support.erase j, e i * ((i : ℕ) + 1) = 0 := by omega
  have hjm : e j * ((j : ℕ) + 1) = k := by omega
  have hej1 : e j = 1 := by nlinarith
  have hjv : j = (⟨k - 1, by omega⟩ : Fin N) := by
    rw [hej1, one_mul] at hjm
    exact Fin.ext (by simp; omega)
  have hother : ∀ i, i ≠ j → e i = 0 := by
    intro i hij
    by_contra hne
    have hi : i ∈ e.support.erase j :=
      Finset.mem_erase.mpr ⟨hij, Finsupp.mem_support_iff.mpr hne⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hrest) i hi
    rw [Nat.mul_eq_zero] at h0
    omega
  ext i
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [← h, ← hjv, hej1]
  · exact hother i (fun hij => h (hjv.symm.trans hij.symm))

theorem SchEvalPowerSumHom.proof (h1 : SchPowerSumAtRootsOfUnity.Statement) :
    SchEvalPowerSumHom.Statement := by
  intro N k hk1 hkN S hS
  have hzv : ∀ i : Fin N, aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1)) =
      if k ∣ (i : ℕ) + 1 then (k : ℂ) else 0 := fun i =>
    h1 N k ((i : ℕ) + 1) hk1 hkN (by omega)
  have hcomp : aeval (rootOfUnityPoint N k) (powerSumHom N S) =
      aeval (fun i : Fin N => aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1))) S := by
    rw [powerSumHom, ← AlgHom.comp_apply, comp_aeval]
  rw [hcomp]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [S.as_sum, map_sum]
  rw [Finset.sum_eq_single (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1)]
  · have hdvd : k ∣ ((⟨k - 1, by omega⟩ : Fin N) : ℕ) + 1 := by
      simp only [Nat.sub_add_cancel hk1, dvd_refl]
    rw [aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, hzv, if_pos hdvd]
    simp [mul_comm]
  · intro e he hne
    rw [aeval_monomial]
    have hw := hS (MvPolynomial.mem_support_iff.mp he)
    obtain ⟨i, hi, hik⟩ : ∃ i ∈ e.support, ¬ k ∣ (i : ℕ) + 1 := by
      by_contra hcon
      push Not at hcon
      exact hne (SchEvalPowerSumHom.eq_single_of_dvd hk1 hkN e hw hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    rw [hzv, if_neg hik, zero_pow (Finsupp.mem_support_iff.mp hi)]
  · intro h
    rw [MvPolynomial.notMem_support_iff.mp h, monomial_zero, map_zero]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAltPartitionExpansion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchAltPartitionExpansion.alt_partition_add_stair_eq {r : ℕ} (lam : Fin r → ℕ) :
    Comb.alt (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) =
      vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam := by
  unfold Comb.alt
  rw [← Matrix.det_transpose, mul_comm]
  exact Schur.det_pow_add_staircase_eq lam

theorem SchAltPartitionExpansion.strictAnti_partition_add_stair {r n : ℕ} {lam : Fin r → ℕ} (hlam : lam ∈ partitionsOf r n) :
    StrictAnti (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) := by
  unfold partitionsOf at hlam
  rw [Finset.mem_filter] at hlam
  intro i j hij
  have h1 := hlam.2 i j hij.le
  have hj := j.isLt
  have hij' : (i : ℕ) < j := hij
  simp only
  omega

theorem SchAltPartitionExpansion.proof (h1 : SchStrictAntiSplit.Statement) :
    SchAltPartitionExpansion.Statement := by
  intro r n P hP hhom
  set e : (Fin r → ℕ) → (Fin r →₀ ℕ) := fun lam =>
    Finsupp.equivFunOnFinite.symm fun i : Fin r => lam i + (r - 1 - (i : ℕ)) with he
  have e_inj : Set.InjOn e (partitionsOf r n : Set (Fin r → ℕ)) := by
    intro a _ b _ hab
    funext i
    have := congrArg (fun f : Fin r →₀ ℕ => f i) hab
    simp only [he, Finsupp.coe_equivFunOnFinite_symm] at this
    omega

  have hR : ∑ lam ∈ partitionsOf r n,
      C (AddMonoidAlgebra.coeff P (e lam)) *
        (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam) =
      ∑ d ∈ (partitionsOf r n).image e, AddMonoidAlgebra.coeff P d • Comb.alt (⇑d) := by
    rw [Finset.sum_image e_inj]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [C_mul', ← SchAltPartitionExpansion.alt_partition_add_stair_eq]
    simp [he]
  rw [hR]
  conv_lhs => rw [Comb.IsAlt.eq_sum_alt hP]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hsum : ∑ i, d i = r * (r - 1) / 2 + n := by
      have := hhom (mem_support_iff.mp hd.1)
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
      exact this
    obtain ⟨hge, hmem⟩ := h1 r n (⇑d) hd.2 hsum
    refine Finset.mem_image.mpr ⟨_, hmem, ?_⟩
    ext i
    simp only [he, Finsupp.coe_equivFunOnFinite_symm]
    have := hge i
    omega
  · intro d hd hnot
    obtain ⟨lam, hlam, rfl⟩ := Finset.mem_image.mp hd
    have hz : AddMonoidAlgebra.coeff P (e lam) = 0 := by
      by_contra hne
      apply hnot
      rw [Finset.mem_filter]
      refine ⟨mem_support_iff.mpr hne, ?_⟩
      simpa [he] using SchAltPartitionExpansion.strictAnti_partition_add_stair hlam
    rw [hz, zero_smul]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatExponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

noncomputable section

def SchConcatExponent.rotateFun (r a : ℕ) (p : Fin (r + a)) : Fin (r + a) :=
  if h : (p : ℕ) < a then ⟨r + p, by omega⟩ else ⟨p - a, by have := p.isLt; omega⟩

def SchConcatExponent.rotateInv (r a : ℕ) (q : Fin (r + a)) : Fin (r + a) :=
  if h : (q : ℕ) < r then ⟨q + a, by omega⟩ else ⟨q - r, by have := q.isLt; omega⟩

theorem SchConcatExponent.rotateFun_val (r a : ℕ) (p : Fin (r + a)) :
    (SchConcatExponent.rotateFun r a p : ℕ) = if (p : ℕ) < a then r + p else p - a := by
  unfold SchConcatExponent.rotateFun; split <;> rfl

theorem SchConcatExponent.rotateInv_val (r a : ℕ) (q : Fin (r + a)) :
    (SchConcatExponent.rotateInv r a q : ℕ) = if (q : ℕ) < r then q + a else q - r := by
  unfold SchConcatExponent.rotateInv; split <;> rfl

def SchConcatExponent.rotate (r a : ℕ) : Equiv.Perm (Fin (r + a)) where
  toFun := SchConcatExponent.rotateFun r a
  invFun := SchConcatExponent.rotateInv r a
  left_inv p := by
    have hp := p.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateInv_val, SchConcatExponent.rotateFun_val]
    split_ifs <;> omega
  right_inv q := by
    have hq := q.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateFun_val, SchConcatExponent.rotateInv_val]
    split_ifs <;> omega

theorem SchConcatExponent.proof : SchConcatExponent.Statement := by
  intro r a c
  cases c with
  | first =>
    refine ⟨Equiv.refl _, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    by_cases h : (p : ℕ) < r
    · have := hlam ⟨p, h⟩
      simp [smallBlockOf, Schur.padPartition, h]
      omega
    · simp [smallBlockOf, Schur.padPartition, h]
      omega
  | last =>
    refine ⟨SchConcatExponent.rotate r a, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    simp only [Function.comp_apply]
    generalize hq : SchConcatExponent.rotate r a p = q
    have hv : (q : ℕ) = if (p : ℕ) < a then r + p else p - a := by
      rw [← hq]; exact SchConcatExponent.rotateFun_val r a p
    simp only [Schur.padPartition, smallBlockOf]
    by_cases h : (p : ℕ) < a
    · have hn : ¬ ((q : ℕ) < r) := by rw [hv, if_pos h]; omega
      rw [dite_eq_left h, dite_eq_right hn]
      simp only [Sum.elim_inr]
      rw [hv, if_pos h]
      omega
    · have h' : (p : ℕ) - a < r := by omega
      have hn : (q : ℕ) < r := by rw [hv, if_neg h]; exact h'
      rw [dite_eq_right h, dite_eq_left hn]
      simp only [Sum.elim_inl]
      have hqe : (⟨q, hn⟩ : Fin r) = ⟨(p : ℕ) - a, h'⟩ := Fin.ext (by rw [hv, if_neg h])
      rw [hqe, hv, if_neg h]
      have := hlam ⟨(p : ℕ) - a, h'⟩
      omega

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeDvd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

namespace FlagVandermondeDvd

theorem blockVandermonde_eq_prod (f N : ℕ) :
    blockVandermonde f N =
      ∏ t ∈ (univ : Finset (Fin f × Fin N × Fin N)).filter (fun t => t.2.1 < t.2.2),
        ((X (t.1, t.2.1) - X (t.1, t.2.2) : RootRing f N)) := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [blockVandermonde, vandermondeOf]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have : Finset.Ioi i = (univ : Finset (Fin N)).filter (fun j => i < j) := by ext; simp
  rw [this, Finset.prod_filter]

theorem rename_swap_eq (f N : ℕ) (τ : Fin f) (i j : Fin N) :
    (rename (Equiv.swap (τ, i) (τ, j)) : RootRing f N →ₐ[ℚ] RootRing f N) =
      blockPermute f N (Function.update 1 τ (Equiv.swap i j)) := by
  unfold blockPermute
  congr 1
  funext p
  obtain ⟨σ, k⟩ := p
  by_cases hσ : σ = τ
  · subst hσ
    simp only [Function.update_self, Equiv.swap_apply_def, Prod.mk.injEq, true_and]
    split_ifs <;> rfl
  · simp only [Function.update_of_ne hσ, Pi.one_apply, Equiv.Perm.coe_one, id]
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [hσ]

theorem blockSign_update_swap (f N : ℕ) (τ : Fin f) (i j : Fin N) (hij : i ≠ j) :
    blockSign f N (Function.update 1 τ (Equiv.swap i j)) = -1 := by
  unfold blockSign
  rw [Fintype.prod_eq_single τ]
  · simp [Equiv.Perm.sign_swap hij]
  · intro σ hσ
    simp [Function.update_of_ne hσ]

end FlagVandermondeDvd


open FlagVandermondeDvd in
theorem FlagVandermondeDvd.proof (h1 : FlagSwapDivisible.Statement) (h2 : FlagDiffPrime.Statement)
    (h3 : FlagDiffNotDvd.Statement) (h4 : FlagProdPrimesDvd.Statement) :
    FlagVandermondeDvd.Statement := by
  intro f N P hP
  rw [blockVandermonde_eq_prod]
  refine h4 (RootRing f N) (Fin f × Fin N × Fin N) _ _ P ?_ ?_ ?_
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact h2 _ _ _ (by simp [ht.ne])
  · rintro ⟨τ, i, j⟩ ht ⟨τ', i', j'⟩ ht' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    refine h3 _ _ _ _ _ (by simp [ht.ne]) (by simp [ht'.ne]) ?_ ?_
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      exact hne (by rw [ha.1, ha.2, hb.2])
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      rw [ha.2, hb.2] at ht
      exact absurd (ht.trans ht') (lt_irrefl _)
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    refine h1 _ P _ _ (by simp [ht.ne]) ?_
    rw [rename_swap_eq, hP, blockSign_update_swap f N τ i j ht.ne, neg_one_smul]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestBoundOfPrimeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset Elem

noncomputable section

theorem RestBoundOfPrimeBound.proof : RestBoundOfPrimeBound.Statement := by
  classical
  intro f r a c B₀ hf hr ha hB Q s e hp P
  set R : ℕ → ℝ := fun p => restPrimeModel f r a c Q s e p with hR
  set C : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hC
  set X : ℝ := (restX r a : ℝ) with hXdef
  have hN2 : 2 ≤ r + a := by omega
  have hNR : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN2
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hB0 : 0 < B₀ := by nlinarith
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ X := by
    simp only [hXdef, restX]; push_cast; positivity
  set K : ℝ := 1.5 * f * X * C with hK
  have hK0 : 0 ≤ K := by positivity
  set S : Set ℕ := {p | p ∈ P ∧ p.Prime ∧ B₀ < p} with hS
  set g : ℕ → ℝ := fun i => if i ∈ P ∧ i.Prime ∧ B₀ < i then |R i| else 0 with hg
  have hind : S.indicator (fun p => |R p|) = g := by
    funext i
    by_cases h : i ∈ P ∧ i.Prime ∧ B₀ < i
    · simp [hS, hg, Set.indicator_of_mem, h]
    · rw [Set.indicator_of_notMem (show i ∉ S from h)]
      simp [hg, h]
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    simp only [hg]; split_ifs <;> positivity
  have hgle : ∀ i, g i ≤ K * (primeWeight B₀ i / (i : ℝ) ^ 2) := fun i => by
    simp only [hg]
    split_ifs with h
    · have hw : primeWeight B₀ i = Real.log i := by simp [primeWeight, h.2.1, h.2.2]
      rw [hw]
      calc |R i| ≤ 1.5 * f * X * (Real.log i / (i : ℝ) ^ 2) * ((f * (r * a) + 1 : ℕ) : ℝ) *
            |(fibreDegree f r a c : ℝ)| := hp i h.2.1 h.2.2
        _ = K * (Real.log i / (i : ℝ) ^ 2) := by rw [hK, hC]; ring
    · exact mul_nonneg hK0 (div_nonneg (primeWeight_nonneg B₀ i) (by positivity))
  have hpart : ∀ n, ∑ i ∈ range n, g i ≤ K * (2 * Real.log 4 / B₀) := fun n => by
    calc ∑ i ∈ range n, g i ≤ ∑ i ∈ range n, K * (primeWeight B₀ i / (i : ℝ) ^ 2) :=
          Finset.sum_le_sum fun i _ => hgle i
      _ = K * ∑ i ∈ range n, primeWeight B₀ i / (i : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ K * (2 * Real.log 4 / B₀) :=
          mul_le_mul_of_nonneg_left (prime_partial_le B₀ hB0 n) hK0
  have hgs : Summable g := summable_of_sum_range_le hg0 hpart
  have hsub : Summable (fun p : S => |R p|) :=
    (summable_subtype_iff_indicator (f := fun p : ℕ => |R p|) (s := S)).mpr (by rw [hind]; exact hgs)
  refine ⟨hsub, ?_⟩
  have htsum : ∑' p : S, |R p| ≤ K * (2 * Real.log 4 / B₀) := by
    rw [tsum_subtype S (fun p : ℕ => |R p|), hind]
    exact Real.tsum_le_of_sum_range_le hg0 hpart
  have habs : |∑' p : S, R p| ≤ ∑' p : S, |R p| := by
    have := norm_tsum_le_tsum_norm (f := fun p : S => R p)
      (by simpa [Real.norm_eq_abs] using hsub)
    simpa [Real.norm_eq_abs] using this

  have hXle : X ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := by
    have h := XBound.intersectionNumber_baseChange r a hN2
    simp only [hXdef] at h ⊢
    linarith [h.1, h.2]
  have hNpos : (0 : ℝ) < ((r + a : ℕ) : ℝ) := by linarith
  have hD : (0 : ℝ) < 4 * f * ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hlog : 2 * Real.log 4 / B₀ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) := by
    calc 2 * Real.log 4 / B₀ ≤ 2.78 / B₀ :=
          div_le_div_of_nonneg_right two_log_four_le hB0.le
      _ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) hD hB
  have hconst := RestConstants.intersectionNumber_baseChange.2 f (r + a) hf hN2
  have hfin : K * (2 * Real.log 4 / B₀) ≤ 1.6 * C := by
    have hl0 : 0 ≤ 2 * Real.log 4 / B₀ :=
      div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) hB0.le
    calc K * (2 * Real.log 4 / B₀)
        = (1.5 * f * X) * (2 * Real.log 4 / B₀) * C := by rw [hK]; ring
      _ ≤ (1.5 * f * (3 / 2 * ((r + a : ℕ) : ℝ) ^ 2)) * (2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2)) * C := by
          apply mul_le_mul_of_nonneg_right _ hC0
          apply mul_le_mul _ hlog hl0 (by positivity)
          exact mul_le_mul_of_nonneg_left hXle (by positivity)
      _ ≤ 1.6 * C := mul_le_mul_of_nonneg_right hconst hC0
  calc |∑' p : S, R p| ≤ ∑' p : S, |R p| := habs
    _ ≤ K * (2 * Real.log 4 / B₀) := htsum
    _ ≤ 1.6 * C := hfin
    _ = 1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by rw [hC]; ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchHookResidues
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchHookResidues.proof : SchHookResidues.Statement := by
  intro k nu hk hanti hsum hhook
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set s := univ.filter fun i : Fin (n + 1) => (i : ℕ) ≠ 0 ∧ nu i = 1 with hs
  set t := s.card with ht
  have down : ∀ i j : Fin (n + 1), (i : ℕ) ≠ 0 → i ≤ j → j ∈ s → i ∈ s := by
    intro i j hi hij hj
    simp only [hs, mem_filter, mem_univ, true_and] at hj ⊢
    have h1 := hanti hij
    have h2 := hhook i hi
    exact ⟨hi, by omega⟩
  have hA : ∀ j ∈ s, (j : ℕ) ≤ t := by
    intro j hj
    have hsub : Finset.Icc 1 (j : ℕ) ⊆ s.map Fin.valEmbedding := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_map]
      refine ⟨⟨m, by omega⟩, down _ j (show m ≠ 0 by omega)
        (by rw [Fin.le_iff_val_le_val]; show m ≤ (j : ℕ); omega) hj, rfl⟩
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hB : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → (i : ℕ) ≤ t → i ∈ s := by
    intro i hi hit
    by_contra hni
    have hsub : s.map Fin.valEmbedding ⊆ Finset.Ico 1 (i : ℕ) := by
      intro m hm
      rw [Finset.mem_map] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      have hj' := hj
      simp only [hs, mem_filter, mem_univ, true_and] at hj'
      rw [Finset.mem_Ico]
      refine ⟨by simp only [Fin.valEmbedding_apply]; omega, ?_⟩
      by_contra hle
      exact hni (down i j hi (by rw [Fin.le_iff_val_le_val]; simp at hle; omega) hj)
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hval : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → nu i = if (i : ℕ) ≤ t then 1 else 0 := by
    intro i hi
    have h1 := hhook i hi
    split_ifs with h
    · have := hB i hi h
      simp only [hs, mem_filter, mem_univ, true_and] at this
      exact this.2
    · have : nu i ≠ 1 := by
        intro h1'
        have := hA i (by simp only [hs, mem_filter, mem_univ, true_and]; exact ⟨hi, h1'⟩)
        omega
      omega
  have htn : t ≤ n := by
    have hsub : s ⊆ univ.erase 0 := by
      intro i hi
      simp only [hs, mem_filter, mem_univ, true_and] at hi
      exact Finset.mem_erase.mpr ⟨fun h => hi.1 (by simp [h]), mem_univ _⟩
    have := card_le_card hsub
    simpa [card_erase_of_mem] using this
  have hnu0 : nu 0 + t = n + 1 := by
    have hpt : ∀ i, nu i = (if i = 0 then nu 0 else 0) +
        (if (i : ℕ) ≠ 0 ∧ nu i = 1 then 1 else 0) := by
      intro i
      by_cases h0 : i = 0
      · subst h0; simp
      · have hi : (i : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by simp [h]))
        have := hhook i hi
        rw [if_neg h0, zero_add]
        split_ifs with h <;> omega
    have hsum2 : ∑ i, nu i = nu 0 + t := by
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_boole]
      simp [t, s]
    omega
  refine ⟨(Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)))⁻¹, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := (Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1))).surjective i
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rcases lt_trichotomy (j : ℕ) t with h | h | h
    · have hlt : j < (⟨t, by omega⟩ : Fin (n + 1)) := Fin.lt_def.mpr h
      have hv : ((Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)) j : Fin (n + 1)) : ℕ) = j + 1 :=
        Fin.coe_cycleRange_of_lt hlt
      rw [hval _ (by rw [hv]; omega), hv, if_pos (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Fin.cycleRange_of_eq (Fin.ext h), Fin.val_zero]
      have h2 : nu 0 + (n + 1 - 1 - 0) = (n - t) + (n + 1) := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hgt : (⟨t, by omega⟩ : Fin (n + 1)) < j := Fin.lt_def.mpr h
      rw [Fin.cycleRange_of_gt hgt, hval j (by omega), if_neg (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [Equiv.Perm.sign_inv, Fin.sign_cycleRange]
    simp [t, s]

end GroundTheory.Heights₂.Heights.RestTerms
end
