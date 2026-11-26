module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutionXFirstEmbedding

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MonomialMemPolKSg
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

theorem monomial_mem_PolK_sg {K : Type} [Field K] {L : Type} {r : ℕ} (d : L → ℕ) (α : L × Fin r →₀ ℕ)
    (c : K) (h : ∀ i, ldeg α i = d i) : monomial α c ∈ PolK K r d := by
  rw [mem_PolK_iff]
  intro β hβ
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hβ)]
  exact h

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def outSeg (i : D.ML) : Prop := ¬ ∃ k, D.e0 j k = i

instance : DecidablePred (D.outSeg j) := Classical.decPred _

def pullE (ζ : D.EM) : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ :=
  Finsupp.comapDomain (Prod.map (D.e0 j) id) ζ
    (((D.index_embedding_injective j).prodMap (Function.injective_id (α := Fin D.r))).injOn)

theorem pullE_apply (ζ : D.EM) (k : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.pullE j ζ (k, a) = ζ (D.e0 j k, a) := by
  exact Finsupp.comapDomain_apply _ _ _ _

theorem ldeg_pullE (ζ : D.EM) (k : Fin (D.nB j + D.r)) :
    ldeg (D.pullE j ζ) k = ldeg ζ (D.e0 j k) := by
  unfold ldeg
  simp only [pullE_apply]

theorem mapDomain_pullE (ζ : D.EM) :
    Finsupp.mapDomain (Prod.map (D.e0 j) id) (D.pullE j ζ) = eIn (D.outSeg j) ζ := by
  ext ⟨i, a⟩
  by_cases hi : ∃ k, D.e0 j k = i
  · obtain ⟨k, rfl⟩ := hi
    have hinj : Function.Injective (Prod.map (D.e0 j) (id : Fin D.r → Fin D.r)) :=
      (D.index_embedding_injective j).prodMap Function.injective_id
    have hout : ¬ D.outSeg j (D.e0 j k) := fun h => h ⟨k, rfl⟩
    exact (Finsupp.mapDomain_apply_of_injective hinj (D.pullE j ζ) (k, a)).trans
      ((D.pullE_apply j ζ k a).trans ((eIn_apply (out := D.outSeg j) ζ (D.e0 j k, a)).trans (if_neg hout)).symm)
  · have hout : D.outSeg j i := hi
    rw [Finsupp.mapDomain_notin_range]
    · exact ((eIn_apply (out := D.outSeg j) ζ (i, a)).trans (if_pos hout)).symm
    · rintro ⟨⟨k, b⟩, hkb⟩
      exact hi ⟨k, (Prod.mk.inj hkb).1⟩

theorem pullE_congr (ζ ζ' : D.EM) (h : ∀ k a, ζ (D.e0 j k, a) = ζ' (D.e0 j k, a)) :
    D.pullE j ζ = D.pullE j ζ' := by
  ext ⟨k, a⟩
  rw [pullE_apply, pullE_apply]
  exact h k a

theorem pullE_eIn (ζ : D.EM) : D.pullE j (eIn (D.outSeg j) ζ) = D.pullE j ζ := by
  apply D.pullE_congr j
  intro k a
  have hout : ¬ D.outSeg j (D.e0 j k) := fun h => h ⟨k, rfl⟩
  exact (eIn_apply (out := D.outSeg j) ζ (D.e0 j k, a)).trans (if_neg hout)

theorem pullE_deg (ζ : D.EM) (h : D.PreE j ζ) (k : Fin (D.nB j + D.r)) :
    ldeg (D.pullE j ζ) k = D.dO (D.eA j k) := by
  rw [ldeg_pullE]
  cases k using Fin.addCases with
  | left a =>
    have hseg : D.seg (D.eB j a) = j := (Finset.mem_filter.mp ((D.LLj j).equivFin.symm a).2).2
    rw [first_embedding_castAdd, h.1 _ hseg]
    simp only [eA, dO, Fin.addCases_left, Sum.elim_inl]
  | right m =>
    rw [first_embedding_natAdd, h.2.1]
    simp only [eA, dO, Fin.addCases_right, Sum.elim_inr]

variable {ι : Type} [Fintype ι]

def TT (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K) :
    MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun lam => ∑ b, cc lam b • PP b

def Th (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K) :
    MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun ζ => monomial (eOut (D.outSeg j) ζ) 1 * D.TT j cc PP (monomial (D.pullE j ζ) 1)

variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)

theorem TT_monomial (lam : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) :
    D.TT j cc PP (monomial lam 1) = ∑ b, cc lam b • PP b := by
  simp only [TT, lsup_monomial, one_smul]

theorem Th_monomial (ζ : D.EM) :
    D.Th j cc PP (monomial ζ 1) =
      monomial (eOut (D.outSeg j) ζ) 1 * ∑ b, cc (D.pullE j ζ) b • PP b := by
  simp only [Th, lsup_monomial, one_smul, TT_monomial]

theorem TT_expand (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hli : LinearIndependent K Ψ)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (Q : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hQ : Q ∈ PolK K D.r (fun k => D.dO (D.eA j k))) (a : ι → K) (ha : Q = ∑ b, a b • Ψ b) :
    D.TT j cc PP Q = ∑ b, a b • PP b := by
  classical
  have hQsupp : ∀ lam ∈ Q.support, ∀ k, ldeg lam k = D.dO (D.eA j k) := by
    intro lam hlam k
    exact (mem_PolK_iff _ Q).mp hQ lam hlam k
  set c : ι → K := fun b => ∑ lam ∈ Q.support, Q.coeff lam * cc lam b with hc
  have hT : D.TT j cc PP Q = ∑ b, c b • PP b := by
    simp only [TT, lsup_apply, Finset.smul_sum, smul_smul, hc, Finset.sum_smul]
    exact Finset.sum_comm
  have hQ' : Q = ∑ b, c b • Ψ b := by
    calc Q = ∑ lam ∈ Q.support, Q.coeff lam • monomial lam (1 : K) := by
            conv_lhs => rw [Q.as_sum]
            refine Finset.sum_congr rfl fun lam _ => ?_
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      _ = ∑ lam ∈ Q.support, Q.coeff lam • ∑ b, cc lam b • Ψ b := by
            refine Finset.sum_congr rfl fun lam hlam => ?_
            rw [hcc lam (hQsupp lam hlam)]
      _ = ∑ b, c b • Ψ b := by
            simp only [Finset.smul_sum, smul_smul, hc, Finset.sum_smul]
            exact Finset.sum_comm
  have hca : ∀ b, c b = a b := by
    have h0 : ∑ b, (c b - a b) • Ψ b = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hQ', ← ha, sub_self]
    intro b
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 b)
  rw [hT]
  exact Finset.sum_congr rfl fun b _ => by rw [hca b]

theorem Th_integral {v : AddValuation K (WithTop ℚ)}
    (hccint : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → ∀ b, 0 ≤ v (cc lam b))
    (hPP : ∀ b, Integral v (PP b)) (ζ : D.EM) (hζ : D.PreE j ζ) :
    Integral v (D.Th j cc PP (monomial ζ 1)) := by
  rw [Th_monomial]
  apply integral_mul' (integral_monomial' _ (by simp))
  apply integral_sum'
  intro b _
  exact integral_smul' (hccint _ (D.pullE_deg j ζ hζ) b) (hPP b)

theorem Th_ph (p : ℕ) (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (hPP : ∀ b, D.ph p (PP b) = rename (Prod.map (D.eA j) id) (Ψ b)) (ζ : D.EM) (hζ : D.PreE j ζ) :
    D.ph p (D.Th j cc PP (monomial ζ 1)) = D.ph p (monomial ζ 1) := by
  have hsum : (∑ b, cc (D.pullE j ζ) b • rename (Prod.map (D.eA j) id) (Ψ b)) =
      D.ph p (monomial (eIn (D.outSeg j) ζ) 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← D.mapDomain_pullE j ζ, ← MvPolynomial.rename_monomial, substitution_rename_first_embedding,
      hcc _ (D.pullE_deg j ζ hζ), map_sum]
    simp only [map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Th_monomial, map_mul, map_sum]
  simp only [map_smul, hPP]
  rw [hsum, ← map_mul, MvPolynomial.monomial_mul, one_mul, eOut_add_eIn]

theorem Th_supp (ζ ζ' : D.EM) (h : ζ' ∈ (D.Th j cc PP (monomial ζ 1)).support) :
    ∃ b, ∃ ξ ∈ (PP b).support, ζ' = eOut (D.outSeg j) ζ + ξ := by
  rw [Th_monomial, MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial_mul'] at h
  split_ifs at h with hle
  · rw [one_mul, MvPolynomial.coeff_sum] at h
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [MvPolynomial.coeff_smul, smul_eq_mul] at hb
    refine ⟨b, ζ' - eOut (D.outSeg j) ζ, ?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff]
      exact right_ne_zero_of_mul hb
    · exact (add_tsub_cancel_of_le hle).symm
  · exact absurd rfl h

theorem outSeg_of_not_segL (i : D.ML) (hi : ¬ D.SegL j i) : D.outSeg j i := by
  rintro ⟨k, rfl⟩
  apply hi
  unfold SegL
  cases k using Fin.addCases with
  | left a =>
    rw [first_embedding_castAdd]
    exact Or.inl ⟨D.eB j a, (Finset.mem_filter.mp ((D.LLj j).equivFin.symm a).2).2, rfl⟩
  | right m =>
    rw [first_embedding_natAdd]
    exact Or.inr (Or.inl ⟨Fin.rev m, rfl⟩)

theorem Th_post (hPP : ∀ b, ∀ ξ ∈ (PP b).support, D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0)
    (ζ : D.EM) (hζ : D.PreE j ζ) (ζ' : D.EM) (h : ζ' ∈ (D.Th j cc PP (monomial ζ 1)).support) :
    D.PostE j ζ' ∧ ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a) := by
  obtain ⟨b, ξ, hξ, rfl⟩ := D.Th_supp j cc PP ζ ζ' h
  obtain ⟨hpost, hzero⟩ := hPP b ξ hξ
  have hO : ∀ i, ¬ D.outSeg j i → ∀ a, eOut (D.outSeg j) ζ (i, a) = 0 := by
    intro i hi a
    exact (eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_neg hi)
  have hmb : ∀ c, D.seg c = j → ¬ D.outSeg j (D.mb c) := by
    intro c hc hout
    obtain ⟨a, rfl⟩ := eB_surj (D := D) (j := j) c hc
    exact hout ⟨Fin.castAdd D.r a, by rw [first_embedding_castAdd]⟩
  have hml : ∀ m, ¬ D.outSeg j (D.mlab (j, m)) := by
    intro m hout
    exact hout ⟨Fin.natAdd (D.nB j) (Fin.rev m), by rw [first_embedding_natAdd, Fin.rev_rev]⟩
  have hmt : ∀ m a, eOut (D.outSeg j) ζ (D.mtp (j, m), a) = 0 := by
    intro m a
    rw [eOut_apply]
    split_ifs
    · exact hζ.2.2 m a
    · rfl
  have hldeg : ∀ i, (∀ a, eOut (D.outSeg j) ζ (i, a) = 0) →
      ldeg (eOut (D.outSeg j) ζ + ξ) i = ldeg ξ i := by
    intro i hi
    simp only [ldeg, Finsupp.add_apply, hi, zero_add]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro c hc
    rw [hldeg _ (hO _ (hmb c hc))]
    exact hpost.1 c hc
  · intro m
    rw [hldeg _ (hO _ (hml m)), hldeg _ (hmt m)]
    exact hpost.2.1 m
  · intro m
    rw [hldeg _ (hmt m)]
    exact hpost.2.2.1 m
  · intro m hm a
    rw [Finsupp.add_apply, hmt m a, zero_add]
    exact hpost.2.2.2 m hm a
  · intro i hi a
    rw [Finsupp.add_apply, hzero i hi a, add_zero]
    exact (eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_pos (D.outSeg_of_not_segL j i hi))

theorem Th_away (hPP : ∀ b, ∀ ξ ∈ (PP b).support, ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0)
    (S : Finset D.ML) (hS : ∀ i ∈ S, ¬ D.SegL j i) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    valS D.msg S Z ≤ valS D.msg S (D.Th j cc PP Z) := by
  have hIn : ∀ α : D.EM, eIn (fun i => ¬ D.outSeg j i) α = eOut (D.outSeg j) α := by
    intro α
    ext x
    simp [eIn, eOut, Finsupp.filter_apply]
  have hOut : ∀ α : D.EM, eOut (fun i => ¬ D.outSeg j i) α = eIn (D.outSeg j) α := by
    intro α
    ext x
    simp [eIn, eOut, Finsupp.filter_apply]
  have hIn1 : ∀ α : D.EM,
      D.Th j cc PP (monomial (eIn (D.outSeg j) α) 1) = ∑ b, cc (D.pullE j α) b • PP b := by
    intro α
    rw [Th_monomial, eOut_eIn, pullE_eIn, ← C_apply, map_one, one_mul]
  refine valS_outside_linear (fun i => ¬ D.outSeg j i) D.msg S (D.Th j cc PP) ?_ ?_ ?_ Z
  · intro i hi h
    exact h (D.outSeg_of_not_segL j i (hS i hi))
  · intro α
    rw [hIn, hOut, hIn1, Th_monomial]
  · intro α
    rw [hOut, hIn1]
    apply valS_sum_le
    intro b _
    rw [smul_eq_C_mul]
    refine le_trans ?_ (valS_C_mul_le _ _ _ _)
    apply valS_nonneg_of_vecS
    intro ξ hξ i a hne hiS
    exact absurd (hPP b ξ hξ i (hS i hiS) a) hne

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

theorem coe_untopD_le (x : WithTop ℤ) : ((x.untopD 0 : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe n => exact le_rfl

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def pullL : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K :=
  lsup fun ζ => monomial (D.pullE j ζ) 1

theorem pullL_coefOut (μ : D.EM) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.pullL j (coefOut (D.outSeg j) μ Z) =
      ∑ α ∈ Z.support, if eOut (D.outSeg j) α = μ then monomial (D.pullE j α) (Z.coeff α) else 0 := by
  unfold coefOut
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [pullL, lsup_monomial, pullE_eIn, smul_monomial, smul_eq_mul, mul_one]
  · rw [map_zero]

theorem rename_pullL_coefOut (μ : D.EM) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    rename (Prod.map (D.e0 j) id) (D.pullL j (coefOut (D.outSeg j) μ Z)) = coefOut (D.outSeg j) μ Z := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pullL_coefOut, map_sum]
  unfold coefOut
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [rename_monomial, mapDomain_pullE]
  · rw [map_zero]

variable {ι : Type} [Fintype ι]
  (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)

theorem Th_eq (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.Th j cc PP Z = ∑ μ ∈ Z.support.image (eOut (D.outSeg j)),
      monomial μ 1 * D.TT j cc PP (D.pullL j (coefOut (D.outSeg j) μ Z)) := by
  have h : ∀ μ, D.TT j cc PP (D.pullL j (coefOut (D.outSeg j) μ Z)) =
      ∑ α ∈ Z.support, if eOut (D.outSeg j) α = μ then
        Z.coeff α • D.TT j cc PP (monomial (D.pullE j α) 1) else 0 := by
    intro μ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pullL_coefOut, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs
    · have : monomial (D.pullE j α) (Z.coeff α) = Z.coeff α • monomial (D.pullE j α) (1 : K) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, map_smul]
    · rw [map_zero]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm, Th, lsup_apply]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.sum_eq_single (eOut (D.outSeg j) α)]
  · rw [if_pos rfl, mul_smul_comm]
  · intro μ _ hμ
    rw [if_neg (Ne.symm hμ), mul_zero]
  · intro h2
    exact absurd (Finset.mem_image_of_mem _ hα) h2

theorem Th_val [NeZero D.r] {v : AddValuation K (WithTop ℚ)}
    (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (path : ι → Fin (D.nB j + D.r + 1) → Fin D.r → ℤ)
    (hli : LinearIndependent K Ψ)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (h7 : ∀ (th : Fin (D.nB j + D.r + 1) → ℤ) (F : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K),
      (F ∈ PolO v D.r (fun k => D.dO (D.eA j k)) ∧ ∀ i : Fin (D.nB j + D.r + 1),
        F ∈ Aset (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) (th i)) →
        ∃ c : ι → K, (∀ b, 0 ≤ v (c b)) ∧ (∀ b, c b ≠ 0 → ∀ i, th i ≤ path b i (lastIdx D.r)) ∧
          F = ∑ b, c b • Ψ b)
    (hPPval : ∀ b (m : Fin D.r) (i0 : Fin (D.nB j + D.r + 1)), i0.val = D.stg j m →
      ((path b i0 (lastIdx D.r) : ℤ) : WithTop ℤ) ≤ valS D.msg (D.YPset j m) (PP b))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZ : Integral v Z) (hpre : ∀ ζ ∈ Z.support, D.PreE j ζ)
    (m : Fin D.r) (θ : ℝ) (hθ : vala D.msg (D.TLset j m) θ Z) :
    vala D.msg (D.YPset j m) θ (D.Th j cc PP Z) := by
  rw [Th_eq]
  refine vala_sum _ _ fun μ hμ => ?_
  obtain ⟨α0, hα0, rfl⟩ := Finset.mem_image.mp hμ
  refine vala_mul_left_nonneg ?_ ?_
  · apply valS_nonneg_of_free
    intro α hα i hi a
    have h1 := support_monomial_subset hα
    rw [Finset.mem_singleton] at h1
    rw [h1, eOut_apply]
    simp only [YPset, Finset.mem_union, Finset.mem_image] at hi
    rcases hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩
    · rw [if_neg]
      exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))
    · split_ifs
      · exact (hpre α0 hα0).2.2 m' a
      · rfl
  · set Q := D.pullL j (coefOut (D.outSeg j) (eOut (D.outSeg j) α0) Z) with hQdef
    have hQK : Q ∈ PolK K D.r (fun k => D.dO (D.eA j k)) := by
      rw [hQdef, pullL_coefOut]
      refine Submodule.sum_mem _ fun α hα => ?_
      split_ifs
      · exact monomial_mem_PolK_sg _ _ _ (D.pullE_deg j α (hpre α hα))
      · exact Submodule.zero_mem _
    have hQint : Integral v Q := by
      rw [hQdef, pullL_coefOut]
      refine integral_sum' _ _ fun α _ => ?_
      split_ifs
      · exact integral_monomial' _ (hZ α)
      · exact integral_zero'
    have hout : ∀ i ∈ D.TLset j m, ¬ D.outSeg j i := by
      intro i hi
      simp only [TLset, Finset.mem_union, Finset.mem_image] at hi
      rcases hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩
      · exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))
      · exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inr ⟨m', rfl⟩))
    have hQval : ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤
        valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) (D.stg j m)) Q := by
      have h1 := valS_rename (D.e0 j) (D.index_embedding_injective j) D.msg (D.TLset j m) Q
      rw [hQdef, rename_pullL_coefOut, TL_preimage, ← hQdef] at h1
      rw [← h1]
      exact le_trans ((vala_iff _ _ _ _).mp hθ) (valS_coefOut_le (D.outSeg j) D.msg _ hout _ Z)
    have hlt : D.stg j m < D.nB j + D.r + 1 := by unfold stg; omega
    let i0 : Fin (D.nB j + D.r + 1) := ⟨D.stg j m, hlt⟩
    let th : Fin (D.nB j + D.r + 1) → ℤ := fun i =>
      if i = i0 then ⌈θ⌉ else (valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) Q).untopD 0
    have hmem : ∀ i : Fin (D.nB j + D.r + 1),
        Q ∈ Aset (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) (th i) := by
      intro i
      show ((th i : ℤ) : WithTop ℤ) ≤ _
      by_cases hi : i = i0
      · simp only [th, if_pos hi]
        rw [hi]
        exact hQval
      · simp only [th, if_neg hi]
        exact coe_untopD_le _
    obtain ⟨c, -, hc1, hc2⟩ := (h7 th Q) ⟨⟨hQK, hQint⟩, hmem⟩
    rw [D.TT_expand j cc PP Ψ hli hcc Q hQK c hc2]
    refine vala_sum _ _ fun b _ => ?_
    by_cases hcb : c b = 0
    · rw [hcb, zero_smul]; exact vala_zero θ
    · refine vala_smul _ ?_
      rw [vala_iff]
      have h2 := hc1 b hcb i0
      simp only [th, if_true] at h2
      exact le_trans (WithTop.coe_le_coe.mpr h2) (hPPval b m i0 rfl)

end TwistData

theorem segStep_of {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
    (hS : SPAN K v p) : SegStep K v p := by
  classical
  intro hD D hr _ j
  haveI : NeZero D.r := ⟨hr.ne'⟩
  obtain ⟨ι, hι, Ψ, path, ncol, col, cidx, hts, occ, h3, h4, h5, h7, h8, h10, h11,
    h14, h16, h17⟩ := hS hD (D.nB j + D.r) D.r (D.msg ∘ D.e0 j) (fun k => D.dO (D.eA j k))
  have hmon : ∀ lam : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ, (∀ k, ldeg lam k = D.dO (D.eA j k)) →
      monomial lam (1 : K) ∈ PolO v D.r (fun k => D.dO (D.eA j k)) := fun lam h =>
    ⟨monomial_mem_PolK_sg _ _ _ h, integral_monomial' _ (by simp)⟩
  let cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K := fun lam =>
    if h : monomial lam (1 : K) ∈ PolO v D.r (fun k => D.dO (D.eA j k)) then (h5 _ h).choose else 0
  have hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) →
      monomial lam (1 : K) = ∑ b, cc lam b • Ψ b := by
    intro lam h
    simp only [cc, dif_pos (hmon lam h)]
    exact (h5 _ (hmon lam h)).choose_spec.2
  have hccint : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → ∀ b, 0 ≤ v (cc lam b) := by
    intro lam h b
    simp only [cc, dif_pos (hmon lam h)]
    exact (h5 _ (hmon lam h)).choose_spec.1 b
  let PP : ι → MvPolynomial (D.ML × Fin D.r) K := fun b => D.PsiP j (col b) (occ b)
  have hPPint : ∀ b, Integral v (PP b) := fun b =>
    D.PsiP_integral j (col b) (occ b) (h8 b ▸ (h3 b).2)
  have hPPph : ∀ b, D.ph p (PP b) = rename (Prod.map (D.eA j) id) (Ψ b) := by
    intro b
    rw [h8 b]
    exact D.PsiP_ph j p (col b) (occ b)
  have hPPsupp : ∀ b, ∀ ξ ∈ (PP b).support,
      D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0 := fun b ξ hξ =>
    D.PsiP_support j (col b) (occ b) (h10 b) (h11 b) ξ hξ
  have hPPval : ∀ b (m : Fin D.r) (i0 : Fin (D.nB j + D.r + 1)), i0.val = D.stg j m →
      ((path b i0 (lastIdx D.r) : ℤ) : WithTop ℤ) ≤ valS D.msg (D.YPset j m) (PP b) := by
    intro b m i0 hi0
    rw [h17 b i0]
    refine D.PsiP_val j (col b) (occ b) (h10 b) (cidx b) (fun k => hts b k i0) m ?_ ?_
    · intro k hk
      have := h14 b k i0 hk
      rwa [hi0] at this
    · intro k
      have := h16 b k i0
      rwa [hi0] at this
  refine ⟨D.Th j cc PP, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ζ hζ => D.Th_integral j cc PP hccint hPPint ζ hζ
  · exact fun ζ hζ => D.Th_ph j cc PP p Ψ hcc hPPph ζ hζ
  · exact fun ζ hζ ζ' hζ' => D.Th_post j cc PP hPPsupp ζ hζ ζ' hζ'
  · exact fun Z hZ hpre m θ _ hθ => D.Th_val j cc PP Ψ path h4 hcc h7 hPPval Z hZ hpre m θ hθ
  · exact fun S hS' Z => D.Th_away j cc PP (fun b ξ hξ => (hPPsupp b ξ hξ).2) S hS' Z

end Formalism.MainNotions.PlaneGram
