module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.RestValBdG

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.HomCompRename
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Comp

variable {R : Type} [CommRing R] {ι κ : Type} {n : ℕ}

theorem coeff_homComp (δ : ι → ℕ) (F : MvPolynomial (ι × Fin n) R) (a : ι × Fin n →₀ ℕ) :
    (homComp δ F).coeff a = if (∀ i, multideg a i = δ i) then F.coeff a else 0 := by
  classical
  unfold homComp
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_support_iff]
  by_cases h : ∀ i, multideg a i = δ i <;> by_cases hc : F.coeff a = 0 <;> simp [h, hc]

theorem homComp_rename (f : κ × Fin n → ι × Fin n) (δ : ι → ℕ) (G : MvPolynomial (κ × Fin n) R) :
    ∃ G' : MvPolynomial (κ × Fin n) R, G'.support ⊆ G.support ∧ rename f G' = homComp δ (rename f G) := by
  classical
  refine ⟨∑ mo ∈ G.support.filter (fun mo => ∀ i, multideg (Finsupp.mapDomain f mo) i = δ i),
    monomial mo (G.coeff mo), ?_, ?_⟩
  · intro mo hmo
    obtain ⟨x, hx, h2⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmo)
    rw [Finset.mem_singleton.mp (support_monomial_subset h2)]
    exact (Finset.mem_filter.mp hx).1
  · ext a
    rw [coeff_homComp]
    conv_rhs => rw [G.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, coeff_sum, rename_monomial, coeff_monomial]
    rw [Finset.sum_filter]
    split_ifs with h
    · apply Finset.sum_congr rfl
      intro mo _
      by_cases hm : Finsupp.mapDomain f mo = a
      · have hP : ∀ i, multideg (Finsupp.mapDomain f mo) i = δ i := by rw [hm]; exact h
        rw [if_pos hP]
      · simp only [hm, if_false, ite_self]
    · apply Finset.sum_eq_zero
      intro mo _
      by_cases hm : Finsupp.mapDomain f mo = a
      · have hP : ¬ ∀ i, multideg (Finsupp.mapDomain f mo) i = δ i := by rw [hm]; exact h
        simp [hP]
      · simp [hm]

end Comp

section Big

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

private theorem upPl_monomial_eq_monomial_mPl (bp : TL J nL r × Fin r →₀ ℕ) (c : KK O) :
    upPl Fr p O hk nL (monomial bp c) = monomial (mPl Fr p hk nL bp) c := by
  rw [show monomial (mPl Fr p hk nL bp) c = C c * monomial (mPl Fr p hk nL bp) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upPl, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mPl, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

private theorem upNo_monomial_eq_monomial_mNo (bn : TL J nL r × Fin K →₀ ℕ) (c : KK O) :
    upNo Fr p O hk nL (monomial bn c) = monomial (mNo Fr p hk nL bn) c := by
  rw [show monomial (mNo Fr p hk nL bn) c = C c * monomial (mNo Fr p hk nL bn) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upNo, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mNo, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

theorem asm_support (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N : MvPolynomial (TL J nL r × Fin K) (KK O)) (mm : TV n' (m + 1) →₀ ℕ)
    (h : mm ∈ (asm Fr p O hk nL rho A N).support) :
    ∃ bp ∈ A.support, ∃ bn ∈ N.support, mm = bigM Fr p hk nL rho bp bn := by
  classical
  have e : asm Fr p O hk nL rho A N = ∑ bp ∈ A.support, ∑ bn ∈ N.support,
      monomial (bigM Fr p hk nL rho bp bn) (A.coeff bp * N.coeff bn) := by
    conv_lhs => rw [asm, A.as_sum, N.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, upPl_monomial_eq_monomial_mPl, upNo_monomial_eq_monomial_mNo, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bp _
    apply Finset.sum_congr rfl
    intro bn _
    rw [monomial_mul, monomial_mul, one_mul, bigM_eq]
  rw [e] at h
  obtain ⟨bp, hbp, h2⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum h)
  obtain ⟨bn, hbn, h3⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum h2)
  exact ⟨bp, hbp, bn, hbn, Finset.mem_singleton.mp (support_monomial_subset h3)⟩

theorem bigM_off (htop : ∀ x : TL J nL r, posOf n' (posTL Fr x) ∈ Fr.TT)
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (s : Fin n') (hs : s ∉ Set.range fun x : TL J nL r => posOf n' (posTL Fr x)) (c : Fin (m + 1)) :
    bigM Fr p hk nL rho bp bn (s, c) = 0 := by
  apply bigM_notin
  rintro ⟨v, hv⟩
  exact hs ⟨v.1, congrArg Prod.fst hv⟩

theorem multideg_bigM (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (hsurj : ∀ s ∈ Fr.TT, ∃ x : TL J nL r, posOf n' (posTL Fr x) = s)
    (htop : ∀ x : TL J nL r, posOf n' (posTL Fr x) ∈ Fr.TT)
    (d : Fin n' → ℕ) (hd : ∀ s, s ∉ Fr.TT → d s = 0)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (hB : BlockOK Fr p nL d rho dPl dNo)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (h1 : ∀ x, multideg bp x = dPl x)
    (h2 : ∀ x, multideg bn x = dNo x) (s : Fin n') : multideg (bigM Fr p hk nL rho bp bn) s = d s := by
  by_cases hs : s ∈ Set.range fun x : TL J nL r => posOf n' (posTL Fr x)
  · obtain ⟨x, rfl⟩ := hs
    have hsc : multideg (bigM Fr p hk nL rho bp bn) (posOf n' (posTL Fr x)) =
        ∑ a : Fin r, bigM Fr p hk nL rho bp bn (plVar Fr hk nL x a) +
          ∑ b : Fin K, bigM Fr p hk nL rho bp bn (noVar Fr hk nL x b) := by
      unfold multideg
      rw [← Equiv.sum_comp (finCongr hk.symm) (fun c => bigM Fr p hk nL rho bp bn (posOf n' (posTL Fr x), c)),
        Fin.sum_univ_add]
      rfl
    rw [hsc]
    simp only [bigM_pl hinj, bigM_no hinj, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hB.2 x, ← h1 x, ← h2 x, Fin.sum_univ_add (fun c => rho (x, c))]
    unfold multideg
    ring
  · have hT : s ∉ Fr.TT := fun hT => hs (hsurj s hT)
    rw [hd s hT]
    unfold multideg
    exact Finset.sum_eq_zero (fun c _ => bigM_off Fr p hk nL htop rho bp bn s hs c)

end Big

end Formalism.MainNotions.Proposition5Numerics
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem isNormal_pl {n' r K : ℕ} (s : Fin n') (a : Fin r) :
    IsNormal r ((s, Fin.castAdd K a) : TV n' (r + K)) ↔ ¬ Even s.val := by
  unfold IsNormal
  by_cases h : Even s.val <;> simp [h, a.isLt]

theorem isNormal_no {n' r K : ℕ} (s : Fin n') (b : Fin K) :
    IsNormal r ((s, Fin.natAdd r b) : TV n' (r + K)) ↔ Even s.val := by
  unfold IsNormal
  by_cases h : Even s.val <;> simp [h]

section ND

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def oOf (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : ℕ :=
  ∑ x : TL J nL r, if Even (posOf n' (posTL Fr x)).val then
    ∑ b : Fin K, rho (x, Fin.natAdd r b) + lowP Fr p x * dNo x
    else ∑ a : Fin r, rho (x, Fin.castAdd K a) + lowP Fr p x * dPl x

theorem normDeg_bigM (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (htop : ∀ x : TL J nL r, posOf n' (posTL Fr x) ∈ Fr.TT)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (h1 : ∀ x, multideg bp x = dPl x)
    (h2 : ∀ x, multideg bn x = dNo x) (mm : TV n' (r + K) →₀ ℕ)
    (hmm : ∀ v, mm v = bigM Fr p hk nL rho bp bn (castVK hk v)) :
    normDeg r mm = oOf Fr p nL rho dPl dNo := by
  have hpl : ∀ (x : TL J nL r) (a : Fin r), mm (posOf n' (posTL Fr x), Fin.castAdd K a)
      = rho (x, Fin.castAdd K a) + lowP Fr p x * bp (x, a) := by
    intro x a
    rw [hmm]
    exact bigM_pl hinj rho bp bn x a
  have hno : ∀ (x : TL J nL r) (b : Fin K), mm (posOf n' (posTL Fr x), Fin.natAdd r b)
      = rho (x, Fin.natAdd r b) + lowP Fr p x * bn (x, b) := by
    intro x b
    rw [hmm]
    exact bigM_no hinj rho bp bn x b
  have hoff : ∀ s : Fin n', s ∉ Set.range (fun x : TL J nL r => posOf n' (posTL Fr x)) →
      ∀ c : Fin (r + K), mm (s, c) = 0 := by
    intro s hs c
    rw [hmm]
    exact bigM_off Fr p hk nL htop rho bp bn s hs _
  have h0 : normDeg r mm = ∑ v : TV n' (r + K), (if IsNormal r v then mm v else 0) := by
    unfold normDeg
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have hz : mm v = 0 := by simpa [Finsupp.mem_support_iff] using hv
    simp [hz]
  have hprod : ∑ v : TV n' (r + K), (if IsNormal r v then mm v else 0)
      = ∑ s : Fin n', ∑ c : Fin (r + K), (if IsNormal r ((s, c) : TV n' (r + K)) then mm (s, c) else 0) :=
    Fintype.sum_prod_type _
  have hsub : ∑ s ∈ Finset.univ.image (fun x : TL J nL r => posOf n' (posTL Fr x)),
        ∑ c : Fin (r + K), (if IsNormal r ((s, c) : TV n' (r + K)) then mm (s, c) else 0)
      = ∑ s : Fin n', ∑ c : Fin (r + K), (if IsNormal r ((s, c) : TV n' (r + K)) then mm (s, c) else 0) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro s _ hs
    have hs' : s ∉ Set.range (fun x : TL J nL r => posOf n' (posTL Fr x)) := by
      rintro ⟨x, rfl⟩
      exact hs (Finset.mem_image_of_mem _ (Finset.mem_univ x))
    apply Finset.sum_eq_zero
    intro c _
    simp [hoff s hs' c]
  have himg := Finset.sum_image (s := Finset.univ) (g := fun x : TL J nL r => posOf n' (posTL Fr x))
    (f := fun s : Fin n' => ∑ c : Fin (r + K), (if IsNormal r ((s, c) : TV n' (r + K)) then mm (s, c) else 0))
    (fun x _ y _ h => hinj h)
  rw [h0, hprod, ← hsub, himg]
  unfold oOf
  apply Finset.sum_congr rfl
  intro x _
  rw [Fin.sum_univ_add]
  by_cases he : Even (posOf n' (posTL Fr x)).val
  · simp only [isNormal_pl, isNormal_no, he, not_true_eq_false, if_false, if_true, Finset.sum_const_zero,
      zero_add, hno, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← h2 x]
    rfl
  · simp only [isNormal_pl, isNormal_no, he, not_false_eq_true, if_false, if_true, Finset.sum_const_zero,
      add_zero, hpl, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← h1 x]
    rfl

end ND

theorem castVK_inj {n' k r K : ℕ} (hk : k = r + K) : Function.Injective (castVK (n' := n') hk) := by
  intro v w h
  simp only [castVK, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.ext (by simpa using congrArg Fin.val h.2))

theorem toKK_support {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K) (P : RRing O n' (r + K))
    (mm : Fin n' × Fin (r + K) →₀ ℕ) (h : mm ∈ P.support) :
    Finsupp.mapDomain (castVK hk) mm ∈ (toKK hk P).support := by
  rw [MvPolynomial.mem_support_iff] at h ⊢
  unfold toKK
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_rename_mapDomain _ (castVK_inj hk)]
  intro h0
  apply h
  exact (IsFractionRing.injective O (KK O)) (by simpa using h0)

theorem restDegG : RestDegG := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hMH δ _
  have hV : Fr.Valid L₁ N₁ := hM.frames.2.1
  have hr : 1 ≤ r := le_trans (by norm_num) hM.two_le_r
  have hJ : J = Fr.J := hMH.1.1.1
  have hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card := hMH.1.1.2.1
  have hinj := posTL_inj Fr hV hr hJ hnL
  have hsurj := posTL_surj Fr hV hr hJ hnL
  have htop : ∀ x : TL J Dt.nL r, posOf n' (posTL Fr x) ∈ Fr.TT := fun x => (posTL_seg Fr hV hr hnL x).2.2
  obtain ⟨Go', hsub, hren⟩ := homComp_rename (fun v : ML J Dt.nL r × Fin r => (mlPos Fr Dt.nL v.1, v.2)) δ Go
  have e : homComp δ (xiPl Fr O Dt.nL Go) = xiPl Fr O Dt.nL Go' := hren.symm
  rw [e]
  have hid : toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go') * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
    asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go'))
      (MvPolynomial.map (algebraMap O (KK O)) No) :=
    alg_identity p O hk Fr Dt hV hr hJ hMH.1.1.2.2.2.2.1 rho No Go'
  have hA : Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go') ∈ Pol (KK O) r dPl := by
    rw [← hMH.1.1.2.2.2.1]
    refine ph_mem_pol Dt _ fun mo hmo => hMH.2.2.2.2 mo (hsub ?_)
    rwa [support_of_map] at hmo
  have hN : MvPolynomial.map (algebraMap O (KK O)) No ∈ Pol (KK O) K dNo := hMH.2.2.1.2.1
  have hAd := (mem_restrictSupport_iff (KK O)).1 hA
  have hNd := (mem_restrictSupport_iff (KK O)).1 hN
  refine ⟨?_, oOf Fr p Dt.nL rho dPl dNo, ?_⟩
  · rw [hid]
    unfold HasMultideg Pol
    rw [mem_restrictSupport_iff]
    intro mm hmm
    obtain ⟨bp, hbp, bn, hbn, rfl⟩ := asm_support Fr p O hk Dt.nL rho _ _ mm hmm
    exact multideg_bigM Fr p hk Dt.nL hinj hsurj htop d hM.d_off rho dPl dNo hMH.2.1 bp bn (hAd hbp) (hNd hbn)
  · intro mm hmm
    have h1 := toKK_support hk _ mm hmm
    rw [hid] at h1
    obtain ⟨bp, hbp, bn, hbn, h2⟩ := asm_support Fr p O hk Dt.nL rho _ _ _ h1
    refine normDeg_bigM Fr p hk Dt.nL hinj htop rho dPl dNo bp bn (hAd hbp) (hNd hbn) mm fun v => ?_
    rw [← h2, Finsupp.mapDomain_apply_of_injective (castVK_inj hk)]

end Formalism.MainNotions.Proposition5Numerics
