module

public import Development.EtaleCohomology.EtaleSheaves.LeafConsPfC
public import Development.EtaleCohomology.EtaleSheaves.FiniteChartSurjPf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LiftIdempotentFactorizationHolds
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPolynomialEqMapEvalRootsOfPermInvariant
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEvalRootsSymmetricEqAlgebraMap
noncomputable section
open Polynomial

theorem UpperTheory.exists_eval_roots_symmetric_eq_algebraMap :
    ∀ (A : Type) [CommRing A] (N : ℕ) (g : A[X]) (F : MvPolynomial (Fin N) A), F.IsSymmetric → ∃ a : A, ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → MvPolynomial.aeval x F = algebraMap A S a := by
  intro A _ N g F hF
  obtain ⟨P, hP⟩ := MvPolynomial.esymmAlgHom_fin_surjective A (le_refl N) ⟨F, hF⟩
  have hPF : MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A (i + 1)) P = F := by
    rw [← MvPolynomial.esymmAlgHom_apply, hP]
  let c : Fin N → A := fun i => (-1) ^ ((i : ℕ) + 1) * g.coeff (N - ((i : ℕ) + 1))
  refine ⟨MvPolynomial.aeval c P, ?_⟩
  intro S _ _ x hg
  have key : ∀ i : Fin N, MvPolynomial.aeval x (MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1)) =
      algebraMap A S (c i) := by
    intro i
    have hi := i.2
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    set s := Finset.univ.val.map x with hs
    have hcs : Multiset.card s = N := by simp [s]
    have hprod : (s.map fun t => X - C t).prod = g.map (algebraMap A S) := by
      rw [hg, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
      rfl
    have hk : N - ((i : ℕ) + 1) ≤ Multiset.card s := by omega
    have hco := Multiset.prod_X_sub_C_coeff s hk
    rw [hprod, Polynomial.coeff_map, hcs, show N - (N - ((i : ℕ) + 1)) = (i : ℕ) + 1 by omega]
      at hco
    simp only [c, map_mul, map_pow, map_neg, map_one, hco]
    rw [← mul_assoc, ← mul_pow]
    simp
  have hcomp : (MvPolynomial.aeval x).comp
      (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1))) =
      MvPolynomial.aeval (fun i => algebraMap A S (c i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.aeval_X, key]
  calc MvPolynomial.aeval x F
      = ((MvPolynomial.aeval x).comp
          (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1)))) P := by
        rw [← hPF]
        rfl
    _ = MvPolynomial.aeval (fun i => algebraMap A S (c i)) P := by rw [hcomp]
    _ = algebraMap A S (MvPolynomial.aeval c P) := MvPolynomial.aeval_algebraMap_apply S c P

end
end

noncomputable section
open Polynomial

theorem UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant :
    ∀ (A : Type) [CommRing A] (N : ℕ) (g : A[X]) (Φ : (MvPolynomial (Fin N) A)[X]), (∀ σ : Equiv.Perm (Fin N), Φ.map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom = Φ) →
      ∃ p : A[X], p.natDegree ≤ Φ.natDegree ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → p.map (algebraMap A S) = Φ.map (MvPolynomial.aeval x : MvPolynomial (Fin N) A →ₐ[A] S).toRingHom := by
  intro A _ N g Φ hΦ
  have hsym : ∀ n, (Φ.coeff n).IsSymmetric := by
    intro n σ
    have := congrArg (fun q => q.coeff n) (hΦ σ)
    simpa [Polynomial.coeff_map] using this
  choose a ha using fun n => UpperTheory.exists_eval_roots_symmetric_eq_algebraMap A N g (Φ.coeff n) (hsym n)
  refine ⟨∑ n ∈ Finset.range (Φ.natDegree + 1), monomial n (a n), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun n hn => ?_)
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
  · intro S _ _ x hx
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hn
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ha n S x hx]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicFactorLiftOfPowMulSubOnePow
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicFactorOfRootSubsetProductEquation
noncomputable section
open Polynomial

private lemma exists_roots {A : Type} [CommRing A] [Nontrivial A] {g : A[X]} (hg : g.Monic) {N : ℕ}
    (hN : g.natDegree = N) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra A S), Function.Injective (algebraMap A S) ∧
      ∃ x : Fin N → S, g.map (algebraMap A S) = ∏ i, (X - C (x i)) := by
  induction N generalizing A with
  | zero =>
    refine ⟨A, inferInstance, Algebra.id A, Function.injective_id, Fin.elim0, ?_⟩
    have h1 : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg hN
    simp [h1]
  | succ N ih =>
    have hinj : Function.Injective (AdjoinRoot.of g) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h
      exact AdjoinRoot.mk_ne_zero_of_natDegree_lt hg (C_ne_zero.mpr h)
        (by rw [natDegree_C]; omega) (by rwa [AdjoinRoot.mk_C])
    haveI : Nontrivial (AdjoinRoot g) := hinj.nontrivial
    have hroot : (g.map (AdjoinRoot.of g)).IsRoot (AdjoinRoot.root g) := AdjoinRoot.isRoot_root g
    have hfac : (X - C (AdjoinRoot.root g)) * ((g.map (AdjoinRoot.of g)) /ₘ (X - C (AdjoinRoot.root g)))
        = g.map (AdjoinRoot.of g) := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hqm : ((g.map (AdjoinRoot.of g)) /ₘ (X - C (AdjoinRoot.root g))).Monic :=
      Monic.of_mul_monic_left (monic_X_sub_C _) (hfac ▸ hg.map _)
    have hqd : ((g.map (AdjoinRoot.of g)) /ₘ (X - C (AdjoinRoot.root g))).natDegree = N := by
      have e1 := congrArg Polynomial.natDegree hfac
      rw [(monic_X_sub_C _).natDegree_mul hqm, natDegree_X_sub_C,
        natDegree_map_eq_of_injective hinj, hN] at e1
      omega
    obtain ⟨S, iS, aS, hSinj, x, hx⟩ := ih hqm hqd
    letI : Algebra A S := ((algebraMap (AdjoinRoot g) S).comp (AdjoinRoot.of g)).toAlgebra
    refine ⟨S, iS, this, hSinj.comp hinj, Fin.cons (algebraMap (AdjoinRoot g) S (AdjoinRoot.root g)) x, ?_⟩
    have e2 : g.map (algebraMap A S) = (g.map (AdjoinRoot.of g)).map (algebraMap (AdjoinRoot g) S) := by
      rw [Polynomial.map_map]
      rfl
    rw [e2, ← hfac, Polynomial.map_mul, hx, Fin.prod_univ_succ]
    simp

private lemma idem_mul {S ι : Type} [CommRing S] (Λ : Finset ι) (ε : ι → S) (a b : ι → S[X])
    (G : S[X]) (h1 : ∑ J ∈ Λ, ε J = 1) (h0 : ∀ J ∈ Λ, ∀ J' ∈ Λ, J ≠ J' → ε J * ε J' = 0)
    (hab : ∀ J ∈ Λ, a J * b J = G) :
    (∑ J ∈ Λ, C (ε J) * a J) * (∑ J ∈ Λ, C (ε J) * b J) = G := by
  have hsq : ∀ J ∈ Λ, ε J * ε J = ε J := by
    intro J hJ
    have e := congrArg (ε J * ·) h1
    simp only [mul_one, Finset.mul_sum] at e
    rwa [Finset.sum_eq_single J (fun J' hJ' hne => h0 J hJ J' hJ' (Ne.symm hne))
      (fun h => absurd hJ h)] at e
  rw [Finset.sum_mul_sum]
  calc ∑ J ∈ Λ, ∑ J' ∈ Λ, C (ε J) * a J * (C (ε J') * b J')
      = ∑ J ∈ Λ, C (ε J) * G := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [Finset.sum_eq_single J]
        · rw [← hab J hJ]
          calc C (ε J) * a J * (C (ε J) * b J) = C (ε J * ε J) * (a J * b J) := by
                rw [C_mul]
                ring
            _ = C (ε J) * (a J * b J) := by rw [hsq J hJ]
        · intro J' hJ' hne
          have e : C (ε J) * C (ε J') = 0 := by
            rw [← C_mul, h0 J hJ J' hJ' (Ne.symm hne), C_0]
          calc C (ε J) * a J * (C (ε J') * b J') = (C (ε J) * C (ε J')) * (a J * b J') := by ring
            _ = 0 := by rw [e, zero_mul]
        · intro h
          exact absurd hJ h
    _ = G := by rw [← Finset.sum_mul, ← map_sum, h1, C_1, one_mul]

private lemma weights {S ι : Type} [CommRing S] [DecidableEq ι] (Λ : Finset ι) (t : ι → S)
    (c c' : S) (hc : c' * c = 1) (h0 : ∏ J ∈ Λ, t J = 0)
    (h1 : ∑ J ∈ Λ, ∏ J' ∈ Λ.erase J, t J' = c) :
    (∑ J ∈ Λ, c' * ∏ J' ∈ Λ.erase J, t J' = 1) ∧
    (∀ J ∈ Λ, ∀ J' ∈ Λ, J ≠ J' →
      (c' * ∏ K ∈ Λ.erase J, t K) * (c' * ∏ K ∈ Λ.erase J', t K) = 0) ∧
    (∀ J ∈ Λ, (c' * ∏ K ∈ Λ.erase J, t K) * t J = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.mul_sum, h1, hc]
  · intro J hJ J' hJ' hne
    have hmem : J' ∈ Λ.erase J := Finset.mem_erase.mpr ⟨Ne.symm hne, hJ'⟩
    rw [← Finset.mul_prod_erase (Λ.erase J) t hmem]
    have h2 : t J' * ∏ K ∈ Λ.erase J', t K = 0 := by rw [Finset.mul_prod_erase Λ t hJ', h0]
    calc c' * (t J' * ∏ K ∈ (Λ.erase J).erase J', t K) * (c' * ∏ K ∈ Λ.erase J', t K)
        = c' * c' * (∏ K ∈ (Λ.erase J).erase J', t K) * (t J' * ∏ K ∈ Λ.erase J', t K) := by ring
      _ = 0 := by rw [h2, mul_zero]
  · intro J hJ
    rw [mul_assoc, Finset.prod_erase_mul Λ t hJ, h0, mul_zero]

private def Wt {A : Type} [CommRing A] (N m : ℕ) (α c' : A) (J : Finset (Fin N)) :
    MvPolynomial (Fin N) A :=
  MvPolynomial.C c' * ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J,
    (MvPolynomial.C α - ∏ i ∈ J', MvPolynomial.X i)

private def Ph {A : Type} [CommRing A] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N)) : (MvPolynomial (Fin N) A)[X] :=
  ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
    C (Wt N m α c' J) * ∏ i ∈ f J, (X - C (MvPolynomial.X i))

private lemma Wt_rename {A : Type} [CommRing A] (N m : ℕ) (α c' : A) (σ : Equiv.Perm (Fin N))
    (J : Finset (Fin N)) :
    MvPolynomial.rename σ (Wt N m α c' J) = Wt N m α c' (J.map σ.toEmbedding) := by
  unfold Wt
  rw [map_mul, MvPolynomial.rename_C, map_prod]
  congr 1
  refine Finset.prod_equiv (Equiv.finsetCongr σ) ?_ ?_
  · intro K
    simp [Finset.mem_erase, Finset.mem_powersetCard]
  · intro K _
    simp [map_sub, map_prod, MvPolynomial.rename_X, Finset.prod_map]

private lemma Ph_sym {A : Type} [CommRing A] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N))
    (hf : ∀ (σ : Equiv.Perm (Fin N)) J, f (J.map σ.toEmbedding) = (f J).map σ.toEmbedding)
    (σ : Equiv.Perm (Fin N)) :
    (Ph N m α c' f).map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom =
      Ph N m α c' f := by
  unfold Ph
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Wt_rename,
    MvPolynomial.rename_X]
  refine Finset.sum_nbij' (fun J => J.map σ.toEmbedding) (fun J => J.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    simpa using hJ
  · intro J hJ
    simpa using hJ
  · intro J _
    ext i
    simp [Finset.mem_map_equiv]
  · intro J _
    ext i
    simp [Finset.mem_map_equiv]
  · intro J _
    rw [hf σ J, Finset.prod_map]
    rfl

private lemma Ph_deg {A : Type} [CommRing A] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N)) (d : ℕ)
    (hd : ∀ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (f J).card = d) :
    (Ph N m α c' f).natDegree ≤ d := by
  unfold Ph
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro J hJ
  have e1 : ∑ i ∈ f J, (X - C (MvPolynomial.X i : MvPolynomial (Fin N) A)).natDegree ≤ (f J).card := by
    have e2 := Finset.sum_le_sum (s := f J)
      (f := fun i => (X - C (MvPolynomial.X i : MvPolynomial (Fin N) A)).natDegree)
      (g := fun _ => (1 : ℕ)) (fun i _ => natDegree_X_sub_C_le _)
    simpa using e2
  rw [← hd J hJ]
  exact (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans e1)

private lemma Ph_map {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N)) (x : Fin N → S) :
    (Ph N m α c' f).map (MvPolynomial.aeval x : MvPolynomial (Fin N) A →ₐ[A] S).toRingHom =
      ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
        C (algebraMap A S c' * ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J,
            (algebraMap A S α - ∏ i ∈ J', x i)) * ∏ i ∈ f J, (X - C (x i)) := by
  unfold Ph Wt
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Polynomial.map_sum, Polynomial.map_prod, map_prod, map_sub, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C]

private lemma coeff_sum {S ι : Type} [CommRing S] [Nontrivial S] {N : ℕ} (Λ : Finset ι)
    (ε : ι → S) (s : ι → Finset (Fin N)) (x : Fin N → S) (d : ℕ)
    (hd : ∀ J ∈ Λ, (s J).card = d) :
    (∑ J ∈ Λ, C (ε J) * ∏ i ∈ s J, (X - C (x i))).coeff d = ∑ J ∈ Λ, ε J := by
  rw [finsetSum_coeff]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [coeff_C_mul]
  have hm : (∏ i ∈ s J, (X - C (x i))).Monic :=
    monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)
  have hdeg : (∏ i ∈ s J, (X - C (x i))).natDegree = d := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)]
    simp [hd J hJ]
  rw [← hdeg, hm.coeff_natDegree, mul_one]

private lemma eval_sum {S ι : Type} [CommRing S] {N : ℕ} (Λ : Finset ι) (ε : ι → S)
    (s : ι → Finset (Fin N)) (x : Fin N → S) (a : S) (d : ℕ) (h1 : ∑ J ∈ Λ, ε J = 1)
    (hd : ∀ J ∈ Λ, (s J).card = d) (h3 : ∀ J ∈ Λ, ε J * (a - ∏ i ∈ s J, x i) = 0) :
    (∑ J ∈ Λ, C (ε J) * ∏ i ∈ s J, (X - C (x i))).eval 0 = (-1) ^ d * a := by
  rw [eval_finsetSum]
  have key : ∀ J ∈ Λ, (C (ε J) * ∏ i ∈ s J, (X - C (x i))).eval 0 = (-1) ^ d * (ε J * a) := by
    intro J hJ
    have h := h3 J hJ
    rw [eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    rw [Finset.prod_neg, hd J hJ]
    have e : ε J * ∏ i ∈ s J, x i = ε J * a := by linear_combination -h
    linear_combination (-1) ^ d * e
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Finset.sum_mul, h1, one_mul]

theorem UpperTheory.exists_monic_factor_of_root_subset_product_equation :
    ∀ (A : Type) [CommRing A] (g : A[X]) (n m N : ℕ), n + m = N → g.Monic → g.natDegree = N → ∀ (α : A) (c : Aˣ),
      (∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (algebraMap A S α - ∏ i ∈ J, x i) = 0 ∧
        ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J, (algebraMap A S α - ∏ i ∈ J', x i) = algebraMap A S c) →
      ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧ Q.natDegree ≤ m ∧ Q.coeff m = 1 ∧ Q.eval 0 = (-1) ^ m * α := by
  intro A _ g n m N hnm hg hN α c hyp
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨1, 1, monic_one, monic_one, Subsingleton.elim _ _, by simp,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  classical
  obtain ⟨q, hqdeg, hq⟩ := UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant A N g (Ph N m α (↑c⁻¹ : A) (fun J => J))
    (Ph_sym N m α _ _ (fun σ J => rfl))
  obtain ⟨p, -, hp⟩ := UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant A N g (Ph N m α (↑c⁻¹ : A) (fun J => Jᶜ))
    (Ph_sym N m α _ _ (fun σ J => by ext i; simp [Finset.mem_map_equiv]))
  obtain ⟨S, iS, aS, hinj, x, hx⟩ := exists_roots hg hN
  haveI : Nontrivial S := hinj.nontrivial
  have hinjX : Function.Injective (Polynomial.map (algebraMap A S)) := Polynomial.map_injective _ hinj
  obtain ⟨h0, h1⟩ := hyp S x hx
  have hc : algebraMap A S (↑c⁻¹ : A) * algebraMap A S (↑c : A) = 1 := by
    rw [← map_mul]
    simp
  obtain ⟨w1, w2, w3⟩ := weights (Finset.powersetCard m (Finset.univ : Finset (Fin N)))
    (fun J => algebraMap A S α - ∏ i ∈ J, x i) _ _ hc h0 h1
  have hqS := hq S x hx
  rw [Ph_map] at hqS
  have hpS := hp S x hx
  rw [Ph_map] at hpS
  have hQd : q.natDegree ≤ m :=
    hqdeg.trans (Ph_deg N m α _ _ m (fun J hJ => (Finset.mem_powersetCard.mp hJ).2))
  have hQc : q.coeff m = 1 := by
    apply hinj
    rw [← Polynomial.coeff_map, hqS,
      coeff_sum _ _ (fun J => J) x m (fun J hJ => (Finset.mem_powersetCard.mp hJ).2), w1, map_one]
  have hQm : q.Monic := by
    have e : q.natDegree = m := natDegree_eq_of_le_of_coeff_ne_zero hQd (by rw [hQc]; exact one_ne_zero)
    rw [Monic, leadingCoeff, e, hQc]
  have hg' : g = p * q := by
    apply hinjX
    rw [Polynomial.map_mul, hpS, hqS, hx]
    exact (idem_mul _ _ (fun J => ∏ i ∈ Jᶜ, (X - C (x i))) (fun J => ∏ i ∈ J, (X - C (x i))) _ w1 w2
      (fun J _ => Finset.prod_compl_mul_prod J _)).symm
  refine ⟨p, q, Monic.of_mul_monic_right hQm (hg' ▸ hg), hQm, hg', hQd, hQc, ?_⟩
  apply hinj
  rw [← Polynomial.eval_zero_map, hqS,
    eval_sum _ _ (fun J => J) x _ m w1 (fun J hJ => (Finset.mem_powersetCard.mp hJ).2) w3]
  simp

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootSubsetProductEquationOfHenselianReduct
noncomputable section
open Polynomial

private lemma Phi_sym {A : Type} [CommRing A] (N m : ℕ) (σ : Equiv.Perm (Fin N)) :
    (∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
      ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i))).map
      (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom =
    ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
      ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i)) := by
  rw [Polynomial.map_prod]
  have hterm : ∀ J : Finset (Fin N),
      ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i)).map
        (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom =
      X - C (∏ i ∈ J.map σ.toEmbedding, MvPolynomial.X i) := by
    intro J
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Finset.prod_map,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod]
    simp only [MvPolynomial.rename_X, Equiv.coe_toEmbedding]
  rw [Finset.prod_congr rfl (fun J _ => hterm J)]
  refine Finset.prod_nbij' (fun J => J.map σ.toEmbedding) (fun J => J.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    rw [Finset.mem_powersetCard] at hJ ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map, hJ.2]⟩
  · intro J hJ
    rw [Finset.mem_powersetCard] at hJ ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map, hJ.2]⟩
  · intro J _
    simp [Finset.map_map]
  · intro J _
    simp [Finset.map_map]
  · intro J _
    rfl

private lemma eval_derivative_prod_X_sub_C {R ι : Type*} [CommRing R] [DecidableEq ι] (s : Finset ι) (y : ι → R) (a : R) :
    (derivative (∏ J ∈ s, ((X : R[X]) - C (y J)))).eval a = ∑ J ∈ s, ∏ J' ∈ s.erase J, (a - y J') := by
  rw [derivative_prod_finset]
  simp [eval_finsetSum, eval_prod]

private lemma exists_chi {A : Type} [CommRing A] [Nontrivial A] (g : A[X]) (N m : ℕ) (hm : m ≤ N) :
    ∃ χ : A[X], χ.Monic ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S),
      g.map (algebraMap A S) = ∏ i, (X - C (x i)) →
      χ.map (algebraMap A S) =
        ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (X - C (∏ i ∈ J, x i)) := by
  classical
  set Φ : (MvPolynomial (Fin N) A)[X] := ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
      ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i)) with hΦ
  set d := Nat.choose N m with hd
  have hdpos : 0 < d := Nat.choose_pos hm
  have hΦm : Φ.Monic := Polynomial.monic_prod_of_monic _ _ (fun J _ => Polynomial.monic_X_sub_C _)
  have hΦdeg : Φ.natDegree = d := by
    rw [hΦ, Polynomial.natDegree_prod_of_monic _ _ (fun J _ => Polynomial.monic_X_sub_C _),
      Finset.sum_congr rfl (fun J _ => Polynomial.natDegree_X_sub_C _)]
    simp [Finset.card_powersetCard, hd]
  have hsym : ∀ σ : Equiv.Perm (Fin N),
      (Φ - X ^ d).map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom = Φ - X ^ d := by
    intro σ
    rw [Polynomial.map_sub, hΦ, Phi_sym, Polynomial.map_pow, Polynomial.map_X]
  obtain ⟨p, hpdeg, hp⟩ := UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant A N g (Φ - X ^ d) hsym
  have hlt : (Φ - X ^ d).natDegree < d := by
    by_cases h0 : Φ - X ^ d = 0
    · rw [h0, Polynomial.natDegree_zero]; exact hdpos
    · rw [Polynomial.natDegree_lt_iff_degree_lt h0]
      have hdeg : Φ.degree = (X ^ d : (MvPolynomial (Fin N) A)[X]).degree := by
        rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hΦm.ne_zero, hΦdeg]
      have := Polynomial.degree_sub_lt hdeg hΦm.ne_zero
        (by rw [hΦm.leadingCoeff, Polynomial.leadingCoeff_X_pow])
      rwa [Polynomial.degree_eq_natDegree hΦm.ne_zero, hΦdeg] at this
  refine ⟨X ^ d + p, ?_, ?_⟩
  · apply Polynomial.Monic.add_of_left (Polynomial.monic_X_pow d)
    rw [Polynomial.degree_X_pow]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast lt_of_le_of_lt hpdeg hlt)
  · intro S _ _ x hx
    rw [Polynomial.map_add (f := _), hp S x hx, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, add_sub_cancel, hΦ, Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun J _ => ?_)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, map_prod]
    simp only [MvPolynomial.aeval_X]

theorem UpperTheory.exists_root_subset_product_equation_of_henselian_reduction :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (g : A[X]) (n m N : ℕ), n + m = N → g.Monic → g.natDegree = N → g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
      ∃ (α : A) (c : Aˣ), α - 1 ∈ I ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) →
        ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (algebraMap A S α - ∏ i ∈ J, x i) = 0 ∧
        ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J, (algebraMap A S α - ∏ i ∈ J', x i) = algebraMap A S c := by
  intro A _ I _ g n m N hnm hg hdeg hmod
  classical
  subst hnm
  rcases subsingleton_or_nontrivial A with hA | hA
  · refine ⟨1, 1, by rw [Subsingleton.elim (1 - 1 : A) 0]; exact I.zero_mem, ?_⟩
    intro S _ _ x _
    have h10 : (1 : S) = 0 := by
      rw [← map_one (algebraMap A S), Subsingleton.elim (1 : A) 0, map_zero]
    haveI : Subsingleton S := subsingleton_of_zero_eq_one h10.symm
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · obtain ⟨χ, hχm, hχ⟩ := exists_chi g (n + m) m (Nat.le_add_left m n)
    let x0 : Fin (n + m) → A ⧸ I := fun i => if (i : ℕ) < m then 1 else 0
    have hprod : ∏ i : Fin (n + m), ((X : (A ⧸ I)[X]) - C (x0 i)) = X ^ n * (X - 1) ^ m := by
      have h := Fin.prod_univ_eq_prod_range
        (fun k => (X : (A ⧸ I)[X]) - C (if k < m then 1 else 0)) (n + m)
      rw [h, show n + m = m + n from add_comm n m, Finset.prod_range_add]
      have h1 : ∏ k ∈ Finset.range m, ((X : (A ⧸ I)[X]) - C (if k < m then 1 else 0)) =
          (X - 1) ^ m := by
        rw [Finset.prod_congr rfl (fun k hk => by rw [if_pos (Finset.mem_range.mp hk), map_one])]
        simp
      have h2 : ∏ k ∈ Finset.range n, ((X : (A ⧸ I)[X]) - C (if m + k < m then 1 else 0)) =
          X ^ n := by
        rw [Finset.prod_congr rfl (fun k _ => by rw [if_neg (by omega), map_zero, sub_zero])]
        simp
      rw [h1, h2, mul_comm]
    have hsplit : g.map (algebraMap A (A ⧸ I)) = ∏ i, (X - C (x0 i)) := by
      rw [Ideal.Quotient.algebraMap_eq, hmod, hprod]
    have hS := hχ (A ⧸ I) x0 hsplit
    let T : Finset (Fin (n + m)) := Finset.univ.filter (fun i => (i : ℕ) < m)
    have hT : T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin (n + m))) := by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      simp only [T, Fin.card_filter_val_lt]
      omega
    have hyT : ∏ i ∈ T, x0 i = 1 :=
      Finset.prod_eq_one (fun i hi => by simp [x0, (Finset.mem_filter.mp hi).2])
    have hyJ : ∀ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin (n + m))), J ≠ T →
        ∏ i ∈ J, x0 i = 0 := by
      intro J hJ hne
      by_contra h
      apply hne
      have hsub : J ⊆ T := by
        intro i hi
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        by_contra hlt
        exact h (Finset.prod_eq_zero hi (by simp [x0, hlt]))
      exact Finset.eq_of_subset_of_card_le hsub
        (by rw [(Finset.mem_powersetCard.mp hJ).2, (Finset.mem_powersetCard.mp hT).2])
    have hev : ∀ q : A[X], (q.map (algebraMap A (A ⧸ I))).eval 1 = Ideal.Quotient.mk I (q.eval 1) := by
      intro q
      rw [Polynomial.eval_map, ← map_one (algebraMap A (A ⧸ I)), Polynomial.eval₂_at_apply]
      rfl
    have hE0 : Ideal.Quotient.mk I (χ.eval 1) = 0 := by
      rw [← hev, hS]
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact Finset.prod_eq_zero hT (by rw [hyT, sub_self])
    have hE1 : Ideal.Quotient.mk I ((derivative χ).eval 1) = 1 := by
      rw [← hev, ← Polynomial.derivative_map, hS]
      have hd := eval_derivative_prod_X_sub_C (Finset.powersetCard m (Finset.univ : Finset (Fin (n + m))))
        (fun J => ∏ i ∈ J, x0 i) (1 : A ⧸ I)
      rw [hd, Finset.sum_eq_single T]
      · exact Finset.prod_eq_one (fun J hJ => by
          rw [hyJ J (Finset.mem_of_mem_erase hJ) (Finset.ne_of_mem_erase hJ), sub_zero])
      · intro J _ hne
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hT⟩)
          (by rw [hyT, sub_self])
      · intro h
        exact absurd hT h
    have hmem : χ.eval 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hE0
    have hu1 : IsUnit (Ideal.Quotient.mk I ((derivative χ).eval 1)) := by
      rw [hE1]
      exact isUnit_one
    obtain ⟨α, hαroot, hα1⟩ := HenselianRing.is_henselian (R := A) (I := I) χ hχm 1 hmem hu1
    have hcong : Ideal.Quotient.mk I ((derivative χ).eval α) =
        Ideal.Quotient.mk I ((derivative χ).eval 1) := by
      rw [Ideal.Quotient.eq]
      obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub α 1 (derivative χ)
      rw [hk]
      exact I.mul_mem_right k hα1
    have hunit : IsUnit ((derivative χ).eval α) := by
      haveI := isLocalHom_of_le_jacobson_bot I (by
        simpa only [Ideal.jacobson_bot] using (HenselianRing.jac (I := I)))
      exact isUnit_of_map_unit (Ideal.Quotient.mk I) _ (by rw [hcong, hE1]; exact isUnit_one)
    refine ⟨α, hunit.unit, hα1, ?_⟩
    intro S _ _ x hx
    have hSx := hχ S x hx
    constructor
    · have h := congrArg (fun q => q.eval (algebraMap A S α)) hSx
      simp only [Polynomial.eval_map, Polynomial.eval₂_at_apply, hαroot.eq_zero, map_zero,
        Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
      exact h.symm
    · have h := congrArg (fun q => (derivative q).eval (algebraMap A S α)) hSx
      have hd := eval_derivative_prod_X_sub_C (Finset.powersetCard m (Finset.univ : Finset (Fin (n + m))))
        (fun J => ∏ i ∈ J, x i) (algebraMap A S α)
      simp only [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply] at h
      rw [hd] at h
      rw [hunit.unit_spec]
      exact h.symm

end
end

noncomputable section
open Polynomial

theorem UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (g : A[X]), g.Monic → ∀ n m : ℕ, g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
      ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧ P.map (Ideal.Quotient.mk I) = X ^ n ∧ Q.map (Ideal.Quotient.mk I) = (X - 1) ^ m := by
  intro A _ I _ g hg n m hgm
  by_cases hR : Nontrivial (A ⧸ I)
  swap
  · rw [not_nontrivial_iff_subsingleton] at hR
    exact ⟨g, 1, hg, monic_one, (mul_one g).symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI := hR
  haveI hA : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  have h1 : ((X : (A ⧸ I)[X]) - 1) = X - C 1 := by simp
  have hdeg : g.natDegree = n + m := by
    have h := congrArg natDegree hgm
    rw [hg.natDegree_map, h1, (monic_X_pow n).natDegree_mul ((monic_X_sub_C 1).pow m),
      natDegree_X_pow, (monic_X_sub_C (1 : A ⧸ I)).natDegree_pow, natDegree_X_sub_C, mul_one] at h
    exact h
  obtain ⟨α, c, hα, hc⟩ := UpperTheory.exists_root_subset_product_equation_of_henselian_reduction A I g n m (n + m) rfl hg hdeg hgm
  obtain ⟨P, Q, hP, hQ, hPQ, hQd, hQm, hQ0⟩ := UpperTheory.exists_monic_factor_of_root_subset_product_equation A g n m (n + m) rfl hg hdeg α c hc
  have hQdeg : Q.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hQd (by rw [hQm]; exact one_ne_zero)
  have hPdeg : P.natDegree = n := by
    have h := hP.natDegree_mul hQ
    rw [← hPQ, hdeg, hQdeg] at h
    omega
  set φ := Ideal.Quotient.mk I
  have hPb : (P.map φ).Monic := hP.map φ
  have hprod : P.map φ * Q.map φ = X ^ n * (X - 1) ^ m := by
    rw [← Polynomial.map_mul, ← hPQ, hgm]
  have hQ0b : (Q.map φ).eval 0 = (-1) ^ m := by
    rw [eval_zero_map, hQ0, map_mul, map_pow, map_neg, map_one, Ideal.Quotient.eq.mpr hα, map_one, mul_one]
  have hcop : IsCoprime (X : (A ⧸ I)[X]) (Q.map φ) := by
    have hd : X ∣ Q.map φ - C ((Q.map φ).coeff 0) := X_dvd_sub_C
    obtain ⟨r, hr⟩ := hd
    rw [coeff_zero_eq_eval_zero, hQ0b] at hr
    refine ⟨-(C ((-1) ^ m) * r), C ((-1) ^ m), ?_⟩
    have hu : ((-1 : A ⧸ I) ^ m) * (-1) ^ m = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    calc -(C ((-1) ^ m) * r) * X + C ((-1) ^ m) * Q.map φ
        = C ((-1) ^ m) * (Q.map φ - X * r) := by ring
      _ = 1 := by rw [← hr, sub_sub_cancel, ← C_mul, hu, C_1]
  obtain ⟨s, hs⟩ := hcop.pow_left.dvd_of_dvd_mul_right ⟨(X - 1) ^ m, hprod⟩
  have hsm : s.Monic := (monic_X_pow n).of_mul_monic_left (by rw [← hs]; exact hPb)
  have hsdeg : s.natDegree = 0 := by
    have h := congrArg natDegree hs
    rw [hP.natDegree_map φ, (monic_X_pow n).natDegree_mul hsm, natDegree_X_pow, hPdeg] at h
    omega
  have hs1 : s = 1 := eq_one_of_monic_natDegree_zero hsm hsdeg
  have hPmap : P.map φ = X ^ n := by rw [hs, hs1, mul_one]
  have hQmap : Q.map φ = (X - 1) ^ m := by
    rw [hPmap] at hprod
    have h : X ^ n * (Q.map φ - (X - 1) ^ m) = 0 := by rw [mul_sub, hprod, sub_self]
    exact sub_eq_zero.mp ((monic_X_pow n).mul_right_eq_zero_iff.mp h)
  exact ⟨P, Q, hP, hQ, hPQ, hPmap, hQmap⟩

end
end

noncomputable section

theorem UpperTheory.liftIdempotentFactorization_holds :
    LateralTheory.E.LIdemLiftPf.LFact := by
  intro A _ I _ g hg n m h
  exact UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow A I g hg n m h

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LJacPf
namespace LateralTheory.E.LJacPf

theorem LJac_of : LateralTheory.E.HensIdemCut.LJac := by
  intro A _ I hH B _ φ hφ
  letI := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  have hI : I ≤ Ideal.jacobson ⊥ := by simpa only [Ideal.jacobson_bot] using hH.jac
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro m ⟨-, hm⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (m.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal φ hφ m
  refine hI.trans ?_
  rw [Ideal.jacobson]
  exact sInf_le ⟨bot_le, this⟩

end LateralTheory.E.LJacPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LMonicPf
noncomputable section
open Polynomial

namespace LateralTheory.E.LMonicPf

theorem map_mk_eq_X_pow {A : Type} [CommRing A] (I : Ideal A) (p : A[X]) (hp : p.Monic)
    (h : ∀ i ≠ p.natDegree, p.coeff i ∈ I) :
    p.map (Ideal.Quotient.mk I) = X ^ p.natDegree := by
  ext i
  rw [coeff_map, coeff_X_pow]
  split_ifs with hi
  · subst hi; rw [hp.coeff_natDegree, map_one]
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i hi)

theorem LMonic_of : LateralTheory.E.HensIdemCut.LMonic := by
  intro A _ I B _ φ hφ b hb
  cases subsingleton_or_nontrivial A
  · have : Subsingleton B := by
      refine ⟨fun x y => ?_⟩
      rw [← mul_one x, ← mul_one y, ← map_one φ, Subsingleton.elim (1 : A) 0, map_zero,
        mul_zero, mul_zero]
    exact ⟨0, 1, monic_one, Subsingleton.elim _ _, by simp⟩
  let := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  obtain ⟨p, hpm, hp0, hpI⟩ :=
    exists_monic_aeval_eq_zero_forall_mem_of_mem_map (R := A) (S := B) (I := I) (x := b * b - b) hb
  have hqe : ((X : A[X]) * X - X) = X ^ 2 - X := by rw [sq]
  have hq : ((X : A[X]) * X - X).Monic := by
    rw [hqe]
    exact monic_X_pow_sub (degree_X_le.trans_lt (by norm_num))
  have hqd : ((X : A[X]) * X - X).natDegree ≠ 0 := by
    intro h
    have h1 := congrArg (eval 0) ((Polynomial.Monic.natDegree_eq_zero hq).mp h)
    simp at h1
  refine ⟨p.natDegree, p.comp (X * X - X), hpm.comp hq hqd, ?_, ?_⟩
  · rw [eval₂_comp]
    simp only [eval₂_mul, eval₂_sub, eval₂_X]
    rw [aeval_def] at hp0
    exact hp0
  · rw [Polynomial.map_comp, map_mk_eq_X_pow I p hpm hpI, X_pow_comp, ← mul_pow]
    congr 1
    simp [C_1]
    ring
end LateralTheory.E.LMonicPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LIdemPf
noncomputable section
open Polynomial

namespace LateralTheory.E.LIdemPf

theorem LIdem_of : LateralTheory.E.HensIdemCut.LIdem := by
  intro A _ I B _ φ hJ b hb N g h hg hh hgh
  set J := I.map φ with hJdef
  let π := Ideal.Quotient.mk J
  let ψ : A ⧸ I →+* B ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
  have hcomp : ψ.comp (Ideal.Quotient.mk I) = π.comp φ := by
    ext a; simp [ψ, π, Ideal.quotientMap_mk]
  have key : ∀ p : A[X], π (p.eval₂ φ b) = (p.map (Ideal.Quotient.mk I)).eval₂ ψ (π b) := by
    intro p
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]
  set G := g.eval₂ φ b with hGdef
  set H := h.eval₂ φ b with hHdef
  set e := π b with hedef
  have hG : π G = e ^ N := by rw [key, hg]; simp
  have hH : π H = (e - 1) ^ N := by rw [key, hh]; simp [eval₂_pow, eval₂_sub, eval₂_X, eval₂_one]
  have he : e * e = e := by
    have : π (b * b - b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    rw [map_sub, map_mul] at this
    exact sub_eq_zero.mp this
  have hcop : IsCoprime (e ^ N) ((e - 1) ^ N) :=
    (show IsCoprime e (e - 1) from ⟨1, -1, by ring⟩).pow
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨v', rfl⟩ := Ideal.Quotient.mk_surjective v
  set s := u' * G + v' * H with hsdef
  have hs : π s = π 1 := by
    simp only [hsdef, map_add (f := _), map_mul, hG, hH, map_one]
    exact huv
  have hsJ : s - 1 ∈ Ideal.jacobson (⊥ : Ideal B) := hJ (Ideal.Quotient.eq.mp hs)
  have hunit : IsUnit s := by
    have := (Ideal.mem_jacobson_bot.mp hsJ) 1
    simpa using this
  obtain ⟨w, hw⟩ := hunit
  have hsum : (↑w⁻¹ * u') * G + (↑w⁻¹ * v') * H = 1 := by
    have : (↑w⁻¹ : B) * s = 1 := by rw [← hw]; exact Units.inv_mul w
    rw [hsdef] at this
    linear_combination this
  refine ⟨(↑w⁻¹ * u') * G, ?_, ?_⟩
  · show (↑w⁻¹ * u') * G * ((↑w⁻¹ * u') * G) = (↑w⁻¹ * u') * G
    linear_combination ((↑w⁻¹ * u') * G) * hsum - (↑w⁻¹ * u') * (↑w⁻¹ * v') * hgh
  · rw [← Ideal.Quotient.eq]
    change π ((↑w⁻¹ * u') * G) = e
    have hsum' := congrArg π hsum
    simp only [map_add (f := _), map_mul, map_one, hG, hH] at hsum' ⊢
    set α := π ↑w⁻¹ * π u'
    set γ := π ↑w⁻¹ * π v'
    cases N with
    | zero =>
      have h0 : (1 : B ⧸ J) = 0 := by
        have := congrArg π hgh
        simpa [map_mul, hG, hH] using this
      have := subsingleton_of_zero_eq_one h0.symm
      exact Subsingleton.elim _ _
    | succ n =>
      have hp : e ^ (n + 1) = e := IsIdempotentElem.pow_succ_eq n he
      have h1 : e * (e - 1) ^ (n + 1) = 0 := by
        calc e * (e - 1) ^ (n + 1) = (e * e - e) * (e - 1) ^ n := by ring
          _ = 0 := by rw [he, sub_self, zero_mul]
      rw [hp] at hsum' ⊢
      linear_combination e * hsum' - α * he - γ * h1

end LateralTheory.E.LIdemPf
end
end

namespace UpperTheory.Et.HenselianIdempotents

theorem a0 : LateralTheory.E.HensIdemCut.LJac := LateralTheory.E.LJacPf.LJac_of
theorem a1 : LateralTheory.E.HensIdemCut.LMonic := LateralTheory.E.LMonicPf.LMonic_of
theorem a2 : LateralTheory.E.LIdemLiftPf.LFact := UpperTheory.liftIdempotentFactorization_holds
theorem a3 : LateralTheory.E.LChartPf.LIdemLift := LateralTheory.E.LIdemLiftPf.LIdemLift_of a2
theorem a4 : LateralTheory.E.LSurjChartPf.FiniteChartSurj := LateralTheory.E.FiniteChartSurjPf.FiniteChartSurj_of
theorem a5 : LateralTheory.E.LChartPf.LSurjChart := LateralTheory.E.LSurjChartPf.etale_surjective_chart_of_finite_chart_surj a4
theorem a6 : LateralTheory.E.LEtaleLiftPf.LChart := LateralTheory.E.LChartPf.LChart_of a3 a5
theorem a7 : LateralTheory.E.LFactorPf.LEtaleLift := LateralTheory.E.LEtaleLiftPf.LEtaleLift_of a6
theorem a8 : LateralTheory.E.HensIdemCut.LFactor := LateralTheory.E.LFactorPf.LFactor_of a7
theorem a9 : LateralTheory.E.HensIdemCut.LIdem := LateralTheory.E.LIdemPf.LIdem_of
theorem a10 : LateralTheory.E.t_E1Cut.HensIdem := LateralTheory.E.HensIdemCut.goal_of a0 a1 a8 a9

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.HensIdem := a10

end UpperTheory.Et.HenselianIdempotents
