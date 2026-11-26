module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestSplit

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExistsDominantTopWeightNonzero
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

section basic

variable {L : Type} [CommRing L] {n : ℕ}

theorem partialAct_eq_fullAct_of_vars_lt (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < i) :
    actI isVec i g gi P = actAll isVec g gi P := by
  refine MvPolynomial.hom_congr_vars (f₁ := (actI isVec i g gi).toRingHom)
    (f₂ := (actAll isVec g gi).toRingHom) ?_ ?_ rfl
  · ext r
    simp
  · intro x hx _
    have hxi := hv x hx
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, actI, actAll, MvPolynomial.aeval_X, if_pos hxi]
    split_ifs
    · simp [Matrix.vecMul, dotProduct]
    · simp [Matrix.vecMul, dotProduct]

theorem partialAct_fix_of_vars_ge (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    {Q : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ Q.vars, i ≤ x.1) :
    actI isVec i g gi Q = Q := by
  conv_rhs => rw [← AlgHom.id_apply (R := L) Q]
  refine MvPolynomial.hom_congr_vars (f₁ := (actI isVec i g gi).toRingHom)
    (f₂ := (AlgHom.id L (MvPolynomial (ℕ × Fin n) L)).toRingHom) ?_ ?_ rfl
  · ext r
    simp
  · intro x hx _
    have hxi : ¬ x.1 < i := not_lt.mpr (hv x hx)
    simp [actI, hxi]

theorem partialWeight_eq_torusWeight_of_lt (isVec : ℕ → Bool) (i : ℕ) {e : ℕ × Fin n →₀ ℕ} (h : ∀ x ∈ e.support, x.1 < i) :
    Finsupp.weight (wtI isVec i) e = Finsupp.weight (torusW isVec) e := by
  simp only [Finsupp.weight_apply]
  refine Finsupp.sum_congr (fun x hx => ?_)
  simp [wtI, h x hx]

theorem partialWeight_eq_zero_of_ge (isVec : ℕ → Bool) (i : ℕ) {e : ℕ × Fin n →₀ ℕ} (h : ∀ x ∈ e.support, i ≤ x.1) :
    Finsupp.weight (wtI (n := n) isVec i) e = 0 := by
  simp only [Finsupp.weight_apply]
  refine (Finsupp.sum_congr (g2 := fun _ _ => (0 : Fin n → ℤ)) (fun x hx => ?_)).trans (by simp)
  have hx' : ¬ x.1 < i := not_lt.mpr (h x hx)
  simp [wtI, hx']

theorem fullAct_pathWord_support_dominated (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (i : ℕ) (I' : ℤ → Finset (Fin n))
    (g : (Matrix (Fin n) (Fin n) L)ˣ) (hp : IsPath n isVec B μ i) (hI : IsIndex (μ i) I') :
    ∀ e ∈ (actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
        (psiPath L isVec μ i I')).support, DomLe (Finsupp.weight (torusW isVec) e) (μ i) := by
  intro e he
  refine (Top.factEV L n i isVec B μ I' g hp hI).1 _ ?_
  intro h0
  have h1 := congrArg (AddMonoidAlgebra.coeff · e) h0
  rw [coeff_weightedHomogeneousComponent, if_pos rfl] at h1
  exact (mem_support_iff.1 he) (by simpa using h1)

end basic

theorem restWord : RestWord := by
  classical
  intro L _ n N i isVec B μ I g gi hg hp hI hi e he
  rcases subsingleton_or_nontrivial L with hs | hnt
  · exfalso
    have h0 : actI isVec i g gi (psiPath L isVec μ N I) = 0 := Subsingleton.elim _ _
    rw [h0] at he
    simp at he
  have hpi : IsPath n isVec B μ i :=
    ⟨hp.1, fun j hj => hp.2.1 j (hj.trans hi), fun j hj => hp.2.2 j (lt_of_lt_of_le hj hi)⟩
  let gu : (Matrix (Fin n) (Fin n) L)ˣ := ⟨g, gi, hg, mul_eq_one_comm.1 hg⟩
  obtain ⟨F1, hF1⟩ := A3ev.exists_cols hp
  obtain ⟨F2, hF2⟩ := A3ev.exists_cols hpi
  obtain ⟨F, hF⟩ : ∃ F, F = F1 ∪ F2 := ⟨_, rfl⟩
  have hFN : A3ev.Cols isVec μ N F := fun c hc => hF1 c (fun h => hc (hF ▸ Finset.mem_union_left _ h))
  have hFi : A3ev.Cols isVec μ i F := fun c hc => hF2 c (fun h => hc (hF ▸ Finset.mem_union_right _ h))
  choose Q hQ1 hQ2 using fun c : ℤ => A0.trunc L n i isVec μ c N hi (I c)
  have hexp : psiPath L isVec μ N I = ∑ p ∈ F.pi (fun _ => (univ : Finset (Finset (Fin n)))),
      (∏ c ∈ F, pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) L)) i (A3ev.extF F p c)) *
        (∏ c ∈ F, Q c (A3ev.extF F p c)) := by
    rw [A3ev.psi_eq_prod L hFN hI, Finset.prod_congr rfl (fun c _ => hQ2 c), Finset.prod_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.prod_mul_distrib, ← Finset.prod_attach F]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [A3ev.extF, x.2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hexp, map_sum] at he
  obtain ⟨p, -, hpe⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum he)
  obtain ⟨I', hI'⟩ : ∃ I', I' = A3ev.extF F p := ⟨_, rfl⟩
  rw [← hI'] at hpe
  by_cases hidx : IsIndex (μ i) I'
  · have h1 : ∏ c ∈ F, pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) L)) i (I' c) =
        psiPath L isVec μ i I' := (A3ev.psi_eq_prod L hFi hidx).symm
    rw [h1, map_mul] at hpe
    have hv1 : ∀ x ∈ (psiPath L isVec μ i I').vars, x.1 < i := by
      refine DominanceOrderLemmas.vars_of_polB (N := i) (B := B) ?_
      rw [polB, Submodule.mem_iInf]
      intro j
      exact (pathProductDegrees L n i isVec B μ I' hpi hidx).2 j
    have hv2 : ∀ x ∈ (∏ c ∈ F, Q c (I' c)).vars, i ≤ x.1 := by
      intro x hx
      obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 (vars_prod _ hx)
      exact (mem_supported.1 (hQ1 c (I' c))) (Finset.mem_coe.2 hc)
    rw [partialAct_eq_fullAct_of_vars_lt _ _ _ _ hv1, partialAct_fix_of_vars_ge _ _ _ _ hv2] at hpe
    obtain ⟨e1, he1, e2, he2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hpe)
    have hw2 : Finsupp.weight (wtI (n := n) isVec i) e2 = 0 :=
      partialWeight_eq_zero_of_ge isVec i fun x hx => hv2 x ((mem_vars_iff_mem_support x).2 ⟨e2, he2, hx⟩)
    have hw1 : Finsupp.weight (wtI isVec i) e1 = Finsupp.weight (torusW isVec) e1 :=
      partialWeight_eq_torusWeight_of_lt isVec i fun x hx =>
        DominanceOrderLemmas.vars_act isVec g gi hv1 x ((mem_vars_iff_mem_support x).2 ⟨e1, he1, hx⟩)
    rw [map_add (f := _), hw2, add_zero, hw1]
    exact fullAct_pathWord_support_dominated isVec B μ i I' gu hpi hidx e1 he1
  · exfalso
    have hz : ∏ c ∈ F, pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) L)) i (I' c) = 0 := by
      obtain ⟨c, hc⟩ := not_forall.1 (show ¬ ∀ c : ℤ, (I' c).card =
        if 1 ≤ c then colHeight (μ i) c else n - colHeight (μ i) c from hidx)
      have hcF : c ∈ F := by
        by_contra hn
        apply hc
        have h1 : I' c = ∅ := by rw [hI']; exact dif_neg hn
        have h2 := A1hw.isIndex_can (μ i) c
        rw [(hFi c hn).2 _ (A1hw.isIndex_can (μ i))] at h2
        rw [h1]
        exact h2
      refine Finset.prod_eq_zero hcF ?_
      by_contra hne
      exact hc (A0.pathWord_card hpi c _ i le_rfl _ hne)
    rw [hz, zero_mul, map_zero] at hpe
    simp at hpe

open A3ev DominanceOrderLemmas in
theorem exists_dominant_top_weight_nonzero (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (c : PathIdx n N isVec B →₀ k) (x₁ : PathIdx n N isVec B) (hx₁ : x₁ ∈ c.support) :
    ∃ μ₀, Antitone μ₀ ∧ DomLe (x₁.1.1 N) μ₀ ∧
      evC k n isVec μ₀ (c.sum fun x a => a • psiPath k isVec x.1.1 N x.1.2) ≠ 0 := by
  classical
  have hEV : FactEV := Top.factEV
  have hT : (c.support.filter fun x => DomLe (x₁.1.1 N) (x.1.1 N)).Nonempty :=
    ⟨x₁, Finset.mem_filter.2 ⟨hx₁, domLe_refl _⟩⟩
  obtain ⟨x₀, hx₀, hmax⟩ := Finset.exists_max_image _
    (fun x : PathIdx n N isVec B => height (x.1.1 N)) hT
  rw [Finset.mem_filter] at hx₀
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, x₀.1.1 N = μ₀ := ⟨_, rfl⟩
  have hanti : Antitone μ₀ := hμ₀ ▸ x₀.2.1.2.1 N le_rfl
  have hd₀ : DomLe (x₁.1.1 N) μ₀ := hμ₀ ▸ hx₀.2
  refine ⟨μ₀, hanti, hd₀, fun h1 => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum] at h1
  simp_rw [map_smul] at h1
  have h2 : ∑ x ∈ c.support.filter (fun x => x.1.1 N = μ₀), c x • fam k x = 0 := by
    have h3 := Finset.sum_filter_of_ne (s := c.support)
      (p := fun x : PathIdx n N isVec B => x.1.1 N = μ₀)
      (f := fun x => c x • evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2)) ?_
    · rw [← h1, ← h3]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_filter] at hx
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1, ← hx.2, (ev_gen hEV k x.2.1 x.2.2.2.1).2]
      unfold fam
      rw [smul_eq_C_mul]
    · intro x hx hne
      have he : evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2) ≠ 0 :=
        fun h => hne (by rw [h, smul_zero])
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1] at he
      have hd : DomLe μ₀ (x.1.1 N) := (ev_gen hEV k x.2.1 x.2.2.2.1).1 μ₀ he
      refine domLe_eq hd ?_
      rw [← hμ₀]
      exact hmax x (Finset.mem_filter.2 ⟨hx, domLe_trans hd₀ hd⟩)
  exact (Finsupp.mem_support_iff.1 hx₀.1) (linearIndepOn_iff'.1 (fam_li fact_break k n N isVec B μ₀ hanti) _ c
    (fun x hx => (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2) h2 x₀
    (Finset.mem_filter.2 ⟨hx₀.1, hμ₀⟩))

theorem restTop : RestTop := by
  classical
  intro k _ n N isVec B pi G hpi hG hgood
  have hG' : G ∈ Submodule.span k
      (Set.range fun x : PathIdx n N isVec B => psiPath k isVec x.1.1 N x.1.2) := by
    rw [(Top.psiPath_basis n N isVec B k).2]
    exact hG
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hG'
  have key : ∀ x ∈ c.support, x.1.1 N ∈ pi := by
    intro x hx
    obtain ⟨μ₀, ha, hd, hne⟩ := exists_dominant_top_weight_nonzero k n N isVec B c x hx
    rw [hc] at hne
    have hne' : weightedHomogeneousComponent (torusW isVec) μ₀
        (actAll isVec (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
          (map (algebraMap k (GenField k n)) G)) ≠ 0 := hne
    obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.1 hne'
    rw [coeff_weightedHomogeneousComponent] at he
    split_ifs at he with hw
    · have hvG : ∀ y ∈ (map (algebraMap k (GenField k n)) G).vars, y.1 < N :=
        fun y hy => DominanceOrderLemmas.vars_of_polB hG y (vars_map G (algebraMap k (GenField k n)) hy)
      have hmem : e ∈ (actI isVec N (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
          (map (algebraMap k (GenField k n)) G)).support := by
        rw [partialAct_eq_fullAct_of_vars_lt _ _ _ _ hvG]
        exact mem_support_iff.2 he
      have hwt : Finsupp.weight (wtI isVec N) e = μ₀ := by
        rw [partialWeight_eq_torusWeight_of_lt]
        · exact hw
        · intro y hy
          exact DominanceOrderLemmas.vars_act isVec _ _ hvG y ((mem_vars_iff_mem_support y).2 ⟨e, mem_support_iff.2 he, hy⟩)
      have h3 := hgood e hmem (by rw [hwt]; exact ha)
      rw [hwt] at h3
      exact hpi μ₀ h3 _ (x.2.1.2.1 N le_rfl) hd
    · exact absurd rfl he
  rw [← hc]
  exact Submodule.sum_mem _ fun x hx =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, key x hx, rfl⟩)

end Formalism.MainNotions.G.ColumnFamilies
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.TorusComponentMemDominatedWeightPolynomials
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)
  (Pr : (Fin n → ℤ) → Prop)

def dominatedWeightPolynomials : Submodule R (MvPolynomial (ι × Fin n) R) where
  carrier := {y | ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1),
    g0 * g0inv = 1 → ∀ m ∈ (matrixSubst LL S φ g0inv g0 y).support, Pr (wtS LL S m)}
  zero_mem' := by
    intro k1 _ φ g0 g0inv _ m hm
    simp at hm
  add_mem' := by
    classical
    intro x y hx hy k1 _ φ g0 g0inv h m hm
    rw [map_add (f := _)] at hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h1 | h1
    · exact hx k1 φ g0 g0inv h m h1
    · exact hy k1 φ g0 g0inv h m h1
  smul_mem' := by
    intro c y hy k1 _ φ g0 g0inv h m hm
    rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, ← MvPolynomial.smul_eq_C_mul] at hm
    exact hy k1 φ g0 g0inv h m (MvPolynomial.support_smul hm)

theorem laurentCoeff_mem_dominatedWeightPolynomials (y : MvPolynomial (ι × Fin n) R) (K : Finset ℤ) (yk : ℤ → MvPolynomial (ι × Fin n) R)
    (hh : ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1), ∃ h h' : Matrix (Fin n) (Fin n) (LaurentPolynomial k1),
      h' * h = 1 ∧ matrixSubst LL S (LaurentPolynomial.C.comp φ) h h' y =
        ∑ k ∈ K, C (LaurentPolynomial.T k) * MvPolynomial.map (LaurentPolynomial.C.comp φ) (yk k))
    (hy : y ∈ dominatedWeightPolynomials LL S Pr) : ∀ k ∈ K, yk k ∈ dominatedWeightPolynomials LL S Pr := by
  classical
  intro k0 hk0 k1 _ φ g0 g0inv hg m hm
  obtain ⟨h, h', hh1, hh2⟩ := hh k1 φ
  set ψ : k1 →+* LaurentPolynomial k1 := LaurentPolynomial.C with hψ
  have hone : (h' * g0.map ψ) * (g0inv.map ψ * h) = 1 := by
    have : g0.map ψ * g0inv.map ψ = 1 := by
      rw [← Matrix.map_mul, hg]; simp
    calc (h' * g0.map ψ) * (g0inv.map ψ * h) = h' * (g0.map ψ * g0inv.map ψ) * h := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [this, Matrix.mul_one, hh1]
  refine hy (LaurentPolynomial k1) (ψ.comp φ) (h' * g0.map ψ) (g0inv.map ψ * h) hone m ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← matrixSubst_comp, hh2, map_sum]
  have h1 : ∀ k, matrixSubst LL S (RingHom.id _) (g0inv.map ψ) (g0.map ψ)
      (C (LaurentPolynomial.T k) * MvPolynomial.map (ψ.comp φ) (yk k)) =
      C (LaurentPolynomial.T k) * MvPolynomial.map ψ (matrixSubst LL S φ g0inv g0 (yk k)) := by
    intro k
    rw [map_mul, matrixSubst_C, RingHom.id_apply, matrixSubst_map, map_matrixSubst]
  simp only [h1]
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum]
  intro h0
  have h2 := congrArg (fun f : LaurentPolynomial k1 => f.coeff k0) h0
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at h2
  have h3 : ∀ k, (LaurentPolynomial.T k * ψ (AddMonoidAlgebra.coeff (matrixSubst LL S φ g0inv g0 (yk k)) m)) =
      AddMonoidAlgebra.single k (AddMonoidAlgebra.coeff (matrixSubst LL S φ g0inv g0 (yk k)) m) := by
    intro k
    rw [LaurentPolynomial.single_eq_C_mul_T, mul_comm]
  simp only [h3, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
  rw [Finset.sum_ite_eq' K k0] at h2
  rw [if_pos hk0] at h2
  exact (MvPolynomial.mem_support_iff.1 hm) h2

theorem dividedPower_mem_dominatedWeightPolynomials (hT : TransvectionExpansion) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ dominatedWeightPolynomials LL S Pr) : divPow R LL S a b k y ∈ dominatedWeightPolynomials LL S Pr := by
  classical
  have := laurentCoeff_mem_dominatedWeightPolynomials LL S Pr y ((Finset.range (y.totalDegree + k + 1)).map Nat.castEmbedding)
    (fun z => divPow R LL S a b z.toNat y) ?_ hy (k : ℤ) ?_
  · simpa using this
  · intro k1 _ φ
    refine ⟨Matrix.transvection a b (LaurentPolynomial.T 1), Matrix.transvection a b (-LaurentPolynomial.T 1), ?_, ?_⟩
    · rw [Matrix.transvection_mul_transvection_same a b hab]; simp
    · rw [hT R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) a b hab (LaurentPolynomial.T 1) y
        (y.totalDegree + k + 1) (by omega), Finset.sum_map]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [LaurentPolynomial.T_pow]
  · simp only [Finset.mem_map, Finset.mem_range]
    exact ⟨k, by omega, rfl⟩

theorem torusComponent_mem_dominatedWeightPolynomials (hTo : TorusActsThroughWeight) (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ dominatedWeightPolynomials LL S Pr) : weightEntryComponent LL S a w y ∈ dominatedWeightPolynomials LL S Pr := by
  classical
  by_cases hw : w ∈ y.support.image (fun m => wtS LL S m a)
  · refine laurentCoeff_mem_dominatedWeightPolynomials LL S Pr y (y.support.image (fun m => wtS LL S m a)) (fun z => weightEntryComponent LL S a z y) ?_ hy w hw
    intro k1 _ φ
    set D : Fin n → (LaurentPolynomial k1)ˣ := fun c => if c = a then laurentUnit k1 else 1 with hD
    refine ⟨Matrix.diagonal fun c => ((D c : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1),
      Matrix.diagonal fun c => (((D c)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1), ?_, ?_⟩
    · rw [Matrix.diagonal_mul_diagonal]
      simp
    · have hprod : ∀ m : ι × Fin n →₀ ℕ, ((∏ c, D c ^ (wtS LL S m c) : (LaurentPolynomial k1)ˣ) :
          LaurentPolynomial k1) = LaurentPolynomial.T (wtS LL S m a) := by
        intro m
        rw [← laurentUnit_zpow]
        congr 1
        rw [Finset.prod_eq_single a]
        · simp [hD]
        · intro c _ hc; simp [hD, hc]
        · intro h; exact absurd (Finset.mem_univ a) h
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [y.as_sum, map_sum]
      rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := y.support.image (fun m => wtS LL S m a))
        (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image_of_mem _ hm)]
      refine Finset.sum_congr rfl fun z _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [weightEntryComponent, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [hTo R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) D m (y.coeff m), hprod,
        (Finset.mem_filter.1 hm).2, MvPolynomial.map_monomial, MvPolynomial.C_mul_monomial, mul_comm]
  · have : weightEntryComponent LL S a w y = 0 := by
      rw [weightEntryComponent]
      apply Finset.sum_eq_zero
      intro m hm
      exact absurd (Finset.mem_image.2 ⟨m, (Finset.mem_filter.1 hm).1, (Finset.mem_filter.1 hm).2⟩) hw
    rw [this]; exact Submodule.zero_mem _

theorem binomialPol_mem_dominatedWeightPolynomials (hTo : TorusActsThroughWeight) (a : Fin n) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ dominatedWeightPolynomials LL S Pr) : binomPol R LL S a k y ∈ dominatedWeightPolynomials LL S Pr := by
  classical
  have : binomPol R LL S a k y = ∑ z ∈ y.support.image (fun m => wtS LL S m a),
      (((Ring.choose z k : ℤ) : R)) • weightEntryComponent LL S a z y := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [y.as_sum, map_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := y.support.image (fun m => wtS LL S m a))
        (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image_of_mem _ hm)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [weightEntryComponent, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [binomialOperator_monomial, (Finset.mem_filter.1 hm).2, MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (torusComponent_mem_dominatedWeightPolynomials LL S Pr hTo a z y hy)

end fwd

theorem restFwd : RestFwd := by
  classical
  intro R _ ι _ LL n S Pr G hG
  have hGN : G ∈ dominatedWeightPolynomials LL S Pr := hG
  have hstab : ∀ u ∈ Submonoid.closure (polUZgens R LL S), ∀ y ∈ dominatedWeightPolynomials LL S Pr, u y ∈ dominatedWeightPolynomials LL S Pr := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu =>
      intro y hy
      rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
      · exact dividedPower_mem_dominatedWeightPolynomials LL S Pr transvectionExpansion a b hab k y hy
      · exact binomialPol_mem_dominatedWeightPolynomials LL S Pr torus_acts_through_weight a k y hy
    | one => intro y hy; exact hy
    | mul u v _ _ hu hv => intro y hy; exact hu _ (hv y hy)
  have hW : polGenSub R LL S G ≤ dominatedWeightPolynomials LL S Pr := by
    rw [polGenSub, Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact hstab u hu G hGN
  rintro mu ⟨x, hx, hx0, hmu⟩
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hx0
  have := hW hx R (RingHom.id R) 1 1 (by simp) m (by rw [matrixSubst_one, MvPolynomial.map_id]; exact hm)
  rw [hmu m hm] at this
  exact this

theorem restAct : RestAct := by
  classical
  intro R B' _ _ N n i LL φ m m' G
  have : ((rename (iv N n) : MvPolynomial (Fin N × Fin n) B' →ₐ[B'] MvPolynomial (ℕ × Fin n) B').toRingHom.comp
        (matrixSubst LL {j : Fin N | j.val < i} φ m m')) =
      ((actI (isV LL) i m m').toRingHom.comp ((MvPolynomial.map φ).comp
        (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toRingHom)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [matrixSubst_C, actI]
    · rintro ⟨l, a⟩
      have hv : isV LL l.val = LL.vec l := by simp [isV, l.2]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, matrixSubst_X, rename_X, map_X, actI,
        aeval_X, iv, Set.mem_ofPred_eq, hv]
      by_cases hS : l.val < i
      · by_cases hvec : LL.vec l = true
        set_option synthInstance.maxHeartbeats 100000 in
          · simp only [if_pos hS, if_pos hvec, map_sum, map_mul, rename_C, rename_X, iv]
            exact Finset.sum_congr rfl fun b _ => mul_comm _ _
        set_option synthInstance.maxHeartbeats 100000 in
          · simp only [if_pos hS, if_neg hvec, map_sum, map_mul, rename_C, rename_X, iv]
            exact Finset.sum_congr rfl fun b _ => mul_comm _ _
      · simp only [if_neg hS, rename_X, iv]
  exact congrArg (fun f => f G) this

theorem monomialWeight_eq_letterWeight {N n : ℕ} (LL : Letters (Fin N)) (i : ℕ) (m : Fin N × Fin n →₀ ℕ) :
    Finsupp.weight (wtI (isV LL) i) (m.mapDomain (iv N n)) = wtS LL {j : Fin N | j.val < i} m := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun x c => c • wtI (isV LL) i x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext a
  rw [Finsupp.sum_fintype m (fun x c => c • wtI (isV LL) i (iv N n x)) (fun _ => zero_smul _ _), Finset.sum_apply,
    Fintype.sum_prod_type, wtS]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hv : isV LL l.val = LL.vec l := by simp [isV, l.2]
  simp only [Pi.smul_apply, wtI, iv, Set.mem_ofPred_eq, Formalism.InvariantFactorPaths.GelfandTsetlinBases.torusW, hv]
  by_cases hS : l.val < i
  · by_cases hvec : LL.vec l = true
    · simp only [if_pos hS, if_pos hvec]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ a) h
    · simp only [if_pos hS, if_neg hvec]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ a) h
  · simp [if_neg hS]

theorem dominanceOrder_iff {n : ℕ} (nu mu : Fin n → ℤ) : DomLE nu mu ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.DomLe nu mu := by
  classical
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun j => ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · by_cases hjn : j ≤ n
      · have e : (univ.filter fun m : Fin n => m.val < j) = univ.filter (· ≤ (⟨j - 1, by omega⟩ : Fin n)) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
          omega
        rw [e]
        exact h1 _
      · have e : (univ.filter fun m : Fin n => m.val < j) = univ := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          have := m.2
          omega
        rw [e, h2]
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, h1⟩
    have e : (univ.filter (· ≤ a)) = univ.filter fun m : Fin n => m.val < a.val + 1 := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
      omega
    rw [e]
    exact h2 _

theorem standardWord_monomial_weight_dominated (hW : RestWord) (F : Type) [Field F] {N n : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ}
    (i : Fin (N + 1)) (P : PPath n N LL B) (I : ℤ → Finset (Fin n)) (hI : IsSt P.mu I)
    (k1 : Type) [CommRing k1] (φ : F →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1) (hg : g0 * g0inv = 1)
    (m : Fin N × Fin n →₀ ℕ)
    (hm : m ∈ (matrixSubst LL {j : Fin N | j.val < i.val} φ g0inv g0 (Psi F P.mu I)).support) :
    DomLE (wtS LL {j : Fin N | j.val < i.val} m) (P.mu i) := by
  classical
  have hidx : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I := ((restStd n N P.mu I).1 hI).1
  have hidx' : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (ext P.mu N) I := by rw [ext_last]; exact hidx
  have hpath := restPathTo n N LL B P
  have h1 := hW k1 n N i.val (isV LL) (Bn B) (ext P.mu) I g0inv g0 (mul_eq_one_comm.1 hg) hpath hidx'
    (Nat.lt_succ_iff.1 i.2) (m.mapDomain (iv N n)) ?_
  · rw [monomialWeight_eq_letterWeight, ext_val] at h1
    exact (dominanceOrder_iff _ _).2 h1
  · rw [← Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.map_psi φ hpath hidx', ← restPsi F n N LL B P I hidx,
      ← restAct F k1 N n i.val LL φ g0inv g0, MvPolynomial.mem_support_iff,
      MvPolynomial.coeff_rename_mapDomain _ (iv_inj N n)]
    exact MvPolynomial.mem_support_iff.1 hm

theorem firstLettersLowerSet_of_restWord_restOne (D : Formalism.BasicNotions.D7) (hW : RestWord) (hO : RestOne) : Formalism.MainNotions.CovariantDegrees.FirstLettersLowerSet D := by
  classical
  intro F _ N n LL B i pi hpi G hG
  have hLow : LowerC pi := fun μ hμ ν hν hd => hpi.2 μ hμ ν hν ((dominanceOrder_iff ν μ).2 hd)
  constructor
  · intro hGs mu hmu hdom
    have key := restFwd F (Fin N) LL n {j : Fin N | j.val < i.val} (fun mu => ∃ ν ∈ pi, DomLE mu ν) G ?_ mu hmu
    · obtain ⟨ν, hν, hd⟩ := key
      exact hpi.2 ν hν mu hdom hd
    · intro k1 _ φ g0 g0inv hg
      refine Submodule.span_induction
        (p := fun x _ => ∀ m ∈ (matrixSubst LL {j : Fin N | j.val < i.val} φ g0inv g0 x).support,
          ∃ ν ∈ pi, DomLE (wtS LL {j : Fin N | j.val < i.val} m) ν) ?_ ?_ ?_ ?_ hGs
      · rintro x ⟨P, I, hI, hPi, rfl⟩ m hm
        exact ⟨P.mu i, hPi, standardWord_monomial_weight_dominated hW F i P I hI k1 φ g0 g0inv hg m hm⟩
      · intro m hm
        simp at hm
      · intro x y _ _ hx hy m hm
        rw [map_add (f := _)] at hm
        rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h1 | h1
        · exact hx m h1
        · exact hy m h1
      · intro c x _ hx m hm
        rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, ← MvPolynomial.smul_eq_C_mul] at hm
        exact hx m (MvPolynomial.support_smul hm)
  · intro H
    have hGood : GoodC F (isV LL) i.val pi (rename (iv N n) G) := by
      intro e he hanti
      rw [← restAct F (Formalism.InvariantFactorPaths.GelfandTsetlinBases.GenField F n) N n i.val LL (algebraMap F (Formalism.InvariantFactorPaths.GelfandTsetlinBases.GenField F n))
        (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat F n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat F n)⁻¹ G,
        MvPolynomial.support_rename_of_injective (iv_inj N n)] at he
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 he
      rw [monomialWeight_eq_letterWeight] at hanti ⊢
      have hm' := generic_monomials_specialise F (Fin N) LL n {j : Fin N | j.val < i.val} (Formalism.InvariantFactorPaths.GelfandTsetlinBases.GenField F n)
        (algebraMap F (Formalism.InvariantFactorPaths.GelfandTsetlinBases.GenField F n)) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat F n)⁻¹ (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat F n)
        (Matrix.nonsing_inv_mul _ Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.genMat_isUnit) G hm
      exact H _ (generic_translate_weights_mem LL _ transvectionExpansion torus_acts_through_weight binomial_stable_contains_components G m hm') hanti
    have hmem : rename (iv N n) G ∈ Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB F n N (Bn B) := by
      rw [← restPol F n N B]
      exact Submodule.mem_map_of_mem hG
    have h1 := hO F n N i.val (isV LL) (Bn B) pi (rename (iv N n) G) hLow (Nat.lt_succ_iff.1 i.2) hmem hGood
    set f : MvPolynomial (Fin N × Fin n) F →ₗ[F] MvPolynomial (ℕ × Fin n) F :=
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) F →ₐ[F] MvPolynomial (ℕ × Fin n) F).toLinearMap with hf
    have hinj : Function.Injective f := rename_injective _ (iv_inj N n)
    set T : Set (MvPolynomial (Fin N × Fin n) F) := {H | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n),
      IsSt P.mu I ∧ P.mu i ∈ pi ∧ H = Psi F P.mu I} with hT
    have hle : Submodule.span F (Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiFam F n N (isV LL) (Bn B) '' {x | x.1.1 i.val ∈ pi}) ≤
        (Submodule.span F T).map f := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, rfl⟩ := (e17 restPathTo restPathFrom restStd n N LL B).surjective y
      refine ⟨Psi F x.1.1.mu x.1.2, Submodule.subset_span ⟨x.1.1, x.1.2, x.2, ?_, rfl⟩,
        rename_Psi restPathTo restPathFrom restStd restPsi F x⟩
      have hy' : ext x.1.1.mu i.val ∈ pi := hy
      rwa [ext_val] at hy'
    obtain ⟨G', hG', hGG⟩ := hle h1
    rw [← hinj hGG]
    exact hG'

end Formalism.MainNotions.G.ColumnFamilies
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.CardPathIndexWeightMemEqMulChoose
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {n : ℕ}

def PathsWithInitialLettersEndingIn (n i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ)) : Type :=
  {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ i ∧ (∀ j, i < j → μ j = 0) ∧ (μ i) ∈ pi}

def pathIndexSplitEquiv {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ)) :
    {x : PathIdx n N isVec B // (x.1.1 i) ∈ pi} ≃
      Σ P : PathsWithInitialLettersEndingIn n i isVec B pi, {x // ExponentSetCounting.ContP i N isVec B (P.1 i) x} where
  toFun x := ⟨⟨fun j => if j ≤ i then x.1.1.1 j else 0, by
      obtain ⟨⟨⟨μ, I⟩, ⟨h0, h1, h2⟩, h3, h4⟩, hg⟩ := x
      refine ⟨⟨by simpa using h0, ?_, ?_⟩, ?_, by simpa using hg⟩
      · intro j hj
        simpa [hj] using h1 j (hj.trans hi)
      · intro j hj
        have e1 : j ≤ i := by omega
        have e2 : j + 1 ≤ i := by omega
        simpa [e1, e2] using h2 j (by omega)
      · intro j hj
        have e1 : ¬ j ≤ i := by omega
        simp [e1]⟩,
    ⟨(fun j => if i ≤ j then x.1.1.1 j else 0, x.1.1.2), by
      obtain ⟨⟨⟨μ, I⟩, ⟨h0, h1, h2⟩, h3, h4⟩, hg⟩ := x
      refine ⟨by simp, ?_, ?_, by simpa [hi] using h4⟩
      · intro j hj
        by_cases e1 : i ≤ j
        · simpa [e1] using h3 j (by omega)
        · simp [e1]
      · intro j e1 hj
        have e2 : i ≤ j + 1 := by omega
        simpa [e1, e2] using h2 j hj⟩⟩
  invFun y := ⟨⟨(fun j => if j ≤ i then y.1.1 j else y.2.1.1 j, y.2.1.2), by
      obtain ⟨⟨μ, ⟨h0, h1, h2⟩, h3, hg⟩, ⟨⟨ν, I⟩, c0, c1, c2, c3⟩⟩ := y
      simp only at c0 c1 c2 c3 ⊢
      have key : ∀ j, i ≤ j → (if j ≤ i then μ j else ν j) = ν j := by
        intro j hj
        by_cases e : j ≤ i
        · obtain rfl : j = i := by omega
          simp [c0]
        · simp [e]
      have hr : ∀ j < N, if isVec j then
            Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip (if j + 1 ≤ i then μ (j + 1) else ν (j + 1)) (if j ≤ i then μ j else ν j) (B j)
          else Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip (if j ≤ i then μ j else ν j) (if j + 1 ≤ i then μ (j + 1) else ν (j + 1)) (B j) := by
        intro j hj
        by_cases e : j < i
        · have e1 : j ≤ i := by omega
          have e2 : j + 1 ≤ i := by omega
          simpa [e1, e2] using h2 j e
        · rw [key j (by omega), key (j + 1) (by omega)]
          exact c2 j (by omega) hj
      have h00 : (if 0 ≤ i then μ 0 else ν 0) = 0 := by simpa using h0
      refine ⟨⟨h00, ?_, hr⟩, ?_, ?_⟩
      · exact Count.antitone_of_rules (μ := fun j => if j ≤ i then μ j else ν j)
          (by rw [h00]; exact fun _ _ _ => le_rfl) hr
      · intro j hj
        rw [key j (by omega)]
        exact c1 j (Or.inr hj)
      · rw [key N hi]
        exact c3⟩, by
      simpa using y.1.2.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases e : j ≤ i
      · simp [e]
      · have e' : i ≤ j := by omega
        simp [e, e']
    · rfl
  right_inv y := by
    obtain ⟨⟨μ, ⟨h0, h1, h2⟩, h3, hg⟩, ⟨⟨ν, I⟩, c0, c1, c2, c3⟩⟩ := y
    simp only at c0 c1 c2 c3
    apply Sigma.subtype_ext
    · apply Subtype.ext
      funext j
      by_cases e : j ≤ i
      · simp [e]
      · simp [e, h3 j (by omega)]
    · apply Prod.ext
      · funext j
        by_cases e : i ≤ j
        · by_cases e' : j ≤ i
          · obtain rfl : j = i := by omega
            simp [c0]
          · simp [e, e']
        · simp [e, c1 j (Or.inl (by omega))]
      · rfl

theorem card_pathIndex_weight_mem_eq_mul_choose (hC : CountCont) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ)) :
    Nat.card {x : PathIdx n N isVec B // (x.1.1 i) ∈ pi} =
      Nat.card {x : PathIdx n i isVec B // (x.1.1 i) ∈ pi} *
        ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  set c : ℕ := ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) with hc
  have e : ∀ P : PathsWithInitialLettersEndingIn n i isVec B pi,
      Nonempty ({x // ExponentSetCounting.ContP i N isVec B (P.1 i) x} ≃ {x // ExponentSetCounting.ContP i i isVec B (P.1 i) x} × Fin c) := by
    intro P
    have hP : Antitone (P.1 i) := P.2.1.2.1 i le_rfl
    obtain ⟨f1, c1⟩ := hC n i N isVec B (P.1 i) hi hP
    obtain ⟨f2, c2⟩ := hC n i i isVec B (P.1 i) le_rfl hP
    have f1' : Finite {x // ExponentSetCounting.ContP i N isVec B (P.1 i) x} := f1
    have f2' : Finite {x // ExponentSetCounting.ContP i i isVec B (P.1 i) x} := f2
    have c1' : Nat.card {x // ExponentSetCounting.ContP i N isVec B (P.1 i) x} = dGT n (P.1 i) * c := c1
    have c2' : Nat.card {x // ExponentSetCounting.ContP i i isVec B (P.1 i) x} = dGT n (P.1 i) := by
      have : Nat.card {x // ExponentSetCounting.ContP i i isVec B (P.1 i) x} = _ := c2
      simpa using this
    apply Finite.card_eq.1
    rw [Nat.card_prod, c1', c2', Nat.card_fin]
  rw [Nat.card_congr (pathIndexSplitEquiv hi isVec B pi),
    Nat.card_congr (Equiv.sigmaCongrRight fun P => (e P).some),
    ← Nat.card_congr (Equiv.sigmaProdDistrib _ _), Nat.card_prod, Nat.card_fin,
    ← Nat.card_congr (pathIndexSplitEquiv le_rfl isVec B pi)]

theorem standardWordFamily_satisfies_condition (hW : RestWord) (k : Type) [Field k] {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (pi : Set (Fin n → ℤ)) (hpi : LowerC pi) (x : PathIdx n N isVec B) (hx : x.1.1 i ∈ pi) :
    GoodC k isVec i pi (psiFam k n N isVec B x) := by
  intro e he ha
  rw [psiFam, A3ev.map_psi (algebraMap k (GenField k n)) x.2.1 x.2.2.2.1] at he
  exact hpi _ hx _ ha (hW (GenField k n) n N i isVec B x.1.1 x.1.2 _ _
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (A3ev.genMat_det_ne k n))) x.2.1 x.2.2.2.1 hi e he)

def pathExponentMonomial (k : Type) [Field k] (n i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ))
    (p : {x : PathIdx n i isVec B // x.1.1 i ∈ pi} × ExponentSetCounting.expSet n i N B) : MvPolynomial (ℕ × Fin n) k :=
  psiFam k n i isVec B p.1.1 * monomial p.2.1 1

theorem mem_span_wordMonomialProducts (hT : RestTop) (hF : RestSplit) (k : Type) [Field k] {i N : ℕ} (hi : i ≤ N)
    (isVec : ℕ → Bool) (B : ℕ → ℕ) (pi : Set (Fin n → ℤ)) (hpi : LowerC pi) (G : MvPolynomial (ℕ × Fin n) k)
    (hG : G ∈ polB k n N B) (hg : GoodC k isVec i pi G) :
    G ∈ Submodule.span k (Set.range (pathExponentMonomial k n i N isVec B pi)) := by
  obtain ⟨T, Gc, h1, h2, h3, h4⟩ := hF k n N i isVec B pi G hi hG
  rw [h3]
  refine Submodule.sum_mem _ fun β hβ => ?_
  have hm := hT k n i isVec B pi (Gc β) hpi (h2 β hβ) (h4 hg β hβ)
  have hle : Submodule.map (LinearMap.mulRight k (monomial β (1 : k)))
      (Submodule.span k (psiFam k n i isVec B '' {x | x.1.1 i ∈ pi})) ≤
      Submodule.span k (Set.range (pathExponentMonomial k n i N isVec B pi)) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨(⟨x, hx⟩, ⟨β, h1 β hβ⟩), rfl⟩
  exact hle (Submodule.mem_map_of_mem (f := LinearMap.mulRight k (monomial β (1 : k))) hm)

theorem restOne_of (hW : RestWord) (hT : RestTop) (hF : RestSplit) : RestOne := by
  intro k _ n N i isVec B pi G hpi hi hG hg
  have hI : LemmaA2indep := Top.lemmaA2indep
  have hR : PolBRank := Top.polBRank
  have hC : CountCont := Top.countCont
  have : Finite (PathIdx n N isVec B) := Top.pathIdxFinite n N isVec B
  have : Finite (PathIdx n i isVec B) := Top.pathIdxFinite n i isVec B
  have : Finite (ExponentSetCounting.expSet n i N B) := (ExponentSetCounting.expSet_finite hR n i N B).to_subtype
  let _ := Fintype.ofFinite {x : PathIdx n N isVec B // x.1.1 i ∈ pi}
  let _ := Fintype.ofFinite ({x : PathIdx n i isVec B // x.1.1 i ∈ pi} × ExponentSetCounting.expSet n i N B)
  set U := Submodule.span k (Set.range fun x : {x : PathIdx n N isVec B // x.1.1 i ∈ pi} =>
    psiFam k n N isVec B x.1) with hU
  set W := Submodule.span k (Set.range (pathExponentMonomial k n i N isVec B pi)) with hWd
  have hUW : U ≤ W := by
    rw [hU, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact mem_span_wordMonomialProducts hT hF k hi isVec B pi hpi _ (ExponentSetCounting.psiFam_mem k N isVec B x.1)
      (standardWordFamily_satisfies_condition hW k hi isVec B pi hpi x.1 x.2)
  have hli : LinearIndependent k (fun x : {x : PathIdx n N isVec B // x.1.1 i ∈ pi} =>
      psiFam k n N isVec B x.1) := (hI k n N isVec B).comp Subtype.val Subtype.val_injective
  have dU : Module.finrank k U = Fintype.card {x : PathIdx n N isVec B // x.1.1 i ∈ pi} :=
    finrank_span_eq_card hli
  have dW : Module.finrank k W ≤
      Fintype.card ({x : PathIdx n i isVec B // x.1.1 i ∈ pi} × ExponentSetCounting.expSet n i N B) :=
    finrank_range_le_card _
  have : FiniteDimensional k W := FiniteDimensional.span_of_finite k (Set.finite_range _)
  have hEq : U = W := Submodule.eq_of_le_of_finrank_le hUW (by
    rw [dU]
    refine dW.trans ?_
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod, card_pathIndex_weight_mem_eq_mul_choose hC hi]
    exact Nat.mul_le_mul_left _ (by rw [Nat.card_coe_set_eq]; exact ExponentSetCounting.expSet_card hR n i N B))
  have hGW : G ∈ W := mem_span_wordMonomialProducts hT hF k hi isVec B pi hpi G hG hg
  rw [← hEq, hU] at hGW
  rw [Set.image_eq_range]
  exact hGW

theorem partialAction_X {L : Type*} [CommRing L] (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    (x : ℕ × Fin n) :
    actI isVec i g gi (X x) = if x.1 < i then
      (if isVec x.1 then ∑ b, X (x.1, b) * C (g b x.2) else ∑ b, X (x.1, b) * C (gi x.2 b)) else X x := by
  unfold actI
  rw [aeval_X]

theorem partialAction_eq_fullAction_of_vars_lt {L : Type*} [CommRing L] (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < i) :
    actI isVec i g gi P = actAll isVec g gi P := by
  have h : (actI isVec i g gi).toRingHom P = (actAll isVec g gi).toRingHom P := by
    refine hom_congr_vars ?_ ?_ rfl
    · ext c
      simp
    · rintro ⟨j, a⟩ hx -
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [partialAction_X, DominanceOrderLemmas.actAll_X, if_pos (hv _ hx)]
  exact h

theorem partialAction_monomial_later_letters {L : Type*} [CommRing L] (isVec : ℕ → Bool) (i : ℕ) (g gi : Matrix (Fin n) (Fin n) L)
    (β : ℕ × Fin n →₀ ℕ) (hβ : ∀ x : ℕ × Fin n, x.1 < i → β x = 0) :
    actI isVec i g gi (monomial β 1) = monomial β 1 := by
  unfold actI
  rw [aeval_monomial, monomial_eq, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun x hx => ?_
  have : ¬ x.1 < i := fun h => (Finsupp.mem_support_iff.1 hx) (hβ x h)
  rw [if_neg this]

theorem restSplit : RestSplit := by
  classical
  intro k _ n N i isVec B pi G hi hG
  obtain ⟨T, Gc, h1, h2, h3, -⟩ := Top.factSplit k n N i isVec B ⊥ ⊤ G hi hG
  refine ⟨T, Gc, h1, h2, h3, ?_⟩
  intro hg β₀ hβ₀ e he ha
  have hlow : ∀ β ∈ T, ∀ x : ℕ × Fin n, x.1 < i → β x = 0 := by
    intro β hβ x hx
    have h0 := h1 β hβ x.1
    rw [if_neg (by omega)] at h0
    exact (Finset.sum_eq_zero_iff.1 h0) x.2 (Finset.mem_univ _)
  have hexp : actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) G) =
      ∑ β ∈ T, actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) (Gc β)) * monomial β 1 := by
    conv_lhs => rw [h3]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [map_mul, map_mul, map_monomial, map_one, partialAction_monomial_later_letters _ _ _ _ β (hlow β hβ)]
  have hvars : ∀ β ∈ T, ∀ d ∈ (actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) (Gc β))).support, ∀ x : ℕ × Fin n, i ≤ x.1 → d x = 0 := by
    intro β hβ d hd x hx
    by_contra hne
    have hv0 : ∀ y ∈ (map (algebraMap k (GenField k n)) (Gc β)).vars, y.1 < i :=
      fun y hy => DominanceOrderLemmas.vars_of_polB (h2 β hβ) y (vars_map (Gc β) (algebraMap k (GenField k n)) hy)
    rw [partialAction_eq_fullAction_of_vars_lt _ _ _ _ hv0] at hd
    have := DominanceOrderLemmas.vars_act isVec (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹ hv0 x
      ((mem_vars_iff_mem_support (i := x)).2 ⟨d, hd, Finsupp.mem_support_iff.2 hne⟩)
    omega
  have hcoef : AddMonoidAlgebra.coeff (actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) G)) (e + β₀) =
      AddMonoidAlgebra.coeff (actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) (Gc β₀))) e := by
    rw [hexp, coeff_sum, Finset.sum_eq_single β₀]
    · rw [coeff_mul_monomial, mul_one]
    · intro β hβ hne
      rw [coeff_mul_monomial']
      split_ifs with hle
      · rw [mul_one]
        by_contra hc
        apply hne
        have hz := hvars β hβ (e + β₀ - β) (mem_support_iff.2 hc)
        ext x
        by_cases hx : x.1 < i
        · rw [hlow β hβ x hx, hlow β₀ hβ₀ x hx]
        · have e0 := hvars β₀ hβ₀ e he x (by omega)
          have a1 := hz x (by omega)
          have a2 := hle x
          simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply] at a1 a2
          omega
      · rfl
    · intro h
      exact absurd hβ₀ h
  have hmem : e + β₀ ∈ (actI isVec i (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat k n)⁻¹
        (map (algebraMap k (GenField k n)) G)).support := by
    rw [mem_support_iff, hcoef]
    exact mem_support_iff.1 he
  have hw : Finsupp.weight (wtI isVec i) (e + β₀) = Finsupp.weight (wtI isVec i) e := by
    have h0 : Finsupp.weight (wtI (n := n) isVec i) β₀ = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum]
      refine Finset.sum_eq_zero fun x hx => ?_
      have : ¬ x.1 < i := fun h => (Finsupp.mem_support_iff.1 hx) (hlow β₀ hβ₀ x h)
      simp [wtI, this]
    rw [map_add (f := _), h0, add_zero]
  have hfin := hg (e + β₀) hmem (by rw [hw]; exact ha)
  rwa [hw] at hfin

end Formalism.MainNotions.G.ColumnFamilies
end
end

namespace Formalism.MainNotions.G.ColumnFamilies

theorem restOne : RestOne := restOne_of restWord restTop restSplit

theorem admissible_word_basis (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.FirstLettersLowerSet D := firstLettersLowerSet_of_restWord_restOne D restWord restOne

end Formalism.MainNotions.G.ColumnFamilies
