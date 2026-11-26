module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv

noncomputable section

namespace Comb

def alternantPsum (m : ℕ) (ρ : List ℕ) : MvPolynomial (Fin m) ℚ :=
  vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) *
    (ρ.map fun q => psum (Fin m) ℚ q).prod

def IsStandard {m : ℕ} {lam : Fin m → ℕ} (T : youngCells lam ≃ Fin (youngCells lam).card) : Prop :=
  ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q

def rowWord {m : ℕ} {lam : Fin m → ℕ} (T : youngCells lam ≃ Fin (youngCells lam).card) :
    Fin (youngCells lam).card → Fin m :=
  fun t => (T.symm t).1.1

def cellOfWord {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) : Fin m × ℕ :=
  (w t, pcnt w t (w t))

end Comb

open Comb

def CombCardYoungCells.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), (youngCells lam).card = ∑ i, lam i

def CombYoungRowCard.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (i : Fin m),
    (univ.filter fun p : youngCells lam => p.1.1 = i).card = lam i

def CombTableauRowCount.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (T : youngCells lam ≃ Fin (youngCells lam).card) (t : ℕ)
    (i : Fin m),
    pcnt (rowWord T) t i = (univ.filter fun p : youngCells lam => p.1.1 = i ∧ (T p : ℕ) < t).card

def CombTableauRowPrefix.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
    ∀ t : Fin (youngCells lam).card,
      (univ.filter fun p : youngCells lam =>
        p.1.1 = (T.symm t).1.1 ∧ (T p : ℕ) < (t : ℕ)).card = (T.symm t).1.2

def CombTableauRowLattice.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
    ∀ (t : ℕ) (i j : Fin m), i ≤ j →
      (univ.filter fun p : youngCells lam => p.1.1 = j ∧ (T p : ℕ) < t).card ≤
        (univ.filter fun p : youngCells lam => p.1.1 = i ∧ (T p : ℕ) < t).card

def CombWordOfTableau.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
      rowWord T ∈ latticeWords (youngCells lam).card lam ∧
        ∀ t, cellOfWord (rowWord T) t = (T.symm t).1

def CombCellOfWordMem.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (w : Fin (youngCells lam).card → Fin m),
    w ∈ latticeWords (youngCells lam).card lam → ∀ t, cellOfWord w t ∈ youngCells lam

def CombCellOfWordInj.Statement : Prop :=
  ∀ (m n : ℕ) (w : Fin n → Fin m), Function.Injective (cellOfWord w)

def CombCellOfWordMono.Statement : Prop :=
  ∀ (m n : ℕ) (w : Fin n → Fin m), IsLattice w → ∀ s t : Fin n,
    (cellOfWord w s).1 ≤ (cellOfWord w t).1 → (cellOfWord w s).2 ≤ (cellOfWord w t).2 → s ≤ t

def CombTableauOfWord.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ w ∈ latticeWords (youngCells lam).card lam,
      ∃ T : youngCells lam ≃ Fin (youngCells lam).card, IsStandard T ∧ rowWord T = w

def CombTableEqWords.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    numStandardTable lam = (latticeWords (∑ i, lam i) lam).card

def CombCfUpdateZero.Statement : Prop :=
  ∀ (m : ℕ) (A : MvPolynomial (Fin m) ℚ), IsAlt A →
    ∀ (lam : Fin m → ℕ), Antitone lam → ∀ i : Fin m, 1 ≤ lam i + stair m i →
      (lam i = 0 ∨ ¬ Antitone (Function.update lam i (lam i - 1))) →
        cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - 1)) A = 0

def CombCfAtStair.Statement : Prop :=
  ∀ (m n : ℕ) (lam : Fin m → ℕ), Antitone lam →
    cf (fun i => lam i + stair m i) (alternantPsum m (List.replicate n 1)) =
      (latticeWords n lam).card

def CombCfMonomialPsumOne.Statement : Prop :=
  ∀ (m n : ℕ) (v l : Fin m → ℕ),
    cf l (monomial (ex v) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) =
      if (∀ i, v i ≤ l i) ∧ ∑ i, l i = ∑ i, v i + n then
        (n.factorial : ℚ) / ∏ i, ((l i - v i).factorial : ℚ)
      else 0

def CombDetDescFactorial.Statement : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℕ),
    (Matrix.of fun i j : Fin m => ((l i).descFactorial (stair m j) : ℚ)).det =
      vandermondeOf (fun i => (l i : ℚ))

def CombCfVandermondePsumOne.Statement : Prop :=
  ∀ (m n : ℕ) (l : Fin m → ℕ), ∑ i, l i = ∑ i, stair m i + n →
    cf l (alternantPsum m (List.replicate n 1)) =
      (n.factorial : ℚ) * vandermondeOf (fun i => (l i : ℚ)) / ∏ i, ((l i).factorial : ℚ)

def CombSortLe.Statement : Prop :=
  ∀ (m : ℕ) (u l : Fin m → ℕ) (σ : Perm (Fin m)), Antitone l → (∀ i, u i ≤ l i) →
    Antitone (u ∘ σ) → ∀ k, u (σ k) ≤ l k

def CombSortShift.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam → ∀ (q : ℕ) (i : Fin m), q ≤ lam i + stair m i →
    Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q)) →
    ∃ (σ : Perm (Fin m)) (μ : Fin m → ℕ), Antitone μ ∧ (∀ k, μ k ≤ lam k) ∧
      ∀ k, Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) (σ k) =
        μ k + stair m k

def CombSortShiftDistinct.Statement : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℕ), Function.Injective l → ∀ q : ℕ, 1 ≤ q →
    ∀ i j : Fin m, i ≠ j → q ≤ l i → q ≤ l j → ∀ σ τ : Perm (Fin m),
      Function.update l i (l i - q) ∘ σ ≠ Function.update l j (l j - q) ∘ τ

def CombPcntAppend.Statement : Prop :=
  ∀ (m n q : ℕ) (w : Fin n → Fin m) (s : Fin q → Fin m) (t : ℕ) (i : Fin m),
    pcnt (Fin.append w s) t i = pcnt w t i + pcnt s (t - n) i

def CombExtendWord.Statement : Prop :=
  ∀ (m n q : ℕ) (μ lam : Fin m → ℕ), Antitone μ → Antitone lam → (∀ i, μ i ≤ lam i) →
    ∑ i, lam i = ∑ i, μ i + q →
      ∃ s : Fin q → Fin m, ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam

def CombStripSum.Statement : Prop :=
  ∀ (m n q : ℕ) (lam : Fin m → ℕ), Antitone lam → 1 ≤ q →
    ∑ i : Fin m, (if q ≤ lam i + stair m i then
      |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
        (alternantPsum m (List.replicate n 1))| else 0) ≤
      ((latticeWords (n + q) lam).card : ℚ)

def CombCfBound.Statement : Prop :=
  ∀ (m : ℕ) (ρ : List ℕ), (∀ q ∈ ρ, 1 ≤ q) → ∀ lam : Fin m → ℕ, Antitone lam →
    |cf (fun i => lam i + stair m i) (alternantPsum m ρ)| ≤ ((latticeWords ρ.sum lam).card : ℚ)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsPowerSumDecompositionHomogeneousComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def rootRingToReal (f N j k : ℕ) (h : N = j + k) : RootRing f N →+* IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  (rename (R := ℝ) (Prod.map id (finCongr h))).toRingHom.comp (MvPolynomial.map (algebraMap ℚ ℝ))

@[simp] theorem rootRingToReal_X (f N j k : ℕ) (h : N = j + k) (v : Fin f × Fin N) :
    rootRingToReal f N j k h (X v) = X (v.1, finCongr h v.2) := by
  simp only [rootRingToReal, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    rename_X] <;> rfl

@[simp] theorem rootRingToReal_C (f N j k : ℕ) (h : N = j + k) (q : ℚ) :
    rootRingToReal f N j k h (C q) = C (q : ℝ) := by
  simp [rootRingToReal]

theorem rootRingToReal_isHomogeneous_iff (f N j k : ℕ) (h : N = j + k) (P : RootRing f N) (n : ℕ) :
    (rootRingToReal f N j k h P).IsHomogeneous n ↔ P.IsHomogeneous n := by
  rw [rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    IsHomogeneous.rename_isHomogeneous_iff
      (Function.Injective.prodMap Function.injective_id (finCongr h).injective)]
  constructor
  · intro hP d hd
    apply hP
    rw [coeff_map]
    exact (map_ne_zero_iff _ (algebraMap ℚ ℝ).injective).mpr hd
  · intro hP
    exact hP.map _

theorem map_vandermondeOf {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (vandermondeOf v) = vandermondeOf (fun i => φ (v i)) := by
  simp [vandermondeOf, map_prod, map_sub]

theorem vandermondeOf_eq_vandermonde {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    vandermondeOf v = GroundTheory.Heights₂.Heights.vandermonde v := by
  have hM : (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))) =
      (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply,
      Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  have hW : Matrix.vandermonde (fun i => v (Fin.revPerm i)) =
      (Matrix.vandermonde v).submatrix Fin.revPerm id := by
    ext a b
    simp [Matrix.vandermonde_apply]
  rw [GroundTheory.Heights₂.Heights.vandermonde, hM, Matrix.det_permute', ← Matrix.det_permute, ← hW,
    Matrix.det_vandermonde]
  have key : ∀ g : Fin m → Fin m → R,
      ∏ i, ∏ l ∈ Ioi i, g i l = ∏ i, ∏ l, if i < l then g i l else 1 := by
    intro g
    refine prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext l
    simp
  rw [vandermondeOf, key, key]
  conv_rhs => rw [Finset.prod_comm]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun l => ?_)
  simp [Fin.revPerm_apply, Fin.rev_lt_rev]

theorem rootRingToReal_blockPowerSum (f N j k : ℕ) (h : N = j + k) (m : ℕ) (τ : Fin f) :
    rootRingToReal f N j k h (blockPowerSum f N m τ) = IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by
  subst h
  simp [blockPowerSum, IndefiniteRowSideFullHecke.RestTerms.psumAt]

theorem rootRingToReal_smallPowerSum_last (f r a m : ℕ) (τ : Fin f) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (smallPowerSum f r a .last m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f a r true m τ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [smallPowerSum, yRoot, SmallBlock.sign, yIndex, map_sum, map_pow, map_mul,
    rootRingToReal_C, rootRingToReal_X, IndefiniteRowSideFullHecke.RestTerms.smallPsum, if_true, Rat.cast_one, C_1, one_mul]
  refine sum_congr rfl fun i _ => ?_
  rfl

theorem rootRingToReal_smallPowerSum_first (f r a m : ℕ) (τ : Fin f) :
    rootRingToReal f (r + a) r a rfl (smallPowerSum f r a .first m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f r a false m τ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [smallPowerSum, yRoot, SmallBlock.sign, yIndex, map_sum, map_pow, map_mul,
    rootRingToReal_C, rootRingToReal_X, IndefiniteRowSideFullHecke.RestTerms.smallPsum, Bool.false_eq_true, if_false,
    Rat.cast_neg, Rat.cast_one, C_neg, C_1, neg_one_mul, map_neg]
  refine sum_congr rfl fun i _ => ?_
  rfl

theorem rootRingToReal_smallBlockMu_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (smallBlockMu f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.muClass f a r true := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [IndefiniteRowSideFullHecke.RestTerms.muClass, smallBlockMu, map_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [← rootRingToReal_smallPowerSum_last]
  simp [smallPowerSum]

theorem rootRingToReal_smallBlockMu_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (smallBlockMu f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.muClass f r a false := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [IndefiniteRowSideFullHecke.RestTerms.muClass, smallBlockMu, map_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [← rootRingToReal_smallPowerSum_first]
  simp [smallPowerSum]

theorem rootRingToReal_fibreClass_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (fibreClass f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.fibClass f a r true := by
  simp only [fibreClass, IndefiniteRowSideFullHecke.RestTerms.fibClass, if_true, map_prod, map_mul, map_vandermondeOf]
  refine prod_congr rfl fun τ _ => ?_
  rw [vandermondeOf_eq_vandermonde, vandermondeOf_eq_vandermonde]
  congr 2
  · funext i
    simp only [yRoot, SmallBlock.sign, yIndex, map_mul, rootRingToReal_C, rootRingToReal_X, Rat.cast_one,
      C_1, one_mul] <;> rfl
  · funext i
    simp only [zRoot, zIndex, rootRingToReal_X] <;> rfl

theorem rootRingToReal_fibreClass_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.fibClass f r a false := by
  simp only [fibreClass, IndefiniteRowSideFullHecke.RestTerms.fibClass, Bool.false_eq_true, if_false, map_prod, map_mul,
    map_vandermondeOf]
  refine prod_congr rfl fun τ _ => ?_
  rw [vandermondeOf_eq_vandermonde, vandermondeOf_eq_vandermonde]
  congr 2
  · funext i
    simp only [yRoot, SmallBlock.sign, yIndex, map_mul, rootRingToReal_C, rootRingToReal_X, Rat.cast_neg,
      Rat.cast_one, C_neg, C_1, neg_one_mul, map_neg] <;> rfl
  · funext i
    simp only [zRoot, zIndex, rootRingToReal_X] <;> rfl

theorem rootRingToReal_restPolynomial_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (restPolynomial f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.restPoly f a r true := by
  rw [restPolynomial, IndefiniteRowSideFullHecke.RestTerms.restPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_last,
    rootRingToReal_fibreClass_last, IndefiniteRowSideFullHecke.RestTerms.nDim, show f * a * r = f * (r * a) by ring]

theorem rootRingToReal_restPolynomial_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (restPolynomial f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.restPoly f r a false := by
  rw [restPolynomial, IndefiniteRowSideFullHecke.RestTerms.restPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first,
    rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]

theorem rootRingToReal_degreePolynomial_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a)
        (smallBlockMu f r a .last ^ (f * (r * a)) * fibreClass f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f a r true := by
  rw [IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_last,
    rootRingToReal_fibreClass_last, IndefiniteRowSideFullHecke.RestTerms.nDim, show f * a * r = f * (r * a) by ring]

theorem rootRingToReal_degreePolynomial_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl
        (smallBlockMu f r a .first ^ (f * (r * a)) * fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f r a false := by
  rw [IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first,
    rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]

theorem blockPowerSum_isHomogeneous (f N m : ℕ) (τ : Fin f) :
    (blockPowerSum f N m τ).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _

theorem isPowerSumDecomposition_homogeneousComponent (f N : ℕ) (F : RootRing f N)
    (Q : ℕ → Fin f → RootRing f N) (hF : F.IsHomogeneous (topDegree f N + 1))
    (hQ : IsPowerSumDecomposition f N F Q) :
    IsPowerSumDecomposition f N F
        (fun m τ => homogeneousComponent (topDegree f N + 1 - m) (Q m τ)) ∧
      ∀ m τ, (homogeneousComponent (topDegree f N + 1 - m) (Q m τ)).IsHomogeneous
        (topDegree f N + 1 - m) := by
  refine ⟨?_, fun m τ => homogeneousComponent_isHomogeneous _ _⟩
  have hle : ∀ m, m ≤ N → ∀ τ : Fin f, m ≤ topDegree f N + 1 := by
    intro m hm τ
    have hf : 0 < f := τ.pos
    have h1 : N - 1 ≤ N * (N - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      rcases N with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]
        rcases n with _ | n
        · simp
        · nlinarith
    have h2 : N * (N - 1) / 2 ≤ topDegree f N := Nat.le_mul_of_pos_left _ hf
    omega
  unfold IsPowerSumDecomposition at hQ ⊢
  have hcomp : homogeneousComponent (topDegree f N + 1) F = F := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hF), if_pos rfl]
  conv_lhs => rw [← hcomp, hQ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine sum_congr rfl fun m hm => sum_congr rfl fun τ _ => ?_
  rw [HomogeneousComponentMul.proof _ _ _ _ _ _ (blockPowerSum_isHomogeneous f N m τ),
    if_pos (hle m (Finset.mem_Icc.1 hm).2 τ)]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem FlagVandermondeHomogeneous.proof : FlagVandermondeHomogeneous.Statement := by
  intro f N
  have hblock : ∀ τ : Fin f,
      (vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N))).IsHomogeneous
        (N * (N - 1) / 2) := fun τ =>
    VandermondeOfHomogeneous.proof _ _ N _ (fun i => isHomogeneous_X ℚ (τ, i))
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
    (fun τ => vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N)))
    (fun _ => N * (N - 1) / 2) (fun τ _ => hblock τ)
  simpa [blockVandermonde, topDegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] using h

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem hsymm_isHomogeneous (σ : Type*) [Fintype σ] [DecidableEq σ] (n : ℕ) :
    (hsymm σ ℚ n).IsHomogeneous n := by
  rw [Schur.hsymm_eq_sum_finsuppAntidiag]
  refine IsHomogeneous.sum _ _ _ fun l hl => ?_
  have hsum : ∑ i, l i = n := (mem_finsuppAntidiag.mp hl).1
  rw [← hsum]
  exact IsHomogeneous.prod _ _ _ fun i _ => by
    simpa using (isHomogeneous_X ℚ i).pow (l i)

theorem SchSchurHomogeneous.proof : SchSchurHomogeneous.Statement := by
  intro σ _ _ r lam
  unfold schur
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun π _ => ?_
  rw [Units.smul_def]
  have hmem : (∏ i, (Matrix.of fun i j : Fin r =>
      completeSymmetric σ ((lam i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ))) (π i) i) ∈
      homogeneousSubmodule σ ℚ (∑ i, lam i) := by
    rw [mem_homogeneousSubmodule]
    by_cases h : ∀ i, 0 ≤ (lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)
    · have hdeg : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat = ∑ i, lam i := by
        have h1 : ((∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat : ℕ) : ℤ) =
            ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) := by
          push_cast
          exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h i)
        have h2 : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) = ∑ i, (lam i : ℤ) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Equiv.sum_comp π (fun i => (lam i : ℤ)), Equiv.sum_comp π (fun i => ((i : ℕ) : ℤ))]
          ring
        exact_mod_cast h1.trans h2
      rw [← hdeg]
      refine IsHomogeneous.prod _ _ _ fun i _ => ?_
      simp only [Matrix.of_apply, completeSymmetric, if_pos (h i)]
      exact hsymm_isHomogeneous σ _
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [completeSymmetric, not_le.mpr hi])]
      exact isHomogeneous_zero _ _ _
  exact zsmul_mem hmem _

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoeffRenameProdCongrRight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace FlagEq

variable {f N : ℕ}

def permSign (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : ℤ :=
  ∏ τ, ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)

def stairExp (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - ((w v.1).symm v.2 : ℕ)

def rho (f N : ℕ) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - (v.2 : ℕ)

def stairConst (f N : ℕ) : ℝ := (∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ)) ^ f

theorem stairExp_one : stairExp f N 1 = rho f N := by
  ext v; simp [stairExp, rho, Equiv.Perm.one_def]

theorem permSign_one : permSign f N 1 = 1 := by simp [permSign]

theorem permSign_inv (w : Fin f → Equiv.Perm (Fin N)) : permSign f N w⁻¹ = permSign f N w := by
  simp [permSign, Equiv.Perm.sign_inv]

theorem permSign_mul (u w : Fin f → Equiv.Perm (Fin N)) :
    permSign f N (u * w) = permSign f N u * permSign f N w := by
  simp [permSign, Equiv.Perm.sign_mul, prod_mul_distrib]

theorem permSign_mul_self (u : Fin f → Equiv.Perm (Fin N)) :
    permSign f N u * permSign f N u = 1 := by
  rw [permSign, ← prod_mul_distrib]
  exact prod_eq_one fun τ _ => by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

theorem stairConst_pos : 0 < stairConst f N :=
  pow_pos (prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _) _

theorem coeff_rename_prodCongrRight {R : Type*} [CommSemiring R] (w : Fin f → Equiv.Perm (Fin N))
    (P : MvPolynomial (Fin f × Fin N) R) (d : Fin f × Fin N →₀ ℕ) :
    AddMonoidAlgebra.coeff (rename (Equiv.prodCongrRight w) P) d =
      AddMonoidAlgebra.coeff P (Finsupp.equivFunOnFinite.symm fun v => d (Equiv.prodCongrRight w v)) := by
  rw [← coeff_rename_mapDomain (Equiv.prodCongrRight w) (Equiv.injective _) P]
  congr 1
  ext v
  obtain ⟨u, rfl⟩ := (Equiv.prodCongrRight w).surjective v
  rw [Finsupp.mapDomain_apply_of_injective (Equiv.injective _)]
  simp

theorem coeff_rho_antisym {R : Type*} [CommRing R] (P : MvPolynomial (Fin f × Fin N) R) :
    AddMonoidAlgebra.coeff (∑ w : Fin f → Equiv.Perm (Fin N),
        ((permSign f N w : ℤ) : R) • rename (Equiv.prodCongrRight w) P) (rho f N) =
      ∑ w, ((permSign f N w : ℤ) : R) * AddMonoidAlgebra.coeff P (stairExp f N w) := by
  rw [coeff_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun w => ?_)
  rw [coeff_smul, smul_eq_mul, coeff_rename_prodCongrRight, Equiv.inv_apply, permSign_inv]
  congr 2

theorem blockVandermonde_eq_sum (f N : ℕ) :
    blockVandermonde f N = ∑ w : Fin f → Equiv.Perm (Fin N),
      ((permSign f N w : ℤ) : ℚ) • monomial (stairExp f N w) (1 : ℚ) := by
  simp only [blockVandermonde, Comb.vandermondeOf_eq_det, Matrix.det_apply', Matrix.of_apply]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  refine sum_congr rfl fun w _ => ?_
  rw [prod_mul_distrib, smul_eq_C_mul, monomial_eq, C_1, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  congr 1
  · simp [permSign]
  · refine prod_congr rfl fun τ _ => ?_
    symm
    rw [← Equiv.prod_comp (w τ)]
    simp [stairExp]

theorem coeff_blockVandermonde (α : Fin f × Fin N →₀ ℕ) :
    AddMonoidAlgebra.coeff (blockVandermonde f N) α =
      ∑ w, ((permSign f N w : ℤ) : ℚ) * if stairExp f N w = α then 1 else 0 := by
  rw [blockVandermonde_eq_sum, coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul]

theorem eq_one_of_stairExp_eq (w : Fin f → Equiv.Perm (Fin N)) (h : stairExp f N w = rho f N) :
    w = 1 := by
  funext τ
  ext i
  have h1 := DFunLike.congr_fun h (τ, w τ i)
  simp [stairExp, rho] at h1
  have := (w τ i).isLt
  have := i.isLt
  simp only [Pi.one_apply, Equiv.Perm.coe_one, id_eq]
  omega

theorem prod_factorial_stairExp (w : Fin f → Equiv.Perm (Fin N)) :
    (stairExp f N w).prod (fun _ e => (e.factorial : ℝ)) = stairConst f N := by
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Fintype.prod_prod_type]
  have h : ∀ τ, ∏ i : Fin N, ((stairExp f N w (τ, i)).factorial : ℝ) =
      ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) := by
    intro τ
    simp only [stairExp, Finsupp.coe_equivFunOnFinite_symm]
    exact Equiv.prod_comp (w τ).symm (fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ))
  rw [prod_congr rfl (fun τ _ => h τ), prod_const, card_univ, Fintype.card_fin, stairConst]

theorem rho_degree (f N : ℕ) : (rho f N).degree = f * (N * (N - 1) / 2) := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [rho, Finsupp.coe_equivFunOnFinite_symm, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  have h := sum_range_reflect (fun i => i) N
  rw [h, sum_range_id]

end FlagEq

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchBlockVandermondeOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchBlockVandermondeOne.proof : SchBlockVandermondeOne.Statement := by
  intro N
  simp only [blockVandermonde, vandermondeOf, Fin.prod_univ_one, map_prod, map_sub, rename_X]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem FlagRestrictHomogeneous.proof : FlagRestrictHomogeneous.Statement := by
  intro f N τ R k hR
  have h := hR.aeval (fun p : Fin f × Fin N => if p.1 = τ then X p.2 else 0) (n := 1) (by
    intro p
    split_ifs
    · exact isHomogeneous_X ℚ _
    · exact isHomogeneous_zero _ _ _)
  rw [one_mul] at h
  exact h

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagPowerSumSymmetric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagPowerSumSymmetric.proof : FlagPowerSumSymmetric.Statement := by
  intro f N k τ w
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [blockPowerSum, map_sum, map_pow, Flag.blockPermute_X]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : RootRing f N) ^ k)

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagSymmetricMulAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagSymmetricMulAntisym.proof : FlagSymmetricMulAntisym.Statement := by
  intro f N P H hP
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, hP w, mul_smul_comm]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAlternantHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem SchAlternantHomogeneous.proof : SchAlternantHomogeneous.Statement := by
  intro ι _ _ e
  unfold alternant
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ _
  have h : IsHomogeneous (∏ i, (X (σ i) : MvPolynomial ι ℚ) ^ e i) (∑ i, e i) :=
    IsHomogeneous.prod _ _ _ (fun i _ => isHomogeneous_X_pow _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp only [hs, Matrix.of_apply, one_smul, Units.neg_smul]
  · exact h
  · exact h.neg

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralTopComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralTopComponent.proof (h1 : FlagVandermondeHomogeneous.Statement) :
    FlagIntegralTopComponent.Statement := by
  intro f N Φ
  unfold flagIntegral
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdeg : α.degree = topDegree f N := by
    rw [Finsupp.degree_eq_weight_one]
    exact h1 f N (mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent, if_pos hdeg]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictPowerSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagRestrictPowerSum.proof : FlagRestrictPowerSum.Statement := by
  intro f N k τ σ hk
  have hk0 : k ≠ 0 := by omega
  unfold blockPowerSum restrictToBlock
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_pow, aeval_X]
  split_ifs with h
  · subst h
    simp [psum]
  · simp [zero_pow hk0]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityVandermondeNe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchRootOfUnityVandermondeNe.rootOfUnity_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) : IsPrimitiveRoot (rootOfUnity k) k := by
  unfold rootOfUnity
  exact Complex.isPrimitiveRoot_exp k (by omega)

theorem SchRootOfUnityVandermondeNe.proof : SchRootOfUnityVandermondeNe.Statement := by
  intro k hk
  have hz := SchRootOfUnityVandermondeNe.rootOfUnity_isPrimitiveRoot hk
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [sub_ne_zero]
  intro h
  have hij : (i : ℕ) = j := hz.pow_inj i.isLt j.isLt h
  have hlt : i < j := Finset.mem_Ioi.mp hj
  exact absurd (Fin.ext hij) (ne_of_lt hlt)

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictDecomposition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagRestrictDecomposition.proof (h1 : FlagRestrictPowerSum.Statement) :
    FlagRestrictDecomposition.Statement := by
  intro f N τ R
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, h1 f N l τ _ hl1, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ)]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralVandermondePos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralVandermondePos.proof : FlagIntegralVandermondePos.Statement := by
  intro f N
  unfold flagIntegral
  have hne : (blockVandermonde f N).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact Flag.blockVandermonde_ne_zero f N
  refine Finset.sum_pos (fun α hα => ?_) hne
  have hc : AddMonoidAlgebra.coeff (blockVandermonde f N) α ≠ 0 := mem_support_iff.mp hα
  refine mul_pos (mul_self_pos.mpr hc) ?_
  unfold Finsupp.prod
  exact Finset.prod_pos fun i _ => by simp only; exact_mod_cast Nat.factorial_pos _

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAntisymHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagAntisymHomogeneous.proof : FlagAntisymHomogeneous.Statement := by
  intro f N H d hH
  have hmem : ∀ w : Fin f → Equiv.Perm (Fin N),
      blockSign f N w • blockPermute f N w H ∈ homogeneousSubmodule (Fin f × Fin N) ℚ d := by
    intro w
    refine Submodule.smul_mem _ _ ?_
    rw [mem_homogeneousSubmodule]
    exact hH.rename_isHomogeneous
  have hsum : antisymmetrize f N H ∈ homogeneousSubmodule (Fin f × Fin N) ℚ d :=
    Submodule.sum_mem _ (fun w _ => hmem w)
  rwa [mem_homogeneousSubmodule] at hsum

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictConstantCoeff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagRestrictConstantCoeff.proof : FlagRestrictConstantCoeff.Statement := by
  intro f N τ R
  induction R using MvPolynomial.induction_on with
  | C a => simp [restrictToBlock]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, constantCoeff_X, mul_zero]
    have hX : constantCoeff (restrictToBlock f N τ (X i)) = 0 := by
      simp only [restrictToBlock, aeval_X]
      split_ifs <;> simp
    rw [hX, mul_zero]

end RestTerms

end GroundTheory.Heights₂.Heights
end
