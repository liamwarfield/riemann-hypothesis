module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.HSChoice

namespace GlobalTheory.PencilDisc

def line {F R : Type} [CommRing F] [CommRing R] [Algebra F R] {D N : ℕ} (u : Fin D → Fin N → R) (a b : Fin N → R)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : Polynomial R :=
  aeval (join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X) f

def disc {F R : Type} [CommRing F] [CommRing R] [Algebra F R] {D N : ℕ} (δ : ℕ) (u : Fin D → Fin N → R) (a b : Fin N → R)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : R :=
  Polynomial.resultant (line u a b f) (Polynomial.derivative (line u a b f)) δ (δ - 1)

theorem map_line {F R S : Type} [CommRing F] [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] {D N : ℕ}
    (φ : R →ₐ[F] S) (u : Fin D → Fin N → R) (a b : Fin N → R) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    (line u a b f).map (φ : R →+* S) = line (fun i j => φ (u i j)) (fun j => φ (a j)) (fun j => φ (b j)) f := by
  have h : (Polynomial.mapAlgHom φ).comp
      (aeval (join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X)) =
      aeval (join (fun i j => Polynomial.C (φ (u i j))) fun j => Polynomial.C (φ (a j)) + Polynomial.C (φ (b j)) * Polynomial.X) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [join]
    · simp [join]
  exact congrArg (fun g : MvPolynomial (Fin (D + 1) × Fin N) F →ₐ[F] Polynomial S => g f) h

theorem map_disc {F R S : Type} [CommRing F] [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] {D N : ℕ}
    (φ : R →ₐ[F] S) (δ : ℕ) (u : Fin D → Fin N → R) (a b : Fin N → R) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    φ (disc δ u a b f) = disc δ (fun i j => φ (u i j)) (fun j => φ (a j)) (fun j => φ (b j)) f := by
  rw [disc, disc, ← map_line φ, Polynomial.derivative_map, ← AlgHom.coe_toRingHom, ← Polynomial.resultant_map_map]

end GlobalTheory.PencilDisc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilLinePolynomialNatDegreeLeAndCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilLinePolynomialNatDegreeLeAndCoeff
set_option autoImplicit false

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

theorem prod_pow_natDegree_le_and_coeff {R ι : Type} [CommRing R] (s : Finset ι) (v : ι → Polynomial R) (w m : ι → ℕ)
    (h : ∀ p, (v p).natDegree ≤ w p) :
    (∏ p ∈ s, v p ^ m p).natDegree ≤ ∑ p ∈ s, m p * w p ∧
      (∏ p ∈ s, v p ^ m p).coeff (∑ p ∈ s, m p * w p) = ∏ p ∈ s, (v p).coeff (w p) ^ m p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    have h1 : (v p ^ m p).natDegree ≤ m p * w p :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (h p))
    rw [Finset.prod_insert hp, Finset.sum_insert hp, Finset.prod_insert hp]
    refine ⟨Polynomial.natDegree_mul_le.trans (add_le_add h1 ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih.1, ih.2,
      Polynomial.coeff_pow_of_natDegree_le (h p)]

theorem line_natDegree_le_and_coeff (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (u : Fin D → Fin N → R) (a b : Fin N → R) :
    (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧
      (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  classical
  set v : Fin (D + 1) × Fin N → Polynomial R :=
    join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X with hv
  let w : Fin (D + 1) × Fin N → ℕ := fun p => if p.1 = Fin.last D then 1 else 0
  have hdeg : ∀ p, (v p).natDegree ≤ w p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [hv, w, join, if_true, Fin.lastCases_last]
      rw [add_comm]
      exact Polynomial.natDegree_linear_le
    · simp [hv, w, join]
  have hco : ∀ p, (v p).coeff (w p) = join u b p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [hv, w, join]
    · simp [hv, w, join]
  have hsum : ∀ m ∈ f.support, ∑ p, m p * w p = δ := by
    intro m hm
    have := hf m (by simpa using hm) (Fin.last D)
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa [w] using this
    · intro i _ hi
      simp [w, hi]
    · simp
  have hkey : ∀ m ∈ f.support, (∏ p, v p ^ m p).natDegree ≤ δ ∧
      (∏ p, v p ^ m p).coeff δ = ∏ p, join u b p ^ m p := by
    intro m hm
    have := prod_pow_natDegree_le_and_coeff Finset.univ v w m hdeg
    rw [hsum m hm] at this
    simpa only [hco] using this
  have hline : line u a b f =
      ∑ m ∈ f.support, Polynomial.C (algebraMap F R (f.coeff m)) * ∏ p, v p ^ m p := by
    rw [line, ← hv, aeval_def, eval₂_eq']
    rfl
  rw [hline, aeval_def, eval₂_eq']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm =>
    (Polynomial.natDegree_C_mul_le _ _).trans (hkey m hm).1, ?_⟩
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Polynomial.coeff_C_mul, (hkey m hm).2]

end GlobalTheory.PencilDisc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilLinePolynomialNatDegreeLeAndCoeffStatement
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff : ∀ (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ (u : Fin D → Fin N → R) (a b : Fin N → R), (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧ (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  first | exact @GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | exact GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | (intros; apply GlobalTheory.PencilDisc.line_natDegree_le_and_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreePencilLineDiscriminantLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreePencilLineDiscriminantLe
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDiscDeg

variable {F : Type} [Field F] {σ : Type}

def CoeffDeg (e : ℕ) (P : Polynomial (MvPolynomial σ F)) : Prop :=
  ∀ k, (P.coeff k).totalDegree ≤ e

theorem CoeffDeg.mono {e e' : ℕ} {P : Polynomial (MvPolynomial σ F)} (h : CoeffDeg e P) (he : e ≤ e') :
    CoeffDeg e' P := fun k => (h k).trans he

theorem coeffDeg_C {e : ℕ} {a : MvPolynomial σ F} (ha : a.totalDegree ≤ e) :
    CoeffDeg e (Polynomial.C a) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact ha
  · simp

theorem coeffDeg_one : CoeffDeg 0 (1 : Polynomial (MvPolynomial σ F)) := by
  rw [← Polynomial.C_1]
  exact coeffDeg_C (by simp)

theorem coeffDeg_X : CoeffDeg 0 (Polynomial.X : Polynomial (MvPolynomial σ F)) := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

theorem CoeffDeg.add {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (hQ : CoeffDeg e Q) :
    CoeffDeg e (P + Q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact (totalDegree_add _ _).trans (max_le (hP k) (hQ k))

theorem CoeffDeg.mul {e e' : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e' Q) : CoeffDeg (e + e') (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact totalDegree_finsetSum_le fun x _ => (totalDegree_mul _ _).trans (add_le_add (hP _) (hQ _))

theorem coeffDeg_sum {ι : Type} (s : Finset ι) {e : ℕ} (P : ι → Polynomial (MvPolynomial σ F))
    (h : ∀ i ∈ s, CoeffDeg e (P i)) : CoeffDeg e (∑ i ∈ s, P i) := by
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact totalDegree_finsetSum_le fun i hi => h i hi k

theorem coeffDeg_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (e : ι → ℕ)
    (P : ι → Polynomial (MvPolynomial σ F)) (h : ∀ i ∈ s, CoeffDeg (e i) (P i)) :
    CoeffDeg (∑ i ∈ s, e i) (∏ i ∈ s, P i) := by
  induction s using Finset.induction_on with
  | empty => simpa using coeffDeg_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CoeffDeg.pow {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (n : ℕ) :
    CoeffDeg (n * e) (P ^ n) := by
  induction n with
  | zero => simpa using coeffDeg_one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

theorem CoeffDeg.derivative {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) :
    CoeffDeg e (Polynomial.derivative P) := by
  intro k
  rw [Polynomial.coeff_derivative]
  have h1 : ((k : MvPolynomial σ F) + 1) = C ((k : F) + 1) := by simp
  rw [h1]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, add_zero]
  exact hP (k + 1)

theorem totalDegree_resultant_le {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e Q) (m n : ℕ) : (Polynomial.resultant P Q m n).totalDegree ≤ (m + n) * e := by
  have hH : ∀ i j, (Polynomial.sylvester P Q m n i j).totalDegree ≤ e := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · simp
    | right j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · simp
  rw [Polynomial.resultant, Matrix.det_apply]
  refine totalDegree_finsetSum_le fun s _ => ?_
  refine (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)
  simpa using Finset.sum_le_card_nsmul Finset.univ _ e fun i _ => hH (s i) i

theorem coeffDeg_line {D N δ : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    CoeffDeg (D * δ) (line (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f) := by
  rw [line, aeval_def, eval₂_eq']
  refine coeffDeg_sum _ _ fun d hd => ?_
  have hc : CoeffDeg 0 (algebraMap F (Polynomial (MvPolynomial (Fin D × Fin N) F)) (AddMonoidAlgebra.coeff f d)) := by
    rw [Polynomial.algebraMap_apply]
    exact coeffDeg_C (by rw [MvPolynomial.algebraMap_eq, totalDegree_C])
  have hw : ∀ p : Fin (D + 1) × Fin N, CoeffDeg (if p.1 = Fin.last D then 0 else 1)
      (join (fun i j => Polynomial.C (X (i, j) : MvPolynomial (Fin D × Fin N) F))
        (fun j => Polynomial.C (C (ξ₀ j)) + Polynomial.C (C (ξ₁ j)) * Polynomial.X) p) := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [join, Fin.lastCases_last, if_true]
      exact (coeffDeg_C (totalDegree_C _).le).add ((coeffDeg_C (e := 0) (totalDegree_C _).le).mul coeffDeg_X)
    · simp only [join, Fin.lastCases_castSucc, if_neg (Fin.castSucc_ne_last i)]
      exact coeffDeg_C (totalDegree_X _).le
  refine (hc.mul (coeffDeg_prod Finset.univ _ _ fun p _ => (hw p).pow (d p))).mono (le_of_eq ?_)
  rw [zero_add, Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  have h := hf d hd
  simp [Fin.castSucc_ne_last, h]

theorem totalDegree_disc_le (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    (disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  have h := coeffDeg_line f hf ξ₀ ξ₁
  refine (totalDegree_resultant_le h h.derivative δ (δ - 1)).trans ?_
  calc (δ + (δ - 1)) * (D * δ) ≤ (2 * δ) * (D * δ) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * D * δ ^ 2 := by ring

end GlobalTheory.PencilDiscDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreePencilLineDiscriminantLeStatement
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalDegree_pencilLineDiscriminant_le : ∀ (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ ξ₀ ξ₁ : Fin N → F, (GlobalTheory.PencilDisc.disc δ (fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => MvPolynomial.C (ξ₀ j)) (fun j => MvPolynomial.C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  first | exact @GlobalTheory.PencilDiscDeg.totalDegree_disc_le | exact GlobalTheory.PencilDiscDeg.totalDegree_disc_le | (intros; apply GlobalTheory.PencilDiscDeg.totalDegree_disc_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSquareLinearFactorOfPencilLineDiscriminantNeZ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSquareLinearFactorOfPencilLineDiscriminantNeZ
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

def lineSubst {K : Type} [Field K] {N : ℕ} (a b : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K →ₐ[K] Polynomial K :=
  aeval fun p : Fin 1 × Fin N => Polynomial.C (a p.2) + Polynomial.C (b p.2) * Polynomial.X

theorem line_eq_lineSubst {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (a b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    line s a b f = lineSubst a b (spec s f) := by
  simp only [line, spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C, lineSubst]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K),
      IsScalarTower.algebraMap_apply F K (Polynomial K), AlgHom.commutes]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join, lineSubst]

theorem eval_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) = aeval (join s b) f := by
  simp only [spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K)]
    simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join]

theorem lineSubst_lin {K : Type} [Field K] {N : ℕ} (a b y : Fin N → K) :
    lineSubst a b (lin y) = Polynomial.C (∑ j, a j * y j) + Polynomial.C (∑ j, b j * y j) * Polynomial.X := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, lineSubst, map_sum, map_mul, aeval_X, aeval_C, Polynomial.algebraMap_eq, add_mul,
    Finset.sum_add_distrib, Polynomial.C_mul, Finset.sum_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eval_lin {K : Type} [Field K] {N : ℕ} (b y : Fin N → K) :
    eval (fun p : Fin 1 × Fin N => b p.2) (lin y) = ∑ j, b j * y j := by
  simp [lin]

theorem coeff_ne_zero_of_resultant_ne_zero {K : Type} [Field K] {δ : ℕ} (hδ : 1 ≤ δ) (P : Polynomial K)
    (hP : P.natDegree ≤ δ) (h : Polynomial.resultant P (Polynomial.derivative P) δ (δ - 1) ≠ 0) : P.coeff δ ≠ 0 := by
  by_contra hc
  apply h
  have hlt : P.natDegree < δ := by
    rcases hP.lt_or_eq with h1 | h1
    · exact h1
    exfalso
    by_cases hP0 : P = 0
    · rw [hP0, Polynomial.natDegree_zero] at h1
      omega
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp (by rw [Polynomial.leadingCoeff, h1]; exact hc))
  rcases Nat.lt_or_ge δ 2 with h2 | h2
  · obtain rfl : δ = 1 := by omega
    have hd : Polynomial.derivative P = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero (by omega : P.natDegree = 0), Polynomial.derivative_C]
    simp [hd]
  · apply Polynomial.resultant_eq_zero_of_lt_lt _ _ _ _ hlt
    calc (Polynomial.derivative P).natDegree ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le P
      _ < δ - 1 := by omega

theorem noSquare_spec_of_disc_ne_zero : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (s : Fin D → Fin N → K) (a b : Fin N → K), 1 ≤ δ → (GlobalTheory.PencilDisc.line s a b f).natDegree ≤ δ → (GlobalTheory.PencilDisc.line s a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join s b) f → GlobalTheory.PencilDisc.disc δ s a b f ≠ 0 → GlobalTheory.HSChoice.NoSquare (GlobalTheory.HSChoice.spec s f) := by
  intro F K _ _ _ D N δ f s a b hδ hdeg hcoeff hdisc
  have hres : (line s a b f).resultant (Polynomial.derivative (line s a b f)) δ (δ - 1) ≠ 0 := hdisc
  have hc : (line s a b f).coeff δ ≠ 0 := coeff_ne_zero_of_resultant_ne_zero hδ _ hdeg hres
  have hspec0 : eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) ≠ 0 := by
    rw [eval_spec, ← hcoeff]
    exact hc
  refine ⟨fun h0 => hspec0 (by rw [h0, map_zero]), fun y _ hdvd => ?_⟩
  obtain ⟨q, hq⟩ := hdvd
  by_cases hβ : ∑ j, b j * y j = 0
  · apply hspec0
    rw [hq, map_mul, map_pow, eval_lin, hβ]
    simp
  · have hnat : (line s a b f).natDegree = δ :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hc
    have hP0 : line s a b f ≠ 0 := fun h0 => hc (by rw [h0, Polynomial.coeff_zero])
    have hcop : IsCoprime (line s a b f) (Polynomial.derivative (line s a b f)) := by
      by_contra hnc
      apply hres
      have hd' : (Polynomial.derivative (line s a b f)).natDegree ≤ δ - 1 := by
        rw [← hnat]
        exact Polynomial.natDegree_derivative_le _
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd'
      rw [hk, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, ← hnat,
        Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hP0, hnc⟩, mul_zero]
    have hQ : line s a b f = lineSubst a b (lin y) * lineSubst a b (lin y) * lineSubst a b q := by
      rw [line_eq_lineSubst, hq, map_mul, map_pow, sq]
    have h1 : lineSubst a b (lin y) ∣ line s a b f :=
      ⟨lineSubst a b (lin y) * lineSubst a b q, by rw [hQ]; ring⟩
    have h2 : lineSubst a b (lin y) ∣ Polynomial.derivative (line s a b f) := by
      refine ⟨Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        lineSubst a b (lin y) * Polynomial.derivative (lineSubst a b q), ?_⟩
      rw [hQ, Polynomial.derivative_mul, Polynomial.derivative_mul]
      ring
    have hu := hcop.isUnit_of_dvd' h1 h2
    rw [lineSubst_lin] at hu
    have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [add_comm, Polynomial.natDegree_linear hβ] at hdeg0
    exact one_ne_zero hdeg0

end GlobalTheory.PencilDisc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSquareLinearFactorOfPencilLineDiscriminantNeZStatement
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_square_linear_factor_of_pencilLineDiscriminant_ne_zero : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (s : Fin D → Fin N → K) (a b : Fin N → K), 1 ≤ δ → (GlobalTheory.PencilDisc.line s a b f).natDegree ≤ δ → (GlobalTheory.PencilDisc.line s a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join s b) f → GlobalTheory.PencilDisc.disc δ s a b f ≠ 0 → GlobalTheory.HSChoice.NoSquare (GlobalTheory.HSChoice.spec s f) := by
  first | exact @GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero | exact GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero | (intros; apply GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreduciblePencilLinePolynomialGenericLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreduciblePencilLinePolynomialGenericLine
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc.GenericLine

variable (F : Type) [Field F] (D N : ℕ)

abbrev Idx := (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)

def shiftFun (c : F) : Option (Idx D N) → MvPolynomial (Option (Idx D N)) F
  | some (Sum.inr (Sum.inl j)) =>
      X (some (Sum.inr (Sum.inl j))) + C c * (X (some (Sum.inr (Sum.inr j))) * X none)
  | o => X o

def shift (c : F) : MvPolynomial (Option (Idx D N)) F →ₐ[F] MvPolynomial (Option (Idx D N)) F :=
  aeval (shiftFun F D N c)

theorem shift_comp (c : F) : (shift F D N c).comp (shift F D N (-c)) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  rintro (_ | (p | j | j))
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]

def theta : MvPolynomial (Option (Idx D N)) F ≃ₐ[F] MvPolynomial (Option (Idx D N)) F :=
  AlgEquiv.ofAlgHom (shift F D N 1) (shift F D N (-1))
    (by simpa using shift_comp F D N 1) (by simpa using shift_comp F D N (-1))

def place : Fin (D + 1) × Fin N → Option (Idx D N) := fun p =>
  Fin.lastCases (motive := fun _ => Option (Idx D N)) (some (Sum.inr (Sum.inl p.2)))
    (fun i => some (Sum.inl (i, p.2))) p.1

theorem place_injective : Function.Injective (place D N) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  induction a using Fin.lastCases <;> induction a' using Fin.lastCases <;> simp_all [place]

theorem line_eq (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    GlobalTheory.PencilDisc.line (fun i j => (X (Sum.inl (i, j)) : MvPolynomial (Idx D N) F))
      (fun j => X (Sum.inr (Sum.inl j))) (fun j => X (Sum.inr (Sum.inr j))) f =
    optionEquivLeft F (Idx D N) (theta F D N (rename (place D N) f)) := by
  have key : (aeval (join (fun i j => (Polynomial.C (X (Sum.inl (i, j)) : MvPolynomial (Idx D N) F)))
      (fun j => Polynomial.C (X (Sum.inr (Sum.inl j))) + Polynomial.C (X (Sum.inr (Sum.inr j))) * Polynomial.X)) :
      MvPolynomial (Fin (D + 1) × Fin N) F →ₐ[F] Polynomial (MvPolynomial (Idx D N) F)) =
      ((optionEquivLeft F (Idx D N)).toAlgHom.comp ((theta F D N).toAlgHom.comp (rename (place D N)))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    induction i using Fin.lastCases <;> simp [join, place, theta, shift, shiftFun, AlgEquiv.ofAlgHom_apply]
  exact congrArg (fun φ => φ f) key

end GlobalTheory.PencilDisc.GenericLine

private theorem irreducible_rename_of_injective' {σ τ K : Type} [Field K] (g : σ → τ)
    (hg : Function.Injective g) (f : MvPolynomial σ K) (hf : Irreducible f) :
    Irreducible (rename g f) := by
  classical
  have hk : ∀ p : MvPolynomial σ K, killCompl hg (rename g p) = p := killCompl_rename_app hg
  have hf0 : rename g f ≠ 0 := by
    intro h
    apply hf.ne_zero
    rw [← hk f, h, map_zero]
  have hvars : ∀ a : MvPolynomial τ K, a ∣ rename g f → ∃ q, rename g q = a := by
    rintro a ⟨b, hab⟩
    have ha : a ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hab
      exact hf0 hab
    have hb : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hab
      exact hf0 hab
    refine exists_rename_eq_of_vars_subset_range a g hg ?_
    intro i hi
    by_contra hni
    have h1 : degreeOf i (rename g f) = 0 := by
      by_contra hne
      have hmem : i ∈ (rename g f).vars := mem_vars_iff_degreeOf_ne_zero.2 hne
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (vars_rename g f hmem)
      exact hni ⟨j, rfl⟩
    rw [hab, degreeOf_mul_eq ha hb] at h1
    exact mem_vars_iff_degreeOf_ne_zero.1 (Finset.mem_coe.1 hi) (by omega)
  refine irreducible_iff.2 ⟨?_, ?_⟩
  · intro hu
    exact (irreducible_iff.1 hf).1 (by simpa [hk] using hu.map (killCompl hg))
  · intro a b hab
    obtain ⟨a', rfl⟩ := hvars a ⟨b, hab⟩
    obtain ⟨b', rfl⟩ := hvars b ⟨rename g a', by rw [hab, mul_comm]⟩
    rw [← map_mul] at hab
    rcases (irreducible_iff.1 hf).2 (rename_injective g hg hab) with h | h
    · exact Or.inl (h.map _)
    · exact Or.inr (h.map _)


open GlobalTheory.PencilDisc.GenericLine in
theorem GlobalTheory.PencilDisc.irreducible_line_generic (F : Type) [Field F] (D N : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : Irreducible f) :
    Irreducible (GlobalTheory.PencilDisc.line
      (fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F))
      (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j))) f) := by
  rw [line_eq F D N f, MulEquiv.irreducible_iff, MulEquiv.irreducible_iff]
  exact irreducible_rename_of_injective' (place D N) (place_injective D N) f hf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreduciblePencilLinePolynomialGenericLineStatement
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line : ∀ (F : Type) [Field F] (D N : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), Irreducible f → Irreducible (GlobalTheory.PencilDisc.line (fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F)) (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j))) f) := by
  first | exact @GlobalTheory.PencilDisc.irreducible_line_generic | exact GlobalTheory.PencilDisc.irreducible_line_generic | (intros; apply GlobalTheory.PencilDisc.irreducible_line_generic <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.PencilDisc

theorem resultant_derivative_ne_zero : ∀ (σ F : Type) [Fintype σ] [Field F] [CharZero F] (p : Polynomial (MvPolynomial σ F)) (δ : ℕ), 1 ≤ δ → p.natDegree = δ → Irreducible p → Polynomial.resultant p (Polynomial.derivative p) δ (δ - 1) ≠ 0 := by
  intro σ F _ _ _ p δ hδ hp hirr
  let K := FractionRing (MvPolynomial σ F)
  have hinj : Function.Injective (algebraMap (MvPolynomial σ F) K) := IsFractionRing.injective _ _
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hprim : p.IsPrimitive := hirr.isPrimitive (by omega)
  have h1 : Irreducible (p.map (algebraMap _ K)) := hprim.irreducible_iff_irreducible_map_fraction_map.1 hirr
  have h2 := Polynomial.resultant_ne_zero _ _ h1.separable
  rw [Polynomial.natDegree_derivative, Polynomial.natDegree_map_eq_of_injective hinj, hp, Polynomial.derivative_map,
    Polynomial.resultant_map_map] at h2
  intro h
  exact h2 (by rw [h, map_zero])

theorem exists_specialise_ne_zero : ∀ (F S T : Type) [Field F] [Infinite F] (R : MvPolynomial (S ⊕ T) F), R ≠ 0 → ∃ v : T → F, MvPolynomial.aeval (Sum.elim (fun i => (MvPolynomial.X i : MvPolynomial S F)) fun k => MvPolynomial.C (v k)) R ≠ 0 := by
  intro F S T _ _ R hR
  have h1 : sumAlgEquiv F S T R ≠ 0 := (map_ne_zero_iff _ (sumAlgEquiv F S T).injective).2 hR
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 h1
  obtain ⟨v, hv⟩ : ∃ v : T → F, eval v (AddMonoidAlgebra.coeff (sumAlgEquiv F S T R) m) ≠ 0 := by
    by_contra! H
    exact hm (MvPolynomial.funext fun x => by simpa using H x)
  refine ⟨v, fun h => hv ?_⟩
  have key : ∀ P : MvPolynomial (S ⊕ T) F,
      aeval (Sum.elim (fun i => (X i : MvPolynomial S F)) fun k => C (v k)) P = MvPolynomial.map (eval v) (sumAlgEquiv F S T P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases i <;> simp
  rw [← coeff_map, ← key, h]
  simp

theorem irreducible_of_map {F L : Type} [Field F] [Field L] [Algebra F L] {σ : Type} (f : MvPolynomial σ F)
    (h : Irreducible (MvPolynomial.map (algebraMap F L) f)) : Irreducible f := by
  have hinj := (algebraMap F L).injective
  haveI : IsLocalHom (MvPolynomial.map (σ := σ) (algebraMap F L)) := ⟨fun g hg => by
    obtain ⟨c, hc, e⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hg
    have hc0 : algebraMap F L (AddMonoidAlgebra.coeff g 0) = c := by
      rw [← coeff_map, e, coeff_zero_C]
    refine MvPolynomial.isUnit_iff_eq_C_of_isReduced.2 ⟨AddMonoidAlgebra.coeff g 0, ?_, ?_⟩
    · refine isUnit_iff_ne_zero.2 fun h0 => hc.ne_zero ?_
      rw [← hc0, h0, map_zero]
    · apply MvPolynomial.map_injective _ hinj
      rw [e, map_C, hc0]⟩
  exact Irreducible.of_map h

theorem exists_poly_noSquare : ∀ (F : Type) [Field F] [CharZero F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), 1 ≤ δ → IsMultiHomogeneous (fun _ => δ) f → Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ 2 * D * δ ^ 2 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K), aeval (fun p : Fin D × Fin N => s p.1 p.2) Q ≠ 0 → NoSquare (spec s f) := by
  intro F _ _ D N δ f hδ hf hirr
  have hF : Irreducible f := irreducible_of_map f hirr
  let u : Fin D → Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun i j => X (Sum.inl (i, j))
  let a : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inl j))
  let b : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inr j))
  have hc := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F _ D N δ f hf u a b
  let g : Fin (D + 1) × Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun p =>
    Fin.lastCases (motive := fun _ => (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) (Sum.inr (Sum.inr p.2)) (fun i => Sum.inl (i, p.2)) p.1
  have hg : Function.Injective g := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    induction i using Fin.lastCases <;> induction i' using Fin.lastCases <;> simp_all [g]
  have hjoin : join u b = fun p => X (g p) := by
    funext ⟨i, j⟩
    induction i using Fin.lastCases <;> simp [join, g, u, b]
  have hlead : (line u a b f).coeff δ ≠ 0 := by
    rw [hc.2, hjoin, show (aeval fun p => (X (g p) : MvPolynomial _ F)) f = rename g f from congrArg (fun φ : MvPolynomial _ F →ₐ[F] MvPolynomial _ F => φ f) (MvPolynomial.algHom_ext fun p => by simp)]
    exact (rename_injective g hg).ne_iff' (map_zero _) |>.mpr hF.ne_zero
  have hnat : (line u a b f).natDegree = δ := le_antisymm hc.1 (Polynomial.le_natDegree_of_ne_zero hlead)
  have hR : disc δ u a b f ≠ 0 := resultant_derivative_ne_zero _ F (line u a b f) δ hδ hnat (GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line F D N f hF)
  obtain ⟨v, hv⟩ := exists_specialise_ne_zero F (Fin D × Fin N) (Fin N ⊕ Fin N) _ hR
  refine ⟨disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f,
    ?_, GlobalTheory.T.totalDegree_pencilLineDiscriminant_le F D N δ f hf _ _, ?_⟩
  · have e := map_disc (aeval (Sum.elim (fun i => (X i : MvPolynomial (Fin D × Fin N) F)) fun k => C (v k))) δ u a b f
    rw [e] at hv
    simpa [u, a, b] using hv
  · intro K _ _ s hs
    have e := map_disc (aeval (fun p : Fin D × Fin N => s p.1 p.2)) δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f
    rw [e] at hs
    simp only [aeval_X, aeval_C] at hs
    have hc' := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F K D N δ f hf s (fun j => algebraMap F K (v (Sum.inl j))) (fun j => algebraMap F K (v (Sum.inr j)))
    exact GlobalTheory.T.not_square_linear_factor_of_pencilLineDiscriminant_ne_zero F K D N δ f s _ _ hδ hc'.1 hc'.2 hs

end GlobalTheory.PencilDisc
