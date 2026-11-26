module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartGramMA

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

theorem le_originIdeal_of_isHomogeneous {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hne : I ≠ ⊤) : I ≤ originIdeal n := by
  intro f hf
  rw [originIdeal_eq_ker, RingHom.mem_ker]
  by_contra h0
  have h1 : homogeneousComponent 0 f ∈ I := by
    have := hI 0 hf
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin n) ℂ) f 0 : MvPolynomial (Fin n) ℂ)
      = homogeneousComponent 0 f from decomposition.decompose'_apply _ _] at this
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h1
  exact hne (I.eq_top_of_isUnit_mem h1 (isUnit_iff_ne_zero.2 h0 |>.map C))

theorem isMaximal_of_isPrime_of_quotient_dim_le_zero {R : Type*} [CommRing R] {K Q : Ideal R}
    (hK : ringKrullDim (R ⧸ K) ≤ 0) (hQ : Q.IsPrime) (hKQ : K ≤ Q) : Q.IsMaximal := by
  have : Ring.KrullDimLE 0 (R ⧸ K) := Ring.krullDimLE_iff.2 (by exact_mod_cast hK)
  have hsurj := Ideal.Quotient.mk_surjective (I := K)
  have : (Q.map (Ideal.Quotient.mk K)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rwa [Ideal.mk_ker])
  have hmax := Ideal.isMaximal_of_isPrime (Q.map (Ideal.Quotient.mk K))
  have := Ideal.comap_isMaximal_of_surjective _ hsurj (K := Q.map (Ideal.Quotient.mk K))
  rwa [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    sup_eq_left.2 hKQ] at this

theorem HomogDimZeroPow.proof : HomogDimZeroPow.Statement := by
  intro n K hK hdim
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hKP, hP⟩ => ?_
  set 𝒜 := homogeneousSubmodule (Fin n) ℂ
  have hcP : (P.homogeneousCore 𝒜).toIdeal.IsPrime := hP.homogeneousCore
  have hKc : K ≤ (P.homogeneousCore 𝒜).toIdeal := by
    rw [← hK.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hKP
  have hmax := isMaximal_of_isPrime_of_quotient_dim_le_zero hdim hcP hKc
  have hle := le_originIdeal_of_isHomogeneous (P.homogeneousCore 𝒜).isHomogeneous hmax.ne_top
  exact ((hmax.eq_of_le (originIdeal_isMaximal n).ne_top hle).symm.le).trans
    (Ideal.toIdeal_homogeneousCore_le 𝒜 P)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem leadIdeal_isHomogeneous (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    (leadIdeal J).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, (mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous _ _)⟩)

theorem linIdeal_isHomogeneous {d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    (linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X ℂ j).C_mul (A i j)))⟩)

theorem linIdeal_cons {k : ℕ} (A : Matrix (Fin k) (Fin n) ℂ) (B : Matrix (Fin 1) (Fin n) ℂ) :
    linIdeal (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) = linIdeal A ⊔ linIdeal B := by
  have h : linPoly (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) =
      Fin.cons (linPoly B 0) (linPoly A) := by
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  have hB : Set.range (linPoly B) = {linPoly B 0} := by
    rw [Set.range_unique]
    rfl
  rw [linIdeal, linIdeal, linIdeal, h, Fin.range_cons, hB, Set.insert_eq, Ideal.span_union, sup_comm]

theorem ConeAvoidsExists.proof (hlead : LeadIdealDim.Statement) (hcut : LinearFormCut.Statement)
    (hpow : HomogDimZeroPow.Statement) : ConeAvoidsExists.Statement := by
  intro n d J _ hd
  have key : ∀ k, k ≤ d → ∃ A : Matrix (Fin k) (Fin n) ℂ,
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (leadIdeal J ⊔ linIdeal A)) ≤
        ((d - k : ℕ) : WithBot ℕ∞) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, ?_⟩
      have h0 : linIdeal (0 : Matrix (Fin 0) (Fin n) ℂ) = ⊥ := by
        rw [linIdeal, Set.range_eq_empty, Ideal.span_empty]
      rw [h0, sup_bot_eq, Nat.sub_zero, ← hd]
      exact hlead n J
    | succ k ih =>
      intro hk
      obtain ⟨A, hA⟩ := ih (by omega)
      have hdk : d - k = (d - (k + 1)) + 1 := by omega
      rw [hdk] at hA
      obtain ⟨B, hB⟩ := hcut n _ _ hA
      refine ⟨Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ), ?_⟩
      rw [linIdeal_cons, ← sup_assoc]
      exact hB
  obtain ⟨A, hA⟩ := key d le_rfl
  rw [Nat.sub_self, Nat.cast_zero] at hA
  obtain ⟨N, hN⟩ := hpow n _ ((leadIdeal_isHomogeneous J).sup (linIdeal_isHomogeneous A)) hA
  exact ⟨A, N, hN⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LinearFormCut.formMap (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun a := ∑ j, C (a j) * X j
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_eq_C_mul, Finset.mul_sum, mul_assoc]

theorem LinearFormCut.proof : LinearFormCut.Statement := by
  intro n e I hI
  classical
  let S := {Q : Ideal (MvPolynomial (Fin n) ℂ) | Q ∈ I.minimalPrimes ∧ Q ≠ originIdeal n}
  have : Finite S :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset fun Q (hQ : Q ∈ S) => hQ.1).to_subtype
  let p : S → Submodule ℂ (Fin n → ℂ) := fun Q => (Q.1.restrictScalars ℂ).comap (formMap n)
  have hp : ∀ Q, p Q ≠ ⊤ := by
    intro Q htop
    apply Q.2.2
    have hle : originIdeal n ≤ Q.1 := by
      rw [originIdeal, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : Pi.single j 1 ∈ p Q := htop ▸ Submodule.mem_top
      simpa [p, formMap, Pi.single_apply] using this
    exact ((originIdeal_isMaximal n).eq_of_le Q.2.1.1.1.ne_top hle).symm
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  let B : Matrix (Fin 1) (Fin n) ℂ := Matrix.of fun _ j => a j
  refine ⟨B, ?_⟩
  have hl : formMap n a ∈ linIdeal B := Ideal.subset_span ⟨0, by simp [linPoly, formMap, B]⟩
  rw [ringKrullDim_quotient] at hI ⊢
  refine iSup_le fun l => ?_
  have hIh : I ≤ l.head.1.asIdeal := fun y hy => l.head.2 (Ideal.mem_sup_left hy)
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hIh
  by_cases hQo : Q = originIdeal n
  · have hM : l.head.1.asIdeal.IsMaximal := by
      rw [← (originIdeal_isMaximal n).eq_of_le l.head.1.isPrime.ne_top (hQo ▸ hQle)]
      exact originIdeal_isMaximal n
    have h0 : l.length = 0 := by
      by_contra h
      have hlt : l.head < l.last := l.strictMono (Fin.pos_iff_ne_zero.2 (by simp [Fin.ext_iff]; omega))
      have hlt' : l.head.1.asIdeal < l.last.1.asIdeal := hlt
      exact (hM.eq_of_le l.last.1.isPrime.ne_top hlt'.le ▸ hlt').false
    simp [h0]
  · have hQa : formMap n a ∉ Q := ha ⟨Q, hQ, hQo⟩
    let f : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑(I ⊔ linIdeal B) →
        PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      fun x => ⟨x.1, fun y hy => x.2 (Ideal.mem_sup_left hy)⟩
    have hf : StrictMono f := fun x y h => h
    let q0 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      ⟨⟨Q, hQ.1.1⟩, fun y hy => hQ.1.2 hy⟩
    have hq : q0 < (l.map f hf).head := by
      refine lt_of_le_of_ne hQle fun h => hQa ?_
      have : formMap n a ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right hl)
      have hQh : Q = l.head.1.asIdeal :=
        congrArg (fun x : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I => x.1.asIdeal) h
      rwa [hQh]
    have hlen := (Order.LTSeries.length_le_krullDim ((l.map f hf).cons q0 hq)).trans hI
    simp only [RelSeries.cons_length] at hlen
    have : l.length + 1 ≤ e + 1 := by exact_mod_cast hlen
    exact_mod_cast (by omega : l.length ≤ e)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n d : ℕ}

theorem isHomogeneous_leadIdeal_sup_linIdeal (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    (leadIdeal J ⊔ linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  refine Ideal.IsHomogeneous.sup (Ideal.homogeneous_span _ _ ?_) (Ideal.homogeneous_span _ _ ?_)
  · rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, homogeneousComponent_mem _ _⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)⟩

theorem monomial_mem_originIdeal_pow {N : ℕ} {m : Fin n →₀ ℕ} (hm : m.degree = N) :
    monomial m (1 : ℂ) ∈ originIdeal n ^ N := by
  have hprod : ∏ i ∈ m.support, (X i : MvPolynomial (Fin n) ℂ) ^ m i = ∏ i, X i ^ m i :=
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by simp [Finsupp.notMem_support_iff.1 hi]
  rw [← prod_X_pow_eq_monomial, hprod, ← hm, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow
    (show (X i : MvPolynomial (Fin n) ℂ) ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) _

theorem originIdeal_pow_le_span (N : ℕ) :
    originIdeal n ^ N ≤
      Ideal.span {p | ∃ m : Fin n →₀ ℕ, m.degree = N ∧ monomial m (1 : ℂ) = p} := by
  induction N with
  | zero => simp only [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
            exact Ideal.subset_span ⟨0, by simp, by simp⟩
  | succ N ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [originIdeal, Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨m, hm, rfl⟩, _, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨m + Finsupp.single i 1, by simp [hm], by simp [X, monomial_mul]⟩

theorem originIdeal_pow_le {N : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (h : ∀ m : Fin n →₀ ℕ, m.degree = N → monomial m (1 : ℂ) ∈ I) : originIdeal n ^ N ≤ I := by
  refine (originIdeal_pow_le_span N).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact h m hm

theorem isZariskiOpen_of_local {U : Set (Matrix (Fin d) (Fin n) ℂ)}
    (H : ∀ A₀ ∈ U, ∃ p : MvPolynomial (Fin d × Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => A₀ ij.1 ij.2) p ≠ 0 ∧
        ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U) :
    IsZariskiOpen U := by
  refine ⟨{p | ∀ A : Matrix (Fin d) (Fin n) ℂ,
    eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U}, ?_⟩
  ext A
  constructor
  · intro hA
    obtain ⟨p, hp, hpU⟩ := H A hA
    exact ⟨p, hpU, hp⟩
  · rintro ⟨p, hpU, hp⟩
    exact hpU A hp

theorem ConeAvoidsOpen.proof : ConeAvoidsOpen.Statement := by
  intro n d N J
  classical
  refine isZariskiOpen_of_local fun A₀ hA₀ => ?_
  set V := Finset.finsuppAntidiag (Finset.univ : Finset (Fin n)) N
  have hV : ∀ m : Fin n →₀ ℕ, m ∈ V ↔ m.degree = N := fun m => by
    simp [V, Finsupp.degree_eq_sum]
  have hrep : ∀ m : V, ∃ a ∈ leadIdeal J, ∃ h : Fin d → MvPolynomial (Fin n) ℂ,
      a + ∑ j, h j * linPoly A₀ j = monomial (m : Fin n →₀ ℕ) 1 := by
    intro m
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.1 (hA₀ (monomial_mem_originIdeal_pow ((hV m).1 m.2)))
    obtain ⟨h, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
    exact ⟨a, ha, h, hab⟩
  choose a ha h hah using hrep
  let T : Matrix (Fin d) (Fin n) ℂ → V → MvPolynomial (Fin n) ℂ :=
    fun A m => a m + ∑ j, h m j * linPoly A j
  let P : Matrix V V (MvPolynomial (Fin d × Fin n) ℂ) := fun m' m =>
    C (AddMonoidAlgebra.coeff (a m) (m' : Fin n →₀ ℕ)) +
      ∑ j, ∑ k, C (AddMonoidAlgebra.coeff (h m j * X k) (m' : Fin n →₀ ℕ)) * X (j, k)
  have hP : ∀ (A : Matrix (Fin d) (Fin n) ℂ) (m' m : V),
      (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P m' m =
        AddMonoidAlgebra.coeff (T A m) (m' : Fin n →₀ ℕ) := by
    intro A m' m
    show eval _ (P m' m) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, T, linPoly, map_add (f := _), map_sum, map_mul, eval_C, eval_X, MvPolynomial.coeff_add, coeff_sum,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, coeff_C_mul, mul_comm]
  refine ⟨P.det, ?_, fun A hA => ?_⟩
  · rw [RingHom.map_det]
    have h1 : (eval fun ij : Fin d × Fin n => A₀ ij.1 ij.2).mapMatrix P = 1 := by
      ext m' m
      rw [hP, Matrix.one_apply]
      simp only [T, hah, coeff_monomial, Subtype.ext_iff, eq_comm]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  · rw [RingHom.map_det] at hA
    set M := (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P
    have hMT : ∀ m' m : V, M m' m = AddMonoidAlgebra.coeff (T A m) (m' : Fin n →₀ ℕ) := hP A
    have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hA)
    have hI : ∀ m, T A m ∈ leadIdeal J ⊔ linIdeal A := fun m =>
      Submodule.add_mem_sup (ha m) (Ideal.mem_span_range_iff_exists_fun.2 ⟨h m, rfl⟩)
    have hhom := isHomogeneous_leadIdeal_sup_linIdeal J A
    refine originIdeal_pow_le fun m hm => ?_
    have key : monomial m (1 : ℂ) =
        ∑ m'' : V, C (M⁻¹ m'' ⟨m, (hV m).2 hm⟩) * homogeneousComponent N (T A m'') := by
      ext s
      simp only [coeff_sum, coeff_C_mul, coeff_homogeneousComponent, coeff_monomial]
      by_cases hs : s.degree = N
      · have e := congr_fun (congr_fun hinv ⟨s, (hV s).2 hs⟩) ⟨m, (hV m).2 hm⟩
        simp only [Matrix.mul_apply, hMT, Matrix.one_apply, Subtype.ext_iff] at e
        simp only [hs, if_true]
        simp_rw [mul_comm (M⁻¹ _ _)]
        rw [e]
        by_cases hsm : s = m
        · simp [hsm]
        · simp [hsm, Ne.symm hsm]
      · simp only [hs, if_false, mul_zero, Finset.sum_const_zero]
        rw [if_neg]
        rintro rfl
        exact hs hm
    rw [key]
    exact Ideal.sum_mem _ fun m'' _ =>
      Ideal.mul_mem_left _ _ (homogeneousComponent_mem_of_mem hhom (hI m'') N)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotBotOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Matrix
open scoped ENNReal

noncomputable section

def pairPt {k m : ℕ} (x : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun j => y j))

def coordGraph {n : ℕ} (P : Finset (Fin n)) (Ω : Set (P → ℂ)) (F : (P → ℂ) → Fin n → ℂ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | (fun i : P => z i) ∈ Ω ∧ ∀ j, j ∉ P → z j = F (fun i : P => z i) j}

def frameProj {n : ℕ} (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i : I => e.repr z i)

def ProjectionFormula.Statement : Prop :=
  ∀ (n d : ℕ) (P : Finset (Fin n)) (Ω : Set (P → ℂ)) (F : (P → ℂ) → Fin n → ℂ),
    P.card = d → IsOpen Ω → DifferentiableOn ℂ F Ω →
    ∀ (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
      (B : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet B →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coordGraph P Ω F ∩ B) =
        ∑ I ∈ Finset.powersetCard d (Finset.univ : Finset (Fin n)),
          ∫⁻ x : EuclideanSpace ℂ I,
            (({z | z ∈ coordGraph P Ω F ∩ B ∧ frameProj e I z = x}.encard : ℕ∞) : ℝ≥0∞)
            ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ))


def PolySublevel.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 → ∀ R : ℝ, 0 < R →
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)
          {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 R ∧ ‖eval (fun i => x i) Q‖ ≤ η} ≤
        ENNReal.ofReal (C * η ^ α)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassDivision
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def pointWithLast {σ : Type} (z : σ → ℂ) (t : ℂ) : Option σ → ℂ
  | none => t
  | some i => z i

def WeierstrassDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (f g : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
    analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = d →
    ∃ (q : (Option σ → ℂ) → ℂ) (a : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
        g x = q x * f x + ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermPrimitivePresentation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsGermCombination {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ)
    (f : (σ → ℂ) → ℂ) : Prop :=
  ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧ ∀ᶠ z in 𝓝 w, f z = ∑ i, h i z * p i z

noncomputable def monicOfCoeffs {N : ℕ} (c : Fin N → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ N + ∑ j : Fin N, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

def IsPrimitivePresentation {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) {N : ℕ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (δ : (Fin d → ℂ) → ℂ) : Prop :=
  (∀ j, AnalyticAt ℂ (c j) (A w)) ∧ AnalyticAt ℂ δ (A w) ∧
  IsGermCombination w p (fun z => ℓ z ^ N + ∑ j, c j (A z) * ℓ z ^ (j : ℕ)) ∧
  (∀ a : Fin N → (Fin d → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) (A w)) →
    IsGermCombination w p (fun z => ∑ j, a j (A z) * ℓ z ^ (j : ℕ)) →
    ∀ j, ∀ᶠ y in 𝓝 (A w), a j y = 0) ∧
  (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → (monicOfCoeffs fun j => c j y).Separable) ∧
  (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
    ∃ (M : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A w)) ∧
      IsGermCombination w p (fun z => δ (A z) ^ M * g z - ∑ j, a j (A z) * ℓ z ^ (j : ℕ))) ∧
  (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
    ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
      IsGermCombination w p (fun z => g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ)) ∧
      ∀ T : ℂ, T ^ n + ∑ j, b j (A w) * T ^ (j : ℕ) = (T - g w) ^ n)

def PrimeGermPrimitivePresentation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → (holGermIdeal w p).IsPrime →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ)
      (c : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ),
      IsPrimitivePresentation w p A ℓ c δ ∧ ¬ IsGermCombination w p (fun z => δ (A z))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem graphPt_injective {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) : Function.Injective (graphPt e F) := by
  intro x y h
  ext i
  have := congrArg (fun z : EuclideanSpace ℂ (Fin n) => z (e.symm (Sum.inl i))) h
  simpa [graphPt] using this

theorem differentiableAt_graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℂ F x) : DifferentiableAt ℂ (graphPt e F) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x
  rcases hj : e j with i | i
  · simp only [Sum.elim_inl]
    exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · simp only [Sum.elim_inr]
    exact (differentiableAt_piLp 2).1 hF i

theorem continuous_areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt

theorem ProjectionFormula.proof (h1 : AreaMultiplicity.Statement) (h2 : FrameJacobianSum.Statement)
    (h3 : GraphAreaHolomorphic.Statement) : ProjectionFormula.Statement := by
  classical
  intro d m n e Ω F hΩ hF b B hB
  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ (graphPt e F) x := fun x hx =>
    differentiableAt_graphPt e (hF.differentiableAt (hΩ.mem_nhds hx))
  set A := Ω ∩ graphPt e F ⁻¹' B with hAdef
  have hAΩ : A ⊆ Ω := Set.inter_subset_left
  have hA : MeasurableSet A := by
    have hc : ContinuousOn (graphPt e F) Ω := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
    have hm := (hc.measurable_piecewise (continuousOn_const (c := (0 : EuclideanSpace ℂ (Fin n))))
      hΩ.measurableSet) hB
    have hEq : A = Ω ∩ (Ω.piecewise (graphPt e F) fun _ => 0) ⁻¹' B := by
      ext x
      simp only [hAdef, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx'⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx] at hx'; exact hx'⟩
    rw [hEq]
    exact hΩ.measurableSet.inter hm

  let πR : ∀ I : Finset (Fin n), EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ I := fun I =>
    (LinearMap.toContinuousLinearMap (frameProjLin b I)).restrictScalars ℝ
  have hpt : ∀ x ∈ A, ENNReal.ofReal (areaJacobian
      (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) =
      ∑ I ∈ Finset.univ.powersetCard d, ENNReal.ofReal (areaJacobian
        ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)) := by
    intro x hx
    set L := fderiv ℂ (graphPt e F) x with hL
    have e0 : ((L.restrictScalars ℝ : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) =
        (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
      LinearMap.ext fun v => rfl
    have eI : ∀ I : Finset (Fin n), (((πR I).comp (L.restrictScalars ℝ)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I) =
        (frameProjLin b I ∘ₗ (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).restrictScalars ℝ :=
      fun I => LinearMap.ext fun v => rfl
    rw [(hGd x (hAΩ hx)).fderiv_restrictScalars ℝ, ← hL, e0, ← ENNReal.ofReal_sum_of_nonneg]
    · simp only [eI]
      exact congrArg ENNReal.ofReal (h2 d n _ b)
    · exact fun I _ => Real.sqrt_nonneg _
  have hmeas : ∀ I : Finset (Fin n), AEMeasurable (fun x => ENNReal.ofReal (areaJacobian
      ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)))
      ((μH[((2 * d : ℕ) : ℝ)]).restrict A) := fun I =>
    ((ENNReal.continuous_ofReal.comp (continuous_areaJacobian.comp
      (continuous_const.clm_comp continuous_id))).measurable.comp
        (measurable_fderiv ℝ (graphPt e F))).aemeasurable
  rw [(Set.image_inter_preimage (graphPt e F) Ω B).symm, h3 d m n e Ω F hΩ hF A hAΩ hA,
    setLIntegral_congr_fun hA hpt, lintegral_finsetSum' _ fun I _ => hmeas I]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hcard : I.card = d := (Finset.mem_powersetCard.1 hI).2
  have hfr1 : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]
  have hfr2 : finrank ℝ (EuclideanSpace ℂ I) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_coe, hcard]
  have hder : ∀ x ∈ A, HasFDerivWithinAt (fun x => frameProjLin b I (graphPt e F x))
      ((πR I).comp (fderiv ℝ (graphPt e F) x)) A x := fun x hx =>
    ((πR I).hasFDerivAt.comp x ((hGd x (hAΩ hx)).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  rw [h1 _ _ (2 * d) hfr1 hfr2 A _ _ hA hder]
  refine lintegral_congr fun y => ?_
  have hset : {z ∈ graphPt e F '' A | frameProj b I z = WithLp.ofLp y} =
      graphPt e F '' {x ∈ A | frameProjLin b I (graphPt e F x) = y} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, ⟨hx, WithLp.ofLp_injective 2 (by rw [frameProjLin_apply]; exact hz)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rw [← frameProjLin_apply, hxy]⟩
  unfold frameFibreCount
  rw [hset, (graphPt_injective e F).injOn.encard_image]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

namespace MassFinite

theorem exists_frame {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j := by
  classical
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 fun j => star (U i j)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i k
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    simp [v, PiLp.inner_apply, Matrix.star_apply, mul_comm]
  refine ⟨OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge,
    fun i z => ?_⟩
  rw [OrthonormalBasis.coe_mk]
  simp [v, PiLp.inner_apply, mul_comm]

theorem eval_pullback {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (P : MvPolynomial (Fin d) ℂ)
    (x : Fin n → ℂ) : eval x (ComplexSets.pullback A P) = eval (A *ᵥ x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [ComplexSets.pullback]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [ComplexSets.pullback, ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem dim_sup_lt {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (f : MvPolynomial (Fin n) ℂ) (hf : f ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) < d := by
  have := hJ
  have hr : Ideal.Quotient.mk J f ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have h := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.factor (le_sup_left : J ≤ J ⊔ Ideal.span {f}))
    (Ideal.Quotient.factor_surjective _) hr
    (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  rw [hd] at h
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have he : e ≠ ⊤ := fun he => by simp [he] at h'
    exact_mod_cast (ENat.add_one_le_iff he).mp h'

theorem ball_lt_top {ι : Type*} [Fintype ι] (R : ℝ) :
    μH[((2 * Fintype.card ι : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R) < ⊤ := by
  have hfr : Module.finrank ℝ (ι × Fin 2 → ℝ) = Module.finrank ℝ (EuclideanSpace ℂ ι) := by
    rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, mul_comm]
  let e := (LinearEquiv.ofFinrankEq _ _ hfr).toContinuousLinearEquiv
  have hcard : ((2 * Fintype.card ι : ℕ) : ℝ) = ((Fintype.card (ι × Fin 2) : ℕ) : ℝ) := by
    simp [mul_comm]
  have hsub : Metric.ball (0 : EuclideanSpace ℂ ι) R ⊆ e '' (e.symm '' Metric.ball 0 R) := by
    rw [Set.image_image]
    simp
  have hb : Bornology.IsBounded (e.symm '' Metric.ball (0 : EuclideanSpace ℂ ι) R) :=
    e.symm.lipschitzWith.isBounded_image Metric.isBounded_ball
  rw [hcard]
  calc μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R)
      ≤ μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (e '' (e.symm '' Metric.ball 0 R)) := measure_mono hsub
    _ ≤ _ := e.lipschitzWith.hausdorffMeasure_image_le (by positivity) _
    _ < ⊤ := by
      refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by exact Nat.cast_nonneg (Fintype.card (ι × Fin 2))) ENNReal.coe_ne_top) ?_
      rw [hausdorffMeasure_pi_real]
      exact hb.measure_lt_top

theorem count_le {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I : Finset (Fin n)) (hI : I.card = d) (S : Set (EuclideanSpace ℂ (Fin n)))
    (hS : S ⊆ zeroSetEuc J) (N : ℕ)
    (hN : ∀ y, (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).Finite ∧
      (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).ncard ≤ N)
    (x : I → ℂ) : frameFibreCount b I S x ≤ N := by
  set e := I.orderIsoOfFin hI
  set A := U.submatrix (I.orderEmbOfFin hI) id
  let y : Fin d → ℂ := fun k => x (e k)
  have hsub : WithLp.ofLp '' {z ∈ S | frameProj b I z = x} ⊆ ComplexSets.fibre J A y := by
    rintro _ ⟨z, ⟨hzS, hzx⟩, rfl⟩
    refine ⟨fun q hq => hS hzS q hq, ?_⟩
    funext k
    have h1 := congrFun hzx (e k)
    simp only [frameProj, hb] at h1
    simp only [y, ← h1, A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id,
      Finset.coe_orderIsoOfFin_apply, e]
  have hinj : Set.InjOn (WithLp.ofLp (p := 2)) {z ∈ S | frameProj b I z = x} :=
    (WithLp.ofLp_injective 2).injOn
  unfold frameFibreCount
  rw [← hinj.encard_image, ← (hN y).1.subset hsub |>.cast_ncard_eq]
  have h2 := Set.ncard_le_ncard hsub (hN y).1
  have h3 := (hN y).2
  exact_mod_cast h2.trans h3

theorem good_localGraph {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I₀ : Finset (Fin n)) (hI : I₀.card = d) (P : MvPolynomial (Fin d) ℂ)
    (hP : ∀ y : Fin d → ℂ, eval y P ≠ 0 →
      ∀ x ∈ ComplexSets.fibre J (U.submatrix (I₀.orderEmbOfFin hI) id) y,
        ∃ (U' : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ)) (g : (Fin d → ℂ) → (Fin n → ℂ)),
          IsOpen U' ∧ y ∈ U' ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ g U' ∧ g y = x ∧
          (∀ w ∈ U', U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ g w = w) ∧
          ComplexSets.zeroSet J ∩ V = g '' U') :
    ∀ z ∈ zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0},
      ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
        (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
          DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
          (zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0}) ∩ V =
            g '' Ω := by
  set A := U.submatrix (I₀.orderEmbOfFin hI) id
  set e := I₀.orderIsoOfFin hI
  rintro z ⟨hzZ, hzP⟩
  obtain ⟨U', V, g, hU', -, hV, hzV, hg, -, hAg, hZV⟩ := hP _ hzP (WithLp.ofLp z) ⟨hzZ, rfl⟩
  let σ : (I₀ → ℂ) →L[ℂ] (Fin d → ℂ) := ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e k)
  have hσ : ∀ w k, σ w k = w (e k) := fun _ _ => rfl
  let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm
  have hL : ∀ v, L v = WithLp.toLp 2 v := fun _ => rfl
  have hcP : Continuous fun w : Fin d → ℂ => eval w P := MvPolynomial.continuous_eval P
  have hcA : Continuous fun z' : EuclideanSpace ℂ (Fin n) => A *ᵥ WithLp.ofLp z' :=
    (Continuous.matrix_mulVec continuous_const continuous_id).comp (PiLp.continuous_ofLp 2 _)
  refine ⟨σ ⁻¹' (U' ∩ {w | eval w P ≠ 0}),
    {z' | WithLp.ofLp z' ∈ V ∧ eval (A *ᵥ WithLp.ofLp z') P ≠ 0}, fun w => L (g (σ w)),
    (hU'.inter (isOpen_ne_fun hcP continuous_const)).preimage σ.continuous,
    (hV.preimage (PiLp.continuous_ofLp 2 _)).inter (isOpen_ne_fun (hcP.comp hcA) continuous_const),
    ⟨hzV, hzP⟩, L.differentiable.comp_differentiableOn (hg.comp σ.differentiable.differentiableOn
      fun w hw => hw.1), fun w hw => ?_, ?_⟩
  · funext i
    have h1 := congrFun (hAg _ hw.1) (e.symm i)
    simp only [A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, hσ,
      ← Finset.coe_orderIsoOfFin_apply, e, OrderIso.apply_symm_apply] at h1
    simp only [frameProj, hb, hL]
    simpa using h1
  · ext z'
    constructor
    · rintro ⟨⟨hz'Z, -⟩, hz'V, hz'P⟩
      have hmem : WithLp.ofLp z' ∈ ComplexSets.zeroSet J ∩ V := ⟨hz'Z, hz'V⟩
      rw [hZV] at hmem
      obtain ⟨w0, hw0, hgw0⟩ := hmem
      have hσw : σ (fun i => w0 (e.symm i)) = w0 := by
        funext k
        simp [hσ]
      refine ⟨fun i => w0 (e.symm i), ⟨by rw [hσw]; exact hw0, ?_⟩, ?_⟩
      · rw [Set.mem_ofPred_eq, hσw, ← hAg w0 hw0, hgw0]
        exact hz'P
      · simp only [hσw, hL, hgw0]
    · rintro ⟨w, ⟨hwU, hwP⟩, rfl⟩
      have hmem : g (σ w) ∈ ComplexSets.zeroSet J ∩ V := hZV ▸ ⟨σ w, hwU, rfl⟩
      have hA : A *ᵥ WithLp.ofLp (L (g (σ w))) = σ w := hAg _ hwU
      refine ⟨⟨fun q hq => hmem.1 q hq, ?_⟩, hmem.2, ?_⟩
      · rw [Set.mem_ofPred_eq, hA]
        exact hwP
      · rw [hA]
        exact hwP

end MassFinite

theorem MassFinite.proof (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hF : ComplexSets.FibreBound.Statement) (hD : ComplexSets.DiscriminantCover.Statement)
    (hN : NullSmaller.Statement) (hL : LocalGraphMass.Statement) : MassFinite.Statement := by
  intro n d J hJ hd R
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  obtain ⟨U, hU, hUfin⟩ := (hG n d J hJ hd).2.2.2 1 (fun _ => 1)
  obtain ⟨b, hb⟩ := MassFinite.exists_frame U hU
  have hfin : ∀ (I : Finset (Fin n)) (hI : I.card = d),
      ComplexSets.IsFiniteProjection J (U.submatrix (I.orderEmbOfFin hI) id) := fun I hI => by
    simpa using hUfin 0 (I.orderEmbOfFin hI).toEmbedding
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hdn)
  set A := U.submatrix (I₀.orderEmbOfFin hI₀) id
  obtain ⟨P, hP0, hP⟩ := hD n d J A hJ hd (hfin I₀ hI₀)
  set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}
  have hPJ : ComplexSets.pullback A P ∉ J := fun hmem => hP0 <| (hfin I₀ hI₀).injective <| by
    rw [map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0 :=
    hN n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)
  have hsub : zeroSetEuc J ∩ Metric.ball 0 R ⊆
      zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ Metric.ball 0 R := by
    rintro z ⟨hz, hzR⟩
    by_cases hzP : eval (A *ᵥ WithLp.ofLp z) P = 0
    · left
      intro q hq
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hzj : eval (fun i => z i) j = 0 := hz j hj
      have hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0 := by
        rw [MassFinite.eval_pullback]
        exact hzP
      simp [hzj, hpb]
    · exact Or.inr ⟨⟨hz, hzP⟩, hzR⟩
  have hgood := hL n d b I₀ G hI₀ (MassFinite.good_localGraph J U b hb I₀ hI₀ P
    (fun y hy x hx => ((hP y hy).2.2 x hx))) R
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball 0 R)
      ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪
          G ∩ Metric.ball 0 R) := measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) +
          μH[((2 * d : ℕ) : ℝ)] (G ∩ Metric.ball 0 R) := measure_union_le _ _
    _ < ⊤ := by
      rw [hbad, zero_add]
      refine lt_of_le_of_lt hgood (ENNReal.sum_lt_top.mpr fun I hI => ENNReal.mul_lt_top ?_ ?_)
      · have hIc := (Finset.mem_powersetCard.mp hI).2
        refine lt_of_le_of_lt (iSup_le fun x => MassFinite.count_le J U b hb I hIc G
          (fun z hz => hz.1) (ComplexSets.projDegree J (U.submatrix (I.orderEmbOfFin hIc) id))
          (fun y => ?_) x) ENNReal.coe_lt_top
        have h := hF n d J _ hJ hd (hfin I hIc) y
        exact ⟨h.2.1, h.2.2⟩
      · have h := MassFinite.ball_lt_top (ι := I) R
        rwa [Fintype.card_coe, (Finset.mem_powersetCard.mp hI).2] at h

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphProjectionMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section


open Classical in
def LocalGraphProjectionMass.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))), I₀.card = d →
    (∀ z ∈ S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω) →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (S ∩ B) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s),
          (⨆ x : EuclideanSpace ℂ (Fin d),
              (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
            μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))

end

end GroundTheory.Heights₂.Heights
end
