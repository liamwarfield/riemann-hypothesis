module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaA
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem jpq_N_zero_om : Formalism.UG.Jpq N 0 = 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem mem_lieU_zero_iff_om (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) :
    X ∈ Formalism.BasicNotions.lieU N 0 ↔ Xᴴ = -X := by
  change Xᴴ * Formalism.UG.Jpq N 0 + Formalism.UG.Jpq N 0 * X = 0 ↔ _
  rw [jpq_N_zero_om, Matrix.mul_one, Matrix.one_mul, eq_neg_iff_add_eq_zero]

theorem skMat_diag_om (x : UCo N) (a : Fin N) : skMat x a a = Complex.I * ((x.1 a : ℝ) : ℂ) := by
  simp [skMat]

theorem skMat_low_om (x : UCo N) (l : {ab : Fin N × Fin N // ab.2 < ab.1}) :
    skMat x l.1.1 l.1.2 = x.2 l := by
  obtain ⟨⟨a, b⟩, h⟩ := l
  show skMat x a b = x.2 ⟨(a, b), h⟩
  simp only [skMat, if_neg (ne_of_gt h), dif_pos h]

theorem skMat_up_om (x : UCo N) (l : {ab : Fin N × Fin N // ab.2 < ab.1}) :
    skMat x l.1.2 l.1.1 = -star (x.2 l) := by
  obtain ⟨⟨a, b⟩, h⟩ := l
  show skMat x b a = -star (x.2 ⟨(a, b), h⟩)
  simp only [skMat, if_neg (ne_of_lt h), dif_neg (not_lt.2 h.le), dif_pos h]

theorem skMat_conjTranspose_om (x : UCo N) : (skMat x)ᴴ = -skMat x := by
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : skMat x b a = x.2 ⟨(b, a), h⟩ := skMat_low_om x ⟨(b, a), h⟩
    have h2 : skMat x a b = -star (x.2 ⟨(b, a), h⟩) := skMat_up_om x ⟨(b, a), h⟩
    rw [h1, h2, neg_neg]
  · rw [skMat_diag_om]
    simp [Complex.conj_ofReal]
  · have h1 : skMat x a b = x.2 ⟨(a, b), h⟩ := skMat_low_om x ⟨(a, b), h⟩
    have h2 : skMat x b a = -star (x.2 ⟨(a, b), h⟩) := skMat_up_om x ⟨(a, b), h⟩
    rw [h1, h2, star_neg, star_star]

theorem skMat_add_om (x y : UCo N) : skMat (x + y) = skMat x + skMat y := by
  ext a b
  simp only [skMat, Matrix.add_apply]
  split_ifs <;> simp [mul_add, star_add, neg_add] <;> ring

theorem skMat_smul_om (c : ℝ) (x : UCo N) : skMat (c • x) = (c : ℂ) • skMat x := by
  ext a b
  simp only [skMat, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Complex.real_smul] <;> ring

instance instBorelSpaceUnitaryLie : BorelSpace (Formalism.BasicNotions.lieU N 0) := ⟨rfl⟩

def complexifyLie : (Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0) →ₗ[ℝ] ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) where
  toFun ab := Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
    Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))
  map_add' x y := by
    funext ij
    simp [Formalism.BasicNotions.entries]
    ring
  map_smul' c x := by
    funext ij
    simp [Formalism.BasicNotions.entries]
    ring

theorem complexifyLie_bijective : Function.Bijective (complexifyLie (N := N)) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ h
    have hA' := (mem_lieU_zero_iff_om A).1 hA
    have hB' := (mem_lieU_zero_iff_om B).1 hB
    have h0 : A + Complex.I • B = 0 := by
      ext i j
      exact congrFun h (i, j)
    have h1 : -A + Complex.I • B = 0 := by
      have e := congrArg Matrix.conjTranspose h0
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA', hB', Matrix.conjTranspose_zero] at e
      have hI : star Complex.I = -Complex.I := Complex.conj_I
      rw [hI, neg_smul_neg] at e
      exact e
    have hA0 : A = 0 := by
      have e : (2 : ℂ) • A = 0 := by
        rw [two_smul]
        calc A + A = (A + Complex.I • B) - (-A + Complex.I • B) := by abel
          _ = 0 := by rw [h0, h1, sub_zero]
      exact (smul_eq_zero.1 e).resolve_left two_ne_zero
    have hB0 : B = 0 := by
      have e : Complex.I • B = 0 := by
        rw [hA0, zero_add] at h0
        exact h0
      exact (smul_eq_zero.1 e).resolve_left Complex.I_ne_zero
    exact Prod.ext (Subtype.ext hA0) (Subtype.ext hB0)
  · intro Z
    let M : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ := Matrix.of fun i j => Z (i, j)
    have hA : ((1 / 2 : ℝ) • (M - Mᴴ)) ∈ Formalism.BasicNotions.lieU N 0 := by
      rw [mem_lieU_zero_iff_om, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose, star_trivial, ← smul_neg, neg_sub]
    have hs : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      rw [star_div₀, star_neg]
      have hI : star Complex.I = -Complex.I := Complex.conj_I
      rw [hI]
      norm_num
      ring
    have hB : ((-Complex.I / 2) • (M + Mᴴ)) ∈ Formalism.BasicNotions.lieU N 0 := by
      rw [mem_lieU_zero_iff_om, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose, add_comm Mᴴ M, hs, neg_smul]
    refine ⟨(⟨_, hA⟩, ⟨_, hB⟩), ?_⟩
    funext ij
    show ((1 / 2 : ℝ) • (M - Mᴴ) + Complex.I • ((-Complex.I / 2) • (M + Mᴴ))) ij.1 ij.2 = Z ij
    simp only [M, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    linear_combination (-(Z ij + star (Z (ij.2, ij.1))) / 2) * Complex.I_sq

def complexifyLieEquiv : (Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0) ≃L[ℝ] ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) :=
  haveI : FiniteDimensional ℝ (Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0) := Module.Finite.prod
  (LinearEquiv.ofBijective complexifyLie complexifyLie_bijective).toContinuousLinearEquiv

theorem complexifyLieEquiv_coe : ⇑(complexifyLieEquiv (N := N)) = fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
    Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
      Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)) := rfl

instance instHaarUCoOm : (volume : Measure (UCo N)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

instance instHaarUCo2Om : (volume : Measure (UCo N × UCo N)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

instance instSecondCountableTopologyUnitaryLie : SecondCountableTopology (Formalism.BasicNotions.lieU N 0) :=
  haveI : SecondCountableTopology (Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N ⊕ Fin 0 → Fin N ⊕ Fin 0 → ℂ))
  Topology.IsInducing.subtypeVal.secondCountableTopology

theorem integral_exp_neg_mul_normSq {c : ℝ} (hc : 0 < c) :
    ∫ z : ℂ, Real.exp (-c * Complex.normSq z) = Real.pi / c := by
  have hn : ∀ p : ℝ × ℝ, Complex.normSq (Complex.measurableEquivRealProd.symm p) = p.1 ^ 2 + p.2 ^ 2 := by
    intro p
    show Complex.normSq ⟨p.1, p.2⟩ = _
    rw [Complex.normSq_mk]
    ring
  have e := (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding (fun z : ℂ => Real.exp (-c * Complex.normSq z))
  rw [← e]
  have hrw : (fun p : ℝ × ℝ => Real.exp (-c * Complex.normSq (Complex.measurableEquivRealProd.symm p))) =
      fun p => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by
    funext p
    rw [hn p, ← Real.exp_add]
    congr 1
    ring
  rw [hrw, Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul (fun x : ℝ => Real.exp (-c * x ^ 2)) (fun y : ℝ => Real.exp (-c * y ^ 2)),
    integral_gaussian, Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hc.le)]

abbrev LoOm (N : ℕ) : Type := {ab : Fin N × Fin N // ab.2 < ab.1}

theorem sum_split_diag_low (f : Fin N → Fin N → ℝ) :
    ∑ p : Fin N × Fin N, f p.1 p.2 = ∑ a, f a a + ∑ l : LoOm N, (f l.1.1 l.1.2 + f l.1.2 l.1.1) := by
  classical
  have h3 : ∀ p : Fin N × Fin N, f p.1 p.2 = ((if p.1 = p.2 then f p.1 p.2 else 0) +
      (if p.2 < p.1 then f p.1 p.2 else 0)) + (if p.1 < p.2 then f p.1 p.2 else 0) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  rw [Finset.sum_congr rfl (fun p _ => h3 p), Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hd : ∑ p : Fin N × Fin N, (if p.1 = p.2 then f p.1 p.2 else 0) = ∑ a, f a a := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_ite_eq]
  have hgen : ∀ g : Fin N → Fin N → ℝ,
      ∑ p : Fin N × Fin N, (if p.2 < p.1 then g p.1 p.2 else 0) = ∑ l : LoOm N, g l.1.1 l.1.2 := by
    intro g
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun p => by simp) (fun p : Fin N × Fin N => g p.1 p.2)
  have hl := hgen f
  have hu : ∑ p : Fin N × Fin N, (if p.1 < p.2 then f p.1 p.2 else 0) = ∑ l : LoOm N, f l.1.2 l.1.1 := by
    have e := hgen (fun a b => f b a)
    try simp only at e
    rw [← e]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun p => rfl)
  rw [hd, hl, hu, add_assoc, ← Finset.sum_add_distrib]

theorem card_LoOm : N + 2 * Fintype.card (LoOm N) = N * N := by
  have h := sum_split_diag_low (N := N) (fun _ _ => (1 : ℝ))
  simp at h
  have e : ((N + 2 * Fintype.card (LoOm N) : ℕ) : ℝ) = ((N * N : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast e

theorem normSq_skMat_sum (x y : UCo N) :
    ∑ p : Fin N × Fin N, Complex.normSq (skMat x p.1 p.2 + Complex.I * skMat y p.1 p.2) =
      ∑ a, (x.1 a ^ 2 + y.1 a ^ 2) + ∑ l : LoOm N, 2 * (Complex.normSq (x.2 l) + Complex.normSq (y.2 l)) := by
  have h := sum_split_diag_low (N := N) (fun a b => Complex.normSq (skMat x a b + Complex.I * skMat y a b))
  try simp only at h
  rw [h]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [skMat_diag_om, skMat_diag_om]
    simp [Complex.normSq_apply]
    ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [skMat_low_om x l, skMat_low_om y l, skMat_up_om x l, skMat_up_om y l]
    simp [Complex.normSq_apply]
    ring

def gaussEOm (Z : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) : ℝ := ∏ p, Real.exp (-1 * Complex.normSq (Z p))

theorem continuous_gaussEOm : Continuous (gaussEOm (N := N)) := by
  unfold gaussEOm
  exact continuous_finsetProd _ fun p _ => Real.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_normSq.comp (continuous_apply p)))

theorem integral_gaussEOm : ∫ Z, gaussEOm (N := N) Z = Real.pi ^ (N * N) := by
  unfold gaussEOm
  rw [MeasureTheory.volume_pi, MeasureTheory.integral_fintype_prod_eq_prod (f := fun _ z => Real.exp (-1 * Complex.normSq z))]
  simp only [integral_exp_neg_mul_normSq one_pos, div_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, add_zero]

def gaussUOm (x : UCo N) : ℝ :=
  (∏ a, Real.exp (-1 * x.1 a ^ 2)) * ∏ l, Real.exp (-2 * Complex.normSq (x.2 l))

theorem integral_gaussUOm : ∫ x, gaussUOm (N := N) x = Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N) := by
  unfold gaussUOm
  rw [Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul (fun y : Fin N → ℝ => ∏ a, Real.exp (-1 * y a ^ 2))
      (fun z : LoOm N → ℂ => ∏ l, Real.exp (-2 * Complex.normSq (z l))),
    MeasureTheory.volume_pi, MeasureTheory.volume_pi, MeasureTheory.integral_fintype_prod_eq_prod (f := fun _ (t : ℝ) => Real.exp (-1 * t ^ 2)),
    MeasureTheory.integral_fintype_prod_eq_prod (f := fun _ (z : ℂ) => Real.exp (-2 * Complex.normSq z))]
  simp only [integral_gaussian, integral_exp_neg_mul_normSq two_pos, div_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem omega_key_real : (2 : ℝ) ^ (N * (N - 1) / 2) * 2 ^ (N * (N - 1) / 2) *
    (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 = Real.pi ^ (N * N) := by
  have hK : Fintype.card (LoOm N) = N * (N - 1) / 2 := by
    have h := card_LoOm (N := N)
    rw [Nat.mul_sub_one]
    generalize N * N = M at h ⊢
    omega
  rw [← hK]
  have h := card_LoOm (N := N)
  set K := Fintype.card (LoOm N)
  have hpi : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have e1 : (Real.sqrt Real.pi ^ N) ^ 2 = Real.pi ^ N := by
    rw [← pow_mul, mul_comm, pow_mul, hpi]
  have e3 : Real.pi ^ (N * N) = Real.pi ^ N * Real.pi ^ K * Real.pi ^ K := by
    rw [← h, pow_add, two_mul, pow_add, mul_assoc]
  rw [mul_pow, e1, e3, div_pow]
  field_simp

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def uToLieMat (x : UCo N) : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ :=
  Matrix.reindex (Equiv.sumEmpty (Fin N) (Fin 0)).symm (Equiv.sumEmpty (Fin N) (Fin 0)).symm (skMat x)

theorem uToLieMat_apply (x : UCo N) (i j : Fin N ⊕ Fin 0) :
    uToLieMat x i j = skMat x (Equiv.sumEmpty (Fin N) (Fin 0) i) (Equiv.sumEmpty (Fin N) (Fin 0) j) := by
  rfl

theorem uToLieMat_mem (x : UCo N) : uToLieMat x ∈ Formalism.BasicNotions.lieU N 0 := by
  rw [mem_lieU_zero_iff_om]
  ext i j
  have h := congrFun (congrFun (skMat_conjTranspose_om x) (Equiv.sumEmpty (Fin N) (Fin 0) i))
    (Equiv.sumEmpty (Fin N) (Fin 0) j)
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h ⊢
  rw [uToLieMat_apply, uToLieMat_apply]
  exact h

def uToLie (x : UCo N) : Formalism.BasicNotions.lieU N 0 := ⟨uToLieMat x, uToLieMat_mem x⟩

def uToLieLin : UCo N →ₗ[ℝ] Formalism.BasicNotions.lieU N 0 where
  toFun := uToLie
  map_add' x y := by
    apply Subtype.ext
    show uToLieMat (x + y) = uToLieMat x + uToLieMat y
    ext i j
    simp [uToLieMat_apply, skMat_add_om]
  map_smul' c x := by
    apply Subtype.ext
    show uToLieMat (c • x) = c • uToLieMat x
    ext i j
    simp [uToLieMat_apply, skMat_smul_om, Complex.real_smul]

theorem uToLieLin_bij : Function.Bijective (uToLieLin (N := N)) := by
  constructor
  · intro x y hxy
    have hm : ∀ a b : Fin N, skMat x a b = skMat y a b := fun a b => by
      have := congrArg (fun z : Formalism.BasicNotions.lieU N 0 =>
        (z : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) (Sum.inl a) (Sum.inl b)) hxy
      simpa [uToLieLin, uToLie, uToLieMat_apply] using this
    refine Prod.ext (funext fun a => ?_) (funext fun l => ?_)
    · have h := hm a a
      rw [skMat_diag_om, skMat_diag_om] at h
      have h' := mul_left_cancel₀ Complex.I_ne_zero h
      exact_mod_cast h'
    · have h := hm l.1.1 l.1.2
      rwa [skMat_low_om, skMat_low_om] at h
  · rintro ⟨X, hX⟩
    have hX' := (mem_lieU_zero_iff_om X).1 hX
    have hent : ∀ i j, star (X j i) = -X i j := fun i j => by
      have := congrFun (congrFun hX' i) j
      simpa [Matrix.conjTranspose_apply] using this
    refine ⟨((fun a => (X (Sum.inl a) (Sum.inl a)).im), fun l => X (Sum.inl l.1.1) (Sum.inl l.1.2)), ?_⟩
    apply Subtype.ext
    show uToLieMat _ = X
    ext i j
    rcases i with a | i
    · rcases j with b | j
      · rw [uToLieMat_apply]
        simp only [Equiv.sumEmpty_apply_inl]
        unfold skMat
        split_ifs with h1 h2 h3
        · subst h1
          have hre : (X (Sum.inl a) (Sum.inl a)).re = 0 := by
            have := congrArg Complex.re (hent (Sum.inl a) (Sum.inl a))
            simp at this
            linarith
          apply Complex.ext <;> simp [hre]
        · rfl
        · show -star (X (Sum.inl b) (Sum.inl a)) = X (Sum.inl a) (Sum.inl b)
          rw [hent (Sum.inl a) (Sum.inl b), neg_neg]
        · exact absurd (lt_trichotomy a b) (by tauto)
      · exact j.elim0
    · exact i.elim0

def uToLieE : UCo N ≃L[ℝ] Formalism.BasicNotions.lieU N 0 :=
  (LinearEquiv.ofBijective uToLieLin uToLieLin_bij).toContinuousLinearEquiv

theorem uToLieE_coe : ⇑(uToLieE (N := N)) = uToLie := rfl

def phiOmE : (UCo N × UCo N) ≃L[ℝ] ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) :=
  (uToLieE.prodCongr uToLieE).trans complexifyLieEquiv

theorem phiOmE_apply (x y : UCo N) (p : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0)) :
    phiOmE (x, y) p = skMat x (Equiv.sumEmpty (Fin N) (Fin 0) p.1) (Equiv.sumEmpty (Fin N) (Fin 0) p.2) +
      Complex.I * skMat y (Equiv.sumEmpty (Fin N) (Fin 0) p.1) (Equiv.sumEmpty (Fin N) (Fin 0) p.2) := by
  show complexifyLieEquiv (uToLieE x, uToLieE y) p = _
  rw [complexifyLieEquiv_coe, uToLieE_coe]
  simp [Formalism.BasicNotions.entries, uToLie, uToLieMat_apply]

theorem phiOmE_haar : ((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N))).IsAddHaarMeasure := by
  exact phiOmE.isAddHaarMeasure_map volume
theorem gaussEOm_phiOmE (x y : UCo N) : gaussEOm (phiOmE (x, y)) = gaussUOm x * gaussUOm y := by
  have hsum : ∑ p : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0), Complex.normSq (phiOmE (x, y) p) =
      ∑ a, (x.1 a ^ 2 + y.1 a ^ 2) + ∑ l : LoOm N, 2 * (Complex.normSq (x.2 l) + Complex.normSq (y.2 l)) := by
    rw [← normSq_skMat_sum]
    exact Fintype.sum_equiv ((Equiv.sumEmpty (Fin N) (Fin 0)).prodCongr (Equiv.sumEmpty (Fin N) (Fin 0))) _ _
      (fun p => by rw [phiOmE_apply]; rfl)
  calc gaussEOm (phiOmE (x, y)) = Real.exp (-(∑ p, Complex.normSq (phiOmE (x, y) p))) := by
        rw [gaussEOm, ← Real.exp_sum]
        congr 1
        simp [Finset.sum_neg_distrib]
    _ = gaussUOm x * gaussUOm y := by
        rw [hsum]
        simp only [gaussUOm, ← Real.exp_sum, ← Real.exp_add]
        congr 1
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
        ring

theorem integral_gaussEOm_phiOmE : ∫ Z, gaussEOm Z ∂((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N))) =
    (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 := by
  rw [MeasureTheory.integral_map phiOmE.continuous.measurable.aemeasurable
    continuous_gaussEOm.aestronglyMeasurable]
  show ∫ z : UCo N × UCo N, gaussEOm (phiOmE (z.1, z.2)) = _
  simp_rw [gaussEOm_phiOmE]
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_mul (f := gaussUOm) (g := gaussUOm), integral_gaussUOm, sq]

theorem map_uToLie_haar : (Measure.map (uToLie (N := N)) volume).IsAddHaarMeasure := by
  rw [← uToLieE_coe]
  exact uToLieE.isAddHaarMeasure_map volume

private lemma prod_map_lemma (c : ENNReal) :
    ((c • Measure.map (uToLie (N := N)) volume).prod (c • Measure.map (uToLie (N := N)) volume)).map
      (fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) =
      (c * c) • (volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)) := by
  have hm : Measurable (uToLie (N := N)) := by
    rw [← uToLieE_coe]
    exact uToLieE.continuous.measurable
  have hp : Measurable (fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) := by
    rw [← complexifyLieEquiv_coe]
    exact complexifyLieEquiv.continuous.measurable
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul (c * c) hp.aemeasurable,
    Measure.map_prod_map _ _ hm hm, Measure.map_map hp (hm.prodMap hm)]
  congr 2

private lemma vol_eq_lemma_2 :
    (volume : Measure ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ)) =
      ENNReal.ofReal (2 ^ (N * (N - 1) / 2) * 2 ^ (N * (N - 1) / 2)) •
        (volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)) := by
  haveI := phiOmE_haar (N := N)
  have h1 := Measure.isAddLeftInvariant_eq_smul (volume : Measure ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ))
    ((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)))
  rw [ENNReal.smul_def] at h1
  have hI := integral_gaussEOm (N := N)
  rw [h1, integral_smul_measure, integral_gaussEOm_phiOmE, smul_eq_mul, ENNReal.coe_toReal] at hI
  have hk := omega_key_real (N := N)
  have hI2 : (0 : ℝ) < (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 := by positivity
  have hs := mul_right_cancel₀ hI2.ne' (hI.trans hk.symm)
  rw [h1, ← ENNReal.ofReal_coe_nnreal, hs]

theorem isOmegaLeb_uToLie :
    Formalism.BasicNotions.IsOmegaLeb (ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) • Measure.map (uToLie (N := N)) volume) := by
  refine ⟨?_, ?_⟩
  · haveI := map_uToLie_haar (N := N)
    exact Measure.IsAddHaarMeasure.smul _ (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top
  · rw [prod_map_lemma, ← ENNReal.ofReal_mul (by positivity), vol_eq_lemma_2]

end ReciprocityTheory.ChartRestriction.DS
