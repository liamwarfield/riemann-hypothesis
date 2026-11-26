module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem isOpenEmbedding_entriesGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

theorem measurable_comp_GLInf {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) (Cinf E) → β} (hF : Continuous F) {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_entriesGLInf.measurableEmbedding.measurable_comp_iff).1
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j)
  exact hF.measurable.comp h

theorem htInf_pos' (g : GL (Fin n) (Cinf E)) : 0 < htInf g := by
  unfold htInf
  exact Finset.prod_pos fun w _ => htGL_pos _

theorem htInf_mul_le (g h : GL (Fin n) (Cinf E)) : htInf (g * h) ≤ htInf g * htInf h := by
  unfold htInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => (htGL_pos _).le) fun w _ => ?_
  rw [map_mul]
  exact htGL_mul_le _ _

theorem IsRapidFInf.integrable {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin n) (Cinf E)} {η : X → Z →L[ℝ] ℝ} (h : IsRapidFInf ν k γ η)
    {W : GL (Fin n) (Cinf E) → ℂ} (hW : IsModGrowthInf W) (z : Z) (g : GL (Fin n) (Cinf E)) :
    Integrable (fun x => k x * (𝐞 (η x z) : ℂ) * W (g * γ x)) ν := by
  obtain ⟨hc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)
  refine ((h.2.2.2 N).const_mul (C * htInf g ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Measurable.aestronglyMeasurable ((h.1.mul ?_).mul ?_)
    · exact (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp (h.2.2.1 z)
    · exact measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop) h.2.1
  · rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    have h1 : htInf (g * γ x) ≤ htInf g * (htInf (γ x) * (1 + ‖η x‖)) :=
      (htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (htInf_pos' _).le (by linarith [norm_nonneg (η x)])) (htInf_pos' _).le)
    have h2 := pow_le_pow_left₀ (htInf_pos' _).le h1 N
    rw [mul_pow] at h2
    calc ‖k x‖ * ‖W (g * γ x)‖ ≤ ‖k x‖ * (C * (htInf g ^ N * (htInf (γ x) * (1 + ‖η x‖)) ^ N)) :=
          mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
      _ = _ := by ring

theorem isKerOpInf_zero_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    IsKerOpInf (E := E) (n := n)
      (fun (_ : GL (Fin n) (Cinf E) → ℂ) (_ : Z) (_ : GL (Fin n) (Cinf E)) => (0 : ℂ)) := by
  refine ⟨Unit, inferInstance, 0, inferInstance, fun _ => 0, fun _ => 1, fun _ => 0, ?_, ?_⟩
  · exact ⟨measurable_const, fun _ _ => measurable_const, fun _ => measurable_const, fun _ => integrable_zero_measure⟩
  · intro W _ z g
    simp

theorem isKerOpInf_add_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T T' : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ} (hT : IsKerOpInf T) (hT' : IsKerOpInf T') :
    IsKerOpInf (fun W z g => T W z g + T' W z g) := by
  obtain ⟨X, mX, ν, hν, k, γ, η, hr, hT⟩ := hT
  obtain ⟨X', mX', ν', hν', k', γ', η', hr', hT'⟩ := hT'
  have e1 : MeasurableEmbedding (Sum.inl : X → X ⊕ X') :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => measurableSet_inl_image.2 hs⟩
  have e2 : MeasurableEmbedding (Sum.inr : X' → X ⊕ X') :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => measurableSet_inr_image.2 hs⟩
  refine ⟨X ⊕ X', inferInstance, ν.map Sum.inl + ν'.map Sum.inr, inferInstance, Sum.elim k k', Sum.elim γ γ',
    Sum.elim η η', ?_, ?_⟩
  · refine ⟨hr.1.sumElim hr'.1, fun i j => ?_, fun z => ?_, fun N => ?_⟩
    · have : (fun x : X ⊕ X' => ((Sum.elim γ γ' x : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
          Sum.elim (fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j)
            (fun x => (γ' x : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.1 i j).sumElim (hr'.2.1 i j)
    · have : (fun x : X ⊕ X' => Sum.elim η η' x z) = Sum.elim (fun x => η x z) (fun x => η' x z) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.2.1 z).sumElim (hr'.2.2.1 z)
    · rw [integrable_add_measure, e1.integrable_map_iff, e2.integrable_map_iff]
      exact ⟨hr.2.2.2 N, hr'.2.2.2 N⟩
  · intro W hW z g
    have i1 := hr.integrable hW z g
    have i2 := hr'.integrable hW z g
    show T W z g + T' W z g = _
    rw [integral_add_measure, e1.integral_map, e2.integral_map, hT W hW z g, hT' W hW z g]
    · rfl
    · rw [e1.integrable_map_iff]; exact i1
    · rw [e2.integrable_map_iff]; exact i2

theorem isKerOpInf_fintype_sum (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι]
    (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ) (hT : ∀ i, IsKerOpInf (T i)) :
    IsKerOpInf (fun W z g => ∑ i, T i W z g) := by
  classical
  suffices h : ∀ s : Finset ι, IsKerOpInf (fun W z g => ∑ i ∈ s, T i W z g) from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (isKerOpInf_zero_sum (E := E) (n := n) (Z := Z))
  | insert a s ha ih =>
    have : (fun W z g => ∑ i ∈ insert a s, T i W z g) = fun W z g => T a W z g + ∑ i ∈ s, T i W z g := by
      funext W z g; rw [Finset.sum_insert ha]
    rw [this]
    exact isKerOpInf_add_sum (hT a) ih

end GlobalTheory.JSW.MirCinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSumStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArchimedeanRapidKernelOperator_finset_sum : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι] (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), (∀ i, IsKerOpInf (T i)) → IsKerOpInf (fun W z g => ∑ i, T i W z g) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isKerOpInf_fintype_sum) | (exact GlobalTheory.JSW.MirCinf.isKerOpInf_fintype_sum) | (intros; apply GlobalTheory.JSW.MirCinf.isKerOpInf_fintype_sum  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBound
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.BrCompare GlobalTheory.BrCompare.Shift

noncomputable section

namespace GlobalTheory.BranchLogBound

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

def sgN (lam : DomWeight (n + 1)) (sg : DomWeight n) : Fin n → ℕ := fun i => (sg.w i - lam.w (Fin.last n)).toNat

theorem interlace_w (h : Br.Interlace rfl lam sg) : Formalism.BranchingDeterminantCap.Interlace lam.w sg.w := by
  intro i
  have : 0 ≤ sg.w i - lam.w i.succ ∧ 0 ≤ lam.w i.castSucc - sg.w i := h i
  omega

theorem sgN_cast (h : Br.Interlace rfl lam sg) (i : Fin n) : (sgN lam sg i : ℤ) = sg.w i - lam.w (Fin.last n) := by
  have h1 := (interlace_w h i).2
  have h2 := lam.anti (Fin.le_last i.succ)
  unfold sgN
  omega

theorem interlace_N (h : Br.Interlace rfl lam sg) : Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sgN lam sg i : ℤ)) := by
  intro i
  have := interlace_w h i
  simp only [lamZ_lamN, sgN_cast h]
  omega

theorem xiBr_eq (h : Br.Interlace rfl lam sg) (K : Type) [Field K] :
    Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) (sgN lam sg)) := by
  have hb : ∀ s, (Br.bBr rfl lam sg s).toNat = lamN lam s - sgN lam sg s := by
    intro s
    have h1 := lamN_cast lam s
    have h2 := sgN_cast h s
    have h3 : Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s := rfl
    rw [h3]
    omega
  have ha : ∀ s, (Br.aBr rfl lam sg s).toNat = sgN lam sg s - nuNext (lamN lam) s := by
    intro s
    have h1 := nuNext_cast lam s
    have h2 := sgN_cast h s
    have h3 : Br.aBr rfl lam sg s = sg.w s - lam.w s.succ := rfl
    rw [h3]
    omega
  unfold Br.xiBr xiB
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]
  congr 2

theorem extremal_eq (lam : DomWeight (n + 1)) (K : Type) [Field K] :
    extremal K (n + 1) lam = incl K n (hw K (Nat.le_succ n) (lamN lam)) := by
  unfold extremal hw
  rw [map_prod, Fin.prod_univ_castSucc]
  have h0 : lam.natW (Fin.last n) = 0 := by
    have := natW_top lam (Fin.last n)
    omega
  rw [h0, Nat.zero_sub, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]
  congr 1
  · exact (rename_initMinor K (Fin.castLE (by have := i.2; omega) : Fin (i.val + 1) → Fin (n + 1)) (by have := i.2; omega)).symm
  · have h1 := nuNext_cast lam i
    have h2 := natW_top lam i.succ
    have h3 : nuNext lam.natW i.castSucc = lam.natW i.succ := by
      unfold nuNext
      rw [dite_eq_left (by simp)]
      rfl
    rw [h3]
    have h4 : lamN lam i = lam.natW i.castSucc := rfl
    omega

theorem fockF_map {σ : Type} (f : MvPolynomial σ ℝ) :
    (Formalism.REAL.fockF (map (algebraMap ℝ ℂ) f) (map (algebraMap ℝ ℂ) f)).re = fockB f f := by
  unfold Formalism.REAL.fockF fockB
  rw [support_map_of_injective _ (algebraMap ℝ ℂ).injective, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : ∀ (x : ℝ) (k : ℕ), ((algebraMap ℝ ℂ x) * (starRingEnd ℂ) (algebraMap ℝ ℂ x) * (k : ℂ)).re = x * x * k := by
    intro x k
    simp
  rw [coeff_map]
  exact this _ _

theorem map_xiB (l s : Fin n → ℕ) : map (algebraMap ℝ ℂ) (xiB ℝ l s) = xiB ℂ l s := by
  simp only [xiB, map_prod, map_mul, map_pow, initMinor, RingHom.map_det]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 3 <;> ext1 a b <;> simp

theorem kap_bounds (h : Br.Interlace rfl lam sg) :
    0 < Br.kapBr ℝ rfl lam sg ∧ Br.kapBr ℝ rfl lam sg ≤ weylProd (lamZ (lamN lam)) := by
  have h1 := xiNorm n (lamN lam) (sgN lam sg) (interlace_N h)
  have h2 := (fockPos _ _ (GlobalTheory.Branching.xiB_ne_zero (lamN lam) (sgN lam sg))).1
  have h3 := (fockPos _ _ (hwNe ℂ (n + 1) n (Nat.le_succ n) (lamN lam))).1
  have e : hw ℂ (Nat.le_succ n) (lamN lam) = map (algebraMap ℝ ℂ) (hw ℝ (Nat.le_succ n) (lamN lam)) :=
    (lclosedeq_hw_map _ _ _).symm
  rw [← map_xiB, fockF_map] at h1 h2
  rw [e, fockF_map] at h1 h3
  unfold Br.kapBr
  rw [xiBr_eq h, extremal_eq, fockB_incl, fockB_incl]
  exact ⟨div_pos h2 h3, (div_le_iff₀ h3).2 h1⟩

theorem spread_eq (lam : DomWeight (n + 1)) : lam.spread = lam.w 0 - lam.w (Fin.last n) + (n + 1 : ℕ) := by
  unfold DomWeight.spread
  rw [dite_eq_left (Nat.succ_pos n)]
  rfl

theorem kap_le (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    Br.kapBr ℝ rfl lam sg ≤ A ^ ((n + 1) * n / 2) := by
  have ha : Antitone (lamZ (lamN lam)) := fun a b hab => by
    have := lam.anti hab
    simp only [lamZ_lamN]
    omega
  refine (kap_bounds h).2.trans ((weylDimBound n _ ha).2.trans ?_)
  have h0 := ha (Fin.zero_le (Fin.last n))
  refine pow_le_pow_left₀ (add_nonneg (by exact_mod_cast sub_nonneg.2 h0) (Nat.cast_nonneg n)) ?_ _
  rw [spread_eq] at hA
  simp only [lamZ_lamN]
  push_cast at hA ⊢
  linarith

theorem cBr_eq (lam : DomWeight (n + 1)) (sg : DomWeight n) : Br.cBr rfl lam sg = cCap lam.w sg.w := by
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_
  ring

theorem c_bounds (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    Br.cBr rfl lam sg ≠ 0 ∧ |((Br.cBr rfl lam sg : ℤ) : ℝ)| ≤ A ^ (n * (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg).toNat) := by
  obtain ⟨h1, h2⟩ := capConst n lam.w sg.w (interlace_w h)
  rw [cBr_eq]
  refine ⟨h1, ?_⟩
  have e : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg = d1 lam.w sg.w := rfl
  rw [e]
  have h3 : |((cCap lam.w sg.w : ℤ) : ℝ)| ≤
      ((lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1 : ℤ) : ℝ) ^ (n * (d1 lam.w sg.w).toNat) := by exact_mod_cast h2
  refine h3.trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h0 := lam.anti (Fin.zero_le (Fin.last n))
  refine pow_le_pow_left₀ (by exact_mod_cast (by omega : (0 : ℤ) ≤ lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1)) ?_ _
  rw [spread_eq] at hA
  push_cast at hA ⊢
  linarith

theorem one_position (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    0 < ((Br.cBr rfl lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ rfl lam sg ∧
    Real.log (((Br.cBr rfl lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ rfl lam sg) ≤
      (2 * (((n + 1 : ℕ) : ℝ) - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg : ℤ) : ℝ) +
        ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) / 2) * Real.log A := by
  obtain ⟨c1, c2⟩ := c_bounds h hA
  have k1 := (kap_bounds h).1
  have k2 := kap_le h hA
  have c0 : ((Br.cBr rfl lam sg : ℤ) : ℝ) ≠ 0 := by exact_mod_cast c1
  have hd : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg := (interlaceIdent n lam.w sg.w (interlace_w h)).2.2.2.1
  have hd' : (((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg).toNat : ℕ) : ℝ) = ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg : ℤ) : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hd)
  have he : (((n + 1) * n / 2 : ℕ) : ℝ) = ((n : ℝ) + 1) * n / 2 := by
    rw [Nat.cast_div (by rw [mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd) (by norm_num)]
    push_cast
    ring
  refine ⟨by positivity, ?_⟩
  have l1 := Real.log_le_log (abs_pos.2 c0) c2
  have l2 := Real.log_le_log k1 k2
  rw [Real.log_pow, Real.log_abs, Nat.cast_mul, hd'] at l1
  rw [Real.log_pow, he] at l2
  rw [Real.log_mul (pow_ne_zero 2 c0) k1.ne', Real.log_pow]
  push_cast
  linarith

theorem orthNormLogBound : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.OrthNormLogBound := by
  refine ⟨2, fun ι _ N n hN lam sg h1 a ha => ?_⟩
  refine ⟨?_, ?_, GlobalTheory.BrNormCompare.last_ineq hN lam sg h1 a ha⟩
  · subst hN
    exact Finset.prod_pos fun τ _ => (one_position (h1 τ) (ha τ)).1
  · subst hN
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq
    rw [Real.log_prod fun τ _ => (one_position (h1 τ) (ha τ)).1.ne']
    exact Finset.sum_le_sum fun τ _ => (one_position (h1 τ) (ha τ)).2

end GlobalTheory.BranchLogBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIdeleCharTrivialCongruentOneModulo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIdeleCharTrivialCongruentOneModulo
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct Topology

namespace GlobalTheory.HeckeSplitGen

theorem integralFiniteAdelesTensor_eq_adelicCompletion_integers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    intAEF F E = GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  unfold intAEF GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem char_trivial_modSetF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : (AF F ⊗[F] E)ˣ →* Circle), Continuous ν →
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitGen.modSetF F E N, ν x = 1 := by
  intro F E _ _ _ _ _ ν hν
  obtain ⟨e, he, -, he'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (GlobalTheory.AdLat.RA F E) := ⟨rfl⟩
  haveI : ContinuousAdd (GlobalTheory.AdLat.RA F E) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  have hsmall := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 0 ⊤ (by simp)).2
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.finite_order_of_small (infPartF F E) (finPartF F E) e.symm he'
    (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext (he z).1.symm (he z).2.symm)
    (GlobalTheory.CharFin.hatRing F E) hsmall (GlobalTheory.CharFin.finite_quotient_hatRing F E) ν hν
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨h1, ⟨r, hr, hxr⟩, h3⟩ := hx
  rw [integralFiniteAdelesTensor_eq_adelicCompletion_integers] at hr h3
  have hNr : (N : Af F ⊗[F] E) * r = N • r := (nsmul_eq_mul _ _).symm
  have hfin : finPartF F E (x : AEF F E) ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    have : finPartF F E (x : AEF F E) = 1 + N • r := by rw [← hNr, ← hxr]; ring
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨1, fun w => one_mem _, _, ⟨1, rfl⟩,
      by simp [Algebra.TensorProduct.one_def]⟩) (nsmul_mem hr N)
  exact hker x ⟨h1, hfin, h3⟩ ⟨r, hr, by rw [hxr, hNr]⟩

end GlobalTheory.HeckeSplitGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIdeleCharTrivialCongruentOneModuloStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIdeleChar_trivial_congruentOneModulo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : (AF F ⊗[F] E)ˣ →* Circle), Continuous ν → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitGen.modSetF F E N, ν x = 1 := by
  exact @GlobalTheory.HeckeSplitGen.char_trivial_modSetF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticSubfieldRootDiscriminant
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke Polynomial

namespace GlobalTheory

theorem finrank_eq_two_of_adjoin_sqrt_eq_top (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a) (h1 : a ≠ 1) :
    Module.finrank ℚ K = 2 := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
  rw [hmin, natDegree_X_pow_sub_C _, hadj, IntermediateField.finrank_top'] at this
  exact this

theorem adjoin_gen_eq_top_rat {E : Type} [Field E] [NumberField E] (y : E) :
    IntermediateField.adjoin ℚ {IntermediateField.AdjoinSimple.gen ℚ y} = ⊤ := by
  apply IntermediateField.lift_injective
  exact (IntermediateField.lift_adjoin_simple ℚ _ (IntermediateField.AdjoinSimple.gen ℚ y)).trans
    (IntermediateField.lift_top ℚ (IntermediateField.adjoin ℚ {y})).symm

theorem rootDiscr_and_different_quadField :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
      rootDiscr (AdelicDegreeTameRamification.quadField H) = √(H.d : ℝ) ∧
      (differentIdeal ℤ (𝓞 (AdelicDegreeTameRamification.quadField H))).map (algebraMap (𝓞 (AdelicDegreeTameRamification.quadField H)) (𝓞 E)) =
        Ideal.span {H.rt} := by
  intro E _ _ _ H
  have hd16 := H.d_mod
  have hb2 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  obtain ⟨x, hxdef, hadj⟩ : ∃ x : AdelicDegreeTameRamification.quadField H, (x : E) = (H.rt : E) ∧
      IntermediateField.adjoin ℚ {x} = ⊤ :=
    ⟨IntermediateField.AdjoinSimple.gen ℚ _, rfl, adjoin_gen_eq_top_rat _⟩
  have hx : x ^ 2 = ((-(H.d : ℤ) : ℤ) : AdelicDegreeTameRamification.quadField H) := by
    apply Subtype.ext
    push_cast
    rw [hxdef, hb2]
  have hint : IsIntegral ℤ x := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hx, ← eq_intCast (algebraMap ℤ (AdelicDegreeTameRamification.quadField H))]
    exact isIntegral_algebraMap
  have hsf : Squarefree (-(H.d : ℤ)) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
    exact H.d_prime.squarefree
  obtain ⟨x', hx'⟩ : ∃ x' : 𝓞 (AdelicDegreeTameRamification.quadField H), (x' : AdelicDegreeTameRamification.quadField H) = x := ⟨⟨x, hint⟩, rfl⟩
  have hdiff := Formalism.MainNotions.UnusedSlot33.HK.different_quad (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf
    (by omega) (by omega) x' hx'
  have h2 := finrank_eq_two_of_adjoin_sqrt_eq_top (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega)
  have hD := Formalism.HF.P.quadDiscr_ne_one (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]
    simp
  · rw [hdiff, Ideal.map_span, Set.image_singleton]
    congr 2
    apply RingOfIntegers.coe_injective
    show ((x' : AdelicDegreeTameRamification.quadField H) : E) = _
    rw [hx', hxdef]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOnePara
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOnePara
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem continuous_heisV_snd {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (u : VA F N) (g : VA F N → ℂ) (hg : Continuous g)
    (x : Fin N → AF F) : Continuous fun y : Fin N → AF F => heisV ψ u g (x, y) := by
  unfold heisV symV
  have h1 : Continuous fun y : Fin N → AF F => (x, y).1 ⬝ᵥ u.2 - u.1 ⬝ᵥ (x, y).2 := by
    simp only [dotProduct]
    fun_prop
  refine (hψ.comp (continuous_const.mul h1)).mul (hg.comp ?_)
  fun_prop

theorem heisV_zero {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (g : VA F N → ℂ) : heisV ψ 0 g = g := by
  funext w
  simp [heisV, symV, AddChar.map_zero_eq_one]

open GlobalTheory.GaugeEx in
theorem hasDerivAt_invV_heisV : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ (f f' : VA F N → ℂ) (C : ℝ), Continuous f → Continuous f' → (∀ w, ‖f w‖ ≤ C) → (∀ w, ‖f' w‖ ≤ C) → ∀ M : ℝ →+ VA F N, Continuous M → (∀ w s, HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (heisV ψ (M s) f' w) s) → ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0 := by
  intro F _ _ N _ ψ lam ν hC 𝓓 _ h1 f f' C hf hf' hfC hf'C M _ hM x
  have hψ := hC.2.1
  haveI : IsFiniteMeasure ((muV N ν).restrict 𝓓) := isFiniteMeasure_restrict.2 (by rw [h1]; simp)
  have hcont : ∀ (u : VA F N) (g : VA F N → ℂ), Continuous g →
      Continuous fun y : Fin N → AF F => heisV ψ u g (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
    intro u g hg
    refine (continuous_heisV_snd ψ hψ.1 u g hg x).mul (hψ.1.comp ?_)
    simp only [dotProduct]
    fun_prop
  have hnorm : ∀ (u : VA F N) (g : VA F N → ℂ), (∀ w, ‖g w‖ ≤ C) → ∀ y : Fin N → AF F,
      ‖heisV ψ u g (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))‖ ≤ C := by
    intro u g hg y
    simp only [heisV, norm_mul, hψ.2.1, one_mul, mul_one]
    exact hg _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (muV N ν).restrict 𝓓)
    (F := fun t y => heisV ψ (M t) f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))))
    (F' := fun t y => heisV ψ (M t) f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))))
    (x₀ := (0 : ℝ)) (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hcont _ f hf).aestronglyMeasurable)
    (Integrable.of_bound (hcont _ f hf).aestronglyMeasurable C (Filter.Eventually.of_forall (hnorm _ f hfC)))
    (hcont _ f' hf').aestronglyMeasurable
    (ae_of_all _ fun y t _ => hnorm _ f' hf'C y)
    (integrable_const C)
    (ae_of_all _ fun y t _ => (hM (x, y) t).mul_const _)
  have e : (fun y => heisV ψ (M 0) f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))) =
      fun y => f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
    rw [map_zero, heisV_zero]
  have k2 := key.2
  simp only [e] at k2
  exact k2

end GlobalTheory.ThetaTransform
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOneParaStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ (f f' : VA F N → ℂ) (C : ℝ), Continuous f → Continuous f' → (∀ w, ‖f w‖ ≤ C) → (∀ w, ‖f' w‖ ≤ C) → ∀ M : ℝ →+ VA F N, Continuous M → (∀ w s, HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (heisV ψ (M s) f' w) s) → ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0 := by
  first | exact @GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV | exact GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV | (intros; apply GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLocAdele
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.PlaceApprox

variable {F : Type} [Field F] [NumberField F]


open Classical in
def locAdele (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F)))
    (p : ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion)) : AF F :=
  ((fun u : InfinitePlace F => if h : u ∈ S₁ then p.2 ⟨u, h⟩ else 0 : InfiniteAdeleRing F),
    ∑ v : S₂, GlobalTheory.AdelicU.singleFin v.1 (p.1 v))

open Classical in
theorem continuous_locAdele (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (locAdele S₁ S₂) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun u => ?_
    by_cases h : u ∈ S₁
    · simp only [h, dite_true]
      exact (continuous_apply _).comp continuous_snd
    · simp only [h, dite_false]
      exact continuous_const
  · exact continuous_finsetSum _ fun v _ =>
      (GlobalTheory.AdelicU.continuous_singleFin v.1).comp ((continuous_apply v).comp continuous_fst)

open Classical in
theorem locAdele_zero (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    locAdele S₁ S₂ 0 = 0 := by
  refine Prod.ext ?_ ?_
  · funext u
    change (if h : u ∈ S₁ then (0 : u.Completion) else 0) = 0
    split_ifs <;> rfl
  · simp [locAdele]

open Classical in
theorem mul_eq_locAdele {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (hε : IsPlacesIdem S₁ S₂ ε) (a : AF F) :
    ε * a = locAdele S₁ S₂ ((fun v => evalV F v.1 (sndA F a)), (fun w => fstA F a w.1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hε
  refine Prod.ext ?_ ?_
  · funext u
    change fstA F ε u * fstA F a u = _
    by_cases h : u ∈ S₁
    · simp only [locAdele, h, dite_true, h1 u h, one_mul]
    · simp only [locAdele, h, dite_false, h2 u h, zero_mul]
  · apply GlobalTheory.AdelicU.af_ext
    intro u
    change evalV F u (sndA F ε) * evalV F u (sndA F a) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [locAdele, map_sum]
    by_cases h : u ∈ S₂
    · rw [h3 u h, one_mul, Finset.sum_eq_single ⟨u, h⟩]
      · exact (GlobalTheory.AdelicU.evalV_singleFin_self u _).symm
      · intro b _ hb
        exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun e => hb (Subtype.ext e.symm)) _
      · intro hn; exact absurd (Finset.mem_univ _) hn
    · rw [h4 u h, zero_mul, Finset.sum_eq_zero]
      intro b _
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun e => h (by rw [e]; exact b.2)) _

theorem loc_sub_algebraMap (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (x : AF F) (t : F) :
    (((fun v : S₂ => evalV F v.1 (sndA F (x - algebraMap F (AF F) t))),
      (fun w : S₁ => fstA F (x - algebraMap F (AF F) t) w.1)) :
        ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion)) =
      ((fun v : S₂ => evalV F v.1 (sndA F x)), (fun w : S₁ => fstA F x w.1)) -
        ((fun v : S₂ => algebraMap F (v.1.adicCompletion F) t), (fun w : S₁ => algebraMap F w.1.Completion t)) := by
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · simp only [map_sub, AlgHom.commutes, Prod.fst_sub, Pi.sub_apply]
  · simp only [map_sub, AlgHom.commutes, Prod.snd_sub, Pi.sub_apply]
    rfl

theorem weak_approx_idem : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 (0 : AF F) → ∃ t : F, ε * (x - algebraMap F (AF F) t) ∈ U := by
  intro F _ _ S₁ S₂ ε hε x U hU
  set c : ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion) :=
    ((fun v : S₂ => evalV F v.1 (sndA F x)), (fun w : S₁ => fstA F x w.1)) with hc
  have hO : {p | locAdele S₁ S₂ (c - p) ∈ U} ∈ 𝓝 c := by
    have hcont : Continuous fun p => locAdele S₁ S₂ (c - p) :=
      (continuous_locAdele S₁ S₂).comp (continuous_const.sub continuous_id)
    have h0 : locAdele S₁ S₂ (c - c) = 0 := by
      rw [sub_self, locAdele_zero]
    exact hcont.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  have hd := GroundTheory.Global.denseRange_algebraMap_prod_pi (K := F) S₂ S₁
  obtain ⟨_, hy, t, rfl⟩ := mem_closure_iff_nhds.1 (hd c) _ hO
  refine ⟨t, ?_⟩
  rw [mul_eq_locAdele hε, loc_sub_algebraMap]
  exact hy

end GlobalTheory.PlaceApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.LevelSchwartz

theorem mem_schA_of_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (Φ : (Fin N → AF F) → ℂ),
    (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, Φ (x + u) = Φ x) →
    (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → fin x ∈ K) →
    (∀ x, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) →
    Φ ∈ GlobalTheory.WeilM.schA F (Fin N) := by
  intro F _ _ N Φ ⟨U, hUo, hU⟩ ⟨K, hK, hKs⟩ hS
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let ι : (Fin N → Af F) →+ (Fin N → AF F) :=
    { toFun := fun v i => pairA F 0 (v i)
      map_zero' := rfl
      map_add' := fun a b => by
        funext i
        show (((0 : Ainf F), a i + b i) : Ainf F × Af F) = ((0 : Ainf F), a i) + ((0 : Ainf F), b i)
        simp }
  have hιc : Continuous ι := continuous_pi fun i =>
    (show Continuous fun v : Fin N → Af F => (((0 : Ainf F), v i) : Ainf F × Af F) from
      continuous_const.prodMk (continuous_apply i))
  have hιinf : ∀ v, inf (ι v) = 0 := fun v => rfl
  have hfin : ∀ a t, fin (ι a + embR t) = a := fun a t => by
    funext i
    show (a i + 0 : Af F) = a i
    exact add_zero _
  have hdec : ∀ y : Fin N → AF F, y = ι (fin y) + embR (fun i => e (y i).1) := fun y => by
    funext i
    show (y i : Ainf F × Af F) = (((0 : Ainf F), (y i).2) : Ainf F × Af F) + ((e.symm (e (y i).1), (0 : Af F)))
    rw [RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_ <;> simp
  let W : AddSubgroup (Fin N → Af F) := U.comap ι
  have hWo : IsOpen (W : Set (Fin N → Af F)) := hUo.preimage hιc
  have hWcl : IsClosed (W : Set (Fin N → Af F)) := AddSubgroup.isClosed_of_isOpen W hWo
  have hinv : ∀ a b, -a + b ∈ W → ∀ z, Φ (ι b + z) = Φ (ι a + z) := by
    intro a b hab z
    rw [← hU (ι (-a + b)) hab (hιinf _) (ι a + z)]
    congr 1
    rw [map_add (f := _), map_neg]
    abel
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : Fin N → Af F => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset ((Fin N → Af F) ⧸ W) := t.image QuotientAddGroup.mk
  choose g hg using fun q : (Fin N → Af F) ⧸ W => hS (ι q.out)
  let ind : ((Fin N → Af F) ⧸ W) → (Fin N → Af F) → ℂ := fun q a =>
    if (QuotientAddGroup.mk a : (Fin N → Af F) ⧸ W) = q then 1 else 0
  have key : Φ = ∑ q ∈ T, GlobalTheory.WeilM.pureA F (g q) (ind q) := by
    funext y
    rw [Finset.sum_apply]
    show Φ y = ∑ q ∈ T, g q (fun i => e (y i).1) *
      (if (QuotientAddGroup.mk (fin y) : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hg]
      conv_lhs => rw [hdec y]
      exact hinv _ _ (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)) _
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      exact hT (Finset.mem_image.2 ⟨b, hb, QuotientAddGroup.eq.2 hab⟩)
  rw [key]
  refine Submodule.sum_mem _ fun q _ => ?_
  by_cases h0 : ∀ s, g q s = 0
  · have : GlobalTheory.WeilM.pureA F (g q) (ind q) = 0 := by
      funext y
      simp [GlobalTheory.WeilM.pureA, h0]
    rw [this]
    exact zero_mem _
  push_neg at h0
  obtain ⟨s0, hs0⟩ := h0
  refine Submodule.subset_span ⟨g q, ind q, ?_, rfl⟩
  let C : Set (Fin N → Af F) := {a | -q.out + a ∈ W}
  have hCcl : IsClosed C := hWcl.preimage (continuous_const.add continuous_id)
  have hCK : C ⊆ K := by
    intro a ha
    have h1 : Φ (ι a + embR s0) ≠ 0 := by
      rw [hinv _ _ ha, ← hg]
      exact hs0
    simpa [hfin] using hKs _ h1
  have hmk : IsLocallyConstant (fun a : Fin N → Af F => (a : (Fin N → Af F) ⧸ W)) :=
    (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  refine HasCompactSupport.intro' (hK.of_isClosed_subset hCcl hCK) hCcl fun x hx => ?_
  show (if (QuotientAddGroup.mk x : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  show -q.out + x ∈ W
  exact QuotientAddGroup.eq.1 (by rw [hq, QuotientAddGroup.out_eq'])

end GlobalTheory.LevelSchwartz

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartzStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicSchwartzSpace_of_level_compact_schwartz : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (Φ : (Fin N → AF F) → ℂ), (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, Φ (x + u) = Φ x) → (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → fin x ∈ K) → (∀ x, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) → Φ ∈ GlobalTheory.WeilM.schA F (Fin N) := by
  first | exact @GlobalTheory.LevelSchwartz.mem_schA_of_level | exact GlobalTheory.LevelSchwartz.mem_schA_of_level | (intros; apply GlobalTheory.LevelSchwartz.mem_schA_of_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionAdjointOfAdjointOnSpanningFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionAdjointOfAdjointOnSpanningFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AdjSpan

open GlobalTheory.CechPic

theorem adj_of_span : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ∀ (act : O → (A ⟶ A)), IsRAct A act → (∀ i, LBIso (Q.pull (lift (fst A A ≫ act (e i)) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar (e i)))).left)) → Adj A Q bar act := by
  intro S A _ _ Q hQ O _ bar r e hbar hspan act hact he
  obtain ⟨hA, hL, h₁, h₂, -, hamp⟩ := hQ
  have hbi := GlobalTheory.Biadditive.biadditive_of_triv_axes GlobalTheory.globalFns_holds S A _ hA (pull_isLB hL _) hamp Q hL h₁ h₂

  letI : Add (Pic (A ⊗ A).left) := (inferInstance : AddCommGroup (Pic (A ⊗ A).left)).toAdd
  let B : ((A ⊗ A) ⟶ A) → ((A ⊗ A) ⟶ A) → Pic (A ⊗ A).left := fun u v => pull (lift u v).left (cls Q hL)
  have addL : ∀ u u' v, B (u * u') v = B u v + B u' v := fun u u' v => by
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 (hbi (A ⊗ A) u u' v).1
    rw [cls_linComb hL, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    show pull _ _ = pull _ _ + pull _ _
    rw [← sub_eq_zero, ← z]
    abel
  have addR : ∀ u v v', B u (v * v') = B u v + B u v' := fun u v v' => by
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 (hbi (A ⊗ A) v v' u).2
    rw [cls_linComb hL, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    show pull _ _ = pull _ _ + pull _ _
    rw [← sub_eq_zero, ← z]
    abel
  let f : O → Pic (A ⊗ A).left := fun a => B (fst A A ≫ act a) (snd A A) - B (fst A A) (snd A A ≫ act (bar a))
  have fadd : ∀ a b, f (a + b) = f a + f b := fun a b => by
    simp only [f]
    rw [hbar, hact.2.2.2, hact.2.2.2, MonObj.comp_mul, MonObj.comp_mul, addL, addR]
    abel
  let F : O →+ Pic (A ⊗ A).left := AddMonoidHom.mk' f fadd
  have Fe : ∀ i, F (e i) = 0 := fun i => by
    show f (e i) = 0
    exact sub_eq_zero.2 ((cls_eq_iff (pull_isLB hL _) (pull_isLB hL _)).2 (he i))
  have hker : Submodule.span ℤ (Set.range e) ≤ LinearMap.ker F.toIntLinearMap :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Fe i)
  intro a
  have ha : F a = 0 := hker (hspan ▸ Submodule.mem_top : a ∈ Submodule.span ℤ (Set.range e))
  exact (cls_eq_iff (pull_isLB hL _) (pull_isLB hL _)).1 (sub_eq_zero.1 ha)

end GlobalTheory.AdjSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionAdjointOfAdjointOnSpanningFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringAction_adjoint_of_adjoint_on_spanning_family : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ∀ (act : O → (A ⟶ A)), IsRAct A act → (∀ i, LBIso (Q.pull (lift (fst A A ≫ act (e i)) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar (e i)))).left)) → Adj A Q bar act := by
  first | exact @GlobalTheory.AdjSpan.adj_of_span | exact GlobalTheory.AdjSpan.adj_of_span | (intros; apply GlobalTheory.AdjSpan.adj_of_span <;> assumption)
end
end
