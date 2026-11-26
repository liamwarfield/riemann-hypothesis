module

public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.ConjugatedGeneratorGlRelation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
noncomputable section

open Finset Matrix MeasureTheory

namespace GlobalTheory.CompanionTheory.ActEquivK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

lemma jm_inv (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε :=
  Matrix.inv_eq_left_inv (signature_matrix_sq ε)

lemma hinvol (ε : Fin n → Bool) : AAInvW.HInvol (Formalism.REAL.Jm ε) := by
  refine ⟨?_, signature_matrix_sq ε⟩
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

lemma eabH_eq (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Formalism.QuantumDeterminants.EabH (Formalism.REAL.Jm ε) a b f = Formalism.REAL.Eab ε a b f := by
  funext g
  have h1 : Formalism.QuantumDeterminants.hpart1 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart1 ε (Matrix.single a b 1) := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.REAL.cpart1
    rw [jm_inv]
  have h2 : Formalism.QuantumDeterminants.hpart2 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart2 ε (Matrix.single a b 1) := by
    unfold Formalism.QuantumDeterminants.hpart2 Formalism.REAL.cpart2
    rw [jm_inv]
  unfold Formalism.QuantumDeterminants.EabH
  rw [h1, h2]
  rfl

lemma inUJ_inv {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) : Formalism.REAL.inUJ ε k⁻¹ := by
  have hm : k * k⁻¹ = 1 := AAInvW.ana_mul_inv (hinvol ε) hk
  have h0 : kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε := hk
  show (k⁻¹)ᴴ * Formalism.REAL.Jm ε * k⁻¹ = Formalism.REAL.Jm ε
  calc (k⁻¹)ᴴ * Formalism.REAL.Jm ε * k⁻¹ = (k⁻¹)ᴴ * (kᴴ * Formalism.REAL.Jm ε * k) * k⁻¹ := by rw [h0]
    _ = (k * k⁻¹)ᴴ * Formalism.REAL.Jm ε * (k * k⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hm]; simp

lemma smooth_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) :
    Formalism.REAL.SmoothOnG ε (fun x => f (x * k)) :=
  AAInvW.smooth_right' n (Formalism.REAL.Jm ε) ℂ f k (hinvol ε) hk hf

lemma eab_local {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n)
    (h : ∀ x, Formalism.REAL.inUJ ε x → f x = f' x) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eab ε a b f g = Formalism.REAL.Eab ε a b f' g := by
  rw [← eabH_eq, ← eabH_eq]
  exact AAInvW.eab_h_local n (Formalism.REAL.Jm ε) ℂ f f' a b g (hinvol ε) h hg

lemma eab_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Eab ε a b (fun _ => (0 : ℂ)) g = 0 := by
  simp [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]

lemma eab_lin {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (a b : Fin n)
    (hf : Formalism.REAL.SmoothOnG ε f) (hf' : Formalism.REAL.SmoothOnG ε f')
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => f x + c * f' x) g =
      Formalism.REAL.Eab ε a b f g + c * Formalism.REAL.Eab ε a b f' g := by
  have := AAInvW.eab_h_linear n (Formalism.REAL.Jm ε) ℂ f f' c a b g (hinvol ε) hf hf' hg
  simpa only [eabH_eq, smul_eq_mul] using this

lemma smooth_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) :
    Formalism.REAL.SmoothOnG ε (fun x => ∑ i ∈ s, c i * F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.REAL.smooth_on_group_const_fun (ε := ε) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact Formalism.REAL.smooth_on_group_add (Formalism.REAL.smooth_on_group_const_mul (c i) (hF i)) ih

lemma eab_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ i ∈ s, c i * F i x) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eab ε a b (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using eab_zero (ε := ε) a b g
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have e : (fun x => c i * F i x + ∑ j ∈ s, c j * F j x) =
        fun x => (∑ j ∈ s, c j * F j x) + c i * F i x := funext fun x => add_comm _ _
    rw [e, eab_lin (c i) a b (smooth_sum s c F hF) (hF i) hg, ih, add_comm]

lemma eab_mul_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f) (a b : Fin n)
    {k g : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b f (g * k) =
      ∑ q : Fin n × Fin n, adC k (a, b) q * Formalism.REAL.Eab ε q.1 q.2 (fun x => f (x * k)) g := by
  have hJ := hinvol ε
  have hmi : k * k⁻¹ = 1 := AAInvW.ana_mul_inv hJ hk
  have him : k⁻¹ * k = 1 := AAInvW.ana_inv_mul hJ hk
  have hgk : Formalism.REAL.inUJ ε (g * k) := AAInvW.ana_mul hg hk
  have h := AAInvW.eab_h_right n (Formalism.REAL.Jm ε) ℂ (fun x => f (x * k)) a b k⁻¹ (g * k) hJ
    (smooth_right hf hk) (inUJ_inv hk) hgk
  have e1 : (fun x => (fun y => f (y * k)) (x * k⁻¹)) = f := by
    funext x
    show f (x * k⁻¹ * k) = f x
    rw [Matrix.mul_assoc, him, Matrix.mul_one]
  have e2 : g * k * k⁻¹ = g := by rw [Matrix.mul_assoc, hmi, Matrix.mul_one]
  have e3 : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv hmi
  rw [e1, e2, e3, eabH_eq] at h
  rw [h, Fintype.sum_prod_type]
  simp only [eabH_eq, smul_eq_mul]
  rfl

lemma eword_local (w : List (Fin n × Fin n)) {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ x, Formalism.REAL.inUJ ε x → f x = f' x) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eword ε w f g = Formalism.REAL.Eword ε w f' g := by
  induction w generalizing g with
  | nil => exact h g hg
  | cons p w ih => exact eab_local p.1 p.2 (fun x hx => ih hx) hg

lemma eword_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) (w : List (Fin n × Fin n))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eword ε w (fun x => ∑ i ∈ s, c i * F i x) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eword ε w (F i) g := by
  induction w generalizing g with
  | nil => rfl
  | cons p w ih =>
    show Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w _) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w (F i)) g
    rw [eab_local p.1 p.2 (f' := fun x => ∑ i ∈ s, c i * Formalism.REAL.Eword ε w (F i) x)
      (fun x hx => ih hx) hg]
    exact eab_sum s c _ (fun i => Formalism.REAL.smooth_iterated_lie_derivative (hF i) w) p.1 p.2 hg

lemma sum_cons {α : Type*} [Fintype α] [DecidableEq α] {l : ℕ} (Φ : (Fin (l + 1) → α) → ℂ) :
    ∑ W, Φ W = ∑ q : α, ∑ w : Fin l → α, Φ (Fin.cons q w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm

lemma eword_mul_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) :
    ∀ (l : ℕ) (x : Fin l → Fin n × Fin n) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε (List.ofFn x) f (g * k) =
        ∑ w : Fin l → Fin n × Fin n, (∏ i, adC k (x i) (w i)) *
          Formalism.REAL.Eword ε (List.ofFn w) (fun y => f (y * k)) g := by
  intro l
  induction l with
  | zero =>
    intro x g hg
    simp [Formalism.REAL.Eword]
  | succ l ih =>
    intro x g hg
    have hfk := smooth_right hf hk
    rw [sum_cons, List.ofFn_succ]
    show Formalism.REAL.Eab ε (x 0).1 (x 0).2 (Formalism.REAL.Eword ε (List.ofFn fun i => x i.succ) f) (g * k) = _
    rw [eab_mul_right (Formalism.REAL.smooth_iterated_lie_derivative hf _) _ _ hk hg]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [eab_local q.1 q.2 (f' := fun y => ∑ w : Fin l → Fin n × Fin n,
        (∏ i, adC k (x i.succ) (w i)) * Formalism.REAL.Eword ε (List.ofFn w) (fun y => f (y * k)) y)
      (fun y hy => ih _ y hy) hg,
      eab_sum _ _ _ (fun w => Formalism.REAL.smooth_iterated_lie_derivative hfk _) q.1 q.2 hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.prod_univ_succ, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    show _ = _ * Formalism.REAL.Eab ε q.1 q.2 (Formalism.REAL.Eword ε (List.ofFn w) _) g
    ring

theorem actEquiv : ActEquiv := by
  intro n ε lam T Ψ m hP k a
  have hk : Formalism.REAL.inUJ ε (toMK k) := (mir_inUJ_iff ε _).2 k.1.2
  have hJ : ∀ v, Formalism.REAL.SmoothOnG ε (jfun Ψ T.w v) := fun v =>
    pdA_smooth_clm (pdA_coef T.w v) (f := Ψ) hP.2.2.1
  have hJk : ∀ v y, Formalism.REAL.inUJ ε y →
      jfun Ψ T.w v (y * toMK k) = jfun Ψ T.w (T.op k v) y := by
    intro v y hy
    show inner ℂ T.w (Ψ (y * toMK k) v) = inner ℂ T.w (Ψ y (T.op k v))
    have h1 := hP.1 1 k y ((mir_inUJ_iff ε _).1 hy)
    rw [pdA_toMK_one, Matrix.one_mul, pdA_op_one, one_mul] at h1
    rw [h1]
    rfl
  unfold actL
  rw [rightRegular_toL2 ε _ (show toMK k ∈ UJset ε from k.1.2)]
  refine toL2_congr_of_forall_inUJ_eq fun g hg' => ?_
  have hg : Formalism.REAL.inUJ ε g := (mir_inUJ_iff ε _).2 hg'
  have hL : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (fun y => inner ℂ T.w (Ψ y (a x))) (g * toMK k) =
      ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (x.2 i) (w i)) *
        Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a x))) g := by
    intro x
    refine (eword_mul_right (hJ (a x)) hk x.1 x.2 g hg).trans (Finset.sum_congr rfl fun w _ => ?_)
    rw [eword_local (List.ofFn w) (f' := jfun Ψ T.w (T.op k (a x))) (fun y hy => hJk _ y hy) hg]
  have hR : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x)
        (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) g =
      ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (w i) (x.2 i)) *
        Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (T.op k (a ⟨x.1, w⟩))) g := by
    intro x
    have e : (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) = fun y =>
        ∑ w ∈ (Finset.univ : Finset (Fin x.1 → Fin n × Fin n)), (∏ i, adC (toMK k) (w i) (x.2 i)) *
          jfun Ψ T.w (T.op k (a ⟨x.1, w⟩)) y := by
      funext y
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rhoA, map_sum, map_smul, inner_sum, inner_smul_right, jfun]
    rw [e]
    exact eword_sum _ _ _ (fun w => hJ _) _ hg
  show actF T Ψ a (g * toMK k) = actF T Ψ (rhoA T m k a) g
  unfold actF
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [hL, hR]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Finset.sum_comm (s := (Finset.univ : Finset (Fin (l : ℕ) → Fin n × Fin n))) (t := Finset.univ)
    (f := fun y w => (∏ i, adC (toMK k) (y i) (w i)) *
      Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a ⟨l, y⟩))) g)

end GlobalTheory.CompanionTheory.ActEquivK
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatementStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.action_equivariance_statement : PositivityTheory.RgDs.K.ActEquiv := by
  first | exact @GlobalTheory.CompanionTheory.ActEquivK.actEquiv | exact GlobalTheory.CompanionTheory.ActEquivK.actEquiv | (intros; apply GlobalTheory.CompanionTheory.ActEquivK.actEquiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BetaWeightOfTorusFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BetaWeightOfTorusFacts
noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.TorusSymbol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma isOpen_omegaSet (n : ℕ) : IsOpen (OmegaSet n) := by
  have h : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [h]
  refine isOpen_iInter_of_finite fun i => ?_
  have hc : Continuous fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z := by
    have hi : (i : ℕ) + 1 ≤ n := i.2
    simp only [lead, dif_pos hi]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  exact isOpen_ne_fun hc continuous_const

lemma differentiableAt_of_mem {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : DifferentiableAt ℂ F z :=
  (hF.1.contDiffAt ((isOpen_omegaSet n).mem_nhds hz)).differentiableAt (by simp)

lemma lop_add (Y : Matrix (Fin n) (Fin n) ℂ) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : F ∈ OmF n) (hG : G ∈ OmF n) : lop Y (F + G) = lop Y F + lop Y G := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, Pi.add_apply, if_pos hz]
    have h : fderiv ℂ (F + G) z = fderiv ℂ F z + fderiv ℂ G z :=
      ((differentiableAt_of_mem hF hz).hasFDerivAt.add (differentiableAt_of_mem hG hz).hasFDerivAt).fderiv
    rw [h]
    simp only [ContinuousLinearMap.add_apply]
    ring
  · simp [lop, if_neg hz]

lemma lop_smul (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : F ∈ OmF n) : lop Y (s • F) = s • lop Y F := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, Pi.smul_apply, if_pos hz]
    have h : fderiv ℂ (s • F) z = s • fderiv ℂ F z :=
      ((differentiableAt_of_mem hF hz).hasFDerivAt.const_smul s).fderiv
    rw [h]
    simp
  · simp [lop, if_neg hz]

lemma lop_sum (Y : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) ℂ → ℂ) (hf : ∀ i, f i ∈ OmF n) :
    lop Y (∑ i ∈ s, f i) = ∑ i ∈ s, lop Y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp [lop, if_pos hz]
    · simp [lop, if_neg hz]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, lop_add Y (hf i) (Submodule.sum_mem _ fun j _ => hf j), ih]

def wtL (c : Fin n) (w : List (Fin n × Fin n)) : ℝ :=
  (w.map fun p => (if p.1 = c then (1 : ℝ) else 0) - (if p.2 = c then 1 else 0)).sum

lemma lw_mem (H : HolFacts) (μ : Fin n → ℤ) (w : List (Fin n × Fin n)) : lw w (PhiO μ) ∈ OmF n := by
  induction w with
  | nil => exact (H n μ).2.2.1
  | cons p w ih => exact (H n μ).1 _ _ ih

lemma lop_lw (H : HolFacts) (μ : Fin n → ℤ) (c : Fin n) (w : List (Fin n × Fin n)) :
    lop (Matrix.single c c 1) (lw w (PhiO μ)) =
      ((((μ c : ℤ) : ℝ) + wtL c w : ℝ) : ℂ) • lw w (PhiO μ) := by
  induction w with
  | nil =>
    have h := (H n μ).2.2.2.1 c
    simpa [wtL, lw] using h
  | cons p w ih =>
    obtain ⟨a, b⟩ := p
    have hF := lw_mem H μ w
    have rel := (H n μ).2.1 (lw w (PhiO μ)) c c a b hF
    have hlw : lw ((a, b) :: w) (PhiO μ) = lop (Matrix.single a b 1) (lw w (PhiO μ)) := rfl
    have hwt : wtL c ((a, b) :: w) =
        ((if a = c then (1 : ℝ) else 0) - (if b = c then 1 else 0)) + wtL c w := by
      simp [wtL]
    rw [ih, lop_smul _ _ hF] at rel
    have rel' : lop (Matrix.single c c 1) (lop (Matrix.single a b 1) (lw w (PhiO μ))) =
        ((((μ c : ℤ) : ℝ) + wtL c w : ℝ) : ℂ) • lop (Matrix.single a b 1) (lw w (PhiO μ)) +
        ((((if a = c then (1 : ℝ) else 0) - (if b = c then 1 else 0) : ℝ)) : ℂ) •
          lop (Matrix.single a b 1) (lw w (PhiO μ)) := by
      rw [sub_eq_iff_eq_add] at rel
      rw [rel, add_comm]
      congr 1
      by_cases h1 : a = c <;> by_cases h2 : b = c
      · subst h1; subst h2; simp
      · subst h1; simp [h2]
      · subst h2; simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    rw [hlw, rel', hwt, ← add_smul]
    congr 1
    push_cast
    ring

lemma exists_tor (ε : Fin n → Bool) (θ : Fin n → ℝ) : ∃ k : KG ε, toMK k = tor θ := by
  have hH : (tor θ)ᴴ = tor (-θ) := by
    unfold tor
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp [Pi.star_apply, ← Complex.exp_conj]
  have hm : ∀ θ : Fin n → ℝ, tor θ * tor (-θ) = 1 := by
    intro θ
    unfold tor
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← Complex.exp_add]
    simp
  have h1 : tor θ * (tor θ)ᴴ = 1 := by rw [hH, hm]
  have h2 : (tor θ)ᴴ * tor θ = 1 := by
    have := hm (-θ)
    rwa [neg_neg, ← hH] at this
  have hJ : tor θ * Jm ε = Jm ε * tor θ := by
    unfold tor Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _
  have hUJ : inUJ ε (tor θ) := by
    unfold inUJ
    rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hK : tor θ ∈ Kset ε := by
    refine ⟨?_, hJ⟩
    rw [Matrix.mem_unitaryGroup_iff]
    exact h1
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨tor θ, (tor θ)ᴴ, h1, h2⟩
  let g : UJ ε := ⟨u, hUJ⟩
  exact ⟨⟨g, hK⟩, rfl⟩

lemma inner_op_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (u v : T.V) :
    inner ℂ (T.op k u) (T.op k v) = inner ℂ u v := by
  have hu : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).2
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  have : star (T.op k) (T.op k v) = v := by
    have h : (star (T.op k) * T.op k) v = v := by rw [hu]; rfl
    exact h
  rw [this]

lemma wt_eq (hR : RhoTorus) (hT : TorW) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {m : ℕ}
    {η : Fin n → ℝ} {a : AS T m}
    (ha : ∀ (θ : Fin n → ℝ) (k : KG ε), toMK k = tor θ →
      rhoA T m k a = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • a)
    (x : Wd n m) (hx : inner ℂ T.w (a x) ≠ 0) (c : Fin n) : wtL c (ofW x) = η c - Λ c := by
  by_contra hne
  set v : ℝ := η c - Λ c - wtL c (ofW x) with hv
  have hv0 : v ≠ 0 := fun h => hne (by rw [hv] at h; linarith)
  set t : ℝ := Real.pi / v with ht
  have htv : t * v = Real.pi := by rw [ht]; field_simp
  set θ : Fin n → ℝ := Pi.single c t with hθ
  obtain ⟨k, hk⟩ := exists_tor ε θ
  have h1 : rhoA T m k a x = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • a x := by
    rw [ha θ k hk]; rfl
  have h2 := hR n ε Λ T m θ k hk a x
  have h3 := hT n ε Λ T θ k hk
  have hS : (∑ i, (θ (x.2 i).1 - θ (x.2 i).2) : ℝ) = t * wtL c (ofW x) := by
    unfold wtL ofW
    rw [List.map_ofFn, List.sum_ofFn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hθ, Pi.single_apply, Function.comp_apply]
    split_ifs <;> simp
  have hE : (∑ a, η a * θ a : ℝ) = t * η c := by
    simp [hθ, Pi.single_apply, mul_comm]
  have hL : (∑ a, Λ a * θ a : ℝ) = t * Λ c := by
    simp [hθ, Pi.single_apply, mul_comm]
  rw [hS] at h2
  rw [hE] at h1
  rw [hL] at h3
  set E1 : ℂ := Complex.exp (((t * wtL c (ofW x) : ℝ) : ℂ) * Complex.I) with hE1
  set E2 : ℂ := Complex.exp (((t * η c : ℝ) : ℂ) * Complex.I) with hE2
  set E3 : ℂ := Complex.exp (((t * Λ c : ℝ) : ℂ) * Complex.I) with hE3
  have h4 : E1 • T.op k (a x) = E2 • a x := by rw [← h2, h1]
  have h5 : E1 * inner ℂ T.w (a x) = (starRingEnd ℂ) E3 * E2 * inner ℂ T.w (a x) := by
    calc E1 * inner ℂ T.w (a x) = E1 * inner ℂ (T.op k T.w) (T.op k (a x)) := by rw [inner_op_op]
      _ = inner ℂ (T.op k T.w) (E1 • T.op k (a x)) := by rw [inner_smul_right]
      _ = (starRingEnd ℂ) E3 * E2 * inner ℂ T.w (a x) := by
        rw [h4, h3, inner_smul_right, inner_smul_left]; ring
  have h6 : E1 = (starRingEnd ℂ) E3 * E2 := mul_right_cancel₀ hx h5
  have h7 : (starRingEnd ℂ) E3 * E3 = 1 := by
    rw [hE3, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  have h8 : E1 * E3 = E2 := by
    rw [h6]
    calc (starRingEnd ℂ) E3 * E2 * E3 = ((starRingEnd ℂ) E3 * E3) * E2 := by ring
      _ = E2 := by rw [h7, one_mul]
  have h9 : E2 = -(E1 * E3) := by
    have : ((t * η c : ℝ) : ℂ) * Complex.I = ((t * wtL c (ofW x) : ℝ) : ℂ) * Complex.I +
        ((t * Λ c : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
      rw [← htv, hv]
      push_cast
      ring
    rw [hE2, this, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h10 : E1 * E3 ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  apply h10
  have h11 : E1 * E3 = -(E1 * E3) := by rw [← h9, h8]
  have h12 : (2 : ℂ) * (E1 * E3) = 0 := by linear_combination h11
  simpa using h12

theorem betaWeight : HolFacts → RhoTorus → TorW → BetaWeight := by
  intro H hR hT n ε Λ T μ m η a ha
  refine ⟨?_, ?_⟩
  · unfold betaF
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ofW x, rfl⟩)
  · intro c
    unfold betaF
    rw [lop_sum _ _ _ fun x => Submodule.smul_mem _ _ (lw_mem H μ (ofW x)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lop_smul _ _ (lw_mem H μ (ofW x)), lop_lw H]
    by_cases hx : inner ℂ T.w (a x) = 0
    · simp [hx]
    · rw [wt_eq hR hT T ha x hx c, smul_comm]
      congr 2
      push_cast
      ring

end GlobalTheory.CompanionTheory.TorusSymbol
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BetaWeightOfTorusFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_weight_of_torus_facts : PositivityTheory.RgDs.K.HolFacts → PositivityTheory.RgDs.K.RhoTorus → PositivityTheory.RgDs.K.TorW → PositivityTheory.RgDs.K.BetaWeight := by
  first | exact @GlobalTheory.CompanionTheory.TorusSymbol.betaWeight | exact GlobalTheory.CompanionTheory.TorusSymbol.betaWeight | (intros; apply GlobalTheory.CompanionTheory.TorusSymbol.betaWeight <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittAcrisFlat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittAcrisFlat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FlatW

theorem eq_zero_of_pow_mul_eq_zero {l : ℕ} [Fact l.Prime] (m : ℕ) {x : Acris l}
    (h : (l : Acris l) ^ m * x = 0) : x = 0 := by
  induction m with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply ACris.eq_zero_of_p_mul_eq_zero (K := ℂ_[l]) (p := l)
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem flat_AW {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) :
    Module.Flat (WittVector l r.k) (CrystallineSemistableComparison.Pb.AW r) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro a ha
  obtain ⟨⟨y, hy0⟩, hy⟩ := (Submodule.mem_torsion_iff _).1 ha
  have hne : y ≠ 0 := nonZeroDivisors.ne_zero hy0
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' y hne
  have hu : IsUnit (r.w (b : WittVector l r.k)) := b.isUnit.map r.w
  have key : ∀ x : Acris l, r.w y * x = 0 → x = 0 := by
    intro x h
    rw [e, map_mul, map_pow, map_natCast] at h
    apply eq_zero_of_pow_mul_eq_zero m
    apply hu.mul_right_eq_zero.1
    linear_combination h
  exact (Submodule.mem_bot _).2 (key a hy)

end GlobalTheory.CompanionTheory.FlatW
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittAcrisFlatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_acris_flat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K), Module.Flat (WittVector l r.k) (CrystallineSemistableComparison.Pb.AW r) := by
  first | exact @GlobalTheory.CompanionTheory.FlatW.flat_AW | exact GlobalTheory.CompanionTheory.FlatW.flat_AW | (intros; apply GlobalTheory.CompanionTheory.FlatW.flat_AW <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpan
set_option autoImplicit false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

private theorem galBdRHom_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : BDeRhamPlus (normInteger ℂ_[p]) p)
    (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)) :
    galBdRHom σ x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  have h1 : galBdRHom σ⁻¹ (galBdRHom σ x) = x := by
    rw [← RingHom.comp_apply, ← galBdRHom_mul, inv_mul_cancel, galBdRHom_one, RingHom.id_apply]
  rw [← h1]
  exact hu.map _

theorem span_tBdR_pow_le_comap (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (k : ℕ) (g : K.fixingSubgroup) :
    Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
  have ht : Lat.gP l g (tBdR l) ∈ Ideal.span {tBdR l} := by
    rw [← maximalIdeal_eq_span_tBdR]
    exact galBdRHom_mem_maximalIdeal _ _ (by rw [maximalIdeal_eq_span_tBdR]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ht
  rw [← hc, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.LatGal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpanStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_preserves_t_power_span : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (k : ℕ) (g : K.fixingSubgroup), Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  first | exact @GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | exact GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | (intros; apply GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonGaloisFixed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonGaloisFixed
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.BWGal

theorem gal_wn {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K)
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) (x : (Wc.bs l r.k n).R) :
    galBase σ n (Mid.wn r n x) = Mid.wn r n x := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Mid.wn_mk, galBase_cris, hσ]

abbrev bWM {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n : ℕ) :
    Mor (Wc.L l (B.schFn M.p) r.ρ n) (Mid.Lm r M n) (Mid.wn r n) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl

abbrev gM {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K)
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) :
    Mor (Mid.Lm r M n) (Mid.Lm r M n) (galBase σ n) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl

theorem bW_gal : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (y : (HSW r M j).M n), galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by
  intro l _ K r M σ hσ n j y
  haveI : RingHomCompTriple r.w (ACris.galCris σ) r.w := ⟨RingHom.ext hσ⟩
  refine (pull_pull r.w (bWMor r M n) (galT' r M σ hσ n) j y).trans ?_
  exact cr_pull_eq _ _ (fun T => crHom (T := (bWM r M n).obj ((gM r M σ hσ n).obj T)) (T' := (bWM r M n).obj T)
    (RingHom.id T.B) (fun x => congrArg T.i (gal_wn r σ hσ n x)) (DPMorphism.id T.δ).isDPMorphism
    fun h => (pt_id _ h _).trans rfl) (fun _ _ => rfl) (fun _ _ => rfl) j y

end GlobalTheory.CompanionTheory.BWGal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonGaloisFixedStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_comparison_galois_fixed : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (y : (HSW r M j).M n), galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by
  first | exact @GlobalTheory.CompanionTheory.BWGal.bW_gal | exact GlobalTheory.CompanionTheory.BWGal.bW_gal | (intros; apply GlobalTheory.CompanionTheory.BWGal.bW_gal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBEqZeroIffTPowDvd
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBEqZeroIffTPowDvd
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem lev_toB_ker {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ x : (per l K).P, (lev h k).toB x = 0 ↔ ∃ y : (per l K).P, (x : (per l K).B) = (per l K).tB ^ k * y := by
  have ht : (per l K).tB = algebraMap (BdRp l) (BdR l) (tBdR l) := by
    change DeRhamPotentiallySemistable.DRPst.iC l (tA l) = _
    change algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (tA l)) = _
    rw [show ACris.iota ℂ_[l] l (tA l) = tBdR l from ACris.iota_periodT (untilt_epsilon (p := l))]
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) :=
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  have hp : ∀ x : ↥(algebraMap (BdRp l) (BdR l)).range, algebraMap (BdRp l) (BdR l) (pInv l x) = x := by
    intro x
    obtain ⟨z, hz⟩ := x.2
    have : pInv l x = z := by
      apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_eq.2
      exact Subtype.ext hz.symm
    rw [this, hz]
  intro x
  change pk l k (pInv l x) = 0 ↔ _
  rw [pk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨⟨algebraMap (BdRp l) (BdR l) z, z, rfl⟩, ?_⟩
    have := hp x
    rw [← hz, map_mul, map_pow, mul_comm] at this
    rw [ht]
    exact this.symm
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := y.2
    refine ⟨z, hinj ?_⟩
    rw [map_mul, map_pow, mul_comm, hp x, hz]
    rw [ht] at hy
    exact hy.symm

end GlobalTheory.CompanionTheory.LatC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBEqZeroIffTPowDvdStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_toB_eq_zero_iff_t_pow_dvd : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ x : (per l K).P, (lev h k).toB x = 0 ↔ ∃ y : (per l K).P, (x : (per l K).B) = (per l K).tB ^ k * y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.lev_toB_ker | exact GlobalTheory.CompanionTheory.LatC.lev_toB_ker | (intros; apply GlobalTheory.CompanionTheory.LatC.lev_toB_ker <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonPullbackCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonPullbackCompat
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrisBase

theorem cr_square_coeff {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c₁ : Λ →+* b₁.R} {c₂ : Λ' →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ' →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τ : Λ →+* Λ'}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τ a)) (hb : ∀ a, σb (c₂ a) = c₄ (RingHom.id Λ' a)) (hc : ∀ a, σc (c₁ a) = c₃ (RingHom.id Λ a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τ a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb (RingHom.id Λ') hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τ ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τ hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc (RingHom.id Λ) hc).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

theorem pullM_bW {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {M N : Model l K}
    (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) (y : (HSW r N j).M n) :
    pullM r u hu n j (bW r N n j y) = bW r M n j ((Wc.pullS l r.ρ (B.schMap u hu) j).f n y) := by
  exact cr_square_coeff
    (B.crMor (F := B.schFn N.p) (F' := B.schFn N.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn N.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (Wc.pullM l r.ρ (B.schMap u hu) n)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (Mid.wn_mk r n) (fun _ => rfl) (Wc.idc _) (Mid.wn_mk r n) (fun _ => rfl) (fun _ _ => rfl) j y

end GlobalTheory.CompanionTheory.CrisBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonPullbackCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_comparison_pullback_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) (y : (HSW r N j).M n), pullM r u hu n j (bW r N n j y) = bW r M n j ((Wc.pullS l r.ρ (B.schMap u hu) j).f n y) := by
  first | exact @GlobalTheory.CompanionTheory.CrisBase.pullM_bW | exact GlobalTheory.CompanionTheory.CrisBase.pullM_bW | (intros; apply GlobalTheory.CompanionTheory.CrisBase.pullM_bW <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSub
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSub
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

theorem map_mem_sub_of_mul {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (g : B →+* B) (s : W → W) (hs : ∀ w, g (f w) = f (s w)) (u : W) (hu : s ξ = u * ξ) :
    ∀ x ∈ sub f ξ l M, g x ∈ sub f ξ l M := by
  have hle : sub f ξ l M ≤ (sub f ξ l M).comap g := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · show g (f w) ∈ sub f ξ l M
      rw [hs]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    · show g (dpE f ξ l M i) ∈ sub f ξ l M
      have hη : g (η f ξ l M) = f u * η f ξ l M := by
        rw [η, map_rat_smul, hs, hu, map_mul, mul_smul_comm]
      have hd : g (dpE f ξ l M i) = f u ^ i * dpE f ξ l M i := by
        rw [dpE, map_rat_smul, map_pow, hη, mul_pow, mul_smul_comm]
      rw [hd]
      have h1 : f u ∈ sub f ξ l M := Subring.subset_closure (Or.inl ⟨u, rfl⟩)
      have h2 : dpE f ξ l M i ∈ sub f ξ l M := Subring.subset_closure (Or.inr ⟨i, rfl⟩)
      exact (sub f ξ l M).mul_mem ((sub f ξ l M).pow_mem h1 i) h2
  exact fun x hx => hle hx

theorem gal_mem_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M k : ℕ)
    (g : K.fixingSubgroup) (hT : Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g)),
    ∀ x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M,
      Ideal.quotientMap _ (Lat.gP l g) hT x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K M k g hT
  have hmem : toBot g.1 • xi0 l ∈ RingHom.ker (theta0 l) :=
    gal_smul_mem_ker_fontaineTheta (toBot g.1) (by
      rw [ker_theta0]; exact Ideal.mem_span_singleton_self _)
  rw [ker_theta0, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine map_mem_sub_of_mul (fk l k) (xi0 l) l M _ (fun w => toBot g.1 • w) (fun w => ?_) u hu.symm
  show Ideal.quotientMap _ (gP l g) hT (Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l w)) =
    Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l (toBot g.1 • w))
  rw [Ideal.quotientMap_mk, ← gal_smul_wittToBDeRhamPlus]
  rfl

end GlobalTheory.CompanionTheory.LatGal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSubStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_preserves_lattice_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M k : ℕ) (g : K.fixingSubgroup) (hT : Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g)), ∀ x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M, Ideal.quotientMap _ (Lat.gP l g) hT x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatGal.gal_mem_sub | exact GlobalTheory.CompanionTheory.LatGal.gal_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatGal.gal_mem_sub <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonReductionCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonReductionCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisBaseChange

theorem cr_square_coeff {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c₁ : Λ →+* b₁.R} {c₂ : Λ' →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ' →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τ : Λ →+* Λ'}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τ a)) (hb : ∀ a, σb (c₂ a) = c₄ (RingHom.id Λ' a)) (hc : ∀ a, σc (c₁ a) = c₃ (RingHom.id Λ a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τ a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb (RingHom.id Λ') hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τ ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τ hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc (RingHom.id Λ) hc).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem red_wn (r : CrystallineSemistableComparison.Res l K) (n : ℕ) (x : Wc.Wm l r.k (n + 1)) :
    (base l).red (Nat.le_succ n) (Mid.wn r (n + 1) x) = Mid.wn r n (Wc.red l r.k n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Mid.wn_mk, B.red_cris, Wc.red_mk, Mid.wn_mk]
  rfl

theorem bW_red (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M (n + 1)) :
    (redT r M (Nat.le_succ n)).pull j (bW r M (n + 1) j y) = bW r M n j ((HSW r M j).r n y) :=
  cr_square_coeff (τ := r.w)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k (n + 1)) (b' := B.bs l true (n + 1)) (ht := rfl) (ht' := rfl)
      (Mid.wn r (n + 1)) rfl (dp_wn r (n + 1)) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r (n + 1)) (Mid.im_le r (n + 1))) rfl) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n)) (B.basePt _ _ (red_κm r (Nat.le_succ n))) fun _ _ _ => rfl)
    (Wc.redM l (B.schFn M.p) r.ρ n)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (Mid.wn_mk r (n + 1)) (B.red_cris _ (Nat.le_succ n)) (Wc.red_mk l r.k n)
    (Mid.wn_mk r n) (red_wn r n) (fun _ _ => rfl) j y

end GlobalTheory.CompanionTheory.CrisBaseChange
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonReductionCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_comparison_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M (n + 1)), (redT r M (Nat.le_succ n)).pull j (bW r M (n + 1) j y) = bW r M n j ((HSW r M j).r n y) := by
  first | exact @GlobalTheory.CompanionTheory.CrisBaseChange.bW_red | exact GlobalTheory.CompanionTheory.CrisBaseChange.bW_red | (intros; apply GlobalTheory.CompanionTheory.CrisBaseChange.bW_red <;> assumption)
end
end
