module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.DeterminantPowerSmoothness.GtCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingAdmissibleFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorCenterExpansion

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.AtTraceT
noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Et (lam : Fin n → ℤ) : Matrix (Fin n) (Fin n) (Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :=
  GlobalTheory.Mem.Gelf.rowE ℂ n n + (((dw lam).detShift : ℤ) : ℂ) • (1 : Matrix (Fin n) (Fin n) (Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)))

def At (lam : Fin n → ℤ) : Matrix (Fin n) (Fin n) (Matrix (Jd n lam) (Jd n lam) ℂ) :=
  Matrix.of fun a b i j => Cxc.extL lam i (Et lam a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ))

def AtTrace : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ k : ℕ,
  (At lam ^ k).trace = GlobalTheory.Dec.gelfVal (infOf lam true) k • (1 : Matrix (Jd n lam) (Jd n lam) ℂ)

def AtTraceT : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ k : ℕ,
  ((Matrix.of fun a b => -(At lam b a)) ^ k).trace = GlobalTheory.Dec.gelfVal (infOf lam false) k • (1 : Matrix (Jd n lam) (Jd n lam) ℂ)

def AtDer : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ Y : Mat n,
  fderiv ℝ (Rm lam) 1 Y = ∑ a, ∑ b, Y a b • At lam a b

end PositivityTheory.RgBcC.Cxd2
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.TraceModelAlgebra.AtTraceT
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.TraceModelAlgebra.ExtLExpand
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.TraceModelAlgebra.TraceOnModel
noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2.Alg

open GlobalTheory.Mem.Gelf (rowE GlRel gelfC)

variable {n : ℕ}

theorem dw_w (lam : Fin n → ℤ) (hlam : Antitone lam) : (dw lam).w = lam := by
  unfold dw; rw [dite_eq_left hlam]

theorem natW_anti (lam : Fin n → ℤ) : Antitone (dw lam).natW := by
  intro a b hab
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (sub_le_sub_right ((dw lam).anti hab) _)

theorem natW_add (lam : Fin n → ℤ) (hlam : Antitone lam) (a : Fin n) :
    (((dw lam).natW a : ℕ) : ℂ) + (((dw lam).detShift : ℤ) : ℂ) = (lam a : ℂ) := by
  have hw := dw_w lam hlam
  have hn : 0 < n := a.pos
  have hd : (dw lam).detShift = (dw lam).w ⟨n - 1, by omega⟩ := by
    unfold Formalism.BasicNotions.DomWeight.detShift
    rw [dite_eq_left hn]
  have hle : (dw lam).detShift ≤ (dw lam).w a := by
    rw [hd]
    exact (dw lam).anti (Fin.le_iff_val_le_val.mpr (by simp; omega))
  have hz : (((dw lam).natW a : ℕ) : ℤ) = (dw lam).w a - (dw lam).detShift := by
    unfold Formalism.BasicNotions.DomWeight.natW
    exact Int.toNat_of_nonneg (by omega)
  have hc : (((dw lam).natW a : ℕ) : ℂ) = ((((dw lam).natW a : ℕ) : ℤ) : ℂ) := by push_cast; rfl
  rw [hc, hz, hw]
  push_cast
  ring

theorem glRel_shift {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) (C : A)
    (hC : ∀ F : A, C * F = F * C) (h : GlRel E) :
    GlRel (E + Matrix.of fun a b => if a = b then C else 0) := by
  intro a b c d
  have hD : ∀ (x y : Fin N) (F : A), (if x = y then C else 0) * F = F * (if x = y then C else 0) := by
    intro x y F
    split_ifs <;> simp [hC]
  have key : ∀ (e f p q : A), (∀ F, p * F = F * p) → (∀ F, q * F = F * q) →
      (e + p) * (f + q) - (f + q) * (e + p) = (e * f - f * e) + (p * q - q * p) := by
    intro e f p q hp hq
    simp only [add_mul, mul_add]
    rw [hp f, hq e]
    abel
  simp only [Matrix.add_apply, Matrix.of_apply]
  rw [key _ _ _ _ (hD a b) (hD c d), h a b c d, hD a b (if c = d then C else 0), sub_self, add_zero]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp
  · simp [hbc, hda, Ne.symm hda]
  · simp [hbc, hda, Ne.symm hbc]
  · simp [hbc, hda]

theorem Et_eq (lam : Fin n → ℤ) : Et lam = GlobalTheory.Mem.Gelf.rowE ℂ n n +
    Matrix.of fun a b => if a = b then (((dw lam).detShift : ℤ) : ℂ) • (1 : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) else 0 := by
  refine Matrix.ext fun a b => ?_
  simp only [Et, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]
  congr 1
  split_ifs <;> simp

theorem glRel_Et (lam : Fin n → ℤ) : GlRel (Et lam) := by
  rw [Et_eq]
  refine glRel_shift _ _ (fun F => ?_) (GlobalTheory.Mem.GelfCheck.glRel_rowE ℂ n n)
  rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem Et_mem (lam : Fin n → ℤ) (a b : Fin n) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : Et lam a b f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam) := by
  rw [Et_eq]
  simp only [Matrix.add_apply, Matrix.of_apply, LinearMap.add_apply]
  refine Submodule.add_mem _ (GlobalTheory.BrCompare.rowE_mem a b hf) ?_
  split_ifs
  · simp only [LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.smul_mem _ _ hf
  · simp

theorem Etpow_mem (lam : Fin n → ℤ) (k : ℕ) (a b : Fin n) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : (Et lam ^ k) a b f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam) := by
  induction k generalizing a b f with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · simpa using hf
    · simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun c _ => by
      rw [Module.End.mul_apply]
      exact Et_mem lam a c (ih c b hf)

theorem trace_comm (lam : Fin n → ℤ) (k : ℕ) (c d : Fin n) :
    Et lam c d * (Et lam ^ k).trace = (Et lam ^ k).trace * Et lam c d := by
  rw [← sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [GlobalTheory.Mem.GelfCheck.pow_cov (glRel_Et lam) k]
  rw [Finset.sum_sub_distrib]
  simp

theorem Et_hw (lam : Fin n → ℤ) (hlam : Antitone lam) :
    (∀ a, Et lam a a (Formalism.GradedWeylDivisibility.hw ℂ le_rfl (dw lam).natW) = (lam a : ℂ) • Formalism.GradedWeylDivisibility.hw ℂ le_rfl (dw lam).natW) ∧
    ∀ a b, a < b → Et lam a b (Formalism.GradedWeylDivisibility.hw ℂ le_rfl (dw lam).natW) = 0 := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [Et_eq]
    simp only [Matrix.add_apply, Matrix.of_apply, LinearMap.add_apply, if_true, eq_self_iff_true,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [GlobalTheory.BrCompare.hw_weight (natW_anti lam) a, ← add_smul, natW_add lam hlam a]
  · rw [Et_eq]
    simp only [Matrix.add_apply, Matrix.of_apply, if_neg hab.ne, LinearMap.add_apply, LinearMap.zero_apply,
      add_zero]
    exact GlobalTheory.BrCompare.hw_raise _ a b hab

theorem trace_on_model (lam : Fin n → ℤ) (hlam : Antitone lam) (k : ℕ) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
    (Et lam ^ k).trace f = gelfC (fun a => (lam a : ℂ)) k • f := by
  have hE := glRel_Et lam
  have hstab : ∀ a b, ∀ g ∈ LinearMap.ker ((Et lam ^ k).trace - gelfC (fun a => (lam a : ℂ)) k • 1),
      GlobalTheory.Mem.Gelf.rowE ℂ n n a b g ∈ LinearMap.ker ((Et lam ^ k).trace - gelfC (fun a => (lam a : ℂ)) k • 1) := by
    intro a b g hg
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hg
    have hr : GlobalTheory.Mem.Gelf.rowE ℂ n n a b = Et lam a b
        - (if a = b then (((dw lam).detShift : ℤ) : ℂ) • (1 : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) else 0) := by
      rw [Et_eq]
      simp
    have hcomm : (Et lam ^ k).trace * GlobalTheory.Mem.Gelf.rowE ℂ n n a b = GlobalTheory.Mem.Gelf.rowE ℂ n n a b * (Et lam ^ k).trace := by
      rw [hr, mul_sub, sub_mul, ← trace_comm lam k a b]
      split_ifs <;> simp [smul_mul_assoc, mul_smul_comm]
    have hg2 := congrArg (fun L : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ) => L g) hcomm
    simp only [Module.End.mul_apply] at hg2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hg2, hg]
    simp
  have hhw : Formalism.GradedWeylDivisibility.hw ℂ le_rfl (dw lam).natW ∈ LinearMap.ker ((Et lam ^ k).trace - gelfC (fun a => (lam a : ℂ)) k • 1) := by
    obtain ⟨h1, h2⟩ := Et_hw lam hlam
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, GlobalTheory.Mem.GelfCheck.trace_pow_apply hE h1 h2 k]
    simp
  have hle := GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable ℂ n (dw lam).natW (natW_anti lam) _ hhw hstab
  have := hle hf
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  simpa using this

theorem gelfC_eq (lam : Fin n → ℤ) (k : ℕ) :
    gelfC (fun a => (lam a : ℂ)) k = GlobalTheory.Dec.gelfVal (infOf lam true) k := by
  unfold GlobalTheory.Mem.Gelf.gelfC GlobalTheory.Dec.gelfVal
  rw [GlobalTheory.Mem.GelfCheck.gelfA_eq_Amat]
  have h : Formalism.REAL.lsh (fun a => (lam a : ℂ)) = fun c => infOf lam true c + ((n : ℂ) - 1) / 2 := by
    funext c
    simp [Formalism.REAL.lsh, infOf]
    ring
  rw [h]

end PositivityTheory.RgBcC.Cxd2.Alg
end
end

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2.Alg

open GlobalTheory.Mem.Gelf (rowE GlRel gelfC)

variable {n : ℕ}

def matB (lam : Fin n → ℤ) (F : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  fun i j => Cxc.extL lam i (F ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ))

theorem extL_wb (lam : Fin n → ℤ) (i j : Jd n lam) :
    Cxc.extL lam i ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ) =
      (1 : Matrix (Jd n lam) (Jd n lam) ℂ) i j := by
  rw [Cxc.extL_spec, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all [eq_comm]

theorem extL_expand (lam : Fin n → ℤ) (i : Jd n lam) (F : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ))
    {g : MvPolynomial (Fin n × Fin n) ℂ} (hg : g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
    ∑ l, Cxc.extL lam i (F ((wb lam l : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) *
      Cxc.extL lam l g = Cxc.extL lam i (F g) := by
  have hs := (wb lam).sum_repr ⟨g, hg⟩
  have e : g = ∑ l, (wb lam).repr ⟨g, hg⟩ l • ((wb lam l : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ) := by
    have h2 : ((∑ l, (wb lam).repr ⟨g, hg⟩ l • wb lam l : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
        MvPolynomial (Fin n × Fin n) ℂ) = g := by rw [hs]
    conv_lhs => rw [← h2]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  conv_rhs => rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, mul_comm, Cxc.extL_spec lam l ⟨g, hg⟩]

theorem matB_mul (lam : Fin n → ℤ) (F G : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ))
    (hG : ∀ g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam), G g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
    matB lam (F * G) = matB lam F * matB lam G := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [matB, Module.End.mul_apply]
  rw [extL_expand lam i F (hG _ (wb lam j).2)]

theorem matB_add (lam : Fin n → ℤ) (F G : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :
    matB lam (F + G) = matB lam F + matB lam G := by
  ext i j; simp [matB]

theorem matB_sub (lam : Fin n → ℤ) (F G : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :
    matB lam (F - G) = matB lam F - matB lam G := by
  ext i j; simp [matB]

theorem matB_zero (lam : Fin n → ℤ) : matB lam 0 = 0 := by
  ext i j; simp [matB]

theorem matB_one (lam : Fin n → ℤ) : matB lam 1 = 1 := by
  ext i j; simp only [matB, Module.End.one_apply]; exact extL_wb lam i j

theorem At_eq (lam : Fin n → ℤ) (a b : Fin n) : At lam a b = matB lam (Et lam a b) := rfl

theorem At_pow (lam : Fin n → ℤ) (k : ℕ) (a b : Fin n) : (At lam ^ k) a b = matB lam ((Et lam ^ k) a b) := by
  induction k generalizing a b with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs
    · exact (matB_one lam).symm
    · exact (matB_zero lam).symm
  | succ k ih =>
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    rw [show (∑ c, Et lam a c * (Et lam ^ k) c b) = ∑ c, Et lam a c * (Et lam ^ k) c b from rfl]
    have hs : ∀ (s : Finset (Fin n)), matB lam (∑ c ∈ s, Et lam a c * (Et lam ^ k) c b) =
        ∑ c ∈ s, matB lam (Et lam a c) * matB lam ((Et lam ^ k) c b) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [matB_zero]
      | insert x s hx ih2 =>
        rw [Finset.sum_insert hx, Finset.sum_insert hx, matB_add, ih2,
          matB_mul lam _ _ (fun g hg => Etpow_mem lam k x b hg)]
    rw [hs]
    exact Finset.sum_congr rfl fun c _ => by rw [ih, At_eq]

theorem atTrace' : AtTrace := by
  intro n lam hlam k
  ext i j
  rw [Matrix.trace, Matrix.sum_apply]
  simp only [Matrix.diag_apply, At_pow, matB]
  have e : ∑ a, Cxc.extL lam i ((Et lam ^ k) a a ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) =
      Cxc.extL lam i ((Et lam ^ k).trace ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.trace, LinearMap.sum_apply, map_sum]
    rfl
  rw [e, trace_on_model lam hlam k (wb lam j).2, map_smul, extL_wb, gelfC_eq, Matrix.smul_apply]

theorem glRel_At (lam : Fin n → ℤ) (a b c d : Fin n) :
    At lam a b * At lam c d - At lam c d * At lam a b =
      (if b = c then At lam a d else 0) - (if a = d then At lam c b else 0) := by
  have h := glRel_Et lam a b c d
  have hm : ∀ x y, ∀ g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam), Et lam x y g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam) :=
    fun x y g hg => Et_mem lam x y hg
  have := congrArg (matB lam) h
  rw [matB_sub, matB_mul lam _ _ (hm c d), matB_mul lam _ _ (hm a b), matB_sub] at this
  rw [At_eq, At_eq, At_eq, At_eq, this]
  congr 1
  · split_ifs <;> simp [At_eq, matB_zero]
  · by_cases h1 : a = d
    · subst h1; simp [At_eq]
    · have h2 : ¬ d = a := fun e => h1 e.symm
      simp [h1, h2, matB_zero]

theorem epw_eq_pow {A : Type} [Ring A] (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    GlobalTheory.CompanionTheory.WaveMult.Epw e m a b = ((Matrix.of e) ^ m) a b := by
  induction m generalizing a b with
  | zero => rw [GlobalTheory.CompanionTheory.WaveMult.GlTranspose.epw_zero, pow_zero, Matrix.one_apply]
  | succ m ih =>
    rw [GlobalTheory.CompanionTheory.WaveMult.GlTranspose.epw_succ, pow_succ', Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [ih, Matrix.of_apply]

theorem trE_eq {A : Type} [Ring A] (e : Fin n → Fin n → A) (m : ℕ) :
    GlobalTheory.CompanionTheory.WaveMult.trE e m = ((Matrix.of e) ^ m).trace := by
  simp only [GlobalTheory.CompanionTheory.WaveMult.trE, Matrix.trace, Matrix.diag_apply, epw_eq_pow]

theorem pow_neg_of {A : Type} [Ring A] [Algebra ℂ A] (e : Fin n → Fin n → A) (m : ℕ) :
    (Matrix.of fun a b => -(e a b)) ^ m = ((-1 : ℂ) ^ m) • (Matrix.of e) ^ m := by
  have : (Matrix.of fun a b => -(e a b)) = (-1 : ℂ) • Matrix.of e := by ext a b; simp
  rw [this, smul_pow]

theorem atTraceT' : AtTraceT := by
  intro n lam hlam k
  set A := Matrix (Jd n lam) (Jd n lam) ℂ
  set e : Fin n → Fin n → A := fun a b => At lam a b
  have he : ∀ a b c d, e a b * e c d - e c d * e a b = (if b = c then e a d else 0) - (if a = d then e c b else 0) :=
    fun a b c d => glRel_At lam a b c d
  have hT := GlobalTheory.CompanionTheory.WaveMult.GlTranspose.trE_transpose_eq_phiSeq n e he k
  have htr : GlobalTheory.CompanionTheory.WaveMult.trE e = fun m => algebraMap ℂ A (GlobalTheory.Dec.gelfVal (infOf lam true) m) := by
    funext m
    rw [trE_eq, Algebra.algebraMap_eq_smul_one]
    exact atTrace' n lam hlam m
  have hφ := GlobalTheory.CompanionTheory.WaveMult.GenTr.map_phiSeq (algebraMap ℂ A) (n : ℂ) (GlobalTheory.Dec.gelfVal (infOf lam true)) k
  rw [map_natCast] at hφ
  have hneg := GlobalTheory.CompanionTheory.WaveMult.ValPhi.gelfVal_neg_eq_phiSeq n (infOf lam true) k
  have hinf : (fun a => -(infOf lam true a)) = infOf lam false := by
    funext a; simp [infOf]
  rw [hinf] at hneg
  have h1 : (Matrix.of fun a b => -(At lam b a)) ^ k = ((-1 : ℂ) ^ k) • (Matrix.of fun a b => e b a) ^ k :=
    pow_neg_of (fun a b => e b a) k
  have h2 : GlobalTheory.CompanionTheory.WaveMult.phiSeq (n : A) (fun m => algebraMap ℂ A (GlobalTheory.Dec.gelfVal (infOf lam true) m)) k =
      algebraMap ℂ A (GlobalTheory.CompanionTheory.WaveMult.phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal (infOf lam true)) k) := by
    rw [hφ]; rfl
  rw [h1, Matrix.trace_smul, ← trE_eq, hT, htr, h2, ← hneg, Algebra.algebraMap_eq_smul_one, smul_smul, ← mul_assoc,
    ← mul_pow]
  norm_num

end PositivityTheory.RgBcC.Cxd2.Alg
end
end

namespace PositivityTheory.RgBcC.Cxd2

theorem atTrace : AtTrace := Alg.atTrace'

theorem atTraceT : AtTraceT := Alg.atTraceT'

end PositivityTheory.RgBcC.Cxd2
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.DeterminantRankOneUpdate.DetOneAddSingle
noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2.Der

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem elementaryAct_map_mul (a b : Fin n) (s : ℂ) : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 + single a b s)ᵀ =
      ((Polynomial.aeval (C s : MvPolynomial (Fin n × Fin n) ℂ)).restrictScalars ℂ).comp (Formalism.GradedWeylDivisibility.rowGen ℂ (n := n) a b) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨p, q⟩
  simp only [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen, MvPolynomial.aeval_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply, map_add (f := _)]
  rw [Polynomial.aeval_C]
  simp only [Matrix.transpose_apply, Matrix.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single p]
    · simp
    · intro x _ hx; simp [Matrix.one_apply, hx]
    · simp
  · by_cases hp : p = b
    · subst hp
      rw [Finset.sum_eq_single a]
      · simp [Matrix.single_apply]
        exact mul_comm _ _
      · intro x _ hx
        have : a ≠ x := fun h => hx h.symm
        simp [Matrix.single_apply, this]
      · simp
    · have : b ≠ p := fun h => hp h.symm
      simp [Matrix.single_apply, this, hp]

theorem rowAct_eq_aeval (a b : Fin n) (s : ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 + single a b s)ᵀ f =
      Polynomial.aeval (C s : MvPolynomial (Fin n × Fin n) ℂ) (Formalism.GradedWeylDivisibility.rowGen ℂ (n := n) a b f) := by
  rw [elementaryAct_map_mul]
  rfl

def qP (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) : Polynomial ℂ :=
  ∑ k ∈ Finset.range ((Formalism.GradedWeylDivisibility.rowGen ℂ (n := n) a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
      MvPolynomial (Fin n × Fin n) ℂ)).natDegree + 2),
    Polynomial.C (Cxc.extL lam i (Formalism.GradedWeylDivisibility.rowDiv ℂ a b k ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
      MvPolynomial (Fin n × Fin n) ℂ))) * Polynomial.X ^ k

theorem extL_rowAct (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) (s : ℂ) :
    Cxc.extL lam i (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 + single a b s)ᵀ
      ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) = (qP lam a b i j).eval s := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowAct_eq_aeval, Polynomial.aeval_eq_sum_range' (lt_add_of_pos_right _ two_pos), qP, Polynomial.eval_finsetSum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, ← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul, map_smul]
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul, mul_comm]
  rfl

theorem qP_eval_zero (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) :
    (qP lam a b i j).eval 0 = Cxc.extL lam i ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, qP, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, if_pos (by simp), (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv ℂ n n a b _).2]

theorem qP_deriv_zero (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) :
    (Polynomial.derivative (qP lam a b i j)).eval 0 =
      Cxc.extL lam i (GlobalTheory.Mem.Gelf.rowE ℂ n n a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, qP, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, if_pos (by simp), (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv ℂ n n a b _).1]
  simp

theorem det_one_add_single (a b : Fin n) (w : ℂ) : (1 + single a b w : Mat n).det = if a = b then 1 + w else 1 := by
  have h : (single a b w : Mat n) = replicateCol (Fin 1) (Pi.single a w) * replicateRow (Fin 1) (Pi.single b (1 : ℂ)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.single_apply, Pi.single_apply, replicateCol_apply, replicateRow_apply]
    by_cases hi : i = a <;> by_cases hj : j = b
    · simp [hi, hj]
    · simp [hi, hj, Ne.symm hj]
    · simp [hi, hj, Ne.symm hi]
    · simp [hi, hj, Ne.symm hi]
  rw [h]
  refine (det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (Pi.single a w) (Pi.single b (1 : ℂ))).trans ?_
  split_ifs with hab
  · subst hab; simp
  · simp [Pi.single_apply, dotProduct, hab]

def Fw (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) (w : ℂ) : ℂ :=
  (if a = b then 1 + w else 1) ^ (dw lam).detShift * (qP lam a b i j).eval w

theorem entry_eq (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) (w : ℂ) (hw : (if a = b then 1 + w else (1 : ℂ)) ≠ 0) :
    Rm lam (1 + single a b w) i j = Fw lam a b i j w := by
  have hu : IsUnit (1 + single a b w : Mat n).det := by
    rw [det_one_add_single]; exact isUnit_iff_ne_zero.2 hw
  rw [Cxc.rm_entry lam _ hu i j, det_one_add_single, extL_rowAct, Fw]

theorem hasDerivAt_Fw (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) :
    HasDerivAt (Fw lam a b i j)
      ((if a = b then ((dw lam).detShift : ℂ) else 0) * (qP lam a b i j).eval 0 + (Polynomial.derivative (qP lam a b i j)).eval 0) 0 := by
  unfold Fw
  by_cases hab : a = b
  · simp only [if_pos hab]
    have h1 : HasDerivAt (fun w : ℂ => (1 + w) ^ (dw lam).detShift) ((dw lam).detShift : ℂ) 0 := by
      have := (hasDerivAt_zpow (dw lam).detShift (1 + (0 : ℂ)) (Or.inl (by simp))).comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_add 1)
      simp only [add_zero, _root_.one_zpow, mul_one] at this
      exact this
    have := h1.mul (Polynomial.hasDerivAt (qP lam a b i j) (0 : ℂ))
    simp only [add_zero, _root_.one_zpow, one_mul] at this
    exact this
  · simp only [if_neg hab, _root_.one_zpow, one_mul, zero_mul, zero_add]
    exact Polynomial.hasDerivAt (qP lam a b i j) (0 : ℂ)

theorem line_deriv (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) (z : ℂ) :
    HasDerivAt (fun t : ℝ => Rm lam (1 + t • single a b z) i j)
      (((if a = b then ((dw lam).detShift : ℂ) else 0) * (qP lam a b i j).eval 0 +
        (Polynomial.derivative (qP lam a b i j)).eval 0) * z) 0 := by
  have hF := (hasDerivAt_Fw lam a b i j).comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).mul_const z) (by simp)
  simp only [one_mul] at hF
  have hR : HasDerivAt (fun t : ℝ => Fw lam a b i j ((t : ℂ) * z))
      (((if a = b then ((dw lam).detShift : ℂ) else 0) * (qP lam a b i j).eval 0 +
        (Polynomial.derivative (qP lam a b i j)).eval 0) * z) 0 :=
    HasDerivAt.comp_ofReal (e := fun w : ℂ => Fw lam a b i j (w * z)) (z := 0)
      (by rw [Complex.ofReal_zero]; exact hF)
  refine hR.congr_of_eventuallyEq ?_
  have hc : ∀ᶠ t : ℝ in nhds 0, (if a = b then 1 + (t : ℂ) * z else (1 : ℂ)) ≠ 0 := by
    by_cases hab : a = b
    · simp only [if_pos hab]
      have hcont : ContinuousAt (fun t : ℝ => 1 + (t : ℂ) * z) 0 := by fun_prop
      exact hcont.eventually_ne (by simp)
    · simp only [if_neg hab]
      exact Filter.Eventually.of_forall fun _ => one_ne_zero
  filter_upwards [hc] with t ht
  rw [Matrix.smul_single, Complex.real_smul, entry_eq lam a b i j _ ht]

theorem isOpen_GLs : IsOpen (GLs n) := isOpen_ne_fun Cxc.det_smooth.continuous continuous_const

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem fderiv_single (lam : Fin n → ℤ) (a b : Fin n) (z : ℂ) :
    fderiv ℝ (Rm lam) 1 (single a b z) = z • At lam a b := by
  have hd : DifferentiableAt ℝ (Rm lam) 1 :=
    ((Cxc.rm_smooth lam).contDiffAt (isOpen_GLs.mem_nhds one_mem_GLs)).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • single a b z) (single a b z) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (single a b z)).const_add (1 : Mat n)
    simp only [id, one_smul] at this
    exact this
  have h1 : HasDerivAt (fun t : ℝ => Rm lam (1 + t • single a b z)) (fderiv ℝ (Rm lam) 1 (single a b z)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  ext i j
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 i) j
  rw [← (line_deriv lam a b i j z).unique h2, qP_eval_zero, qP_deriv_zero]
  change _ = z * Cxc.extL lam i (Et lam a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ))
  rw [Et, Matrix.add_apply, LinearMap.add_apply, map_add (f := _), Matrix.smul_apply, Matrix.one_apply]
  split_ifs with hab
  · simp
    ring
  · simp
    ring

theorem atDer' : AtDer := by
  intro n lam _ Y
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun b _ => fderiv_single lam a b (Y a b)

end PositivityTheory.RgBcC.Cxd2.Der

namespace PositivityTheory.RgBcC.Cxd2

theorem atDer : AtDer := Der.atDer'

end PositivityTheory.RgBcC.Cxd2
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.HasDerivAtInvLine
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.HasDerivAtRmOne
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxd2

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  show IsOpen {g : Mat n | g.det ≠ 0}
  exact isOpen_ne_fun continuous_id.matrix_det continuous_const

theorem rm_diff (lam : Fin n → ℤ) {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ (Rm lam) x :=
  ((Cxc.rm_smooth lam).contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)

theorem hasDerivAt_line {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Mat n → W} {x : Mat n}
    (hf : DifferentiableAt ℝ f x) (X : Mat n) :
    HasDerivAt (fun t : ℝ => f (x * (1 + t • X))) (fderiv ℝ f x (x * X)) 0 := by
  have hg : HasDerivAt (fun t : ℝ => x * (1 + t • X)) (x * X) 0 := by
    have e : (fun t : ℝ => x * (1 + t • X)) = fun t => x + t • (x * X) := by
      funext t
      rw [mul_add, mul_one, Matrix.mul_smul]
    rw [e]
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (x * X)).const_add x
    rw [one_smul] at this
    exact this
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hg (by simp)

def entL {J : Type} [Fintype J] [DecidableEq J] (P N : Matrix J J ℂ) (i j : J) : Matrix J J ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (P * M * N) i j
      map_add' := fun M M' => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r M => by simp [Matrix.mul_smul, Matrix.smul_mul] }

theorem entL_apply {J : Type} [Fintype J] [DecidableEq J] (P N M : Matrix J J ℂ) (i j : J) :
    entL P N i j M = (P * M * N) i j := rfl

theorem eventually_det (X : Mat n) : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • X).det := by
  have hc : Continuous (fun t : ℝ => (1 + t • X).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have h0 : (1 + (0 : ℝ) • X).det ≠ 0 := by simp
  exact (hc.continuousAt.eventually_ne h0).mono fun t ht => isUnit_iff_ne_zero.mpr ht

theorem hasDerivAt_rm_one (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (X : Mat n) :
    HasDerivAt (fun t : ℝ => Rm lam (1 + t • X)) (∑ a, ∑ b, X a b • At lam a b) 0 := by
  have h := hasDerivAt_line (rm_diff lam (x := 1) (by show (1 : Mat n).det ≠ 0; simp)) X
  simp only [one_mul] at h
  convert h using 1
  all_goals first
    | rfl
    | exact (hD n lam hlam X).symm
    | (congr 1; exact (hD n lam hlam X).symm)

theorem rd_hol (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (X : Mat n) :
    Rd X (fun y => (Rm lam y * N) i j) x = (Rm lam x * (∑ a, ∑ b, X a b • At lam a b) * N) i j := by
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have hf : DifferentiableAt ℝ (fun y => (Rm lam y * N) i j) x := by
    have := ((entL 1 N i j).differentiableAt).comp x (rm_diff lam hx)
    simp only [Function.comp_def, entL_apply, one_mul] at this
    exact this
  have h1 := hasDerivAt_line hf X
  have h2 : HasDerivAt (fun t : ℝ => (Rm lam x * Rm lam (1 + t • X) * N) i j)
      ((Rm lam x * (∑ a, ∑ b, X a b • At lam a b) * N) i j) 0 := by
    have := (entL (Rm lam x) N i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rm_one lam hD hlam X)
    simp only [Function.comp_def, entL_apply] at this
    exact this
  have h3 : (fun t : ℝ => (Rm lam (x * (1 + t • X)) * N) i j) =ᶠ[nhds 0]
      fun t => (Rm lam x * Rm lam (1 + t • X) * N) i j := by
    filter_upwards [eventually_det X] with t ht
    rw [Cxc.rm_mul lam x _ hxu ht]
  show fderiv ℝ (fun y => (Rm lam y * N) i j) x (x * X) = _
  exact h1.unique (h3.hasDerivAt_iff.mpr h2)

theorem sum_single {lam : Fin n → ℤ} (X : Mat n) (a b : Fin n) (z : ℂ) (A : Fin n → Fin n → Matrix (Jd n lam) (Jd n lam) ℂ) :
    ∑ c, ∑ d, (Matrix.single a b z : Mat n) c d • A c d = z • A a b := by
  simp [Matrix.single_apply, ite_and, ite_smul]

theorem eu_hol (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (s : Bool) (a b : Fin n) :
    Eu s a b (fun y => (Rm lam y * N) i j) x = if s then (Rm lam x * At lam a b * N) i j else 0 := by
  have e1 := rd_hol lam hD hlam N i j hx (Matrix.single a b 1)
  have e2 := rd_hol lam hD hlam N i j hx (Matrix.single a b Complex.I)
  rw [sum_single (0 : Mat n) a b (1 : ℂ) (At lam)] at e1
  rw [sum_single (0 : Mat n) a b Complex.I (At lam)] at e2
  simp only [Eu, Pi.smul_apply, Pi.add_apply, e1, e2]
  cases s <;> simp [Matrix.mul_smul, Matrix.smul_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem eu_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f g : Mat n → V} {x : Mat n}
    (h : f =ᶠ[nhds x] g) (s : Bool) (a b : Fin n) : Eu s a b f x = Eu s a b g x := by
  have e : ∀ Y : Mat n, Rd Y f x = Rd Y g x := fun Y => by
    simp only [Rd, h.fderiv_eq]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, e]

theorem epow_hol (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (M : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow true m a b (fun y => (Rm lam y * M) i j))
      (fun y => (Rm lam y * (At lam ^ m) a b * M) i j) (GLs n) := by
  induction m with
  | zero =>
    intro a b y hy
    rw [Epow.eq_1]
    by_cases h : a = b <;> simp [h, Matrix.one_apply]
  | succ m ih =>
    intro a b y hy
    rw [show m + 1 = m.succ from rfl, Epow.eq_2]
    simp only [Finset.sum_apply]
    have key : ∀ c, Eu true a c (Epow true m c b (fun y => (Rm lam y * M) i j)) y
        = (Rm lam y * At lam a c * ((At lam ^ m) c b * M)) i j := fun c => by
      rw [eu_congr (g := fun z => (Rm lam z * ((At lam ^ m) c b * M)) i j) ?_ true a c]
      · rw [eu_hol lam hD hlam ((At lam ^ m) c b * M) i j hy true a c]
        exact if_pos rfl
      · filter_upwards [isOpen_GLs.mem_nhds hy] with z hz
        exact (ih c b hz).trans (congrFun (congrFun (Matrix.mul_assoc _ _ _) i) j)
    simp only [key]
    rw [pow_succ', Matrix.mul_apply (M := At lam) (N := At lam ^ m), Finset.mul_sum, Finset.sum_mul,
      Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_assoc]

theorem rmHol_of (hT : AtTrace) (hD : AtDer) : RmHol := by
  intro n lam hlam M i j g hg
  refine ⟨fun m => ?_, fun a b => by rw [eu_hol lam hD hlam M i j hg false a b]; rfl⟩
  simp only [gel, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => epow_hol lam hD hlam M i j m a a hg]
  have e : ∑ a, (Rm lam g * (At lam ^ m) a a * M) i j = (Rm lam g * (At lam ^ m).trace * M) i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  rw [e, hT n lam hlam m]
  simp [Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.RgBcC.Cxd2
end
end

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxd2

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem updateRow_smooth (j : Fin n) (v : Fin n → ℂ) : ContDiff ℝ ∞ (fun x : Mat n => x.updateRow j v) := by
  refine contDiff_pi.2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    have e : (fun x : Mat n => x.updateRow k v k) = fun _ => v := by funext x; simp [Matrix.updateRow_apply]
    rw [e]; exact contDiff_const
  · have e : (fun x : Mat n => x.updateRow j v k) = fun x : Mat n => (x : Fin n → Fin n → ℂ) k := by
      funext x; simp [Matrix.updateRow_apply, hk]
    rw [e]; exact contDiff_apply ℝ (fun _ => (Fin n → ℂ)) k

theorem adjugate_smooth : ContDiff ℝ ∞ (fun x : Mat n => x.adjugate) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e : (fun x : Mat n => x.adjugate i j) = fun x : Mat n => (x.updateRow j (Pi.single i 1)).det := by
    funext x; rw [Matrix.adjugate_apply]
  rw [e]
  exact Cxc.det_smooth.comp (updateRow_smooth j _)

theorem inv_smooth : ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun x : Mat n => Matrix.of fun i j => x.det ^ (-1 : ℤ) * x.adjugate i j) (GLs n) := by
    refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
    exact (Cxc.detPow_smooth (-1)).mul ((contDiff_apply_apply ℝ i j).comp adjugate_smooth).contDiffOn
  refine h.congr fun x hx => ?_
  ext i j
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp [_root_.zpow_neg_one]

def cTL : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun r A => by simp [Matrix.conjTranspose_smul] }

theorem det_inv_ne {x : Mat n} (hx : x ∈ GLs n) : (x⁻¹).det ≠ 0 := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero hx

theorem mem_theta {x : Mat n} (hx : x ∈ GLs n) : (x⁻¹)ᴴ ∈ GLs n := by
  show ((x⁻¹)ᴴ).det ≠ 0
  rw [Matrix.det_conjTranspose]
  exact (star_ne_zero).2 (det_inv_ne hx)

theorem theta_diff {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ (fun y : Mat n => (y⁻¹)ᴴ) x := by
  have h := (inv_smooth.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
  exact cTL.differentiableAt.comp x h

theorem hasDerivAt_mat_mul {m : Type} [Fintype m] [DecidableEq m] {P Q : ℝ → Matrix m m ℂ} {P' Q' : Matrix m m ℂ}
    (hP : HasDerivAt P P' 0) (hQ : HasDerivAt Q Q' 0) :
    HasDerivAt (fun t => P t * Q t) (P' * Q 0 + P 0 * Q') 0 := by
  have hP2 : ∀ i k, HasDerivAt (fun t => P t i k) (P' i k) 0 := fun i k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hP i) k
  have hQ2 : ∀ k j, HasDerivAt (fun t => Q t k j) (Q' k j) 0 := fun k j =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hQ k) j
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  have h := HasDerivAt.sum (u := Finset.univ) fun k _ => (hP2 i k).mul (hQ2 k j)
  simp only [Matrix.mul_apply, Matrix.add_apply]
  convert h using 1
  · funext t; simp [Finset.sum_apply]
  · simp [Finset.sum_add_distrib, mul_comm]

theorem hasDerivAt_inv_line (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (-X) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hd : DifferentiableAt ℝ (fun x : Mat n => x⁻¹) (1 : Mat n) :=
    (inv_smooth.contDiffAt (isOpen_GLs.mem_nhds h1)).differentiableAt (by simp)
  have hu : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (fderiv ℝ (fun x : Mat n => x⁻¹) 1 X) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
    exact this
  have hprod := hasDerivAt_mat_mul hc hu
  have hconst : (fun t : ℝ => (1 + t • X) * (1 + t • X)⁻¹) =ᶠ[nhds 0] fun _ => (1 : Mat n) := by
    filter_upwards [eventually_det X] with t ht
    exact Matrix.mul_nonsing_inv _ ht
  have h0 := (hasDerivAt_const (0 : ℝ) (1 : Mat n)).congr_of_eventuallyEq hconst
  have e := hprod.unique h0
  simp only [zero_smul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul] at e
  have e2 : fderiv ℝ (fun x : Mat n => x⁻¹) 1 X = -X := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact e
  rwa [e2] at hu

theorem hasDerivAt_rm_theta (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (X : Mat n) :
    HasDerivAt (fun t : ℝ => Rm lam ((1 + t • X)⁻¹)ᴴ) (∑ a, ∑ b, (-Xᴴ) a b • At lam a b) 0 := by
  have hc : HasDerivAt (fun t : ℝ => ((1 + t • X)⁻¹)ᴴ) (-Xᴴ) 0 := by
    have := cTL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_inv_line X)
    exact this.congr_deriv (Matrix.conjTranspose_neg X)
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have h := (rm_diff lam h1).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  exact h.congr_deriv (hD n lam hlam _)

theorem rd_anti (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (X : Mat n) :
    Rd X (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x = (Rm lam (x⁻¹)ᴴ * (∑ a, ∑ b, (-Xᴴ) a b • At lam a b) * N) i j := by
  have hdf : DifferentiableAt ℝ (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x := by
    have : (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) = entL 1 N i j ∘ Rm lam ∘ fun y : Mat n => (y⁻¹)ᴴ := by
      funext y; simp [entL_apply]
    rw [this]
    exact (entL 1 N i j).differentiableAt.comp x ((rm_diff lam (mem_theta hx)).comp x (theta_diff hx))
  have h1 := hasDerivAt_line hdf X
  have h2 : HasDerivAt (fun t : ℝ => entL (Rm lam (x⁻¹)ᴴ) N i j (Rm lam ((1 + t • X)⁻¹)ᴴ))
      (entL (Rm lam (x⁻¹)ᴴ) N i j (∑ a, ∑ b, (-Xᴴ) a b • At lam a b)) 0 :=
    (entL (Rm lam (x⁻¹)ᴴ) N i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rm_theta lam hD hlam X)
  have hxu : IsUnit ((x⁻¹)ᴴ).det := isUnit_iff_ne_zero.2 (mem_theta hx)
  have h3 : (fun t : ℝ => (Rm lam ((x * (1 + t • X))⁻¹)ᴴ * N) i j) =ᶠ[nhds 0]
      fun t : ℝ => entL (Rm lam (x⁻¹)ᴴ) N i j (Rm lam ((1 + t • X)⁻¹)ᴴ) := by
    filter_upwards [eventually_det X] with t ht
    have ht' : IsUnit (((1 + t • X)⁻¹)ᴴ).det := by
      rw [Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact (isUnit_iff_ne_zero.2 (star_ne_zero.2 (inv_ne_zero (isUnit_iff_ne_zero.1 ht))))
    rw [entL_apply, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Cxc.rm_mul lam _ _ hxu ht']
  exact h1.unique (h2.congr_of_eventuallyEq h3)

theorem sum_single_neg {lam : Fin n → ℤ} (a b : Fin n) (z : ℂ) (A : Fin n → Fin n → Matrix (Jd n lam) (Jd n lam) ℂ) :
    ∑ c, ∑ d, (-(Matrix.single a b z : Mat n)ᴴ) c d • A c d = (-star z) • A b a := by
  rw [Matrix.conjTranspose_single]
  simp only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]
  rw [sum_single (lam := lam) 0 b a _ A]

theorem eu_anti (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (s : Bool) (a b : Fin n) :
    Eu s a b (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x = if s then 0 else (Rm lam (x⁻¹)ᴴ * -At lam b a * N) i j := by
  have e1 := rd_anti lam hD hlam N i j hx (Matrix.single a b 1)
  have e2 := rd_anti lam hD hlam N i j hx (Matrix.single a b Complex.I)
  rw [sum_single_neg a b 1 (At lam)] at e1
  rw [sum_single_neg a b Complex.I (At lam)] at e2
  simp only [Eu, Pi.add_apply, Pi.smul_apply, e1, e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
  cases s <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def Bt (lam : Fin n → ℤ) : Matrix (Fin n) (Fin n) (Matrix (Jd n lam) (Jd n lam) ℂ) := Matrix.of fun a b => -(At lam b a)

theorem epow_anti (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (M : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow false m a b (fun y => (Rm lam (y⁻¹)ᴴ * M) i j))
      (fun y => (Rm lam (y⁻¹)ᴴ * (Bt lam ^ m) a b * M) i j) (GLs n) := by
  induction m with
  | zero =>
    intro a b y _
    simp only [Epow, pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ m ih =>
    intro a b y hy
    simp only [Epow, Finset.sum_apply]
    have e : ∀ c, Eu false a c (Epow false m c b fun y => (Rm lam (y⁻¹)ᴴ * M) i j) y =
        (Rm lam (y⁻¹)ᴴ * Bt lam a c * ((Bt lam ^ m) c b * M)) i j := by
      intro c
      have hev : (Epow false m c b fun y => (Rm lam (y⁻¹)ᴴ * M) i j) =ᶠ[nhds y]
          fun y => (Rm lam (y⁻¹)ᴴ * ((Bt lam ^ m) c b * M)) i j := by
        filter_upwards [isOpen_GLs.mem_nhds hy] with z hz
        rw [ih c b hz]
        simp only [Matrix.mul_assoc]
      rw [eu_congr hev, eu_anti lam hD hlam _ i j hy]
      simp [Bt, Matrix.mul_assoc]
    simp only [e]
    have hp : (Bt lam ^ (m + 1)) a b = ∑ c, Bt lam a c * (Bt lam ^ m) c b := by rw [pow_succ', Matrix.mul_apply]
    show ∑ c, _ = (Rm lam (y⁻¹)ᴴ * (Bt lam ^ (m + 1)) a b * M) i j
    rw [hp, Matrix.mul_sum, Finset.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.mul_assoc]

theorem rmAnti_of (hT : AtTraceT) (hD : AtDer) : RmAnti := by
  intro n lam hlam M i j g hg
  refine ⟨fun m => ?_, fun a b => by rw [eu_anti lam hD hlam M i j hg true a b]; rfl⟩
  simp only [gel, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => epow_anti lam hD hlam M i j m a a hg]
  have e : ∑ a, (Rm lam (g⁻¹)ᴴ * (Bt lam ^ m) a a * M) i j = (Rm lam (g⁻¹)ᴴ * (Bt lam ^ m).trace * M) i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  rw [e]
  have hB : (Bt lam ^ m).trace = GlobalTheory.Dec.gelfVal (infOf lam false) m • (1 : Matrix (Jd n lam) (Jd n lam) ℂ) :=
    hT n lam hlam m
  rw [hB]
  simp [Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.RgBcC.Cxd2
end
end

namespace PositivityTheory.RgBcC

theorem rmHol : RmHol := Cxd2.rmHol_of Cxd2.atTrace Cxd2.atDer

theorem rmAnti : RmAnti := Cxd2.rmAnti_of Cxd2.atTraceT Cxd2.atDer

end PositivityTheory.RgBcC
