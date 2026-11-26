module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalUnitaryCoordinateZeroOfRationalPoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormCloseToOneOfCloseAbovePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicative
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtMul

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def substL (A : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.C (A v.1 v.2.1 m) * MvPolynomial.X (v.1, m, v.2.2)

def substR (B : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.X (v.1, v.2.1, m) * MvPolynomial.C (B v.1 m v.2.2)

theorem eval_bind_substL (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q) =
      MvPolynomial.eval (upt (fun σ => A σ * Y σ)) Q := by
  calc MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q)
      = MvPolynomial.aeval (fun v => MvPolynomial.aeval (upt Y) (substL A v)) Q :=
        MvPolynomial.aeval_bind₁ _ _ _
    _ = _ := by
      change MvPolynomial.eval (fun v => MvPolynomial.eval (upt Y) (substL A v)) Q = _
      have hf : (fun v => MvPolynomial.eval (upt Y) (substL A v)) = upt (fun σ => A σ * Y σ) := by
        funext v
        simp [substL, upt, Matrix.mul_apply]
      rw [hf]

theorem eval_bind_substR (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) Q) =
      MvPolynomial.eval (upt (fun σ => X σ * B σ)) Q := by
  calc MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) Q)
      = MvPolynomial.aeval (fun v => MvPolynomial.aeval (upt X) (substR B v)) Q :=
        MvPolynomial.aeval_bind₁ _ _ _
    _ = _ := by
      change MvPolynomial.eval (fun v => MvPolynomial.eval (upt X) (substR B v)) Q = _
      have hf : (fun v => MvPolynomial.eval (upt X) (substR B v)) = upt (fun σ => X σ * B σ) := by
        funext v
        simp [substR, upt, Matrix.mul_apply]
      rw [hf]

theorem defectL_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt A) i m) * P m j) =
      evM P (upt (fun σ => A σ * Y σ)) i j - (evM P (upt A) * evM P (upt Y)) i j := by
  rw [map_sub, eval_bind_substL]
  simp [evM, Matrix.mul_apply]

theorem defectR_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) (P i j) -
        ∑ m, P i m * MvPolynomial.C (evM P (upt B) m j)) =
      evM P (upt (fun σ => X σ * B σ)) i j - (evM P (upt X) * evM P (upt B)) i j := by
  rw [map_sub, eval_bind_substR]
  simp [evM, Matrix.mul_apply]

theorem evM_ratPt (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (hA : Agrees a b P)
    (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ) := by
  rw [hA γ γ₀ h]
  ext i j
  rfl

theorem ratPt_one :
    ratPt ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
  funext σ
  simp [ratPt]

theorem ratPt_mul (γ₀ γ₁ : GL (Fin n) L) :
    ratPt ((γ₀ * γ₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * ratPt (γ₁ : Matrix (Fin n) (Fin n) L) σ := by
  funext σ
  simp [ratPt, Matrix.map_mul]

theorem evM_mul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    Agrees a b P → evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 ∧
      ∀ X Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → IsUPt Y →
        evM P (upt (fun σ => X σ * Y σ)) = evM P (upt X) * evM P (upt Y) := by
  intro L _ _ _ n a ι _ _ b P hA
  have h1 : evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 := by
    have hm : ((((1 : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      simp only [OneMemClass.coe_one, Units.val_one]
      exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
    rw [← ratPt_one, evM_ratPt a b P hA 1 1 hm, map_one, LinearMap.toMatrix_one]
  have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ γ₁ : GL (Fin n) L, γ₁ ∈ GQ0 L n →
      evM P (upt (fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * ratPt (γ₁ : Matrix (Fin n) (Fin n) L) σ)) =
        evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * evM P (upt (ratPt (γ₁ : Matrix (Fin n) (Fin n) L))) := by
    intro γ₀ h₀ γ₁ h₁
    obtain ⟨γ, hγ⟩ := exists_gq γ₀ h₀
    obtain ⟨γ', hγ'⟩ := exists_gq γ₁ h₁
    have hm : ((((γ * γ' : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((γ₀ * γ₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      simp only [Subgroup.coe_mul, Units.val_mul, hγ, hγ', Matrix.map_mul]
    rw [← ratPt_mul, evM_ratPt a b P hA _ _ hm, evM_ratPt a b P hA _ _ hγ, evM_ratPt a b P hA _ _ hγ', map_mul,
      LinearMap.toMatrix_mul]
  have hL : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt Y →
      evM P (upt (fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * Y σ)) =
        evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * evM P (upt Y) := by
    intro γ₀ h₀ Y hY
    ext i j
    have e := GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n (MvPolynomial.bind₁ (substL (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) i m) * P m j)
      (fun γ₁ h₁ => by rw [defectL_eval, hrat γ₀ h₀ γ₁ h₁, sub_self]) Y hY
    rw [defectL_eval, sub_eq_zero] at e
    exact e
  refine ⟨h1, fun X Y hX hY => ?_⟩
  ext i j
  have e := GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n (MvPolynomial.bind₁ (substR Y) (P i j) -
      ∑ m, P i m * MvPolynomial.C (evM P (upt Y) m j))
    (fun γ₀ h₀ => by rw [defectR_eval, hL γ₀ h₀ Y hY, sub_self]) X hX
  rw [defectR_eval, sub_eq_zero] at e
  exact e

end GlobalTheory.AlgWtMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicativeStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 ∧ ∀ X Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → IsUPt Y → evM P (upt (fun σ => X σ * Y σ)) = evM P (upt X) * evM P (upt Y) := by
  first | exact @GlobalTheory.AlgWtMul.evM_mul | exact GlobalTheory.AlgWtMul.evM_mul | (intros; apply GlobalTheory.AlgWtMul.evM_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.FrobSemisimple

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem minpoly_eval_zero_ne_zero {f : End ℂ V} (hf : IsUnit f) : (minpoly ℂ f).eval 0 ≠ 0 := by
  intro h0
  have h1 : f.HasEigenvalue 0 := End.hasEigenvalue_iff_isRoot.mpr h0
  exact spectrum.zero_notMem ℂ hf (End.hasEigenvalue_iff_mem_spectrum.mp h1)

theorem isSemisimple_of_pow {g : End ℂ V} (hg : IsUnit g) {m : ℕ} (hm : 0 < m)
    (hs : (g ^ m).IsSemisimple) : g.IsSemisimple := by
  have hsep : (minpoly ℂ (g ^ m)).Separable :=
    PerfectField.separable_iff_squarefree.mpr hs.minpoly_squarefree
  have h0 := minpoly_eval_zero_ne_zero (hg.pow m)
  set p := minpoly ℂ (g ^ m) with hp
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := expand ℂ m p)
    (Separable.squarefree ?_) ?_
  · rw [Separable, derivative_expand]
    refine IsCoprime.mul_right (IsCoprime.map hsep (expand ℂ m).toRingHom)
      (IsCoprime.mul_right ?_ (IsCoprime.pow_right ?_))
    · have : IsUnit ((m : ℕ) : ℂ[X]) := by
        rw [← C_eq_natCast]
        exact isUnit_C.mpr (Ne.isUnit (Nat.cast_ne_zero.mpr hm.ne'))
      exact (isCoprime_mul_unit_left_right this _ 1).mpr isCoprime_one_right |>.of_mul_right_left
    · refine ((irreducible_X.coprime_iff_not_dvd).mpr ?_).symm
      rw [X_dvd_iff, coeff_zero_eq_eval_zero, expand_eval, zero_pow hm.ne']
      exact h0
  · rw [expand_aeval]
    exact minpoly.aeval ℂ _

end GlobalTheory.WeilDeligne.FrobSemisimple

namespace GlobalTheory.WeilDeligne

private theorem isSemisimple_of_mul_eq_one' {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {f g : End ℂ V} (hf : f.IsSemisimple) (hgf : g * f = 1) :
    g.IsSemisimple := by
  apply _root_.GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
  have htop : ⨆ α, f.eigenspace α = ⊤ :=
    hf.iSup_maxGenEigenspace_eq_top_iff.1 (Module.End.iSup_maxGenEigenspace_eq_top f)
  rw [eq_top_iff, ← htop]
  refine iSup_le fun α => le_trans ?_ (le_iSup _ α⁻¹)
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : v = α • g v := by
    have := congrArg g hv
    rwa [← Module.End.mul_apply, hgf, Module.End.one_apply, map_smul] at this
  by_cases hα : α = 0
  · subst hα
    rw [zero_smul] at h1
    simp [h1]
  · conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hα, one_smul]

private theorem isSemisimple_of_isUnit_of_pow_isSemisimple {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {f : End ℂ V} (hf : IsUnit f) {m : ℕ} (hm : 0 < m)
    (hfm : (f ^ m).IsSemisimple) : f.IsSemisimple := by
  have hint : IsIntegral ℂ (f ^ m) := Algebra.IsIntegral.isIntegral _
  have hX : ¬ X ∣ minpoly ℂ (f ^ m) := by
    rintro ⟨q, hq⟩
    have h0 : aeval (f ^ m) q = 0 := by
      have h1 := minpoly.aeval ℂ (f ^ m)
      rw [hq, map_mul, aeval_X] at h1
      exact (hf.pow m).mul_right_eq_zero.1 h1
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact minpoly.ne_zero hint (by simpa using hq)
    have hdeg := natDegree_le_of_dvd (minpoly.dvd ℂ (f ^ m) h0) hq0
    rw [hq, natDegree_mul X_ne_zero hq0, natDegree_X] at hdeg
    omega
  have hsep : (minpoly ℂ (f ^ m)).Separable :=
    PerfectField.separable_iff_squarefree.2 hfm.minpoly_squarefree
  have hXe : ¬ X ∣ expand ℂ m (minpoly ℂ (f ^ m)) := by
    rw [X_dvd_iff, coeff_expand hm]
    rw [X_dvd_iff] at hX
    simpa using hX
  have hunit : IsUnit ((m : ℂ[X])) := by
    rw [← map_natCast C]
    exact isUnit_C.2 (Ne.isUnit (by exact_mod_cast hm.ne'))
  have hP : (expand ℂ m (minpoly ℂ (f ^ m))).Separable := by
    rw [separable_def, derivative_expand]
    refine IsCoprime.mul_right
      (((separable_def _).1 hsep).map (expand ℂ m).toRingHom) (IsCoprime.mul_right ?_ ?_)
    · exact isCoprime_one_right.of_isCoprime_of_dvd_right (hunit.dvd)
    · exact IsCoprime.pow_right ((Irreducible.coprime_iff_not_dvd irreducible_X).2 hXe).symm
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hP.squarefree
  rw [expand_aeval]
  exact minpoly.aeval ℂ (f ^ m)

theorem _root_.GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type)
      [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
      _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ φ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg φ = 1 →
      End.IsSemisimple (ρ φ) → ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, End.IsSemisimple (ρ σ) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ φ hφ hss σ
  have hunit : IsUnit (ρ σ) := (Group.isUnit σ).map ρ
  obtain ⟨τ, hτdeg, hτ⟩ : ∃ τ : _root_.GlobalTheory.WeilDeligne.Weil h,
      _root_.GlobalTheory.WeilDeligne.deg τ = _root_.GlobalTheory.WeilDeligne.deg σ ∧ End.IsSemisimple (ρ τ) := by
    rcases le_or_gt 0 (_root_.GlobalTheory.WeilDeligne.deg σ) with hd | hd
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hd
      refine ⟨φ ^ k, by rw [_root_.GlobalTheory.WeilDeligne.deg_pow, hφ, hk]; ring, ?_⟩
      rw [map_pow]
      exact hss.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
    · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hd.le
      have hinv : End.IsSemisimple (ρ φ⁻¹) :=
        isSemisimple_of_mul_eq_one' hss (by rw [← map_mul, inv_mul_cancel, map_one])
      refine ⟨φ⁻¹ ^ k, ?_, ?_⟩
      · rw [_root_.GlobalTheory.WeilDeligne.deg_pow, ← zpow_neg_one, _root_.GlobalTheory.WeilDeligne.deg_zpow, hφ, hk]
        ring
      · rw [map_pow]
        exact hinv.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
  obtain ⟨m, hm, hpow⟩ :=
    _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ σ τ hτdeg.symm
  apply isSemisimple_of_isUnit_of_pow_isSemisimple hunit hm
  rw [hpow]
  exact hτ.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) m)

end GlobalTheory.WeilDeligne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrobStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V), IsSmooth ρ → ∀ φ : Weil h, deg φ = 1 → End.IsSemisimple (ρ φ) → ∀ σ : Weil h, End.IsSemisimple (ρ σ) := by
  first | exact @GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob | exact GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob | (intros; apply GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAevalEqSmulOnEigenspace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_pow_frob_commute {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ, Commute (ρ (frob (h := h)) ^ m) (ρ σ) := by
  have h1 : ∀ τ : Weil h, ∃ m : ℕ, 0 < m ∧ Commute (ρ (frob (h := h)) ^ m) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, he⟩ := exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ (frob (h := h))
      (τ * frob (h := h) * τ⁻¹) (by simp [deg_mul, deg_inv])
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, ← map_pow, conj_pow] at he
    show _ * _ = _ * _
    rw [← map_pow]
    conv_lhs => rw [he]
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have h2 : ∀ S : Set (End ℂ V), S.Finite → (∀ x ∈ S, ∃ τ, ρ τ = x) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ S, Commute (ρ (frob (h := h)) ^ m) x := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨1, one_pos, by simp⟩
    | @insert x S _ _ ih =>
      intro hx
      obtain ⟨m, hm, hc⟩ := ih fun y hy => hx y (Set.mem_insert_of_mem _ hy)
      obtain ⟨τ, rfl⟩ := hx x (Set.mem_insert _ _)
      obtain ⟨n, hn, hc'⟩ := h1 τ
      refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      rintro y (rfl | hy)
      · rw [mul_comm, pow_mul]; exact hc'.pow_left m
      · rw [pow_mul]; exact (hc y hy).pow_left n
  obtain ⟨m, hm, hc⟩ := h2 _ hρ.finite_range (by rintro _ ⟨σ, rfl⟩; exact ⟨_, rfl⟩)
  refine ⟨m, hm, fun σ => ?_⟩
  have h0 : deg ((frob (h := h) ^ deg σ)⁻¹ * σ) = 0 := by
    simp [deg_mul, deg_inv, deg_zpow, deg_frob]
  have h3 : Commute (ρ (frob (h := h)) ^ m) (ρ ((frob (h := h) ^ deg σ)⁻¹ * σ)) :=
    hc _ ⟨⟨_, deg_eq_zero_iff.mp h0⟩, rfl⟩
  have h4 : Commute (ρ (frob (h := h)) ^ m) (ρ (frob (h := h) ^ deg σ)) :=
    (((Commute.refl (frob (h := h))).zpow_right _).map ρ).pow_left m
  have := h4.mul_right h3
  rwa [← map_mul, mul_inv_cancel_left] at this

private lemma exists_polynomial_eigenspace_smul_lemma {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (f : ℂ → ℂ) :
    ∃ p : ℂ[X], ∀ (α : ℂ) (v : V), v ∈ T.eigenspace α → aeval T p v = f α • v := by
  classical
  have hfin : Set.Finite {μ | T.HasEigenvalue μ} := Module.End.finite_hasEigenvalue T
  refine ⟨Lagrange.interpolate hfin.toFinset id f, fun α v hv => ?_⟩
  by_cases hv0 : v = 0
  · simp [hv0]
  have hev : T.HasEigenvector α v := ⟨hv, hv0⟩
  rw [Module.End.aeval_apply_of_hasEigenvector hev]
  have hnode := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) f
    (Set.injOn_id _) (i := α) (by simpa using Module.End.hasEigenvalue_of_hasEigenvector hev)
  simp only [id] at hnode
  rw [hnode]

private lemma eq_of_eq_on_eigenspaces_lemma_2 {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (hT : T.IsSemisimple) {g g' : Module.End ℂ V}
    (h : ∀ (α : ℂ) (v : V), v ∈ T.eigenspace α → g v = g' v) : g = g' := by
  have hle : ⨆ α, T.eigenspace α ≤ LinearMap.ker (g - g') :=
    iSup_le fun α v hv => by simp [sub_eq_zero, h α v hv]
  rw [hT.iSup_eigenspace_eq_top] at hle
  ext v
  simpa [sub_eq_zero] using hle (Submodule.mem_top : v ∈ ⊤)

private lemma mem_eigenspace_pow_lemma_3 {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) {α : ℂ} {v : V} (hv : v ∈ T.eigenspace α) (m : ℕ) :
    v ∈ (T ^ m).eigenspace (α ^ m) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

private lemma commute_aeval_of_commute_lemma_4 {V : Type} [AddCommGroup V] [Module ℂ V]
    {S T : Module.End ℂ V} (hST : Commute S T) (p : ℂ[X]) : Commute S (aeval T p) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add (f := _)]; exact hp.add_right hr
  | monomial n x => rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right x S).mul_right (hST.pow_right n)

theorem _root_.GlobalTheory.WeilDeligne.WDRep.iso_of_N_eq_smul : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a b : _root_.GlobalTheory.WeilDeligne.WDRep h V) (c : ℂ), c ≠ 0 → a.ρ = b.ρ →
    b.N = c • a.N → a.Iso b := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a b c hc hρ hN
  classical
  set φ := _root_.GlobalTheory.WeilDeligne.frob (h := h) with hφ
  set Φ : Module.End ℂ V := a.ρ φ with hΦdef
  have hΦ : Φ.IsSemisimple := a.semisimple φ
  have hq : (1 : ℝ) < (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) := by exact_mod_cast _root_.GlobalTheory.WeilDeligne.one_lt_normV w
  set s : ℂ := Complex.log c / (Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) : ℂ) with hsdef
  have hlogq : (Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  have hs : Complex.exp (s * Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ)) = c := by
    rw [hsdef, div_mul_cancel₀ _ hlogq, Complex.exp_log hc]
  set lam : ℂ → ℂ := fun α => Complex.exp (s * Real.log ‖α‖) with hlamdef
  have hlam : ∀ α : ℂ, α ≠ 0 → lam ((_root_.Formalism.ConjugateSelfDual.normV w : ℂ) * α) = c * lam α := by
    intro α hα
    simp only [hlamdef, norm_mul, Complex.norm_natCast]
    rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hα)]
    rw [Complex.ofReal_add, mul_add, Complex.exp_add, hs]
  have hΦinj : ∀ v : V, Φ v = 0 → v = 0 := by
    intro v hv
    have : a.ρ φ⁻¹ (Φ v) = v := by
      rw [hΦdef, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hv, map_zero]
  obtain ⟨p, hp⟩ := exists_polynomial_eigenspace_smul_lemma Φ lam
  obtain ⟨p', hp'⟩ := exists_polynomial_eigenspace_smul_lemma Φ (fun α => (lam α)⁻¹)
  have hgg' : aeval Φ p * aeval Φ p' = 1 := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
    rw [Module.End.mul_apply, hp' α v hv, map_smul, hp α v hv, smul_smul,
      inv_mul_cancel₀ (Complex.exp_ne_zero _), one_smul, Module.End.one_apply]
  have hg'g : aeval Φ p' * aeval Φ p = 1 := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
    rw [Module.End.mul_apply, hp α v hv, map_smul, hp' α v hv, smul_smul,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_smul, Module.End.one_apply]
  refine ⟨LinearEquiv.ofLinear (aeval Φ p) (aeval Φ p') hgg' hg'g, ?_, ?_⟩
  · intro σ v
    rw [← hρ]
    change aeval Φ p (a.ρ σ v) = a.ρ σ (aeval Φ p v)
    obtain ⟨m, hm, hpow⟩ := _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V a.ρ
      a.smooth (σ * φ * σ⁻¹) φ
      (by rw [_root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_inv]; ring)
    rw [← map_pow, conj_pow, map_mul, map_mul, map_pow] at hpow
    have hcomm : Commute (a.ρ σ) (Φ ^ m) := by
      calc a.ρ σ * Φ ^ m = a.ρ σ * Φ ^ m * (a.ρ σ⁻¹ * a.ρ σ) := by
            rw [← map_mul, inv_mul_cancel, map_one, mul_one]
        _ = Φ ^ m * a.ρ σ := by rw [← mul_assoc, hpow]
    obtain ⟨pm, hpm⟩ := exists_polynomial_eigenspace_smul_lemma (Φ ^ m)
      (fun μ => Complex.exp (s * Real.log ‖μ‖ / m))
    have hgm : aeval Φ p = aeval (Φ ^ m) pm := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
      rw [hp α v hv, hpm (α ^ m) v (mem_eigenspace_pow_lemma_3 Φ hv m)]
      congr 1
      simp only [hlamdef, norm_pow, Real.log_pow]
      congr 1
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    rw [hgm]
    exact (LinearMap.congr_fun (commute_aeval_of_commute_lemma_4 hcomm pm) v).symm
  · intro v
    rw [hN]
    change aeval Φ p (a.N v) =
      c • a.N (aeval Φ p v)
    have key : aeval Φ p * a.N =
        c • (a.N * aeval Φ p) :=
      eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
        rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, hp α v hv, map_smul]
        by_cases hα : α = 0
        · have hv0 : v = 0 := hΦinj v (by
            rw [Module.End.mem_eigenspace_iff] at hv
            rw [hv, hα, zero_smul])
          simp [hv0]
        · rw [hp _ _ (a.map_N_eigenspace
            (_root_.GlobalTheory.WeilDeligne.deg_frob) hv), hlam α hα, smul_smul]
    exact LinearMap.congr_fun key v

end GlobalTheory.WeilDeligne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAbove
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAbove
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem prod_zpow_const {ι B : Type} [CommGroup B] (c : B) (s : Finset ι) (e : ι → ℤ) :
    ∏ i ∈ s, c ^ e i = c ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

theorem finite_setOf_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have h0 : v.valuation F (x : F) ≠ 0 := by simp
  rcases lt_or_gt_of_ne hv with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.2 h0)).2 h
  · left
    exact h

theorem valued_locUnit (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : Fˣ) :
    Valued.v ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = v.valuation F (b : F) := by
  show Valued.v ((b : F) : v.adicCompletion F) = _
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem map_locUnit_eq_zpow {F B : Type} [Field F] [NumberField F] [CommGroup B] (ψ : Ideles F →* B)
    (v : HeightOneSpectrum (𝓞 F)) (hu : ∀ x, IsUnitAt v x → ψ (localIdele F v x) = 1)
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : IsUnifAt v ϖ) (b : Fˣ) :
    ψ (locUnit F v b) = ψ (localIdele F v ϖ) ^ ordF v b := by
  set x : (v.adicCompletion F)ˣ := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b with hx
  have hb0 : v.valuation F (b : F) ≠ 0 := by simp
  have hu' : IsUnitAt v (x * ϖ ^ (-ordF v b)) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, valued_locUnit, hϖ, ordF, neg_neg,
      ← WithZero.exp_zsmul, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.log_exp]
    simp
  have h := hu _ hu'
  rw [map_mul, map_mul, map_zpow, map_zpow, zpow_neg, mul_inv_eq_one] at h
  rw [locUnit_apply, ← hx]
  exact h

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem under_eq_iff {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 E)) :
    w.under (𝓞 E) = v ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  constructor
  · rintro rfl; rfl
  · intro h; exact HeightOneSpectrum.ext h

theorem finite_setOf_under_eq {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) = v}.Finite := by
  have h0 : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← (under_eq_iff w v).mp hw]

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem prod_locUnit_eq_prod_locUnit_norm : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (B : Type) [CommGroup B] (ψ1 : Ideles K →* B) (ψ2 : Ideles E →* B) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v ∉ S, ∀ x, IsUnitAt v x → ψ2 (localIdele E v x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x, IsUnitAt w x → ψ1 (localIdele K w x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → ψ1 (localIdele K w x) = ψ2 (localIdele E v ϖ) ^ w.asIdeal.inertiaDeg (𝓞 E)) → ∀ a : Kˣ, ∃ (TK : Finset (HeightOneSpectrum (𝓞 K))) (TE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ TK, ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) ∧ (∀ w ∉ TK, (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) → ψ1 (locUnit K w a) = 1) ∧ (∀ v ∈ TE, v ∉ S) ∧ (∀ v ∉ TE, v ∉ S → ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) = 1) ∧ ∏ w ∈ TK, ψ1 (locUnit K w a) = ∏ v ∈ TE, ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) := by
  classical
  intro E K _ _ _ _ _ B _ ψ1 ψ2 S h2u h1u h1f a
  set Na : Eˣ := Units.map (Algebra.norm E (S := K)) a with hNa
  have hfinE : ((fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E)) ''
      {w | w.valuation K (a : K) ≠ 1} ∪ {v : HeightOneSpectrum (𝓞 E) | v.valuation E (Na : E) ≠ 1}).Finite :=
    ((finite_setOf_valuation_ne_one K a).image _).union (finite_setOf_valuation_ne_one E Na)
  set TE : Finset (HeightOneSpectrum (𝓞 E)) := hfinE.toFinset.filter (· ∉ S) with hTE
  set TK : Finset (HeightOneSpectrum (𝓞 K)) :=
    TE.biUnion (fun v => (finite_setOf_under_eq (K := K) v).toFinset) with hTK
  have memTK : ∀ w, w ∈ TK ↔ w.under (𝓞 E) ∈ TE := by
    intro w
    simp only [hTK, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨_, h, rfl⟩⟩
  have memTE : ∀ v, v ∈ TE ↔ v ∉ S ∧ ((∃ w : HeightOneSpectrum (𝓞 K), w.valuation K (a : K) ≠ 1 ∧
      w.under (𝓞 E) = v) ∨ v.valuation E (Na : E) ≠ 1) := by
    intro v
    simp only [hTE, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
    exact and_comm
  have hcomap : ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = (w.under (𝓞 E)).asIdeal := fun w => rfl
  refine ⟨TK, TE, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv h
    have := ((memTE _).mp ((memTK w).mp hw)).1
    rw [(under_eq_iff w v).mpr h] at this
    exact this hv
  · intro w hw hS
    have hS' : w.under (𝓞 E) ∉ S := fun h => hS _ h (hcomap w)
    have hval : w.valuation K (a : K) = 1 := by
      by_contra h
      exact hw ((memTK w).mpr ((memTE _).mpr ⟨hS', Or.inl ⟨w, h, rfl⟩⟩))
    rw [locUnit_apply]
    refine h1u _ hS' w (hcomap w) _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  · intro v hv
    exact ((memTE v).mp hv).1
  · intro v hv hS
    have hval : v.valuation E (Na : E) = 1 := by
      by_contra h
      exact hv ((memTE v).mpr ⟨hS, Or.inr h⟩)
    rw [locUnit_apply]
    refine h2u v hS _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  ·
    set c : HeightOneSpectrum (𝓞 E) → B := fun v => ψ2 (localIdele E v (atFin v (unif v))) with hc
    have hK : ∀ w ∈ TK, ψ1 (locUnit K w a) =
        c (w.under (𝓞 E)) ^ ((w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * ordF w a) := by
      intro w hw
      have hS : w.under (𝓞 E) ∉ S := ((memTE _).mp ((memTK w).mp hw)).1
      rw [map_locUnit_eq_zpow ψ1 w (h1u _ hS w (hcomap w)) _ (unif_spec w),
        h1f _ hS w (hcomap w) _ _ (unif_spec w) (unif_spec _), zpow_mul, zpow_natCast]
    have hE : ∀ v ∈ TE, ψ2 (locUnit E v Na) = c v ^ ordF v Na := by
      intro v hv
      exact map_locUnit_eq_zpow ψ2 v (h2u v ((memTE v).mp hv).1) _ (unif_spec v) Na
    rw [Finset.prod_congr rfl hK, Finset.prod_congr rfl hE,
      ← Finset.prod_fiberwise_of_maps_to (g := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E))
        (t := TE) (fun w hw => (memTK w).mp hw)]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hfib : ∀ w ∈ TK.filter (fun w => w.under (𝓞 E) = v), c (w.under (𝓞 E)) = c v := by
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    rw [Finset.prod_congr rfl fun w hw => by rw [hfib w hw], prod_zpow_const]
    congr 1
    have hs : ∀ w, w ∈ TK.filter (fun w => w.under (𝓞 E) = v) ↔
        w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
      intro w
      rw [Finset.mem_filter, ← under_eq_iff]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨(memTK w).mpr (h ▸ hv), h⟩
    have key := GlobalTheory.T.intValuation_norm_eq_sum_residueDegree_mul E K v a _ hs
    simp only [ordF, hNa, Units.coe_map, MonoidHom.coe_coe] at key ⊢
    rw [key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end GlobalTheory.NormCompat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAboveStatement
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_localValues_global_over_places_above : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (B : Type) [CommGroup B] (ψ1 : Ideles K →* B) (ψ2 : Ideles E →* B) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v ∉ S, ∀ x, IsUnitAt v x → ψ2 (localIdele E v x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x, IsUnitAt w x → ψ1 (localIdele K w x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → ψ1 (localIdele K w x) = ψ2 (localIdele E v ϖ) ^ w.asIdeal.inertiaDeg (𝓞 E)) → ∀ a : Kˣ, ∃ (TK : Finset (HeightOneSpectrum (𝓞 K))) (TE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ TK, ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) ∧ (∀ w ∉ TK, (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) → ψ1 (locUnit K w a) = 1) ∧ (∀ v ∈ TE, v ∉ S) ∧ (∀ v ∉ TE, v ∉ S → ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) = 1) ∧ ∏ w ∈ TK, ψ1 (locUnit K w a) = ∏ v ∈ TE, ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) := by
  first | exact @GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm | exact GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm | (intros; apply GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm <;> assumption)
end
end
