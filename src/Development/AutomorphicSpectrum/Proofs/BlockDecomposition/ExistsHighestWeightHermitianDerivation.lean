module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoeffRowAct
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.WInfCont

theorem continuous_coeff_rowAct {r m : ℕ} (f : MvPolynomial (Fin r × Fin m) ℂ) :
    ∀ s : (Fin r × Fin m) →₀ ℕ, Continuous fun M : Matrix (Fin r) (Fin r) ℂ =>
      AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M f) s := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro s
    simpa [MvPolynomial.algebraMap_eq] using
      (continuous_const : Continuous fun _ : Matrix (Fin r) (Fin r) ℂ => AddMonoidAlgebra.coeff (MvPolynomial.C a) s)
  | add p q hp hq =>
    intro s
    simp only [map_add (f := _), MvPolynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    have key : ∀ M : Matrix (Fin r) (Fin r) ℂ, AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M (p * MvPolynomial.X v)) s =
        ∑ b : Fin r, M v.1 b * (if (b, v.2) ∈ s.support then
          AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M p) (s - Finsupp.single (b, v.2) 1) else 0) := by
      intro M
      have hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M (MvPolynomial.X v) =
          ∑ b : Fin r, MvPolynomial.C (M v.1 b) * MvPolynomial.X (b, v.2) := by
        simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
    simp only [key]
    refine continuous_finsetSum _ fun b _ => ?_
    refine ((continuous_id.matrix_elem v.1 b)).mul ?_
    split_ifs
    · exact hp _
    · exact continuous_const

theorem continuous_detPow (n : ℕ) (c : ℤ) : Continuous fun g : GL (Fin n) ℂ => detPow ℂ n g c := by
  have h0 : Continuous (Matrix.detMonoidHom : Matrix (Fin n) (Fin n) ℂ →* ℂ) := continuous_id.matrix_det
  have h1 : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ →* ℂˣ) :=
    Continuous.units_map _ h0
  exact Units.continuous_val.comp (h1.zpow c)

theorem continuous_coeff_sqAct {n : ℕ} (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) ℂ)
    (s : (Fin n × Fin n) →₀ ℕ) :
    Continuous fun g : GL (Fin n) ℂ => AddMonoidAlgebra.coeff (sqAct ℂ n lam g f) s := by
  simp only [sqAct, MvPolynomial.coeff_smul, smul_eq_mul]
  exact (continuous_detPow n _).mul
    ((continuous_coeff_rowAct f s).comp Units.continuous_val.matrix_transpose)

theorem exists_finset_factor {σ : Type} (W : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) : ∃ (S : Finset (σ →₀ ℕ)) (c : S → ℂ),
      ∀ p : W, φ p = ∑ s : S, c s * AddMonoidAlgebra.coeff p.1 s.1 := by
  let b := Module.finBasis ℂ W
  let S : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun i => (b i : MvPolynomial σ ℂ).support
  let L : W →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun p s => AddMonoidAlgebra.coeff p.1 s.1
      map_add' := fun p q => by funext s; simp
      map_smul' := fun a p => by funext s; simp }
  have hL : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun p hp => ?_
    apply Subtype.ext
    refine MvPolynomial.ext _ _ fun s => ?_
    by_cases hs : s ∈ S
    · simpa [L] using congrFun hp ⟨s, hs⟩
    · have h0 : ∀ i, AddMonoidAlgebra.coeff (b i : MvPolynomial σ ℂ) s = 0 := fun i => by
        by_contra h
        exact hs (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, MvPolynomial.mem_support_iff.2 h⟩)
      have hp' : (p : MvPolynomial σ ℂ) = ∑ i, b.repr p i • (b i : MvPolynomial σ ℂ) := by
        have h := congrArg Subtype.val (b.sum_repr p)
        rw [AddSubmonoidClass.coe_finsetSum] at h
        exact h.symm
      rw [hp']
      simp [MvPolynomial.coeff_sum, h0]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective L hL
  refine ⟨S, fun s => (φ ∘ₗ ψ) fun j => if s = j then 1 else 0, fun p => ?_⟩
  have e : φ p = (φ ∘ₗ ψ) (L p) := by
    have h := LinearMap.congr_fun hψ p
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h ⊢
    rw [h]
  rw [e, LinearMap.pi_apply_eq_sum_univ (φ ∘ₗ ψ) (L p)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_eq_mul, mul_comm]
  rfl

theorem continuous_sqRep_coeff {n : ℕ} (lam : DomWeight n) (f : nablaSq ℂ n lam)
    (φ : Module.Dual ℂ (nablaSq ℂ n lam)) :
    Continuous fun g : GL (Fin n) ℂ => φ (GlobalTheory.Branching.sqRep ℂ n lam g f) := by
  obtain ⟨S, c, h⟩ := exists_finset_factor (nablaSq ℂ n lam) φ
  simp only [h]
  exact continuous_finsetSum _ fun s _ => continuous_const.mul (continuous_coeff_sqAct lam f.1 s.1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.CompanionTheory.WInfCont
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnitary
noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker InnerProductSpace

namespace GlobalTheory.CompanionTheory.CxAvg

section Abstract

variable {K E : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  (μ : Measure K) [μ.IsHaarMeasure] (F : K →* (E →L[ℂ] E))

variable {F}

end Abstract

section Concrete

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC

variable {n : ℕ}

theorem Rm_unitary (lam : Fin n → ℤ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm lam k.1 = LinearMap.toMatrix (wb lam) (wb lam)
      (GlobalTheory.Branching.sqRep ℂ n (dw lam) (GlobalTheory.Branching.unitaryIncl n k)) := by
  have h : IsUnit k.1.det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
  have e : Matrix.nonsingInvUnit k.1 h = GlobalTheory.Branching.unitaryIncl n k := Units.ext rfl
  rw [Rm, dite_eq_left h, e]

theorem Rm_mul (lam : Fin n → ℤ) (k k' : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm lam (k * k').1 = Rm lam k.1 * Rm lam k'.1 := by
  rw [Rm_unitary, Rm_unitary, Rm_unitary, map_mul, map_mul, Module.End.mul_eq_comp]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : Matrix.unitaryGroup (Fin n) ℂ).1 = 1 := by
  rw [Rm_unitary, map_one, map_one]
  exact LinearMap.toMatrix_id _

theorem continuous_unitaryIncl : Continuous (GlobalTheory.Branching.unitaryIncl n) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

theorem continuous_Rm (lam : Fin n → ℤ) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rm lam k.1 := by
  simp only [Rm_unitary]
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  exact (GlobalTheory.CompanionTheory.WInfCont.continuous_sqRep_coeff (dw lam) (wb lam j) ((wb lam).coord i)).comp
    continuous_unitaryIncl

end Concrete

end GlobalTheory.CompanionTheory.CxAvg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableCoeffRowAct
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem differentiable_entry {r : ℕ} (a b : Fin r) :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M a b :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)).differentiable

theorem differentiable_det {r : ℕ} :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M.det := by
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum fun σ _ => Differentiable.const_mul ?_ _
  have h : ∀ t : Finset (Fin r), Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => ∏ i ∈ t, M (σ i) i := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (differentiable_entry (σ a) a).mul ih
  exact h Finset.univ

theorem differentiable_coeff_rowAct {r m : ℕ} (f : MvPolynomial (Fin r × Fin m) ℂ) :
    ∀ s : (Fin r × Fin m) →₀ ℕ, Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ =>
      AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ f) s := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro s
    simpa [MvPolynomial.algebraMap_eq] using
      (differentiable_const (AddMonoidAlgebra.coeff (MvPolynomial.C a : MvPolynomial (Fin r × Fin m) ℂ) s) :
        Differentiable ℂ fun _ : Matrix (Fin r) (Fin r) ℂ => _)
  | add p q hp hq =>
    intro s
    simp only [map_add (f := _), MvPolynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    have key : ∀ M : Matrix (Fin r) (Fin r) ℂ,
        AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (p * MvPolynomial.X v)) s =
        ∑ b : Fin r, M b v.1 * (if (b, v.2) ∈ s.support then
          AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ p) (s - Finsupp.single (b, v.2) 1) else 0) := by
      intro M
      have hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (MvPolynomial.X v) =
          ∑ b : Fin r, MvPolynomial.C (M b v.1) * MvPolynomial.X (b, v.2) := by
        simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
    simp only [key]
    refine Differentiable.fun_sum fun b _ => ?_
    refine (differentiable_entry b v.1).mul ?_
    split_ifs
    · exact hp _
    · exact differentiable_const _

theorem detPow_nonsingInvUnit {n : ℕ} {x : Mat n} (h : IsUnit x.det) (c : ℤ) :
    Formalism.BasicNotions.detPow ℂ n (Matrix.nonsingInvUnit x h) c = x.det ^ c := by
  have e : ((Matrix.GeneralLinearGroup.det (Matrix.nonsingInvUnit x h) : ℂˣ) : ℂ) = x.det := rfl
  rw [Formalism.BasicNotions.detPow, Units.val_zpow_eq_zpow_val, e]

theorem holRm (n : ℕ) (lam : Fin n → ℤ) : HolRm lam := by
  intro i j g hg
  obtain ⟨S, c, hc⟩ := GlobalTheory.CompanionTheory.WInfCont.exists_finset_factor (Formalism.BasicNotions.nablaSq ℂ n (dw lam)) ((wb lam).coord i)
  have hev : (fun x : Mat n => Rm lam x i j) =ᶠ[𝓝 g] fun x : Mat n =>
      ∑ s : S, c s * (x.det ^ (dw lam).detShift *
        AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) xᵀ (wb lam j).1) s.1) := by
    filter_upwards [isOpen_GLs.mem_nhds hg] with x hx
    have hu := isUnit_det_of_mem hx
    rw [Rm_of_unit lam hu, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hc]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [GlobalTheory.Branching.sqRep_coe, Formalism.BasicNotions.sqAct, MvPolynomial.coeff_smul, smul_eq_mul,
      detPow_nonsingInvUnit hu]
    rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  refine DifferentiableAt.fun_sum fun s _ => DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.mul ?_ (differentiable_coeff_rowAct _ _ _)
  exact (differentiable_det g).zpow (Or.inl hg)

end GlobalTheory.CompanionTheory.RmHol
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtMulVec
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)
open Formalism.BasicNotions Formalism.GradedWeylDivisibility

namespace GlobalTheory.CompanionTheory.RmHol.HW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hv (lam : Fin n → ℤ) : nablaSq ℂ n (dw lam) :=
  ⟨extremal ℂ n (dw lam), hwMem ℂ n n le_rfl _ (factNatW n (dw lam)).1⟩

theorem hv_ne (lam : Fin n → ℤ) : hv lam ≠ 0 := fun h =>
  hwNe ℂ n n le_rfl (dw lam).natW (congrArg Subtype.val h)

theorem dw_w {lam : Fin n → ℤ} (h : Antitone lam) (a : Fin n) : (dw lam).w a = lam a := by
  unfold dw
  rw [dite_eq_left h]

theorem Rm_mulVec (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) (v : nablaSq ℂ n (dw lam)) :
    Rm lam x *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
      ((wb lam).repr (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h) v) : Jd n lam → ℂ) := by
  rw [Rm_of_unit lam h]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

theorem hasDerivAt_mulVec {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (c : Jd n lam → ℂ)
    (i : Jd n lam) :
    HasDerivAt (fun t : ℂ => (Rm lam (1 + t • B) *ᵥ c) i) ((XA lam B *ᵥ c) i) 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_line hD B i j).mul_const _

theorem fix_upper (lam : Fin n → ℤ) {a b : Fin n} (hab : a < b) {t : ℂ}
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) = hv lam := by
  apply Subtype.ext
  refine (factSqHighestWeight ℂ n (dw lam)).2 _ ?_ ?_
  · intro i j hij
    have hij' : j < i := hij
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i j = 0
    have h1 : (1 : Mat n) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij')
    have h2 : Matrix.single a b (1 : ℂ) i j = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (not_lt.2 hij'.le)
    rw [Matrix.add_apply, Matrix.smul_apply, h1, h2]
    simp
  · intro i
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i i = 1
    have h2 : Matrix.single a b (1 : ℂ) i i = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, h⟩
      exact hab.ne' h
    rw [Matrix.add_apply, Matrix.smul_apply, h2]
    simp

theorem diag_act {lam : Fin n → ℤ} (hA : Antitone lam) (a : Fin n) {t : ℂ} (ht : 1 + t ≠ 0)
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) =
      ((1 + t) ^ (lam a)) • hv lam := by
  classical
  let u : Fin n → ℂˣ := fun i => if i = a then Units.mk0 (1 + t) ht else 1
  have e : Matrix.nonsingInvUnit _ h = diagGL ℂ n u := by
    apply Units.ext
    ext i j
    show ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)) i j = Matrix.diagonal (fun k => (u k : ℂ)) i j
    by_cases hij : i = j
    · subst hij
      by_cases hia : i = a
      · subst hia; simp [u]
      · have h2 : Matrix.single a a (1 : ℂ) i i = 0 := by
          rw [Matrix.single_apply_of_ne]
          rintro ⟨h, -⟩
          exact hia h.symm
        rw [Matrix.add_apply, Matrix.smul_apply, h2]
        simp [u, hia]
    · have h2 : Matrix.single a a (1 : ℂ) i j = 0 := by
        rw [Matrix.single_apply_of_ne]
        rintro ⟨h, h'⟩
        exact hij (h.symm.trans h')
      rw [Matrix.add_apply, Matrix.smul_apply, h2, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
      simp
  have hp : ((∏ i, (u i) ^ ((dw lam).w i) : ℂˣ) : ℂ) = (1 + t) ^ (lam a) := by
    rw [Finset.prod_eq_single a]
    · simp [u, dw_w hA]
    · intro b _ hb
      simp [u, hb]
    · simp
  rw [e]
  apply Subtype.ext
  have hh := (factSqHighestWeight ℂ n (dw lam)).1 u
  rw [hp] at hh
  exact hh

theorem exists_hw (n : ℕ) (lam : Fin n → ℤ) (hD : HolRm lam) (hA : Antitone lam) :
    ∃ v : Formalism.BasicNotions.nablaSq ℂ n (dw lam), v ≠ 0 ∧
      (∀ a b : Fin n, a < b → Xu lam a b *ᵥ ((wb lam).repr v : Jd n lam → ℂ) = 0) ∧
      ∀ a : Fin n, Xu lam a a *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
        (lam a : ℂ) • ((wb lam).repr v : Jd n lam → ℂ) := by
  refine ⟨hv lam, hv_ne lam, fun a b hab => ?_, fun a => ?_⟩
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a b (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a b (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun _ => ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a b (1 : ℂ))] with t ht
      rw [Rm_mulVec lam ht, fix_upper lam hab ht]
    have h2 := (hasDerivAt_const (0 : ℂ) (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a a (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hne : ∀ᶠ t : ℂ in 𝓝 0, 1 + t ≠ 0 := by
      have hc : ContinuousAt (fun t : ℂ => 1 + t) 0 := by fun_prop
      exact hc.eventually_ne (by simp)
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a a (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun t => (1 + t) ^ (lam a) * ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a a (1 : ℂ)), hne] with t ht ht'
      rw [Rm_mulVec lam ht, diag_act hA a ht' ht]
      simp
    have hz : HasDerivAt (fun t : ℂ => (1 + t) ^ (lam a)) (lam a : ℂ) 0 := by
      have h0 := hasDerivAt_zpow (lam a) ((1 : ℂ) + 0) (Or.inl (by simp))
      have h3 := h0.comp_const_add 1 0
      have e : (lam a : ℂ) * ((1 : ℂ) + 0) ^ (lam a - 1) = lam a := by simp
      rw [e] at h3
      exact h3
    have h2 := (hz.mul_const (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2

end GlobalTheory.CompanionTheory.RmHol.HW
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineInverse
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem line_inverse {e : Mat n} {δ t s : ℂ} (he : e * e = δ • e) (hs : s * (1 + t * δ) = t) :
    (1 + t • e) * (1 - s • e) = 1 ∧ (1 - s • e) * (1 + t • e) = 1 := by
  have key : t - s - t * s * δ = 0 := by linear_combination -hs
  have key' : t - s - s * t * δ = 0 := by linear_combination -hs
  constructor
  · calc (1 + t • e) * (1 - s • e) = 1 + (t - s - t * s * δ) • e := by
          simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, he, smul_smul, sub_smul]
          abel
      _ = 1 := by rw [key, zero_smul, add_zero]
  · calc (1 - s • e) * (1 + t • e) = 1 + (t - s - s * t * δ) • e := by
          simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, he, smul_smul, sub_smul]
          abel
      _ = 1 := by rw [key', zero_smul, add_zero]

theorem conj_line {lam : Fin n → ℤ} (hD : HolRm lam) {e : Mat n} (B : Mat n) {δ : ℂ} (he : e * e = δ • e) :
    ∀ᶠ t : ℂ in 𝓝 0, Rm lam (1 + t • e) * XA lam B =
      (XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) * Rm lam (1 + t • e) := by
  have hc : ContinuousAt (fun t : ℂ => 1 + t * δ) 0 := by fun_prop
  have hδ : ∀ᶠ t : ℂ in 𝓝 0, 1 + t * δ ≠ 0 := hc.eventually_ne (by simp)
  filter_upwards [eventually_line_unit e, hδ] with t hu hne
  have hs : t / (1 + t * δ) * (1 + t * δ) = t := div_mul_cancel₀ t hne
  obtain ⟨-, hyx⟩ := line_inverse he hs
  have hB' : (1 + t • e) * B * (1 - (t / (1 + t * δ)) • e) =
      B + t • (e * B) + (-(t / (1 + t * δ))) • (B * e) + (-(t * (t / (1 + t * δ)))) • (e * B * e) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      mul_assoc]
    module
  have hcomm : (1 + t • e) * B = ((1 + t • e) * B * (1 - (t / (1 + t * δ)) • e)) * (1 + t • e) := by
    rw [mul_assoc ((1 + t • e) * B), hyx, mul_one]
  rw [conj_XA hD hu hcomm, hB', XA_add, XA_add, XA_add, XA_smul, XA_smul, XA_smul]

theorem comm_XA {lam : Fin n → ℤ} (hD : HolRm lam) {e : Mat n} (B : Mat n) {δ : ℂ} (he : e * e = δ • e) :
    XA lam e * XA lam B - XA lam B * XA lam e = XA lam (e * B) - XA lam (B * e) := by
  have hden : HasDerivAt (fun t : ℂ => 1 + t * δ) δ 0 := by
    simpa using ((hasDerivAt_id' (0:ℂ)).mul_const δ).const_add 1
  have hs : HasDerivAt (fun t : ℂ => t / (1 + t * δ)) 1 0 := by
    have h := (hasDerivAt_id' (0:ℂ)).div hden (by simp)
    refine h.congr_deriv ?_
    simp
  have hts : HasDerivAt (fun t : ℂ => t * (t / (1 + t * δ))) 0 0 := by
    have h := (hasDerivAt_id' (0:ℂ)).mul hs
    refine h.congr_deriv ?_
    simp
  have hprod : ∀ (P Q : ℂ → Matrix (Jd n lam) (Jd n lam) ℂ) (P' Q' : Matrix (Jd n lam) (Jd n lam) ℂ),
      (∀ i k, HasDerivAt (fun t => P t i k) (P' i k) 0) → (∀ k j, HasDerivAt (fun t => Q t k j) (Q' k j) 0) →
      ∀ i j, HasDerivAt (fun t => (P t * Q t) i j) ((P' * Q 0 + P 0 * Q') i j) 0 := by
    intro P Q P' Q' hP hQ i j
    simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun k _ => (hP i k).mul (hQ k j)
  have hR : ∀ i k, HasDerivAt (fun t : ℂ => Rm lam (1 + t • e) i k) (XA lam e i k) 0 :=
    hasDerivAt_line hD e
  have hC : ∀ k j, HasDerivAt (fun _ : ℂ => XA lam B k j)
      ((0 : Matrix (Jd n lam) (Jd n lam) ℂ) k j) 0 := fun k j => by
    simpa using hasDerivAt_const (0:ℂ) (XA lam B k j)
  have hG : ∀ i k, HasDerivAt (fun t : ℂ => (XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) i k) ((XA lam (e * B) - XA lam (B * e)) i k) 0 := by
    intro i k
    have h := ((((hasDerivAt_id' (0:ℂ)).mul_const (XA lam (e * B) i k)).const_add (XA lam B i k)).add
      (hs.neg.mul_const (XA lam (B * e) i k))).add (hts.neg.mul_const (XA lam (e * B * e) i k))
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
    exact h.congr_deriv (by ring)
  ext i j
  have hL := hprod (fun t => Rm lam (1 + t • e)) (fun _ => XA lam B) (XA lam e) 0 hR hC i j
  have hRt := hprod (fun t : ℂ => XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) (fun t => Rm lam (1 + t • e))
      (XA lam (e * B) - XA lam (B * e)) (XA lam e) hG hR i j
  have heq : (fun t : ℂ => (Rm lam (1 + t • e) * XA lam B) i j) =ᶠ[𝓝 0]
      (fun t : ℂ => ((XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) * Rm lam (1 + t • e)) i j) := by
    filter_upwards [conj_line hD B he] with t ht
    exact congrArg (fun M => M i j) ht
  have huniq := hL.unique (hRt.congr_of_eventuallyEq heq)
  simp only [zero_smul, add_zero, Rm_one, mul_zero, mul_one, zero_div, neg_zero, zero_mul] at huniq
  rw [Matrix.sub_apply, huniq, Matrix.add_apply]
  ring

theorem XA_zero (lam : Fin n → ℤ) : XA lam (0 : Mat n) = 0 := by
  simpa using XA_smul lam (0 : ℂ) (0 : Mat n)

theorem xu_glRel : ∀ (n : ℕ) (lam : Fin n → ℤ), HolRm lam → Formalism.HadamardInequality.GlRel (Xu lam) := by
  intro n lam hD a b c d
  have hsq : (Matrix.single a b (1:ℂ) : Mat n) * Matrix.single a b 1 =
      (if b = a then (1:ℂ) else 0) • Matrix.single a b 1 := by
    by_cases h : b = a
    · subst h; rw [if_pos rfl, one_smul, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, zero_smul, Matrix.single_mul_single_of_ne _ _ _ _ h]
  have key := comm_XA hD (Matrix.single c d (1:ℂ)) hsq
  have hEB : XA lam ((Matrix.single a b (1:ℂ) : Mat n) * Matrix.single c d 1) =
      if b = c then XA lam (Matrix.single a d 1) else 0 := by
    by_cases h : b = c
    · subst h; rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, Matrix.single_mul_single_of_ne _ _ _ _ h, XA_zero]
  have hBE : XA lam ((Matrix.single c d (1:ℂ) : Mat n) * Matrix.single a b 1) =
      if d = a then XA lam (Matrix.single c b 1) else 0 := by
    by_cases h : d = a
    · subst h; rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, Matrix.single_mul_single_of_ne _ _ _ _ h, XA_zero]
  simp only [Xu]
  rw [key, hEB, hBE]

end GlobalTheory.CompanionTheory.RmHol
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInfinitesimalCharacter
noncomputable section

open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.GelfAct

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Mat n) (a b : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) a b) (X a b) 0 := by
  have hsmul (t : ℝ) : (t : ℂ) • X = t • X := by ext; simp
  simp only [hsmul]
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let entry : Mat n →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  exact entry.hasFDerivAt.comp_hasDerivAt 0 h

end GlobalTheory.CompanionTheory.GelfAct

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightHermitianDerivation
noncomputable section

open Matrix Finset Filter Topology
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmModel

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem rm_unitary_apply (ν : Fin n → ℤ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm ν k.1 = LinearMap.toMatrix (wb ν) (wb ν)
      (GlobalTheory.Branching.sqRep ℂ n (dw ν) (GlobalTheory.Branching.unitaryIncl n k)) := by
  have h : IsUnit k.1.det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
  have e : Matrix.nonsingInvUnit k.1 h = GlobalTheory.Branching.unitaryIncl n k := Units.ext rfl
  rw [Rm, dite_eq_left h, e]

private theorem rm_unitary_mul (ν : Fin n → ℤ) (a b : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm ν (a * b).1 = Rm ν a.1 * Rm ν b.1 := by
  rw [rm_unitary_apply, rm_unitary_apply, rm_unitary_apply, map_mul, map_mul, Module.End.mul_eq_comp]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem exists_frame (ν : Fin n → ℤ) :
    ∃ (d : ℕ) (e : (Jd n ν → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d)),
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : Jd n ν → ℂ),
        ⟪e (Rm ν k.1 *ᵥ x), e (Rm ν k.1 *ᵥ y)⟫_ℂ = ⟪e x, e y⟫_ℂ := by
  let ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (Jd n ν → ℂ) :=
    { toFun := fun k => Matrix.mulVecLin (Rm ν k.1)
      map_one' := by
        show Matrix.mulVecLin (Rm ν (1 : Mat n)) = 1
        rw [GlobalTheory.CompanionTheory.RmHol.Rm_one, Matrix.mulVecLin_one]
        rfl
      map_mul' := fun a b => by
        show Matrix.mulVecLin (Rm ν (a * b).1) = _
        rw [rm_unitary_mul, Matrix.mulVecLin_mul]
        rfl }
  have hcont : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rm ν k.1 := by
    simp only [rm_unitary_apply]
    refine continuous_matrix fun i j => ?_
    simp only [LinearMap.toMatrix_apply]
    exact (GlobalTheory.CompanionTheory.WInfCont.continuous_sqRep_coeff (dw ν) (wb ν j) ((wb ν).coord i)).comp
      GlobalTheory.CompanionTheory.CxAvg.continuous_unitaryIncl
  have hρc : ∀ v, Continuous fun k => ρ k v := fun v =>
    hcont.matrix_mulVec continuous_const
  obtain ⟨c, hc⟩ := GlobalTheory.exists_invariant_core ρ hρc
  obtain ⟨d, τ, e, hτ, he⟩ := GlobalTheory.ThetaCplV.UnitaryTrick.exists_isURep_of_core ρ
    (fun φ v => (LinearMap.continuous_of_finiteDimensional φ).comp (hρc v)) c hc
  refine ⟨d, e, fun k x y => ?_⟩
  have h1 : ∀ z, e (Rm ν k.1 *ᵥ z) = τ k (e z) := fun z => he k z
  rw [h1, h1]
  exact (LinearIsometry.mk (τ k).toLinearMap (hτ.2.2.1 k)).inner_map_map _ _

theorem hasDerivAt_Rm (ν : Fin n → ℤ) (X : Mat n) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) (c : Jd n ν → ℂ) :
    HasDerivAt (fun t : ℝ => Rm ν (γ t).1 *ᵥ c) (XA ν X *ᵥ c) 0 := by
  have hp : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
    refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
    exact GlobalTheory.CompanionTheory.GelfAct.hasDerivAt_exp_entry X a b
  have hentry : ∀ i j, HasDerivAt (fun t : ℝ => Rm ν (NormedSpace.exp ((t : ℂ) • X)) i j) (XA ν X i j) 0 := by
    intro i j
    have h1 := (holRm n ν i j 1 one_mem_GLs).hasFDerivAt.restrictScalars ℝ
    have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
    exact h1.comp_hasDerivAt_of_eq (0 : ℝ) hp h0.symm
  simp only [hγ]
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hentry i j).mul_const _

theorem XA_eq_sum (ν : Fin n → ℤ) (X : Mat n) : XA ν X = ∑ a, ∑ b, X a b • Xu ν a b := by
  have h : XA ν X = XA ν (∑ a, ∑ b, Matrix.single a b (X a b)) := congrArg (XA ν) (Matrix.matrix_eq_sum_single X)
  rw [h, XA_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [XA_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h2 : (Matrix.single a b (X a b) : Mat n) = X a b • Matrix.single a b (1 : ℂ) := by simp
  rw [h2, XA_smul]
  rfl

theorem strict_kill (ν : Fin n → ℤ) (c : Jd n ν → ℂ) (hc : ∀ a b, a < b → Xu ν a b *ᵥ c = 0) (B : Mat n)
    (hB : ∀ i j, j ≤ i → B i j = 0) : XA ν B *ᵥ c = 0 := by
  rw [XA_eq_sum]
  have h : (∑ a, ∑ b, B a b • Xu ν a b) *ᵥ c = ∑ a, ∑ b, B a b • (Xu ν a b *ᵥ c) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← Matrix.toLin'_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  rw [h]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rcases lt_or_ge a b with h | h
  · rw [hc a b h, smul_zero]
  · rw [hB a b h, zero_smul]

theorem fix_of_killed (ν : Fin n → ℤ) (c : Jd n ν → ℂ) (hc : ∀ a b, a < b → Xu ν a b *ᵥ c = 0) (g : Mat n)
    (h1 : ∀ i j, j < i → g i j = 0) (h2 : ∀ i, g i i = 1) : Rm ν g *ᵥ c = c := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Mat n, N = g - 1 := ⟨_, rfl⟩
  have hNs : ∀ i j, j ≤ i → N i j = 0 := by
    intro i j hji
    rcases hji.eq_or_lt with rfl | h
    · simp [hN, h2]
    · simp [hN, h1 i j h, Matrix.one_apply_ne h.ne']
  let G : ℂ → Mat n := fun t => 1 + t • N
  have hGt : ∀ t, (G t).BlockTriangular id := fun t i j hij => by
    have hij' : j < i := hij
    simp [G, Matrix.one_apply_ne hij'.ne', hNs i j hij'.le]
  have hGd : ∀ t, (G t).det = 1 := by
    intro t
    rw [Matrix.det_of_isUpperTriangular (hGt t)]
    simp [G, hNs _ _ le_rfl]
  have hGu : ∀ t, IsUnit (G t).det := fun t => by rw [hGd]; exact isUnit_one
  have hGm : ∀ t, G t ∈ GLs n := fun t => mem_GLs_of_isUnit (hGu t)
  have hinv : ∀ t i j, j < i → (G t)⁻¹ i j = 0 := by
    intro t i j hij
    haveI := Matrix.invertibleOfIsUnitDet (G t) (hGu t)
    exact Matrix.blockTriangular_inv_of_blockTriangular (hGt t) hij
  let B : ℂ → Mat n := fun t => (G t)⁻¹ * N
  have hB : ∀ t i j, j ≤ i → B t i j = 0 := by
    intro t i j hji
    simp only [B, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hinv t i k h, zero_mul]
    · rw [hNs k j (hji.trans h), mul_zero]
  have hGB : ∀ t, G t * B t = N := fun t => by
    simp only [B]
    rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hGu t), one_mul]
  have hline : ∀ t, HasDerivAt G N t := fun t => by
    have h := ((hasDerivAt_id t).smul_const N).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have hdi : ∀ i t, HasDerivAt (fun s => (Rm ν (G s) *ᵥ c) i) 0 t := by
    intro i t
    have hij : ∀ j, HasDerivAt (fun s => Rm ν (G s) i j) ((Rm ν (G t) * XA ν (B t)) i j) t := by
      intro j
      have h0 := (holRm n ν i j (G t) (hGm t)).hasFDerivAt.comp_hasDerivAt t (hline t)
      rw [← fderiv_Rm (holRm n ν) (hGm t) (B t) i j, hGB]
      exact h0
    have hs : HasDerivAt (fun s => (Rm ν (G s) *ᵥ c) i) (∑ j, (Rm ν (G t) * XA ν (B t)) i j * c j) t := by
      simp only [Matrix.mulVec, dotProduct]
      exact HasDerivAt.fun_sum fun j _ => (hij j).mul_const _
    have hz : ∑ j, (Rm ν (G t) * XA ν (B t)) i j * c j = 0 := by
      have h3 : (Rm ν (G t) * XA ν (B t)) *ᵥ c = 0 := by
        rw [← Matrix.mulVec_mulVec, strict_kill ν c hc (B t) (hB t), Matrix.mulVec_zero]
      simpa [Matrix.mulVec, dotProduct] using congrFun h3 i
    rwa [hz] at hs
  funext i
  have h3 := is_const_of_deriv_eq_zero (fun t => (hdi i t).differentiableAt) (fun t => (hdi i t).deriv) 1 0
  have e1 : G 1 = g := by simp [G, hN]
  have e0 : G 0 = 1 := by simp [G]
  simp only [e1, e0, GlobalTheory.CompanionTheory.RmHol.Rm_one, Matrix.one_mulVec] at h3
  exact h3

theorem line_of_killed (ν : Fin n → ℤ) (c : Jd n ν → ℂ) (hc : ∀ a b, a < b → Xu ν a b *ᵥ c = 0) :
    ∃ s : ℂ, c = s • ((wb ν).repr (HW.hv ν) : Jd n ν → ℂ) := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, ((wb ν).repr u : Jd n ν → ℂ) = c :=
    ⟨(wb ν).equivFun.symm c, by
      have h := (wb ν).equivFun.apply_symm_apply c
      rw [Module.Basis.equivFun_apply] at h
      exact h⟩
  have hfix : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      Formalism.BasicNotions.sqAct ℂ n (dw ν) g u.1 = u.1 := by
    intro g h1 h2
    have hdet : IsUnit (g.1).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    have e := HW.Rm_mulVec ν hdet u
    have e1 : Matrix.nonsingInvUnit g.1 hdet = g := Units.ext rfl
    rw [e1, hu, fix_of_killed ν c hc g.1 h1 h2] at e
    have e2 : (wb ν).repr (GlobalTheory.Branching.sqRep ℂ n (dw ν) g u) = (wb ν).repr u :=
      DFunLike.coe_injective (e.symm.trans hu.symm)
    exact congrArg Subtype.val ((wb ν).repr.injective e2)
  obtain ⟨s, hs⟩ := (highest_weight_irreducible n (dw ν)).2.2 u.1 u.2 hfix
  refine ⟨s, ?_⟩
  have h3 : u = s • HW.hv ν := Subtype.ext hs
  rw [← hu, h3, map_smul]
  rfl

section Frame

variable {ν : Fin n → ℤ} {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
  (e : (Jd n ν → ℂ) ≃ₗ[ℂ] L)

def frameL : Matrix (Jd n ν) (Jd n ν) ℂ →ₗ[ℂ] Module.End ℂ L :=
  e.conj.toLinearMap ∘ₗ (Matrix.toLin' : _ ≃ₗ[ℂ] _).toLinearMap

theorem frameL_apply (A : Matrix (Jd n ν) (Jd n ν) ℂ) (x : Jd n ν → ℂ) : frameL e A (e x) = e (A *ᵥ x) := by
  simp [frameL, LinearEquiv.conj_apply]

theorem frameL_one : frameL e 1 = 1 := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨x, rfl⟩ := e.surjective w
  simp [frameL_apply]

theorem frameL_mul (A B : Matrix (Jd n ν) (Jd n ν) ℂ) : frameL e (A * B) = frameL e A * frameL e B := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨x, rfl⟩ := e.surjective w
  simp [frameL_apply]

theorem frameL_XA (X : Mat n) (w : L) :
    ∑ a, ∑ b, X a b • frameL e (Xu ν a b) w = frameL e (XA ν X) w := by
  rw [XA_eq_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem glRel_frame : Formalism.REAL.GlRel fun a b => frameL e (Xu ν a b) := by
  intro a b c d
  have h := congrArg (frameL e) (xu_glRel n ν (holRm n ν) a b c d)
  rw [map_sub, map_sub, frameL_mul, frameL_mul] at h
  rw [h]
  split_ifs <;> simp

theorem deriv_frame (X : Mat n) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) (x : Jd n ν → ℂ) :
    HasDerivAt (fun t : ℝ => e (Rm ν (γ t).1 *ᵥ x)) (e (XA ν X *ᵥ x)) 0 := by
  let E : (Jd n ν → ℂ) →L[ℂ] L := e.toLinearMap.toContinuousLinearMap
  exact (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_Rm ν X γ hγ x)

variable (he : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : Jd n ν → ℂ),
  ⟪e (Rm ν k.1 *ᵥ x), e (Rm ν k.1 *ᵥ y)⟫_ℂ = ⟪e x, e y⟫_ℂ)


include he in
theorem skew_frame (X : Mat n) (hX : Xᴴ = -X) (x y : Jd n ν → ℂ) :
    ⟪e (XA ν X *ᵥ x), e y⟫_ℂ + ⟪e x, e (XA ν X *ᵥ y)⟫_ℂ = 0 := by
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := GlobalTheory.CompanionTheory.RealCount.InjHw.expU X hX
  have hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) := fun _ => rfl
  have h0 : (γ 0).1 = 1 := by simp [hγ]
  have d3 := (deriv_frame e X γ hγ x).inner ℂ (deriv_frame e X γ hγ y)
  have hc : (fun t : ℝ => ⟪e (Rm ν (γ t).1 *ᵥ x), e (Rm ν (γ t).1 *ᵥ y)⟫_ℂ) = fun _ => ⟪e x, e y⟫_ℂ :=
    funext fun t => he _ x y
  rw [hc] at d3
  have h := d3.unique (hasDerivAt_const _ _)
  rw [h0, GlobalTheory.CompanionTheory.RmHol.Rm_one, Matrix.one_mulVec, Matrix.one_mulVec] at h
  rw [add_comm]
  exact h

include he in
theorem herm_frame (a b : Fin n) (x y : Jd n ν → ℂ) :
    ⟪e (Xu ν a b *ᵥ x), e y⟫_ℂ = ⟪e x, e (Xu ν b a *ᵥ y)⟫_ℂ := by
  have s1 : (Matrix.single a b (1 : ℂ) + (-1 : ℂ) • Matrix.single b a (1 : ℂ) : Mat n)ᴴ =
      -(Matrix.single a b (1 : ℂ) + (-1 : ℂ) • Matrix.single b a (1 : ℂ)) := by
    rw [conjTranspose_add, conjTranspose_smul, InjHw.single_conjT, InjHw.single_conjT]
    simp [add_comm]
  have s2 : (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a (1 : ℂ)) : Mat n)ᴴ =
      -(Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a (1 : ℂ))) := by
    rw [conjTranspose_smul, conjTranspose_add, InjHw.single_conjT, InjHw.single_conjT]
    simp [add_comm]
  have h1 := skew_frame e he _ s1 x y
  have h2 := skew_frame e he _ s2 x y
  unfold Xu
  simp only [XA_add, XA_smul, Matrix.add_mulVec, Matrix.smul_mulVec, map_add (f := _), map_smul,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right] at h1 h2
  simp only [map_neg, map_one, Complex.conj_I] at h1 h2
  generalize ⟪e (XA ν (Matrix.single a b 1) *ᵥ x), e y⟫_ℂ = p at h1 h2 ⊢
  generalize ⟪e (XA ν (Matrix.single b a 1) *ᵥ x), e y⟫_ℂ = q at h1 h2
  generalize ⟪e x, e (XA ν (Matrix.single a b 1) *ᵥ y)⟫_ℂ = r at h1 h2
  generalize ⟪e x, e (XA ν (Matrix.single b a 1) *ᵥ y)⟫_ℂ = s at h1 h2 ⊢
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 + (1 / 2 : ℂ) * (p + q - r - s) * Complex.I_sq


include he in
theorem frame_model (hν : Antitone ν) :
    ∃ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L)) (K : Fin n → Fin n → Module.End ℂ L) (v : L),
      Formalism.REAL.GlRel K ∧ (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧ IsDerivK σ K ∧ v ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧
        (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ L (σ k) = weylChar ν z := by
  obtain ⟨v0, hv0, hup, hwt⟩ := HW.exists_hw n ν (holRm n ν) hν
  generalize hc : ((wb ν).repr v0 : Jd n ν → ℂ) = c0 at hup hwt
  have hc0 : c0 ≠ 0 := fun h => hv0 ((wb ν).repr.map_eq_zero_iff.1 (DFunLike.coe_injective (hc.trans h)))
  let σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L) :=
    { toFun := fun k => frameL e (Rm ν k.1)
      map_one' := by
        show frameL e (Rm ν (1 : Mat n)) = 1
        rw [GlobalTheory.CompanionTheory.RmHol.Rm_one, frameL_one]
      map_mul' := fun a b => by
        show frameL e (Rm ν (a * b).1) = _
        rw [rm_unitary_mul, frameL_mul] }
  have hσ : ∀ k x, σ k (e x) = e (Rm ν k.1 *ᵥ x) := fun k x => frameL_apply e _ x
  refine ⟨σ, fun a b => frameL e (Xu ν a b), e c0, glRel_frame e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    show ⟪frameL e (Xu ν a b) (e x), e y⟫_ℂ = ⟪e x, frameL e (Xu ν b a) (e y)⟫_ℂ
    rw [frameL_apply, frameL_apply]
    exact herm_frame e he a b x y
  · refine ⟨fun k x y => ?_, fun w => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ => Submodule.mem_top,
      fun _ _ _ _ => Submodule.mem_top, fun X γ hγ w' _ => ?_⟩⟩
    · obtain ⟨x, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [hσ, hσ]
      exact he k x y
    · obtain ⟨x, rfl⟩ := e.surjective w'
      have h := deriv_frame e X γ hγ x
      have e1 : (∑ a, ∑ b, X a b • frameL e (Xu ν a b) (e x)) = e (XA ν X *ᵥ x) := by
        rw [frameL_XA, frameL_apply]
      show HasDerivAt (fun t : ℝ => σ (γ t) (e x)) (∑ a, ∑ b, X a b • frameL e (Xu ν a b) (e x)) 0
      rw [e1]
      simpa only [hσ] using h
  · exact e.map_ne_zero_iff.2 hc0
  · refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · show frameL e (Xu ν a a) (e c0) = ((wtR ν a : ℝ) : ℂ) • e c0
      rw [frameL_apply, hwt a, map_smul]
      simp [wtR]
    · show frameL e (Xu ν a b) (e c0) = 0
      rw [frameL_apply, hup a b hab, map_zero]
  · intro w hw
    obtain ⟨x, rfl⟩ := e.surjective w
    have hx : ∀ a b, a < b → Xu ν a b *ᵥ x = 0 := fun a b hab =>
      e.map_eq_zero_iff.1 (by rw [← frameL_apply]; exact hw a b hab)
    obtain ⟨s, hs⟩ := line_of_killed ν x hx
    obtain ⟨s0, hs0⟩ := line_of_killed ν c0 hup
    have hs00 : s0 ≠ 0 := by
      rintro rfl
      exact hc0 (by simpa using hs0)
    refine ⟨s / s0, ?_⟩
    have hxc : x = (s / s0) • c0 := by
      rw [hs]
      conv_rhs => rw [hs0]
      rw [smul_smul, div_mul_cancel₀ _ hs00]
    rw [hxc, map_smul]
  · intro k z hk hz
    have hu : IsUnit (k.1).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
    have h0 : ∀ a, z a ≠ 0 := by
      rw [hk, Matrix.det_diagonal] at hu
      exact fun a => (Finset.prod_ne_zero_iff.1 hu.ne_zero) a (Finset.mem_univ a)
    show LinearMap.trace ℂ L (frameL e (Rm ν k.1)) = _
    have h1 : frameL e (Rm ν k.1) = e.conj (Matrix.toLin' (Rm ν k.1)) := rfl
    rw [h1, LinearMap.trace_conj', Matrix.trace_toLin'_eq, hk]
    exact GlobalTheory.CompanionTheory.RmCharacter.rmChar n ν hν z h0 hz

end Frame

theorem rmModel : ∀ {n : ℕ} (ν : Fin n → ℤ), Antitone ν → ∃ (L : Type) (_ : NormedAddCommGroup L)
    (_ : InnerProductSpace ℂ L) (_ : FiniteDimensional ℂ L) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L))
    (K : Fin n → Fin n → Module.End ℂ L) (v : L), Formalism.REAL.GlRel K ∧
      (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧ IsDerivK σ K ∧ v ≠ 0 ∧
      Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧
      (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
        LinearMap.trace ℂ L (σ k) = weylChar ν z := by
  intro n ν hν
  obtain ⟨d, e, he⟩ := exists_frame ν
  exact ⟨EuclideanSpace ℂ (Fin d), inferInstance, inferInstance, inferInstance, frame_model e he hν⟩

end GlobalTheory.CompanionTheory.RmModel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightHermitianDerivationStatement
open Matrix
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem GlobalTheory.T.exists_highest_weight_hermitian_derivation :
    ∀ {n : ℕ} (ν : Fin n → ℤ), Antitone ν →
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L)
      (_ : FiniteDimensional ℂ L) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L))
      (K : Fin n → Fin n → Module.End ℂ L) (v : L),
      Formalism.REAL.GlRel K ∧ (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧
      IsDerivK σ K ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧
      (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ),
        k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ L (σ k) = weylChar ν z :=
  @GlobalTheory.CompanionTheory.RmModel.rmModel
end
