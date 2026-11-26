module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PEvalBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDomInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PHalfTerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPSupp
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.RGrowthJ
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EllFormula2J

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTrFin
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem trFin_pf : TrFin := by
  intro V B _ _ _ L w e h
  classical
  have hr : ∀ r : LinearMap.range L, (r : V) = ∑ b, e b (r : V) • w b := by
    rintro ⟨_, v, rfl⟩
    exact h v
  let A : LinearMap.range L →ₗ[ℂ] (B → ℂ) :=
    LinearMap.pi fun b => (e b).comp (LinearMap.range L).subtype
  let c : (B → ℂ) →ₗ[ℂ] LinearMap.range L :=
    L.rangeRestrict.comp (Fintype.linearCombination ℂ w)
  have hA : Function.Injective A := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr0
    apply Subtype.ext
    rw [hr r]
    have hz : ∀ b, e b (r : V) = 0 := fun b => congrFun hr0 b
    simp [hz]
  haveI : FiniteDimensional ℂ (LinearMap.range L) := FiniteDimensional.of_injective A hA
  have hL : (L.restrict fun x _ => LinearMap.mem_range_self L x) = c ∘ₗ A := by
    ext r
    have h1 : (c (A r) : V) = L (∑ b, e b (r : V) • w b) := by
      simp [c, A, Fintype.linearCombination_apply]
    rw [LinearMap.comp_apply, h1, ← hr r]
    rfl
  rw [hL, LinearMap.trace_comp_comm', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ B)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [c, A, Fintype.linearCombination_apply, Pi.single_apply, ite_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.WeakPf
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ctx_fub (X : Ctx) (φ : X.G → ℂ) (hφ : Tst φ) (g f : X.G → ℂ) (hg : MemLp g 2 X.ν) (hf : MemLp f 2 X.ν) :
    Integrable (fun y => (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y) X.ν ∧
      Integrable (fun z => g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν) X.ν ∧
      ∫ y, (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y ∂X.ν = ∫ z, g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν ∂X.ν := by
  obtain ⟨A, hA, h1, h2⟩ := rowInt X φ hφ
  have hm : Measurable (Function.uncurry (ker X.Γ φ)) := (kerBasic X φ hφ).2.1.measurable
  have hν : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hP := schurInt X.G X.ν (ker X.Γ φ) A hm hA h1 h2 g f hg hf
  have e1 : ∀ y, ∫ z, g z * ker X.Γ φ z y * f y ∂X.ν = (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y :=
    fun y => integral_mul_const _ _
  have e2 : ∀ z, ∫ y, g z * ker X.Γ φ z y * f y ∂X.ν = g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν := fun z => by
    simp_rw [mul_assoc]; exact integral_const_mul _ _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e1] using hP.integral_prod_right
  · simpa only [e2] using hP.integral_prod_left
  · simp_rw [← e1, ← e2]
    exact (integral_integral_swap (f := fun z y => g z * ker X.Γ φ z y * f y) hP).symm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.weak_pf :
    Weak := by
  intro E _ _ _ n ι _ s v u i
  have hth : ∀ y : H E n 0, th (th y) = y := fun y =>
    Prod.ext (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _) (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _)
  let c : ι → ℂ := fun l => s.M l i
  let g : ι → H E n 0 → ℂ := fun j z => starRingEnd ℂ ((u j : H E n 0 → ℂ) z)
  have hg : ∀ j, MemLp (g j) 2 s.D.ν := fun j => (Lp.memLp (u j)).star
  have F : ∀ j l, Integrable (fun y => (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) s.D.ν ∧
      Integrable (fun z => g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) s.D.ν ∧
      ∫ y, (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y ∂s.D.ν =
        ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := fun j l =>
    ctx_fub (ctx ratProper_holds s.D) (s.Φ₂ j l) (s.t₂ j l) (g j) v (hg j) (Lp.memLp v)
  have hrep : ∀ y, (v : H E n 0 → ℂ) y * inner ℂ u (s.k₂ (th y) i) =
      ∑ j, ∑ l, c l * ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) := by
    intro y
    rw [s.vecs.rep₂ (th y) i u, hth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const]
    ring
  have hv : ∀ (l : ι) (φ : H E n 0 → ℂ), ∫ y, φ y * ((vecM v c l : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) y ∂s.D.ν =
      c l * ∫ y, φ y * (v : H E n 0 → ℂ) y ∂s.D.ν := by
    intro l φ
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have e : (vecM v c l : Lp ℂ 2 s.D.ν) = c l • v := rfl
    filter_upwards [Lp.coeFn_smul (c l) v] with y hy
    rw [e, hy, Pi.smul_apply, smul_eq_mul]
    ring
  have hR : inner ℂ u (s.T₂ (vecM v c)) =
      ∑ j, ∑ l, c l * ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [L2.inner_def]
    have h : (fun z => inner ℂ ((u j : Lp ℂ 2 s.D.ν) z) ((s.T₂ (vecM v c) j : Lp ℂ 2 s.D.ν) z)) =ᵐ[s.D.ν]
        fun z => ∑ l, c l * (g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) := by
      filter_upwards [s.o₂ (vecM v c) j] with z hz
      rw [hz, RCLike.inner_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hv]
      simp only [g]
      ring
    rw [integral_congr_ae h, integral_finsetSum _ fun l _ => (F j l).2.1.const_mul _]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  have hint : Integrable (fun y => ∑ j, ∑ l, c l *
      ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y)) s.D.ν :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (F j l).1.const_mul _
  refine ⟨?_, ?_⟩
  · simpa only [hrep] using hint
  · simp only [hrep]
    change _ = inner ℂ u (s.T₂ (vecM v c))
    rw [hR, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, (F j l).2.2]

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPComm
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem op_unique {D : Dom E n 0} {Φ : Matrix ι ι (H E n 0 → ℂ)}
    {T T' : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D} (h : IsROp D Φ T) (h' : IsROp D Φ T') : T = T' := by
  refine ContinuousLinearMap.ext fun f => PiLp.ext fun i => ?_
  exact Lp.ext ((h f i).trans (h' f i).symm)

private theorem isTestM_adjM {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) : IsTestM (adjM Φ) := by
  intro i j
  refine ⟨Complex.continuous_conj.comp ((hΦ j i).1.comp continuous_inv), ?_⟩
  have h := (hΦ j i).2.comp_homeomorph (Homeomorph.inv (H E n 0))
  exact h.comp_left (g := starRingEnd ℂ) (map_zero _)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pComm_pf :
    PComm := by
  intro E _ _ _ n hn D π hfix ι _ Φ T hΦ hT f
  obtain ⟨T₀, h₀, hadj, -⟩ := PositivityTheory.Rg.BcB.E1.kernel_operator_exists_holds E n 0 D ι Φ hΦ
  obtain rfl : T₀ = T := op_unique h₀ hT
  have hS : ∀ g ∈ piSp D π ι, T₀ g ∈ piSp D π ι := piInv E n hn D π hfix ι Φ T₀ hΦ hT
  have hS' : ∀ g ∈ piSp D π ι, ContinuousLinearMap.adjoint T₀ g ∈ piSp D π ι :=
    piInv E n hn D π hfix ι (adjM Φ) _ (isTestM_adjM hΦ) hadj
  have hO : ∀ g ∈ (piSp D π ι)ᗮ, T₀ g ∈ (piSp D π ι)ᗮ := by
    intro g hg
    rw [Submodule.mem_orthogonal] at hg ⊢
    intro u hu
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact hg _ (hS' u hu)
  refine Submodule.eq_starProjection_of_mem_orthogonal (hS _ (Submodule.starProjection_apply_mem _ _)) ?_
  rw [← map_sub]
  exact hO _ (Submodule.sub_starProjection_mem_orthogonal _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPDiag
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {D : Dom E n 0} {ι : Type}

private lemma vecM_apply (v : Lp ℂ 2 D.ν) (c : ι → ℂ) (l : ι) : vecM v c l = c l • v := rfl

private lemma vecM_zero (c : ι → ℂ) : vecM (0 : Lp ℂ 2 D.ν) c = 0 := by
  ext1 l
  simp [vecM_apply]

private lemma vecM_add (a b : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (a + b) c = vecM a c + vecM b c := by
  ext1 l
  simp [vecM_apply, smul_add]

private lemma vecM_sub (a b : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (a - b) c = vecM a c - vecM b c := by
  ext1 l
  simp [vecM_apply, smul_sub]

private lemma vecM_smul (r : ℂ) (a : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (r • a) c = r • vecM a c := by
  ext1 l
  simp [vecM_apply, smul_comm r]

private lemma vecM_unit (f : Hs (ι := Unit) D) : vecM (f ()) (fun _ : Unit => 1) = f := by
  ext1 l
  simp [vecM_apply]

private lemma continuous_vecM [Fintype ι] (c : ι → ℂ) :
    Continuous fun f : Hs (ι := Unit) D => (vecM (f ()) c : Hs (ι := ι) D) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun l => (continuous_const_smul (c l)).comp (PiLp.continuous_apply 2 _ ()))

private lemma isPiVec_vecM (π : CuspSub E n) {f : Hs (ι := Unit) D} (hf : IsPiVec D π f) (c : ι → ℂ) :
    IsPiVec D π (vecM (f ()) c : Hs (ι := ι) D) := by
  intro l
  obtain ⟨ψ, hψ, u, hu, hc, he⟩ := hf ()
  refine ⟨c l • ψ, π.V.smul_mem _ hψ, u, hu, hc, ?_⟩
  have h1 := Lp.coeFn_smul (c l) (f ())
  filter_upwards [h1, he] with x h1 h2
  rw [vecM_apply, h1, Pi.smul_apply, h2]
  simp [mul_assoc]

private lemma isPiVec_comp (π : CuspSub E n) {g : Hs (ι := ι) D} (hg : IsPiVec D π g) (l : ι) :
    IsPiVec D π (vecM (g l) (fun _ : Unit => 1) : Hs (ι := Unit) D) := by
  intro _
  obtain ⟨ψ, hψ, u, hu, hc, he⟩ := hg l
  refine ⟨ψ, hψ, u, hu, hc, ?_⟩
  simpa [vecM_apply] using he

private lemma vecM_mem [Fintype ι] (π : CuspSub E n) (c : ι → ℂ) {f : Hs (ι := Unit) D}
    (hf : f ∈ piSp D π Unit) : (vecM (f ()) c : Hs (ι := ι) D) ∈ piSp D π ι := by
  have hspan : ∀ f ∈ Submodule.span ℂ {f : Hs (ι := Unit) D | IsPiVec D π f},
      (vecM (f ()) c : Hs (ι := ι) D) ∈ Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (isPiVec_vecM π hx c)
    | zero => simpa [vecM_zero] using Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (x + y) () = x () + y () := rfl
      rw [this, vecM_add]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have : (r • x) () = r • x () := rfl
      rw [this, vecM_smul]
      exact Submodule.smul_mem _ _ hx
  have hf' : f ∈ closure (Submodule.span ℂ {f : Hs (ι := Unit) D | IsPiVec D π f} : Set (Hs (ι := Unit) D)) := hf
  have : (vecM (f ()) c : Hs (ι := ι) D) ∈
      closure (Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} : Set (Hs (ι := ι) D)) :=
    map_mem_closure (f := fun f : Hs (ι := Unit) D => (vecM (f ()) c : Hs (ι := ι) D))
      (continuous_vecM c) hf' hspan
  exact this

private lemma vecM_orth [Fintype ι] (π : CuspSub E n) (c : ι → ℂ) {w : Lp ℂ 2 D.ν}
    (hw : (vecM w fun _ : Unit => 1 : Hs (ι := Unit) D) ∈ (piSp D π Unit)ᗮ) :
    (vecM w c : Hs (ι := ι) D) ∈ (piSp D π ι)ᗮ := by
  rw [piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h := (Submodule.mem_orthogonal _ _).1 hw _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (isPiVec_comp π hg l)))
    rw [PiLp.inner_apply] at h
    simp only [vecM_apply, one_smul, Finset.univ_unique, Finset.sum_singleton] at h
    rw [vecM_apply, inner_smul_right, h, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pDiag_pf :
    PDiag := by
  intro E _ _ _ n D π ι _ v c
  show _ = vecM ((piSp D π Unit).starProjection (vecM v fun _ : Unit => 1) ()) c
  have hmem := (piSp D π Unit).starProjection_apply_mem (vecM v fun _ : Unit => 1)
  have horth := (piSp D π Unit).sub_starProjection_mem_orthogonal (vecM v fun _ : Unit => 1)
  refine Submodule.eq_starProjection_of_mem_orthogonal (vecM_mem π c hmem) ?_
  rw [← vecM_sub]
  refine vecM_orth π c ?_
  rw [vecM_sub, vecM_unit]
  exact horth

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSizes
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.Rs
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem centre_eq (τ : ℝ) : splitCentre E n τ = (An.tor E (fun _ : Fin n => τ) : GA E n) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) n (Real.exp_pos τ)
  rw [Real.log_exp] at h
  rw [← h, DiscreteGroups.T1.G.Dcy.tor_eq]

private theorem logSize_centre (τ : ℝ) :
    logSize (splitCentre E n τ) ≤ 2 * Module.finrank ℚ E * |τ| := by
  rw [centre_eq]
  refine ((torNorm_holds E).2 n _).2.trans ?_
  have h : ‖(fun _ : Fin n => τ)‖ ≤ |τ| :=
    (pi_norm_le_iff_of_nonneg (abs_nonneg τ)).2 fun _ => by simp
  gcongr

private theorem logSize_inv' (g : GA E n) : logSize (g⁻¹) = logSize g := by
  unfold logSize
  rw [inv_inv, add_comm]

private theorem deg_top (g : GA E n) : deg g ⊤ = deg (1 : GA E n) ⊤ + logAbs g.val.det := by
  have e : (((1 : Matrix (Fin n) (Fin n) E)ᵀ : Matrix (Fin n) (Fin n) E) : Fin n → Fin n → E) =
      ⇑(Pi.basisFun E (Fin n)) := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hli : LinearIndependent E ((1 : Matrix (Fin n) (Fin n) E)ᵀ) := by
    rw [e]; exact (Pi.basisFun E (Fin n)).linearIndependent
  have hsp : Submodule.span E (Set.range ((1 : Matrix (Fin n) (Fin n) E)ᵀ)) = ⊤ := by
    rw [e]; exact (Pi.basisFun E (Fin n)).span_eq
  have h1 := D1.degBasis E n n g 1 hli
  have h2 := D1.degBasis E n n 1 1 hli
  have h3 := D1.degAdelic E n n 1 g g 1 hli (by simp)
  rw [mul_one] at h3
  rw [hsp] at h1 h2
  rw [← h1, ← h2, h3]

private theorem abs_logAbs_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E n,
    |logAbs g.val.det| ≤ C * (1 + logSize g) := by
  obtain ⟨C, hC, h⟩ := degRight E n
  refine ⟨C, hC, fun g => abs_le.2 ⟨?_, ?_⟩⟩
  · have h1 := h g g⁻¹ ⊤
    rw [mul_inv_cancel, logSize_inv', deg_top g] at h1
    linarith
  · have h1 := h 1 g ⊤
    rw [one_mul, deg_top g] at h1
    linarith

private theorem sizes' : Sizes := by
  intro E _ _ _ n hn
  obtain ⟨C, hC, hdet⟩ := abs_logAbs_le (E := E) (n := n)
  obtain ⟨-, -, -, c₀, hc₀⟩ := D1.sizeBasic E n
  have hc : 0 ≤ 2 + |c₀| + C := by positivity
  refine ⟨2 + |c₀| + C, hc, fun x => ⟨?_, ?_, DiscreteGroups.T1.G.Dcy.redSize_nonneg _⟩⟩
  · set l := ldet x with hl
    set d : ℝ := (Module.finrank ℚ E : ℝ) with hd
    have hd0 : 0 < d := by
      rw [hd]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := E)
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set τ : ℝ := l / (n * d) with hτ
    set y : GA E n := splitCentre E n (-l / (n * d)) * x.1 with hy
    have hr : r0 x = redSize y := rfl
    have hx : x.1 = splitCentre E n τ * y := by
      rw [hy, ← mul_assoc, ← CuspidalL2GL.splitCentre_add]
      have : τ + -l / (n * d) = 0 := by rw [hτ]; ring
      rw [this, CuspidalL2GL.splitCentre_zero, one_mul]
    have hτle : 2 * d * |τ| ≤ 2 * |l| := by
      have hpos : 0 < (n : ℝ) * d := by positivity
      rw [hτ, abs_div, abs_of_pos hpos]
      have e : 2 * d * (|l| / (n * d)) = 2 * |l| / n := by field_simp
      rw [e]
      exact div_le_self (by positivity) hn0
    have hK : 2 * |l| + c₀ ≤ (2 + |c₀| + C) * (1 + |l|) := by
      have h1 := le_abs_self c₀
      have h2 := abs_nonneg l
      have h3 := abs_nonneg c₀
      nlinarith [mul_nonneg h3 h2, mul_nonneg hC h2]
    have key : redSize x.1 - (2 + |c₀| + C) * (1 + |l|) ≤ redSize y := by
      refine le_ciInf fun γ => ?_
      have h1 := DiscreteGroups.T1.G.Dcy.redSize_le x.1 γ
      have h2 : ratGL E n γ * x.1 = splitCentre E n τ * (ratGL E n γ * y) := by
        rw [hx, ← mul_assoc, ← CuspidalL2GL.splitCentre_comm, mul_assoc]
      rw [h2] at h1
      have h3 := hc₀ (splitCentre E n τ) (ratGL E n γ * y)
      have h4 : logSize (splitCentre E n τ) ≤ 2 * d * |τ| := logSize_centre τ
      linarith
    rw [hr]
    linarith
  · have h1 : |ldet x| ≤ C * (1 + logSize x.1) := hdet x.1
    have h2 := DiscreteGroups.T1.G.Dcy.logSize_nonneg x.1
    have h3 := abs_nonneg c₀
    nlinarith [mul_nonneg h3 h2]

theorem sizes_of_basic : Basic → Sizes := fun _ => sizes'

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailOf
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

section SlopeTestRemainingChoices

open NumberField MeasureTheory GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem mem_cut_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {τ : ℝ} (hτ : 0 ≤ τ)
    (x : GA E 0) : x ∈ cutSet E 0 τ := by
  have key : ∀ (k : ℕ), k = 0 → ∀ M : Matrix (Fin 0) (Fin k) E, degM x M = 0 := by
    intro k hk M
    subst hk
    exact degM_zero x M
  have hr : ∀ W : Submodule E (Fin 0 → E), Module.finrank E W = 0 := fun W =>
    Module.finrank_zero_of_subsingleton
  refine ⟨fun W => ?_, ?_⟩
  · rw [deg, key _ (hr W), hr W]
    simp [prof]
  · rw [deg, key _ (hr ⊤)]
    simpa using hτ

private theorem tail_num (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) (N k : ℕ) (ρ : ℝ) (hρ : 1 + (k : ℝ) ≤ ρ) :
    (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ)) ≤
      ((1 + c) ^ N * (N.factorial * Real.exp 1)) * ε ^ k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hρ0 : 0 ≤ ρ := by linarith
  set l := max 0 (-Real.log ε) with hl
  have hl0 : 0 ≤ l := le_max_left _ _
  have hl1 : -Real.log ε ≤ l := le_max_right _ _
  have h1 : 1 + c * ρ ≤ (1 + c) * (1 + ρ) := by nlinarith
  have h2 : (1 + ρ) ^ N ≤ N.factorial * Real.exp (1 + ρ) := by
    have := Real.pow_div_factorial_le_exp (1 + ρ) (by linarith) N
    rwa [div_le_iff₀' (by positivity)] at this
  have h3 : Real.exp (-(l * ρ)) ≤ ε ^ k := by
    have e : ε ^ k = Real.exp (k * Real.log ε) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hε, Real.rpow_natCast]
    rw [e]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hl0 (by linarith : (0 : ℝ) ≤ ρ - k), mul_le_mul_of_nonneg_right hl1 hk]
  have h4 : Real.exp (-((1 + l) * ρ)) = Real.exp (-ρ) * Real.exp (-(l * ρ)) := by
    rw [← Real.exp_add]
    ring_nf
  have h5 : Real.exp (1 + ρ) * Real.exp (-ρ) = Real.exp 1 := by
    rw [← Real.exp_add]
    ring_nf
  calc (1 + c * ρ) ^ N * Real.exp (-((1 + l) * ρ))
      ≤ ((1 + c) * (1 + ρ)) ^ N * Real.exp (-((1 + l) * ρ)) := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 N) (Real.exp_pos _).le
    _ = (1 + c) ^ N * ((1 + ρ) ^ N * Real.exp (-ρ)) * Real.exp (-(l * ρ)) := by
        rw [h4, mul_pow]
        ring
    _ ≤ (1 + c) ^ N * (N.factorial * Real.exp 1) * ε ^ k := by
        have h6 : (1 + ρ) ^ N * Real.exp (-ρ) ≤ N.factorial * Real.exp 1 := by
          calc (1 + ρ) ^ N * Real.exp (-ρ) ≤ (N.factorial * Real.exp (1 + ρ)) * Real.exp (-ρ) :=
                mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
            _ = N.factorial * Real.exp 1 := by rw [mul_assoc, h5]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h6 (by positivity)) h3 (Real.exp_pos _).le (by positivity)

private theorem diff_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (f g : X → ℂ) (A : Set X)
    (hA : MeasurableSet A) (hf : Integrable f ν) (h : ∀ x, g x = f x - A.indicator f x) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∫⁻ x, A.indicator (fun x => ‖f x‖ₑ) x ∂ν ≤ ENNReal.ofReal B) :
    ‖∫ x, g x ∂ν - ∫ x, f x ∂ν‖ ≤ B := by
  have e : ∫ x, g x ∂ν - ∫ x, f x ∂ν = -∫ x, A.indicator f x ∂ν := by
    simp only [h]
    rw [integral_sub hf (hf.indicator hA)]
    ring
  rw [e, norm_neg]
  have h1 : ‖∫ x, A.indicator f x ∂ν‖ₑ ≤ ENNReal.ofReal B := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_trans (le_of_eq ?_) hb)
    refine lintegral_congr fun x => ?_
    exact enorm_indicator_eq_indicator_enorm ..
  rw [← ofReal_norm] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h1

private theorem tail_main : UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.Sizes → UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.InCut → UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TailInt →
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.DiagInt → DiscreteGroups.T1.G.CutTail2 := by
  intro hS hI hT hD E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ r₀ r₁ ε a1 a2 hfin b1 b2 hv hr₀ hr₁ hε
  let s : Su E n ι := ⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩
  obtain ⟨c, hc, hsz⟩ := hS E n hn
  obtain ⟨c', hc', hcut⟩ := hI E n
  obtain ⟨N, hN⟩ := hT E n ι s
  obtain ⟨Ct, hCt, hbd⟩ := hN (1 + max 0 (-Real.log ε)) (by positivity)
  refine ⟨(c' + 1) * (2 + c + c ^ 2), fun C' hC' =>
    ⟨Ct * ((1 + c) ^ N * (N.factorial * Real.exp 1)), fun k U Uπ Φ t o pp ht => ?_⟩⟩
  let m : Mid s := ⟨U, Uπ, Φ, t, o, pp⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (1 + k) * (1 + r₀ + r₁) := ⟨_, rfl⟩
  have hρk : 1 + (k : ℝ) ≤ ρ := by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hρ1 : 1 ≤ ρ := by linarith
  have hρr : 1 + (r₀ + k * r₁) ≤ ρ := by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hC'0 : 0 ≤ C' := le_trans (by positivity) hC'
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = C' * ρ := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτdef]; positivity
  have hR0 : 0 ≤ c * ρ := by positivity
  have hsupp : ∀ z, m.φ z ≠ 0 → |ldet z| ≤ c * ρ := fun z hz => by
    have h1 := (ht.toIsTest2.size z hz).1
    refine (hsz z).2.1.trans (mul_le_mul_of_nonneg_left ?_ hc)
    linarith
  let A : Set (H E n 0) := {x | x.1 ∉ cutSet E n τ}
  have hAm : MeasurableSet A := by
    have ho : IsOpen A := ((mahler_holds E n τ).1.preimage continuous_fst).isOpen_compl
    haveI : BorelSpace (H E n 0) := ⟨rfl⟩
    exact ho.measurableSet
  have hAρ : ∀ x ∈ A, |ldet x| ≤ c * ρ → ρ ≤ r0 x := fun x hx hl => by
    by_contra hlt
    refine hx (hcut τ x.1 ?_)
    have h1 := (hsz x).1
    have h2 : redSize x.1 ≤ ρ + c * (1 + c * ρ) := h1.trans (add_le_add (not_le.mp hlt).le
      (mul_le_mul_of_nonneg_left (by linarith) hc))
    have h3 : 1 + redSize x.1 ≤ (2 + c + c ^ 2) * ρ := by nlinarith [mul_nonneg hc (by linarith : (0 : ℝ) ≤ ρ - 1)]
    have hq : 0 ≤ (2 + c + c ^ 2) * ρ := by positivity
    calc c' * (1 + redSize x.1) ≤ c' * ((2 + c + c ^ 2) * ρ) := mul_le_mul_of_nonneg_left h3 hc'
      _ ≤ (c' + 1) * ((2 + c + c ^ 2) * ρ) := mul_le_mul_of_nonneg_right (by linarith) hq
      _ = ((c' + 1) * (2 + c + c ^ 2)) * ρ := by ring
      _ ≤ C' * ρ := mul_le_mul_of_nonneg_right hC' (by linarith)
      _ = τ := hτdef.symm
  have hb := hbd m (c * ρ) ρ hR0 hsupp A hAρ
  have hB : 0 ≤ Ct * ‖U‖ * (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ)) := by positivity
  have hmain := diff_le D.ν (lInt0 D k₁ k₂ Uπ) (lInt D k₁ k₂ τ Uπ) A hAm (hD E n ι s m) (fun x => by
      have h2 : chiT τ x.2 = (1 : ℂ) := Set.indicator_of_mem (mem_cut_zero hτ0 x.2) _
      by_cases hx : x.1 ∈ cutSet E n τ
      · have h1 : chiT τ x.1 = (1 : ℂ) := Set.indicator_of_mem hx _
        have h3 : x ∉ A := fun h => h hx
        simp [lInt, lInt0, h1, h2, h3]
      · have h1 : chiT τ x.1 = (0 : ℂ) := Set.indicator_of_notMem hx _
        have h3 : x ∈ A := hx
        simp [lInt, lInt0, h1, h2, h3]) _ hB hb
  rw [← hρdef, ← hτdef]
  refine hmain.trans ?_
  have hn' := tail_num c ε hc hε N k ρ hρk
  calc Ct * ‖U‖ * (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ))
      = Ct * ‖U‖ * ((1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ))) := by ring
    _ ≤ Ct * ‖U‖ * (((1 + c) ^ N * (N.factorial * Real.exp 1)) * ε ^ k) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = Ct * ((1 + c) ^ N * (N.factorial * Real.exp 1)) * ‖U‖ * ε ^ k := by ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.tailOf_pf :
    Basic → Sizes → InCut → TailInt → DiagInt → DiscreteGroups.T1.G.CutTail2 := fun _ => tail_main
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDropP
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.dropP_pf :
    Zero → KInv → Basic → Weak → PointRep → PComm → DropP := by
  intro hZ hK hB hW hR hC E _ _ _ n ι _ s m x y
  classical
  obtain ⟨-, -, -, -, -, -, -, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  set S := piSp s.D s.π ι with hS
  set P := S.starProjection with hP
  have hmem : ∀ f, P f ∈ S := fun f => Submodule.starProjection_apply_mem S f
  have hPP : ∀ f, P (P f) = P f := fun f => (Submodule.starProjection_eq_self_iff).2 (hmem f)
  have hUπ : ∀ f, m.Uπ f = m.U (P f) := fun f => by
    have h2 : f - P f ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal f
    have hdec : P f + (f - P f) = f := by abel
    calc m.Uπ f = m.Uπ (P f + (f - P f)) := by rw [hdec]
      _ = m.U (P f) := by rw [map_add (f := _), m.pp.1 _ (hmem f), m.pp.2 _ h2, add_zero]
  have C₁ : ∀ f, P (s.T₁ f) = s.T₁ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₁ s.T₁ s.t₁ s.o₁
  have C₂ : ∀ f, P (s.T₂ f) = s.T₂ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂
  have C₃ : ∀ f, P ((s.T₁ * m.U * s.T₂) f) = (s.T₁ * m.U * s.T₂) (P f) := hC E n s.pos s.D s.π s.fix ι m.Φ (s.T₁ * m.U * s.T₂) m.t m.o
  set Q : Hs (ι := ι) s.D →L[ℂ] Hs (ι := ι) s.D := (ContinuousLinearMap.id ℂ _ - P) ∘L m.Uπ with hQ
  have hQa : ∀ f, Q f = m.Uπ f - P (m.Uπ f) := fun f => rfl
  have key : ∀ g, s.T₁ (Q (s.T₂ g)) = 0 := fun g => by
    have e : s.T₁ (m.U (s.T₂ (P g))) = (s.T₁ * m.U * s.T₂) (P g) := rfl
    rw [hQa, map_sub, ← C₁, hUπ, C₂, e, ← C₃, hPP, sub_self]
  have hz : ∀ g i, inner ℂ (s.k₁ x i) (Q (s.T₂ g)) = 0 := fun g i => by
    have h0 := hR E n ι s s.Φ₁ s.T₁ s.t₁ s.o₁ (Q (s.T₂ g)) 0 (by rw [map_zero]; exact key g) x i
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : (((0 : Hs (ι := ι) s.D) j : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) =ᵐ[s.D.ν] 0 := Lp.coeFn_zero _ _ _
    rw [integral_congr_ae (g := fun _ => (0 : ℂ)) (hj.mono fun z hz => by rw [hz]; simp)]
    simp
  set f : H E n 0 → ℂ := fun z => ∑ i, inner ℂ (s.k₁ x i) (Q (s.k₂ (th z) i)) with hf
  have hfc : Continuous f := continuous_finsetSum _ fun i _ =>
    continuous_const.inner (Q.continuous.comp ((s.vecs.cont i).2.comp hthc))
  have hfi : Inv f := fun γ z => by
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th z)
    simp only [hf, hthmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th z) = s.k₂ (th z) from h]
  have hf0 := hZ E n s.D f Set.univ hfc hfi isOpen_univ (fun v _ => by
    have hw := fun i => hW E n ι s v (ContinuousLinearMap.adjoint Q (s.k₁ x i)) i
    have hpt : ∀ z, (v : H E n 0 → ℂ) z * f z =
        ∑ i, (v : H E n 0 → ℂ) z * inner ℂ (ContinuousLinearMap.adjoint Q (s.k₁ x i)) (s.k₂ (th z) i) := fun z => by
      simp only [hf, Finset.mul_sum, ContinuousLinearMap.adjoint_inner_left]
    simp only [hpt]
    rw [integral_finsetSum _ fun i _ => (hw i).1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hw i).2, ContinuousLinearMap.adjoint_inner_left]
    exact hz _ i)
  have h1 := hf0 (th y) (Set.mem_univ _)
  simp only [hf, hthth, hQa, inner_sub_right, Finset.sum_sub_distrib] at h1
  exact sub_eq_zero.1 h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PFinGen
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ker_integral_shift (X : Ctx) {φ f : X.G → ℂ} (hφ : Tst φ)
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν) (x : X.G) :
    ∫ y, ker X.Γ φ x y * f y ∂X.ν = ∫ z, φ z * f (x * z) ∂X.μ := by
  rw [(unfold X kerBasic kernel_rows_columns_square_integrable hφ hinv hf x).2,
    ← integral_mul_left_eq_self (fun y => φ (x⁻¹ * y) * f y) x]
  simp only [inv_mul_cancel_left]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finGen_pf :
    Basic → FinGen := by
  intro hB E _ _ _ n ι _ s
  classical
  obtain ⟨-, hmul, -, -, -, -, -, -, -, hrat, -, -⟩ := hB E n s.pos
  choose W hWle hWfd hW using s.fin
  have hfd : FiniteDimensional ℂ (⨆ p : ι × ι, W p.1 p.2 : Submodule ℂ (Sm E n)) := by
    haveI : ∀ p : ι × ι, FiniteDimensional ℂ (W p.1 p.2) := fun p => hWfd _ _
    exact Submodule.finiteDimensional_iSup _
  refine ⟨⨆ p : ι × ι, W p.1 p.2, iSup_le fun p => hWle _ _, hfd, ?_⟩
  intro v hv i t
  choose ψ hψ u hu hu' hvu using hv
  let X : Ctx := by
    haveI := CuspidalL2GL.t2Space_GA E n
    haveI := CuspidalL2GL.t2Space_GA E 0
    haveI := CuspidalL2GL.locallyCompactSpace_GA E n
    haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
    haveI := CuspidalL2GL.secondCountableTopology_GA E n
    haveI := CuspidalL2GL.secondCountableTopology_GA E 0
    haveI := (ratProper_holds E n).2.1
    haveI := (ratProper_holds E 0).2.1
    exact { G := H E n 0
            ms := borelH E n 0
            bs := ⟨rfl⟩
            μ := s.D.μ
            haar := { toIsFiniteMeasureOnCompacts :=
                        @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ s.D.μ s.D.haar.2.2.2
                      toIsMulLeftInvariant := s.D.haar.1
                      toIsOpenPosMeasure := s.D.haar.2.2.1 }
            Γ := ratH E n 0
            cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
            proper := by
              intro C hC
              have h1 := (ratProper_holds E n).2.2 _ (hC.image continuous_fst)
              have h2 := (ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
              refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
              rintro ⟨_, γ, rfl⟩ hγ
              exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
            F := s.D.F
            fd := s.D.fd }
  have hform : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), (ψ j).1 ((γ : H E n 0) * y).1 = (ψ j).1 y.1 := by
    intro j γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp _ (hψ j)).1.left γ₁ y.1
  set Ft : ι → H E n 0 → ℂ := fun j x => (ψ j).1 x.1 * u j (ldet x) with hFt
  have hinv : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), Ft j ((γ : H E n 0) * y) = Ft j y := by
    intro j γ y
    simp only [hFt, hform j γ y, hmul, (hrat γ).1, zero_add]
  have hmem : ∀ j, MemLp (Ft j) 2 s.D.ν := fun j => (Lp.memLp (v j)).ae_eq (hvu j)
  have hex : ∀ j, ∃ ψ' ∈ W i j, ∀ g, ψ'.1 g =
      ∫ y, s.Φ₁ i j y * (fun r => u j (t + r)) (ldet y) * (ψ j).1 (g * y.1) ∂s.D.μ := fun j =>
    hW i j (fun r => u j (t + r)) ((hu j).comp (continuous_const.add continuous_id)) (ψ j) (hψ j)
  choose ψ' hψ' hval using hex
  refine ⟨∑ j, ψ' j, Submodule.sum_mem _ fun j _ =>
    (le_iSup (fun p : ι × ι => W p.1 p.2) (i, j)) (hψ' j), fun x hx => ?_⟩
  rw [s.vecs.rep₁]
  have hsum : (∑ j, ψ' j).1 x.1 = ∑ j, (ψ' j).1 x.1 := by
    simp [Submodule.coe_sum]
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hae : ∫ y, kerH (s.Φ₁ i j) x y * (v j : H E n 0 → ℂ) y ∂s.D.ν =
      ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν :=
    integral_congr_ae ((hvu j).mono fun y hy => by simp only [hy, hFt])
  rw [hae, hval j]
  have hs : ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν = ∫ z, s.Φ₁ i j z * Ft j (x * z) ∂s.D.μ :=
    ker_integral_shift X (φ := s.Φ₁ i j) (f := Ft j) (s.t₁ i j) (hinv j) (hmem j) x
  refine hs.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  show s.Φ₁ i j z * ((ψ j).1 (x * z).1 * u j (ldet (x * z))) =
    s.Φ₁ i j z * u j (t + ldet z) * (ψ j).1 (x.1 * z.1)
  rw [hmul, hx, Prod.fst_mul]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDiagInt
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.diagInt_pf :
    GFac → HalfTerm → DiagInt := by
  intro hF hH
  unfold DiagInt ForSu
  intro E _ _ _ n ι _ s m
  obtain ⟨p, hp⟩ := hF E n ι s
  have hb := fun b => (hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)).1
  have hsum := MeasureTheory.integrable_finsetSum (Finset.univ : Finset p.B) fun b _ => hb b
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.sum_apply]
  exact (hp m x x).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PositionPairFunctionsEq
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem tst_trM (D : Dom E n 0) {ι : Type} [Fintype ι] {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ)
    (M : Matrix ι ι ℂ) : PositivityTheory.Rg.BcB.E1.Tst (G := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).G) (trM Φ M) := by
  have h := (PositivityTheory.Rg.BcB.E1.kerLin (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) (ι × ι)
    (fun p => Φ p.1 p.2) (fun p => M p.2 p.1) (fun p => hΦ p.1 p.2)).1
  have e : trM Φ M = fun y => ∑ p : ι × ι, Φ p.1 p.2 y * M p.2 p.1 := by
    funext y
    rw [Fintype.sum_prod_type]
    rfl
  rw [e]
  exact h

private theorem cusp_projection_self (D : Dom E n 0) (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) {w : ℝ → ℂ}
    (hw : Continuous w) (hws : HasCompactSupport w) (v : Lp ℂ 2 D.ν)
    (hv : (v : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * w (ldet x)) : P0 D π v = v := by
  have hvec : IsPiVec D π (vecM v fun _ : Unit => (1 : ℂ)) := fun _ => ⟨ψ, hψ, w, hw, hws, by
    have e : (vecM v fun _ : Unit => (1 : ℂ)) () = v := one_smul ℂ v
    simpa [e] using hv⟩
  have hmem : (vecM v fun _ : Unit => (1 : ℂ)) ∈ piSp D π Unit :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span hvec)
  unfold P0
  rw [Submodule.starProjection_eq_self_iff.2 hmem]
  exact one_smul ℂ v

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rep_pf :
    Basic → ThetaInt → KInv → PDiag → Ker → Rep := by
  intro hB hTI hK _ hKer E _ _ _ n ι _ s m ψ hψ u hu hus x₀
  obtain ⟨-, bMul, -, -, -, -, bThL, bThTh, bThMul, bRat, -, -⟩ := hB E n s.pos
  obtain ⟨ψ₁, hψ₁, hψe⟩ := s.fix.2 ψ hψ
  have hw : Continuous fun t : ℝ => u (-t) := hu.comp continuous_neg
  have hws : HasCompactSupport fun t : ℝ => u (-t) := hus.comp_homeomorph (Homeomorph.neg ℝ)
  set f : H E n 0 → ℂ := fun x => ψ₁.1 x.1 * u (-ldet x) with hf
  have hmem : MemLp f 2 s.D.ν := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n s.pos s.D s.π s.fix ψ₁ hψ₁ _ hw hws).1
  set v : Lp ℂ 2 s.D.ν := hmem.toLp f with hvdef
  have hv : (v : H E n 0 → ℂ) =ᵐ[s.D.ν] f := hmem.coeFn_toLp
  have hP : P0 s.D s.π v = v := cusp_projection_self s.D s.π hψ₁ hw hws v hv
  obtain ⟨kI, kE⟩ := hKer E n ι s m v x₀
  rw [hP] at kE
  have hψinv : ∀ (γ : ratH E n 0) (y : H E n 0), ψ₁.1 ((γ : H E n 0) * y).1 = ψ₁.1 y.1 := by
    intro γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp ψ₁ hψ₁).1.left γ₁ y.1
  have hfinv : ∀ (γ : ratH E n 0) (y : H E n 0), f ((γ : H E n 0) * y) = f y := by
    intro γ y
    simp only [hf]
    rw [hψinv γ y, bMul, (bRat γ).1, zero_add]
  have hGinv : ∀ (γ : ratH E n 0) (y : H E n 0), m.G x₀ (th ((γ : H E n 0) * y)) = m.G x₀ (th y) := by
    intro γ y
    have h2 := hK E n ι s |>.2 ⟨th (γ : H E n 0), (bRat γ).2⟩ (th y)
    simp only [Mid.G, Gk]
    rw [bThMul, h2]
  set F : H E n 0 → ℂ := fun y => f y * m.G x₀ (th y) with hF
  have hFinv : Inv F := fun γ y => by
    simp only [hF]
    rw [hfinv, hGinv]
  have hFint : Integrable F s.D.ν := kI.congr (hv.mono fun y hy => by simp only [hF, hy])
  obtain ⟨tI, tE⟩ := hTI E n s.D F hFinv hFint
  have hFth : ∀ x, F (th x) = ψ.1 x.1 * m.G x₀ x * u (ldet x) := by
    intro x
    have h1 : ψ₁.1 (th x).1 = ψ.1 x.1 := by
      have e : thetaA E n (th x).1 = x.1 := congrArg Prod.fst (bThTh x)
      rw [hψe, e]
    simp only [hF, hf]
    rw [h1, bThL, neg_neg, bThTh]
    ring
  refine ⟨tI.congr (Filter.Eventually.of_forall hFth), ?_⟩
  have hμl : s.D.μ.IsMulLeftInvariant := s.D.haar.1
  haveI hmm : MeasurableMul (H E n 0) :=
    (inferInstance : MeasurableMul (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D).G)
  have hun := (DiscreteGroups.T1.G.unfold (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D)
    PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable (tst_trM s.D m.t s.M) (f := f) hfinv hmem x₀).2
  have hun' : ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun
  calc ∫ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) ∂s.D.ν
      = ∫ x, F (th x) ∂s.D.ν := integral_congr_ae (Filter.Eventually.of_forall fun x => (hFth x).symm)
    _ = ∫ x, F x ∂s.D.ν := tE
    _ = ∫ y, (v : H E n 0 → ℂ) y * m.G x₀ (th y) ∂s.D.ν :=
        integral_congr_ae (hv.mono fun y hy => by simp only [hF, hy])
    _ = ∫ y, kerH m.φ x₀ y * (v : H E n 0 → ℂ) y ∂s.D.ν := kE
    _ = ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν := integral_congr_ae (hv.mono fun y hy => by simp only [hy])
    _ = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun'
    _ = ∫ z, m.φ (x₀⁻¹ * (x₀ * z)) * f (x₀ * z) ∂s.D.μ :=
        (integral_mul_left_eq_self (fun y => m.φ (x₀⁻¹ * y) * f y) x₀).symm
    _ = ∫ z, m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) * u (-(ldet x₀ + ldet z)) ∂s.D.μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hf]
        rw [inv_mul_cancel_left, bMul, Prod.fst_mul, hψe]
        ring

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PUncutOf
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1 GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.uncutOf_pf :
    Basic → GFac → HalfTerm → RangeW → TrFin → DiscreteGroups.T1.G.UncutHalf := by
  intro hB hF hH hR hT E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  let s : Su E n ι := ⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩
  let m : Mid s := ⟨U, Uπ, Φ, c1, c2, hpi⟩
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨hac, hmul, -⟩ := hB E n hn
  have hsum : lInt0 D k₁ k₂ Uπ = fun x => ∑ b, (p.w b).1 x.1 * m.G (ac E n (ldet x) * p.x b) x :=
    funext fun x => hp m x x
  have hterm := fun b => hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)
  obtain ⟨L, hL, -, rfl⟩ := ht
  let w : p.B → π.V := fun b => ⟨p.w b, p.mem b⟩
  let e : p.B → (π.V →ₗ[ℂ] ℂ) := fun b =>
    { toFun := fun ψ => ψ.1.1 (p.x b).1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hcentre : ∀ (ψ : Sm E n), ψ ∈ π.V → ∀ g : GA E n,
      ψ.1 (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)).1 = ψ.1 g := by
    intro ψ hψ g
    exact hπ.1 ψ hψ _ g
  have hspan : ∀ v, L v = ∑ b, e b (L v) • w b := by
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hac]; ring
    have h1 := hR E n ι s p hp m v.1 v.2 _ h0
    have h2 : (L v).1.1 g = ∑ b, (L v).1.1 (p.x b).1 * (p.w b).1 g := by
      rw [← hcentre (L v).1 (L v).2 g, hL v]
      refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
      rw [hcentre _ (p.mem b), hL v, mul_comm]
      rfl
    let ev : π.V →ₗ[ℂ] ℂ :=
      { toFun := fun ψ => ψ.1.1 g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h3 : (∑ b, e b (L v) • w b).1.1 g = ev (∑ b, e b (L v) • w b) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h3, map_sum]
    exact h2
  have htr := hT π.V p.B L w e hspan
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finsetSum _ fun b _ => (hterm b).1
  · rw [hsum, integral_finsetSum _ fun b _ => (hterm b).1, htr, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hterm b).2]
    congr 1
    exact (hL (w b) (p.x b).1).symm
end

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem aeEq : AeEq := aeEq_pf basic_pf
theorem zero : Zero := zero_pf aeEq
theorem pointRep : PointRep := pointRep_pf aeEq kInv_pf
theorem ker : Ker := ker_pf weak_pf pointRep pComm_pf pDiag_pf
theorem supp : Supp := supp_pf basic_pf zero kInv_pf pSupp_pf ker
theorem gBound : GBound := gBound_pf basic_pf
theorem gFac : GFac := gFac_pf (finFac_pf basic_pf evalBasis_pf (finGen_pf basic_pf))
  (dropP_pf zero kInv_pf basic_pf weak_pf pointRep pComm_pf)
theorem rep : Rep := rep_pf basic_pf (thetaInt_pf basic_pf) kInv_pf pDiag_pf ker
theorem sizes : Sizes := by first | exact sizes_of_basic basic_pf | exact sizes_of_basic
theorem domInt : DomInt := domInt_pf basic_pf sizes
theorem halfTerm : HalfTerm := halfTerm_pf basic_pf gBound supp rep flip_pf domInt
theorem uncutHalf : DiscreteGroups.T1.G.UncutHalf := uncutOf_pf basic_pf gFac halfTerm (rangeW_pf rep) trFin_pf
theorem cutTail : DiscreteGroups.T1.G.CutTail2 :=
  tailOf_pf basic_pf sizes inCut_pf (tailInt_of_bounds gFac gBound supp domInt) (diagInt_pf gFac halfTerm)

theorem growthPiJ_holds : PositivityTheory.Rg.BcB.Desc.GrowthPiJ :=
  DiscreteGroups.T1.G.rGrowthPiJ_of (fun _ _ => uncutHalf) (fun _ _ => cutTail) PositivityTheory.Rg.BcB.CV.ellFormula2J
    PositivityTheory.Rg.BcB.E1.sFun_holds DiscreteGroups.T1.G.Dcy.piVecEx_holds DiscreteGroups.T1.G.piInv

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
