module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Transfer
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivB

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.IndicatorRholMem
noncomputable section

open Finset
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def cOm (n : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {F | ContDiffOn ℂ ∞ F (OmegaP n) ∧ ∀ z, z ∉ OmegaP n → F z = 0}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, fun z hz => by simp [ha.2 z hz, hb.2 z hz]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' := fun c F hF => ⟨hF.1.const_smul c, fun z hz => by simp [hF.2 z hz]⟩

theorem mem_cOm {F : Matrix (Fin n) (Fin n) ℂ → ℂ} :
    F ∈ cOm n ↔ ContDiffOn ℂ ∞ F (OmegaP n) ∧ ∀ z, z ∉ OmegaP n → F z = 0 := Iff.rfl

theorem cOm_smooth (F : cOm n) : ContDiffOn ℂ ∞ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaP n) :=
  (mem_cOm.1 F.2).1

theorem indicator_rhol_mem (X : Matrix (Fin n) (Fin n) ℂ) (F : cOm n) :
    (OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) ∈ cOm n := by
  have hF := cOm_smooth F
  have hs : IsOpen (OmegaP n) := isOpen_positiveOmega
  have hd := ((contDiffOn_infty_iff_fderiv_of_isOpen hs).1 hF).2
  have hg : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z * X) := by
    have h0 := (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ X)).contDiff (n := ∞)
    first
      | exact h0
      | simpa using h0
      | (convert h0 using 1; funext z; rfl)
      | (convert h0 using 1; funext z; simp [LinearMap.mulRight_apply])
  refine mem_cOm.2 ⟨?_, fun z hz => Set.indicator_of_notMem hz _⟩
  refine (hd.clm_apply hg.contDiffOn).congr fun z hz => ?_
  rw [Set.indicator_of_mem hz]
  rfl

def rOm (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (cOm n) where
  toFun F := ⟨(OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)), indicator_rhol_mem X F⟩
  map_add' F G := by
    apply Subtype.ext
    funext z
    show (OmegaP n).indicator (Rhol X ((F + G : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ)) z =
      (OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) z +
        (OmegaP n).indicator (Rhol X (G : Matrix (Fin n) (Fin n) ℂ → ℂ)) z
    by_cases hz : z ∈ OmegaP n
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      show fderiv ℂ ((F : Matrix (Fin n) (Fin n) ℂ → ℂ) + (G : Matrix (Fin n) (Fin n) ℂ → ℂ)) z (z * X) =
        fderiv ℂ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) z (z * X) + fderiv ℂ (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z (z * X)
      erw [((differentiableAt_of_contDiffOn_omega (cOm_smooth F) hz).hasFDerivAt.add
        (differentiableAt_of_contDiffOn_omega (cOm_smooth G) hz).hasFDerivAt).fderiv]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, add_zero]
  map_smul' c F := by
    apply Subtype.ext
    funext z
    show (OmegaP n).indicator (Rhol X ((c • F : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ)) z =
      c * (OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) z
    by_cases hz : z ∈ OmegaP n
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      show fderiv ℂ (c • (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) z (z * X) =
        c * fderiv ℂ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) z (z * X)
      erw [fderiv_const_smul (differentiableAt_of_contDiffOn_omega (cOm_smooth F) hz)]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]

theorem rOm_apply (X : Matrix (Fin n) (Fin n) ℂ) (F : cOm n) :
    ((rOm X F : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ) =
      (OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) := rfl

theorem rOm_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : rOm (n := n) (X - Y) = rOm X - rOm Y := by
  refine LinearMap.ext fun F => Subtype.ext (funext fun z => ?_)
  simp only [LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply, rOm_apply]
  by_cases hz : z ∈ OmegaP n
  · simp only [Set.indicator_of_mem hz]
    exact rightHol_sub X Y _ z
  · simp only [Set.indicator_of_notMem hz, sub_zero]

theorem rOm_zero : rOm (n := n) 0 = 0 := by
  have h := rOm_sub (n := n) 0 0
  rwa [sub_zero, sub_self] at h

theorem rOm_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    rOm X * rOm Y - rOm Y * rOm X = rOm (n := n) (X * Y - Y * X) := by
  refine LinearMap.ext fun F => Subtype.ext (funext fun z => ?_)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, rOm_apply]
  by_cases hz : z ∈ OmegaP n
  · simp only [Set.indicator_of_mem hz]
    have e1 : ∀ W : Matrix (Fin n) (Fin n) ℂ, Set.EqOn
        ((OmegaP n).indicator (Rhol W (F : Matrix (Fin n) (Fin n) ℂ → ℂ)))
        (Rhol W (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) (OmegaP n) :=
      fun W w hw => Set.indicator_of_mem hw _
    rw [rightHol_congr_on_omega (e1 Y) hz, rightHol_congr_on_omega (e1 X) hz]
    have hinf := (cOm_smooth F).contDiffAt (isOpen_positiveOmega.mem_nhds hz)
    have h2 : ContDiffAt ℂ 2 (F : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
      first
        | exact hinf.of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
        | exact contDiffAt_infty.1 hinf 2
        | exact hinf.of_le (by norm_cast)
        | exact hinf.of_le (by simp)
    exact rightHol_commutator h2 X Y
  · simp only [Set.indicator_of_notMem hz, sub_zero]

def eOm (a b : Fin n) : Module.End ℂ (cOm n) := rOm (Matrix.single a b 1)

def phiOm (μ : Fin n → ℤ) : cOm n :=
  ⟨(OmegaP n).indicator (PhiP μ), mem_cOm.2 ⟨(contDiffOn_powerDet μ).congr fun _ hz => Set.indicator_of_mem hz _,
    fun _ hz => Set.indicator_of_notMem hz _⟩⟩

private theorem single_one_mul_single_one_eq_ite (i j k l : Fin n) :
    Matrix.single i j (1 : ℂ) * Matrix.single k l 1 = if j = k then Matrix.single i l 1 else 0 := by
  split_ifs with h
  · subst h
    first
      | rw [Matrix.single_mul_single_same, mul_one]
      | simp
  · first
      | rw [Matrix.single_mul_single_of_ne h]
      | simp [h]

theorem isGlRep_eOm : IsGlRep (eOm (n := n)) := by
  intro a b c d
  simp only [eOm]
  rw [rOm_comm, rOm_sub, single_one_mul_single_one_eq_ite, single_one_mul_single_one_eq_ite]
  split_ifs <;> first | rfl | simp only [rOm_zero, sub_zero, zero_sub]

def mmSub (μ : Fin n → ℤ) : Submodule ℂ (cOm n) := genSub (eOm (n := n)) (Submodule.span ℂ {phiOm μ})

theorem mmSub_stable (μ : Fin n → ℤ) (a b : Fin n) : ∀ x ∈ mmSub μ, eOm a b x ∈ mmSub μ := by
  intro x hx
  simp only [mmSub, genSub] at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  intro T hT
  exact hT.2 a b x (hx T hT)

theorem phiOm_mem (μ : Fin n → ℤ) : phiOm μ ∈ mmSub μ := by
  simp only [mmSub, genSub]
  rw [Submodule.mem_sInf]
  intro T hT
  exact hT.1 (Submodule.subset_span (Set.mem_singleton _))

abbrev MMT (μ : Fin n → ℤ) : Type := ↥(mmSub μ)

def eMM (μ : Fin n → ℤ) (a b : Fin n) : Module.End ℂ (MMT μ) := (eOm a b).restrict (mmSub_stable μ a b)

def phiMM (μ : Fin n → ℤ) : MMT μ := ⟨phiOm μ, phiOm_mem μ⟩

theorem k2vM (lam : Fin n → ℝ) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    IsGlRep (eMM μ) ∧ (∀ a b, b < a → eMM μ a b (phiMM μ) = 0) ∧
      (∀ a, eMM μ a a (phiMM μ) = ((lam a + rho n a : ℝ) : ℂ) • phiMM μ) ∧
      genSub (eMM μ) (Submodule.span ℂ {phiMM μ}) = ⊤ := by
  have hgl : IsGlRep (eMM μ) := by
    intro a b c d
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h := LinearMap.congr_fun (isGlRep_eOm (n := n) a b c d) (v : cOm n)
    split_ifs at h ⊢ <;> simpa [eMM, LinearMap.restrict_coe_apply] using h
  refine ⟨hgl, ?_, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    funext z
    show (OmegaP n).indicator (Rhol (Matrix.single a b 1) ((OmegaP n).indicator (PhiP μ))) z = 0
    by_cases hz : z ∈ OmegaP n
    · rw [Set.indicator_of_mem hz, rightHol_congr_on_omega (fun y hy => Set.indicator_of_mem hy _) hz]
      exact rightHol_powerDet_lower_eq_zero μ hab hz
    · exact Set.indicator_of_notMem hz _
  · intro a
    apply Subtype.ext
    apply Subtype.ext
    funext z
    show (OmegaP n).indicator (Rhol (Matrix.single a a 1) ((OmegaP n).indicator (PhiP μ))) z =
      ((lam a + rho n a : ℝ) : ℂ) * (OmegaP n).indicator (PhiP μ) z
    by_cases hz : z ∈ OmegaP n
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        rightHol_congr_on_omega (fun y hy => Set.indicator_of_mem hy _) hz, rightHol_powerDet_diag μ a hz, ← hμ a]
      norm_cast
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  · have hGS : Submodule.span ℂ {phiMM μ} ≤ genSub (eMM μ) (Submodule.span ℂ {phiMM μ}) :=
      le_sInf fun T hT => hT.1
    have hGc : ∀ a b, ∀ v ∈ genSub (eMM μ) (Submodule.span ℂ {phiMM μ}),
        eMM μ a b v ∈ genSub (eMM μ) (Submodule.span ℂ {phiMM μ}) :=
      fun a b v hv => Submodule.mem_sInf.2 fun T hT => hT.2 a b v (Submodule.mem_sInf.1 hv T hT)
    have key : mmSub μ ≤ (genSub (eMM μ) (Submodule.span ℂ {phiMM μ})).map (mmSub μ).subtype := by
      apply sInf_le
      refine Set.mem_setOf.2 ⟨?_, ?_⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.mem_map.2 ⟨phiMM μ, hGS (Submodule.subset_span (Set.mem_singleton _)), rfl⟩
      · rintro a b _ ⟨y, hy, rfl⟩
        exact Submodule.mem_map.2 ⟨eMM μ a b y, hGc a b y hy, rfl⟩
    rw [eq_top_iff]
    intro v _
    obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 (key v.2)
    rwa [← Subtype.ext hyv]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SASingle
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.EqZeroOfCoef
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.DerivEntries
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem ode_zero {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (A : Module.End ℂ U)
    (G : ℝ → U →ₗ[ℂ] ℂ) (hG : ∀ s y, HasDerivAt (fun s => G s y) (-(G s (A y))) s) (h0 : G 0 = 0)
    (s : ℝ) : G s = 0 := by
  let b := Module.finBasis ℂ U
  let L : (Fin (Module.finrank ℂ U) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ U) → ℂ) :=
    LinearMap.toContinuousLinearMap
      (LinearMap.pi fun i => -∑ j, b.repr (A (b i)) j • LinearMap.proj j)
  have hg : ∀ t, HasDerivAt (fun s i => G s (b i)) (L fun i => G t (b i)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    refine (hG t (b i)).congr_deriv ?_
    have := congrArg (G t) (b.sum_repr (A (b i)))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul] at this
    simp [L, this]
  have hz := ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊)
    (t₀ := 0) (f := fun s i => G s (b i)) (g := fun _ => 0)
    (fun _ => L.lipschitz.lipschitzOnWith) (fun t => ⟨hg t, trivial⟩)
    (fun t => ⟨by simpa using hasDerivAt_const t (0 : Fin (Module.finrank ℂ U) → ℂ), trivial⟩)
    (by funext i; simp [h0])
  exact b.ext fun i => congrFun (congrFun hz s) i

def ei (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (((-s : ℝ) : ℂ) • X)

def cj (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ei X s * Y * NormedSpace.exp ((s : ℂ) • X)

open scoped Matrix.Norms.Operator in
theorem deriv_entries (X Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (a b : Fin n) :
    HasDerivAt (fun s => ei X s a b) (-((ei X s * X) a b)) s ∧
      HasDerivAt (fun s => cj X s Y a b) (-(cj X s (X * Y - Y * X) a b)) s := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) s
  have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s
  have e : ∀ s : ℝ, s • (-X) = ((-s : ℝ) : ℂ) • X := fun s => by
    rw [Complex.coe_smul, smul_neg, neg_smul]
  have e' : ∀ s : ℝ, s • X = (s : ℂ) • X := fun s => (Complex.coe_smul s X).symm
  simp only [e] at h1
  simp only [e'] at h2
  let P := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)
  refine ⟨(P.hasFDerivAt.comp_hasDerivAt s h1).congr_deriv ?_,
    (P.hasFDerivAt.comp_hasDerivAt s ((h1.mul_const Y).mul h2)).congr_deriv ?_⟩
  · show (ei X s * -X) a b = _
    rw [Matrix.mul_neg]; rfl
  · show (ei X s * -X * Y * NormedSpace.exp ((s : ℂ) • X) +
      ei X s * Y * (X * NormedSpace.exp ((s : ℂ) • X))) a b = _
    have e2 : ei X s * -X * Y * NormedSpace.exp ((s : ℂ) • X) +
        ei X s * Y * (X * NormedSpace.exp ((s : ℂ) • X)) = -cj X s (X * Y - Y * X) := by
      simp only [cj]; noncomm_ring
    rw [e2]; rfl

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def actL (E : Fin n → Fin n → Module.End ℂ M) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M where
  toFun := actM E
  map_add' X Y := by simp [actM, add_smul, sum_add_distrib]
  map_smul' c X := by simp [actM, smul_sum, smul_smul]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b 1) = E a b := by
  simp [actM, Matrix.single_apply, ite_smul, ite_and]

def wB (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (w : List (Fin n × Fin n)) : M :=
  (w.map fun p => actM E (cj X s (Matrix.single p.1 p.2 1))).prod φ

def adX (X : Matrix (Fin n) (Fin n) ℂ) (w : List (Fin n × Fin n)) : List (Fin n × Fin n) →₀ ℂ :=
  ∑ a, ∑ b, X a b • adLW a b w

theorem lc_adL (a b : Fin n) (p : Fin n × Fin n) :
    Finsupp.linearCombination ℂ (fun q : Fin n × Fin n => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))
      (adL a b p) = Matrix.single a b 1 * Matrix.single p.1 p.2 1 -
        Matrix.single p.1 p.2 1 * Matrix.single a b 1 := by
  rw [adL, map_sub]
  congr 1
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]

theorem lc_adX_cons (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Finsupp.linearCombination ℂ (wB E φ X s) (adX X (p :: w)) =
      actM E (cj X s (X * Matrix.single p.1 p.2 1 - Matrix.single p.1 p.2 1 * X)) (wB E φ X s w) +
        actM E (cj X s (Matrix.single p.1 p.2 1))
          (Finsupp.linearCombination ℂ (wB E φ X s) (adX X w)) := by
  let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M :=
    { toFun := fun Y => actM E (cj X s Y) (wB E φ X s w)
      map_add' := fun Y Y' => by
        have := (actL E).map_add (cj X s Y) (cj X s Y')
        simp only [cj, Matrix.mul_add, Matrix.add_mul]
        exact congrArg (fun A : Module.End ℂ M => A (wB E φ X s w)) this
      map_smul' := fun c Y => by
        have := (actL E).map_smul c (cj X s Y)
        simp only [cj, Matrix.mul_smul, Matrix.smul_mul]
        exact congrArg (fun A : Module.End ℂ M => A (wB E φ X s w)) this }
  have h1 : ∀ u : (Fin n × Fin n) →₀ ℂ,
      Finsupp.linearCombination ℂ (wB E φ X s) (u.mapDomain (· :: w)) =
        C (Finsupp.linearCombination ℂ
          (fun q : Fin n × Fin n => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ)) u) := fun u => by
    rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]; rfl
  have h2 : ∀ u : List (Fin n × Fin n) →₀ ℂ,
      Finsupp.linearCombination ℂ (wB E φ X s) (u.mapDomain (p :: ·)) =
        actM E (cj X s (Matrix.single p.1 p.2 1)) (Finsupp.linearCombination ℂ (wB E φ X s) u) :=
    fun u => by rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]; rfl
  have h3 : X * Matrix.single p.1 p.2 1 - Matrix.single p.1 p.2 1 * X =
      ∑ a, ∑ b, X a b • ((Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) * Matrix.single p.1 p.2 1 -
        Matrix.single p.1 p.2 1 * Matrix.single a b 1) := by
    have hX : X = ∑ a, ∑ b, X a b • (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp
    conv_lhs => rw [hX]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
      sum_sub_distrib]
  show _ = C _ + _
  rw [h3]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [adX, adLW, map_sum, map_smul, map_add (f := _), smul_add, sum_add_distrib, h1, h2, lc_adL]

theorem deriv_word (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (w : List (Fin n × Fin n)) : ∀ l : M →ₗ[ℂ] ℂ, HasDerivAt (fun s => l (wB E φ X s w))
      (-(l (Finsupp.linearCombination ℂ (wB E φ X s) (adX X w)))) s := by
  induction w with
  | nil => intro l; simpa [wB, adX, adLW] using hasDerivAt_const s (l φ)
  | cons p w ih =>
    intro l
    have e : (fun s => l (wB E φ X s (p :: w))) = fun s => ∑ a, ∑ b,
        cj X s (Matrix.single p.1 p.2 1) a b * (l ∘ₗ E a b) (wB E φ X s w) := by
      funext s
      set_option synthInstance.maxHeartbeats 100000 in
        simp [wB, actM, map_sum]
    rw [e]
    refine (HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ =>
      ((deriv_entries X (Matrix.single p.1 p.2 1) s a b).2.mul (ih (l ∘ₗ E a b)))).congr_deriv ?_
    rw [lc_adX_cons]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_add (f := _), map_sum, map_smul,
      smul_eq_mul, LinearMap.comp_apply, neg_add, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

theorem adLW_length (a b : Fin n) : ∀ (w w' : List (Fin n × Fin n)), w' ∈ (adLW a b w).support →
    w'.length = w.length := by
  classical
  intro w
  induction w with
  | nil => intro w' h; simp [adLW] at h
  | cons p w ih =>
    intro w' h
    rcases mem_union.mp (Finsupp.support_add h) with h | h
    · obtain ⟨q, -, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support h); rfl
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support h)
      simp [ih q hq]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
end
end

noncomputable section

open Finset Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Coef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem coef_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) (u : H) (m : D) :
    HasDerivAt (fun t : ℝ => ⟪u, σ (g * NormedSpace.exp ((t : ℂ) • X)) (m : H)⟫_ℂ)
      ⟪u, σ g ((actM E X m : D) : H)⟫_ℂ 0 := by
  have h := (((innerSL ℂ u).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hD.deriv X hX m)
  refine HasDerivAt.congr_of_eventuallyEq h (Eventually.of_forall fun t => ?_)
  simp only [hσ.1.2 _ hg _ (exp_smul_mem_UJset hX t)]
  rfl

theorem act_cpart (E : Fin n → Fin n → Module.End ℂ D) (Z : Matrix (Fin n) (Fin n) ℂ) (m : D) :
    actM E Z m = actM E (cpart1 ε Z) m + Complex.I • actM E (cpart2 ε Z) m := by
  have h : actL E Z = actL E (cpart1 ε Z) + Complex.I • actL E (cpart2 ε Z) := by
    rw [← map_smul, ← map_add (f := _), ta_cpart_sum]
  exact congrArg (fun A : Module.End ℂ D => A m) h

theorem eq_zero_of_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    {y : D} (hy : y ∈ genSub E V)
    (h : ∀ g ∈ UJset ε, ∀ v' : V, ⟪((v' : D) : H), σ g (y : H)⟫_ℂ = 0) : y = 0 := by
  let N : Set D := {m | ∀ g ∈ UJset ε, ∀ v' : V, ⟪((v' : D) : H), σ g (m : H)⟫_ℂ = 0}
  have hNr : ∀ X, inG ε X → ∀ m ∈ N, actM E X m ∈ N := fun X hX m hm g hg v' => by
    refine (coef_deriv hσ hD hg hX _ m).unique ?_
    have : (fun t : ℝ => ⟪((v' : D) : H), σ (g * NormedSpace.exp ((t : ℂ) • X)) (m : H)⟫_ℂ) =
        fun _ => 0 := funext fun t => hm _ (ta_inUJ_mul_exp ε hg hX t) v'
    rw [this]; exact hasDerivAt_const _ _
  have hN : ∀ a b, ∀ m ∈ N, E a b m ∈ N := fun a b m hm g hg v' => by
    rw [← actM_single E a b, act_cpart (ε := ε), Submodule.coe_add, Submodule.coe_smul, map_add (f := _),
      map_smul, inner_add_right, inner_smul_right, hNr _ (ta_inG_cpart1 ε _) m hm g hg v',
      hNr _ (ta_inG_cpart2 ε _) m hm g hg v']
    simp
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  let P : Submodule ℂ D :=
    { carrier := {u | ∀ m ∈ N, ⟪u, m⟫_ℂ = 0}
      add_mem' := fun hu hu' m hm => by rw [inner_add_left, hu m hm, hu' m hm, add_zero]
      zero_mem' := fun m _ => inner_zero_left m
      smul_mem' := fun c u hu m hm => by rw [inner_smul_left, hu m hm, mul_zero] }
  have h1J : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hle : genSub E V ≤ P := sInf_le ⟨fun v hv m hm => by
      have := hm 1 h1J ⟨v, hv⟩
      rw [hσ.1.1] at this
      exact this,
    fun a b u hu m hm => by rw [hU a b, hu _ (hN b a m hm), mul_zero]⟩
  exact inner_self_eq_zero.mp (hle hy y h)

theorem inner_deriv {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (f : ℝ → (U →L[ℂ] U)) (φ : U → U → ℂ)
    (h : ∀ a b, HasDerivAt (fun t => ⟪a, f t b⟫_ℂ) (φ a b) 0) (a b : U) :
    ⟪a, deriv f 0 b⟫_ℂ = φ a b := by
  let e := stdOrthonormalBasis ℂ U
  have hf : f = fun t => ∑ i, ∑ j, ⟪e i, f t (e j)⟫_ℂ • (innerSL ℂ (e j)).smulRight (e i) := by
    funext t
    ext x
    conv_lhs => rw [← e.sum_repr' (f t x), ← e.sum_repr' x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, inner_sum, inner_smul_right, sum_smul,
      _root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [mul_comm]
  have hd : DifferentiableAt ℝ f 0 := by
    rw [hf]
    exact DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
      (h _ _).differentiableAt.smul_const _
  have h2 := (((innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ U b)).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  exact h2.unique (h a b)

theorem rWord_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (ι : V ≃ₗ[ℂ] U) (Ψ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U))
    (hco : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', Ψ g (ι v)⟫_ℂ)
    (L : List (Matrix (Fin n) (Fin n) ℂ)) : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪ι v', rWord ε L Ψ g (ι v)⟫_ℂ =
        ⟪((v' : D) : H), σ g (((L.map (actM E)).prod (v : D) : D) : H)⟫_ℂ := by
  induction L with
  | nil => intro g hg v v'; exact (hco g hg v v').symm
  | cons Z L ih =>
    intro g hg v v'
    have hR : ∀ X, inG ε X → ⟪ι v', RdV X (rWord ε L Ψ) g (ι v)⟫_ℂ =
        ⟪((v' : D) : H), σ g ((actM E X ((L.map (actM E)).prod (v : D)) : D) : H)⟫_ℂ := by
      intro X hX
      have := inner_deriv (fun t : ℝ => rWord ε L Ψ (g * NormedSpace.exp ((t : ℂ) • X)))
        (fun a b => ⟪((ι.symm a : D) : H),
          σ g ((actM E X ((L.map (actM E)).prod (ι.symm b : D)) : D) : H)⟫_ℂ)
        (fun a b => by
          refine (coef_deriv hσ hD hg hX _ _).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
          have := ih _ (ta_inUJ_mul_exp ε hg hX t) (ι.symm b) (ι.symm a)
          rwa [ι.apply_symm_apply, ι.apply_symm_apply] at this) (ι v') (ι v)
      rwa [ι.symm_apply_apply, ι.symm_apply_apply] at this
    show ⟪ι v', (RdV (cpart1 ε Z) (rWord ε L Ψ) g + Complex.I • RdV (cpart2 ε Z) (rWord ε L Ψ) g) (ι v)⟫_ℂ = _
    rw [_root_.add_apply, _root_.smul_apply, inner_add_right,
      inner_smul_right, hR _ (ta_inG_cpart1 ε Z), hR _ (ta_inG_cpart2 ε Z), List.map_cons,
      List.prod_cons, Module.End.mul_apply, act_cpart (ε := ε) E Z, Submodule.coe_add,
      Submodule.coe_smul, map_add, map_smul, inner_add_right, inner_smul_right]

end Coef

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem omegaP_mem_nhds {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ OmegaP n) : OmegaP n ∈ 𝓝 x :=
  (tb_inv_hasFDerivAt (tb_isUnit_of_omegaP hx)).choose_spec.1.continuousAt.preimage_mem_nhds
    (isOpen_omega.mem_nhds hx)

def evZ (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) : MMT μ →ₗ[ℂ] ℂ :=
  (LinearMap.proj z : (Matrix (Fin n) (Fin n) ℂ → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (cOm n).subtype ∘ₗ (mmSub μ).subtype

theorem evZ_word (μ : Fin n → ℤ) (L : List (Matrix (Fin n) (Fin n) ℂ)) : ∀ z ∈ OmegaP n,
    evZ μ z ((L.map (actM (eMM μ))).prod (phiMM μ)) = hWord L (PhiP μ) z := by
  induction L with
  | nil => intro z hz; exact Set.indicator_of_mem hz _
  | cons Z L ih =>
    intro z hz
    set F := (L.map (actM (eMM μ))).prod (phiMM μ) with hF
    have h1 : ∀ a b, evZ μ z (eMM μ a b F) =
        fderiv ℂ (hWord L (PhiP μ)) z (z * Matrix.single a b 1) := fun a b => by
      have e : ((F : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ) =ᶠ[𝓝 z] hWord L (PhiP μ) :=
        eventually_of_mem (omegaP_mem_nhds hz) ih
      rw [← e.fderiv_eq]
      exact Set.indicator_of_mem hz _
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ← hF]
    show _ = fderiv ℂ (hWord L (PhiP μ)) z (z * Z)
    have hZ : z * Z = ∑ a, ∑ b, Z a b • (z * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ)) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp only [Matrix.mul_sum, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hZ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h1]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
end
end

noncomputable section

open Finset Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {M : Type*} [AddCommGroup M] [Module ℂ M]

def aF (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ D) (w0 : H)
    (g : Matrix (Fin n) (Fin n) ℂ) : V →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ w0) ∘ₗ (σ g : H →ₗ[ℂ] H) ∘ₗ D.subtype ∘ₗ V.subtype

def Xi (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ D) (w0 : H)
    (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ) (c' : Fin n)
    (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : KS (n := n) V →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun p => (ei X s c' p.2 * l (wB EM φ X s p.1)) • aF σ V w0 (ei X s)

theorem Xi_single (w0 : H) (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ) (c' : Fin n)
    (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    Xi σ V w0 EM φ l c' X s (Finsupp.single p v) =
      ei X s c' p.2 * l (wB EM φ X s p.1) * aF σ V w0 (ei X s) v := by
  simp [Xi]

theorem sA_single (hV : IsKStableSub ε E V) (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    sA ε E V hV a b (Finsupp.single p v) =
      (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) +
      (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) +
      (if p.2 = b then Finsupp.single (p.1, a) v else 0) := by
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lsingle_apply]
  congr 1
  · congr 1
    split_ifs <;> rfl
  · split_ifs <;> rfl

theorem deriv_aF (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (w0 : H)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) (v : V) :
    HasDerivAt (fun s => aF σ V w0 (ei X s) v)
      (-⟪w0, σ (ei X s) ((actM E X (v : D) : D) : H)⟫_ℂ) s := by
  have h := coef_deriv hσ hD (exp_smul_mem_UJset hX (-s)) hX w0 (v : D)
  rw [← sub_self s] at h
  have h2 := h.scomp s ((hasDerivAt_id s).const_sub s)
  refine HasDerivAt.congr_deriv (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
  · show ⟪w0, σ (ei X t) _⟫_ℂ = ⟪w0, σ (_ * NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) _⟫_ℂ
    rw [← exp_add_smul, show -s + (s - t) = -t by ring]; rfl
  · simp [ei]

theorem deriv_Xi (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKStableSub ε E V)
    (w0 : H) (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ) (c' : Fin n)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (s : ℝ) (y : KS (n := n) V) :
    HasDerivAt (fun s => Xi σ V w0 EM φ l c' X s y)
      (-(Xi σ V w0 EM φ l c' X s ((∑ a, ∑ b, X a b • sA ε E V hV a b) y))) s := by
  induction y using Finsupp.induction_linear with
  | zero => simpa using hasDerivAt_const s (0 : ℂ)
  | add y y' h h' =>
    simp only [map_add (f := _), neg_add]
    exact h.add h'
  | single p v =>
    simp only [Xi_single]
    refine ((((deriv_entries X 0 s c' p.2).1.mul (deriv_word EM φ X s p.1 l))).mul
      (deriv_aF hσ hD w0 hX.1 s v)).congr_deriv ?_
    set A := aF σ V w0 (ei X s) with hA
    set B := l (wB EM φ X s p.1) with hB
    have t1 : ∀ a b, Xi σ V w0 EM φ l c' X s
        (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) =
        ei X s c' p.2 * l (Finsupp.linearCombination ℂ (wB EM φ X s) (adLW a b p.1)) * A v := by
      intro a b
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Xi_single, Finsupp.linearCombination_apply, Finsupp.sum,
        smul_eq_mul, mul_sum, sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    have t2 : ∀ a b, X a b * Xi σ V w0 EM φ l c' X s
        (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) =
        ei X s c' p.2 * B * (X a b * ⟪w0, σ (ei X s) ((E a b (v : D) : D) : H)⟫_ℂ) := by
      intro a b
      split_ifs with h
      · rw [Xi_single]
        show _ * (_ * ⟪w0, σ (ei X s) ((E a b (v : D) : D) : H)⟫_ℂ) = _
        ring
      · simp [inK_apply_eq_zero hX h]
    have t3 : ∀ a b, Xi σ V w0 EM φ l c' X s (if p.2 = b then Finsupp.single (p.1, a) v else 0) =
        if p.2 = b then ei X s c' a * B * A v else 0 := by
      intro a b
      split_ifs
      · rw [Xi_single]
      · exact map_zero _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sA_single, map_add (f := _),
      smul_eq_mul, mul_add, sum_add_distrib, t1, t2, t3, mul_ite, mul_zero, sum_ite_eq, mem_univ,
      if_true, adX, actM, Submodule.coe_sum, Submodule.coe_smul, inner_sum, inner_smul_right,
      Matrix.mul_apply, Pi.mul_apply, ← mul_sum, ← hB]
    have u1 : ∑ a, ∑ b, X a b * (ei X s c' p.2 *
        l (Finsupp.linearCombination ℂ (wB EM φ X s) (adLW a b p.1)) * A v) =
        ei X s c' p.2 * (∑ a, ∑ b, X a b *
          l (Finsupp.linearCombination ℂ (wB EM φ X s) (adLW a b p.1))) * A v := by
      simp only [mul_sum, sum_mul]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    have u3 : ∑ a, X a p.2 * (ei X s c' a * B * A v) = (∑ a, ei X s c' a * X a p.2) * B * A v := by
      simp only [sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    rw [u1, u3]
    ring

theorem Xi_vanish (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) [FiniteDimensional ℂ V]
    (hV : IsKStableSub ε E V) (w0 : H) (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ)
    (c' : Fin n) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (W : Submodule ℂ (KS (n := n) V))
    (hW : IsKStableSub ε (sA ε E V hV) W) (h0 : ∀ y ∈ W, Xi σ V w0 EM φ l c' X 0 y = 0) (s : ℝ) :
    ∀ y ∈ W, Xi σ V w0 EM φ l c' X s y = 0 := by
  intro x hx
  set R := x.support.sup fun p => p.1.length with hR
  let S : Set (List (Fin n × Fin n) × Fin n) := {p | p.1.length ≤ R}
  have hSf : S.Finite := ((List.finite_length_le (Fin n × Fin n) R).prod Set.finite_univ).subset
    fun p hp => ⟨hp, trivial⟩
  have := hSf.to_subtype
  have : FiniteDimensional ℂ (Finsupp.supported V ℂ S) :=
    Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := V) (R := ℂ) S).symm
  have : FiniteDimensional ℂ (W ⊓ Finsupp.supported V ℂ S : Submodule ℂ _) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hS : ∀ a b, ∀ y ∈ Finsupp.supported V ℂ S, sA ε E V hV a b y ∈ Finsupp.supported V ℂ S := by
    intro a b y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finsupp.sum_single y, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun p hp => ?_
    have hpS : p.1.length ≤ R := hy hp
    rw [sA_single]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun w' hw' =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ ?_)) ?_) ?_
    · show w'.length ≤ R
      rw [adLW_length a b _ _ hw']; exact hpS
    · split_ifs
      · exact Finsupp.single_mem_supported ℂ _ hpS
      · exact Submodule.zero_mem _
    · split_ifs
      · exact Finsupp.single_mem_supported ℂ _ hpS
      · exact Submodule.zero_mem _
  have hA : ∀ y ∈ W ⊓ Finsupp.supported V ℂ S,
      (∑ a, ∑ b, X a b • sA ε E V hV a b) y ∈ W ⊓ Finsupp.supported V ℂ S := by
    intro y hy
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    by_cases h : ε a = ε b
    · exact Submodule.smul_mem _ _ ⟨hW a b h y hy.1, hS a b y hy.2⟩
    · rw [inK_apply_eq_zero hX h, zero_smul]; exact Submodule.zero_mem _
  have key := ode_zero ((∑ a, ∑ b, X a b • sA ε E V hV a b).restrict hA)
    (fun s => Xi σ V w0 EM φ l c' X s ∘ₗ (W ⊓ Finsupp.supported V ℂ S).subtype)
    (fun s y => deriv_Xi hσ hD hV w0 EM φ l c' hX s y) (LinearMap.ext fun y => h0 y y.2.1) s
  exact LinearMap.congr_fun key
    ⟨x, hx, fun p hp => Finset.le_sup (f := fun p : List (Fin n × Fin n) × Fin n => p.1.length) hp⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
end
end

noncomputable section

open Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def submoduleEvaluationFunctional {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H} (V : Submodule ℂ D)
    (w0 : V) : V →ₗ[ℂ] ℂ where
  toFun v := ⟪((w0 : D) : H), ((v : D) : H)⟫_ℂ
  map_add' x y := by simp [inner_add_right]
  map_smul' c x := by simp [inner_smul_right]

theorem lowestKType_vector_exists (ε : Fin n → Bool) (lam : Fin n → ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (T : KType ε (lowK ε lam)) (ι : V ≃ₗ[ℂ] T.V)
    (hιK : ∀ (k : KG ε) (v w : V), ((w : D) : H) = σ (toMK k) ((v : D) : H) → ι w = T.op k (ι v)) :
    IsKHWVec ε E (lowK ε lam) ((ι.symm T.w : V) : D) := by
  have := hV.1
  have hVK : ∀ (k : KG ε) (v : V), ∃ w : V, ((w : D) : H) = σ (toMK k) ((v : D) : H) := by
    intro k v
    obtain ⟨Z, hZ, he⟩ := HW.exists_log ε k
    have hs := KTypeIsomorphism.orbit_hasSum hσ hD hV.1 hV.2.1 hZ v
    let P : Submodule ℂ H := LinearMap.range (D.subtype ∘ₗ V.subtype)
    have hmem : σ (NormedSpace.exp Z) ((v : D) : H) ∈ P :=
      P.closed_of_finiteDimensional.mem_of_tendsto hs (Filter.Eventually.of_forall fun t =>
        P.sum_mem fun m _ => P.smul_mem _ ⟨_, rfl⟩)
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, by rw [he]; exact hw⟩
  let L : T.V →L[ℂ] H := LinearMap.toContinuousLinearMap (D.subtype ∘ₗ V.subtype ∘ₗ ι.symm.toLinearMap)
  have hK : ∀ X, inK ε X → ((actM E X ((ι.symm T.w : V) : D) : D) : H) = L (T.dτ X T.w) := by
    intro X hX
    obtain ⟨γ, hγ⟩ := HW.exists_curve ε hX
    have h1 := ((L.comp (ContinuousLinearMap.apply ℂ T.V T.w)).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (T.hasDeriv X hX γ hγ)
    refine (hD.deriv X hX.1 _).unique (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
    obtain ⟨w, hw⟩ := hVK (γ t) (ι.symm T.w)
    have h2 := hιK (γ t) _ w hw
    rw [ι.apply_symm_apply] at h2
    show σ _ _ = ((ι.symm (T.op (γ t) T.w) : D) : H)
    rw [← h2, ι.symm_apply_apply, hw, hγ]
  have hC : ∀ a b, ε a = ε b →
      ((E a b ((ι.symm T.w : V) : D) : D) : H) = L (T.dτ (Matrix.single a b 1) T.w) := by
    intro a b hab
    have hZ : (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
      ext i j
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
      split_ifs with h <;> simp_all
    have hJ : Jm ε * Jm ε = 1 := by
      rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp
    have hJh : (Jm ε).conjTranspose = Jm ε := by
      rw [Jm, Matrix.diagonal_conjTranspose]; congr 1; funext i
      simp only [Pi.star_apply]; split_ifs <;> simp
    have hZ' : Jm ε * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * Jm ε =
        Jm ε * (Jm ε * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε) := by
      have := congrArg Matrix.conjTranspose hZ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh] at this
      rw [Matrix.mul_assoc _ (Jm ε) (Jm ε), hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        hJ, Matrix.one_mul, this]
    have k1 : inK ε (cpart1 ε (Matrix.single a b 1)) := ⟨ta_inG_cpart1 ε _, by
      simp only [cpart1, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, hZ, hZ']⟩
    have k2 : inK ε (cpart2 ε (Matrix.single a b 1)) := ⟨ta_inG_cpart2 ε _, by
      simp only [cpart2, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hZ, hZ']⟩
    rw [← TRA.actM_single E a b, TRA.act_cpart (ε := ε), Submodule.coe_add, Submodule.coe_smul,
      hK _ k1, hK _ k2]
    conv_rhs => rw [← ta_cpart_sum ε (Matrix.single a b 1), map_add (f := _), map_smul, _root_.add_apply,
      _root_.smul_apply, map_add, map_smul]
  refine ⟨fun a => Subtype.ext ?_, fun a b hab he => Subtype.ext ?_⟩
  · rw [hC a a rfl, T.w_wt a, map_smul]; rfl
  · rw [hC a b he, T.w_hw a b hab he, map_zero]; rfl

theorem lowestKType_trace_integral (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (ι : V ≃ₗ[ℂ] T.V) (hμ : IsMu lam μ)
    (hcoef : ∀ g : Matrix (Fin n) (Fin n) ℂ, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', PsiM T μ g (ι v)⟫_ℂ)
    (W : Submodule ℂ (KS (n := n) V)) (hW : IsKStableSub ε (sA ε E V hV.2.1) W)
    (hθ : ∀ x ∈ W, sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) x = 0) :
    ∀ x ∈ W, sT E V x = 0 := by
  have := hV.1
  intro x hx
  funext c
  set w0 : H := (((ι.symm T.w : V) : D) : H) with hw0
  have hsT : sT E V x c = ∑ p ∈ x.support, if p.2 = c then wordE E p.1 (x p : D) else 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← Finsupp.sum_single x, Finsupp.sum, map_sum, Finset.sum_apply]
    refine sum_congr rfl fun p _ => ?_
    rw [show p = (p.1, p.2) from rfl, sT_single, Pi.single_apply]
    simp only [eq_comm]
  have hword : ∀ w : List (Fin n × Fin n),
      ((w.map fun p => (Matrix.single p.1 p.2 1 : Matrix (Fin n) (Fin n) ℂ)).map (actM E)).prod =
        wordE E w := fun w => by
    rw [List.map_map, wordE]; congr 2; funext p; exact TRA.actM_single E p.1 p.2
  have h1J : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
    show (1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * 1 = Jm ε
    simp
  refine TRA.eq_zero_of_coef hσ hD (V := V) ?_ fun g hg v' => ?_
  · rw [hsT]
    refine Submodule.sum_mem _ fun p _ => ?_
    split_ifs
    · generalize p.1 = w
      induction w with
      | nil => exact Submodule.mem_sInf.mpr fun S hS => hS.1 (x p).2
      | cons q w ih => exact Submodule.mem_sInf.mpr fun S hS => hS.2 _ _ _ (Submodule.mem_sInf.mp ih S hS)
    · exact Submodule.zero_mem _
  let e := x.support.equivFin
  have hsum : ∀ F : List (Fin n × Fin n) × Fin n → ℂ, ∑ i, F (e.symm i) = ∑ p ∈ x.support, F p :=
    fun F => by rw [Equiv.sum_comp e.symm (fun p : x.support => F p), Finset.sum_coe_sort]
  have key := transfer n ε lam T μ ⟨hanti, hint⟩ hμ _
    (fun i => (e.symm i).1.1.map fun p => (Matrix.single p.1 p.2 1 : Matrix (Fin n) (Fin n) ℂ))
    (fun i => if (e.symm i).1.2 = c then ι (x (e.symm i)) else 0) ?_ g hg
  · have h2 := congrArg (fun u => ⟪ι v', u⟫_ℂ) key
    simp only [inner_sum, inner_zero_right] at h2
    rw [hsum fun p => ⟪ι v', rWord ε (p.1.map fun q =>
      (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ)) (PsiM T μ) g
        (if p.2 = c then ι (x p) else 0)⟫_ℂ] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsT, ← h2, Submodule.coe_sum, map_sum, inner_sum]
    refine sum_congr rfl fun p _ => ?_
    split_ifs
    · rw [TRA.rWord_coef hσ hD ι _ hcoef _ g hg, hword]
    · simp
  intro k z hz
  obtain ⟨X, hX, he⟩ := HW.exists_log ε k
  have he1 : NormedSpace.exp (((1 : ℝ) : ℂ) • X) = toMK k := by rw [he]; simp
  have hinv : toMK k * TRA.ei X 1 = 1 := by
    rw [← he1, TRA.ei, ← exp_add_smul]; simp
  have hki : toMK k⁻¹ = TRA.ei X 1 := by
    rw [← Matrix.mul_one (toMK k⁻¹), ← hinv, ← Matrix.mul_assoc, toMK_inv_mul', Matrix.one_mul]
  have hXi : ∀ c', TRA.Xi σ V w0 (eMM μ) (phiMM μ) (TRA.evZ μ z) c' X 1 x = 0 := fun c' =>
    TRA.Xi_vanish hσ hD hV.2.1 w0 _ _ _ c' hX W hW (fun y hy => by
      have h0 : ∀ y, TRA.Xi σ V w0 (eMM μ) (phiMM μ) (TRA.evZ μ z) c' X 0 y =
          TRA.evZ μ z (sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) y c') := by
        intro y
        induction y using Finsupp.induction_linear with
        | zero => simp
        | add y y' h h' => simp only [map_add (f := _), Pi.add_apply, h, h']
        | single p v =>
          have e0 : TRA.ei X 0 = 1 := by simp [TRA.ei]
          have e1 : TRA.wB (eMM μ) (phiMM μ) X 0 p.1 = wordE (eMM μ) p.1 (phiMM μ) := by
            simp [TRA.wB, TRA.cj, e0, TRA.actM_single, wordE]
          have e2 : TRA.aF σ V w0 1 v = submoduleEvaluationFunctional V (ι.symm T.w) v := by
            show ⟪w0, σ 1 _⟫_ℂ = _
            rw [hσ.1.1]; rfl
          rw [TRA.Xi_single, e0, e1, e2, show p = (p.1, p.2) from rfl, sθ_single, Pi.single_apply,
            Matrix.one_apply]
          split_ifs <;> simp [mul_comm]
      rw [h0, hθ y hy, Pi.zero_apply, map_zero]) 1 x hx
  let a : List (Fin n × Fin n) × Fin n → ℂ := fun p => ⟪T.op k T.w, ι (x p)⟫_ℂ *
    hWord (adW ε k (p.1.map fun q => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))) (PhiP μ) z
  have hXa : ∀ c', ∑ p ∈ x.support, TRA.ei X 1 c' p.2 * a p = 0 := fun c' => by
    rw [← hXi c']
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← Finsupp.sum_single x, Finsupp.sum, map_sum]
    refine sum_congr rfl fun p _ => ?_
    have e1 : TRA.evZ μ z (TRA.wB (eMM μ) (phiMM μ) X 1 p.1) = hWord (adW ε k (p.1.map fun q =>
        (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))) (PhiP μ) z := by
      rw [← TRA.evZ_word μ _ z hz, adW, List.map_map, List.map_map, hki, ← he1]; rfl
    have e2 : TRA.aF σ V w0 (TRA.ei X 1) (x p) = ⟪T.op k T.w, ι (x p)⟫_ℂ := by
      have hP : PsiM T μ (toMK k⁻¹) = T.op k⁻¹ := by
        have := psiM_equiv T μ k⁻¹ 1 h1J
        rwa [toMK_one', Matrix.mul_one, Matrix.mul_one, psiM_one, op_one', mul_one, mul_one] at this
      have h3 := hcoef (toMK k⁻¹) (k⁻¹).1.2 (x p) (ι.symm T.w)
      rw [ι.apply_symm_apply, hP] at h3
      rw [← hki]
      refine h3.trans ?_
      have hu : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).2
      have h4 : T.op k⁻¹ = star (T.op k) := by
        rw [← one_mul (T.op k⁻¹), ← hu, mul_assoc, ← op_mul', mul_inv_cancel, op_one', mul_one]
      rw [h4, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    rw [TRA.Xi_single, e1, e2]
    simp only [a]; ring
  rw [hsum fun p => ⟪T.op k T.w, if p.2 = c then ι (x p) else 0⟫_ℂ *
    hWord (adW ε k (p.1.map fun q => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))) (PhiP μ) z]
  calc _ = ∑ p ∈ x.support, (toMK k * TRA.ei X 1) c p.2 * a p := sum_congr rfl fun p _ => by
        rw [hinv, Matrix.one_apply]
        by_cases h : p.2 = c
        · simp [h, a]
        · simp [h, Ne.symm h]
    _ = ∑ c', toMK k c c' * ∑ p ∈ x.support, TRA.ei X 1 c' p.2 * a p := by
        simp only [Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]
        exact sum_comm
    _ = 0 := by simp [hXa]

theorem lowestKType_trace (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (hgap : GapLap ε lam h) (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε)
    (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (ι : V ≃ₗ[ℂ] T.V) (hμ : IsMu lam μ)
    (hιK : ∀ (k : KG ε) (v w : V), ((w : D) : H) = σ (toMK k) ((v : D) : H) → ι w = T.op k (ι v))
    (hcoef : ∀ g : Matrix (Fin n) (Fin n) ℂ, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', PsiM T μ g (ι v)⟫_ℂ)
    (W : Submodule ℂ (KS (n := n) V)) (hW : IsKStableSub ε (sA ε E V hV.2.1) W)
    (hθ : ∀ x ∈ W, sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) x = 0) :
    ∀ x ∈ W, sT E V x = 0 := by
  exact lowestKType_trace_integral ε lam H σ D E V hσ hD hV hint hanti T μ ι hμ hcoef W hW hθ

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
