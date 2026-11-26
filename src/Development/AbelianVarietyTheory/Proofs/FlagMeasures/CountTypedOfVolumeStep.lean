module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableOfSupport
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneTypeArith
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCountingOfFiniteAndBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDimensionalRowsSpaceDiscreteSeriesCount
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductio
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRat
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointKernelBoundOfPointwiseBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalCuspidalIsometricIntertwiners
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalCuspidalIsometricIntertwiners
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspFrameOneType

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨(Formalism.UG.stabGL I.Lf).one_mem, fun y _ => ⟨0, I.Lf.zero_mem, ?_⟩⟩
  have : I.fmat 1 = 1 := rfl
  simp [this]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hinv, -⟩ := B.e_adm
  obtain ⟨-, hT⟩ := B.Re_spec
  have p1 : (fun g : B.I.Gf => B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  exact GlobalTheory.IdemProj.op_fixed B.μf (fun g => B.R (1, g)) p1 pm pn B.e B.Re hT k
    (fun x => by simpa using hinv x k hk 1 (one_mem_Kg B.I B.g))

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := _root_.GlobalTheory.Dec.CuspAll.integrable_ph B d h hd hl hb

theorem cuspidal_frame : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∃ Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund, B.I.IsRConv B.μf B.fund B.R (phe B d) Rφ ∧ ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames.IsCuspidalFrame B Rφ T := by
  intro B d h hd hS _ hgap hl hb hfin
  obtain ⟨-, hcomm, ⟨Rφ, hR⟩, hP⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hl hb)
  obtain ⟨hproj, hfix, hex, -, -⟩ := hP Rφ hR
  obtain ⟨hU, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hle : B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R := by
    rintro _ ⟨A, hA, rfl⟩ g
    show (B.Re.comp A).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  obtain ⟨T, hT, hn, ho, hsp⟩ := GlobalTheory.IntertwinerFrame.exists_orthonormal_frame B d hd hfin hle
  obtain ⟨S, hSm, hScl, hSst, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  refine ⟨Rφ, hR, T, hT, fun i => hle (hT i), hn, ho, hsp, fun i u => ?_, fun i u k hk => ?_, ?_, ?_⟩
  · have hw' : T i (B.tens B.w) ∈ S := by
      rw [hSm, ← hfix _ (hT i)]
      exact (GlobalTheory.T.convolution_range_cuspidal_of_lowestKType B d h hd hS hgap hl hb hfin Rφ hR _).2
    have hcl : IsClosed ((S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) : Submodule ℂ B.Hs) : Set B.Hs) :=
      hScl.preimage (T i).continuous
    rcases hirr _ hcl (fun g v hv => by
      have e := congrArg (fun A : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => A v) (hle (hT i) g)
      simp only [ContinuousLinearMap.comp_apply] at e
      show T i (B.σs g v) ∈ S
      rw [e]
      exact hSst _ _ hv) with h0 | h0
    · have : B.tens B.w ∈ S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := hw'
      rw [h0, Submodule.mem_bot] at this
      rw [this] at hw
      simp at hw
    · have : u ∈ S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := by rw [h0]; trivial
      exact (hSm _).1 this
  · obtain ⟨A, -, hA⟩ := hT i
    rw [← hA]
    exact congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C (A u)) (re_fixed B k hk)
  · exact ⟨fun i => by rw [hn, hw], fun i j hij => ho i j hij _ _⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨_, hfix _ (hT i)⟩
    · rintro _ ⟨z, rfl⟩
      have hz : Rφ (Rφ z) = Rφ z :=
        congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C z) hproj.1
      obtain ⟨A, ⟨hA, hAw⟩, -⟩ := hex _ hz
      rw [← hsp] at hA
      have := Submodule.mem_map_of_mem
        (f := (ContinuousLinearMap.apply ℂ (B.I.L2 B.μf B.fund) (B.tens B.w)).toLinearMap) hA
      rw [Submodule.map_span, ← Set.range_comp] at this
      show Rφ z ∈ _
      rw [← hAw]
      exact this

end GlobalTheory.Dec.CuspFrameOneType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalCuspidalIsometricIntertwinersStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_cuspidal_isometric_intertwiners : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∃ Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund, B.I.IsRConv B.μf B.fund B.R (phe B d) Rφ ∧ ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames.IsCuspidalFrame B Rφ T := by
  first | exact @GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame | exact GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame | (intros; apply GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KerDiagBasisIndep
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem kerDiag_expand {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y : Fin D → H) (hy : Orthonormal ℂ y) (v : H) (hv : v ∈ Submodule.span ℂ (Set.range y)) :
    v = ∑ i, ⟪y i, v⟫_ℂ • y i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy.inner_right_fintype]

theorem kerDiag_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y y' : Fin D → H) (hy : Orthonormal ℂ y) (hy' : Orthonormal ℂ y') (a b : Fin D → ℂ)
    (hb : ∀ j, b j = ∑ i, ⟪y i, y' j⟫_ℂ * a i) :
    ∑ j, ‖b j‖ ^ 2 ≤ ∑ i, ‖a i‖ ^ 2 := by
  set u : H := ∑ i, (starRingEnd ℂ) (a i) • y i with hu
  have h1 : ∀ j, ‖b j‖ = ‖⟪y' j, u⟫_ℂ‖ := by
    intro j
    rw [norm_inner_symm, hb, hu, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, Complex.conj_conj, mul_comm]
  have h2 : ‖u‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
    have h3 : ⟪u, u⟫_ℂ = ∑ i, ((‖a i‖ ^ 2 : ℝ) : ℂ) := by
      rw [hu, hy.inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [inner_self_eq_norm_sq_to_K] at h3
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, ← h3, Complex.ofReal_pow]
    rfl
  simp only [h1]
  rw [← h2]
  exact hy'.sum_inner_products_le u

theorem kerDiag_add_rep (B : RowsAut) (F F' : B.I.L2 B.μf B.fund) (f f' : B.I.GA → ℂ) (c : ℂ)
    (h : IsContRep B F f) (h' : IsContRep B F' f') :
    IsContRep B (F + c • F') (fun x => f x + c * f' x) := by
  refine ⟨h.1.add (continuous_const.mul h'.1), fun γ hγ x => ?_, ?_⟩
  · simp only [h.2.1 γ hγ x, h'.2.1 γ hγ x]
  · filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', h.2.2, h'.2.2] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

theorem kerDiag_sum_rep (B : RowsAut) {ι : Type} (s : Finset ι) (y : ι → B.I.L2 B.μf B.fund)
    (f : ι → B.I.GA → ℂ) (c : ι → ℂ) (F : B.I.L2 B.μf B.fund) (g : B.I.GA → ℂ)
    (hg : IsContRep B F g) (h : ∀ i, IsContRep B (y i) (f i)) :
    IsContRep B (F + ∑ i ∈ s, c i • y i) (fun x => g x + ∑ i ∈ s, c i * f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have := kerDiag_add_rep B _ _ _ _ (c a) ih (h a)
    simp only [Finset.sum_insert ha]
    convert this using 1
    · abel
    · funext x; ring

theorem kerDiag_vals (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund)
    (f f' : Fin D → B.I.GA → ℂ) (hy : Orthonormal ℂ y)
    (hs : Submodule.span ℂ (Set.range y') ≤ Submodule.span ℂ (Set.range y))
    (h : ∀ i, IsContRep B (y i) (f i)) (h' : ∀ i, IsContRep B (y' i) (f' i)) (j : Fin D)
    (x : B.I.GA) : f' j x = ∑ i, ⟪y i, y' j⟫_ℂ * f i x := by
  have e := kerDiag_expand y hy (y' j) (hs (Submodule.subset_span ⟨j, rfl⟩))
  have h1 := kerDiag_sum_rep B Finset.univ y f (fun i => ⟪y i, y' j⟫_ℂ) _ _ (h' j) h
  rw [← e] at h1
  have h2 := kerDiag_add_rep B _ _ _ _ 1 (h' j) (h' j)
  rw [one_smul] at h2
  have h3 := congrFun ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B _ _ h2).2.1 _ h1) x
  simp only [one_mul, add_right_inj] at h3
  exact h3.symm

theorem kerDiag_basis_indep : ∀ (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund) (f f' : Fin D → B.I.GA → ℂ), Orthonormal ℂ y → Orthonormal ℂ y' → Submodule.span ℂ (Set.range y) = Submodule.span ℂ (Set.range y') → (∀ i, IsContRep B (y i) (f i) ∧ IsContRep B (y' i) (f' i)) → ∀ x, ∑ i, ‖f i x‖ ^ 2 = ∑ i, ‖f' i x‖ ^ 2 := by
  intro B D y y' f f' hy hy' hs h x
  apply le_antisymm
  · exact kerDiag_le y' y hy' hy _ _ fun j =>
      kerDiag_vals B D y' y f' f hy' hs.le (fun i => (h i).2) (fun i => (h i).1) j x
  · exact kerDiag_le y y' hy hy' _ _ fun j =>
      kerDiag_vals B D y y' f f' hy hs.ge (fun i => (h i).1) (fun i => (h i).2) j x

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointKernelBoundOfPointwiseBound
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepKernel

theorem deep_kernel_bound_of_ptBound : PtBound →
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound := by
  intro hP hF Cg n₀ B d p q b c x _ hn hq hC hc hx
  obtain ⟨-, -, -, -, -, hqn, hrk, hmin, -, -, -, -, h, -, hgap, h40, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn hC
  have hD : IsDSData B d := hC.1
  have hg : 1 ≤ B.g := hC.2.2.2.2.2.2.2.2.2.1
  have hS := GlobalTheory.T.isKTypeOf_lowK_of_countHyp B Cg n₀ d p q b hn hC
  have hfin := hF B Cg n₀ d p q b hn hC
  have hloc : LocDec B h := (hP B d p q h hD hC.2.1 hgap (by rw [hmin]; exact h120)).2.2.2.2.2.2
  obtain ⟨Rφ, hR, T, -, hT2, hT3, -, -, hT6, hT7, hT8, hT9⟩ :=
    GlobalTheory.T.exists_orthonormal_cuspidal_isometric_intertwiners B d h hD hS hg (fun v => by rw [hrk v]; exact h120) hloc h40 hfin
  choose Fr hFr using fun i => GlobalTheory.T.exists_continuousRowRepresentatives_lowestKType B d hD hS hg (T i) (hT2 i) (hT7 i)
  obtain ⟨y, Fc, hy, hsp, hFc, hk, -⟩ := GlobalTheory.KernelExpansion.kernelB B d h hD (by omega) hloc h32 hfin Rφ hR
  have hw := (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hD 0).1
  have e := GlobalTheory.Dec.kerDiag_basis_indep B B.D y (fun i => T i (B.tens B.w)) Fc (fun i => Fr i (B.tens B.w))
    hy hT8 (hsp.trans hT9.symm) (fun i => ⟨hFc i, (hFr i 0 _ hw).1⟩) x
  have e2 : (kern B.I (phe B d) x x).re = ‖vv B Fr (B.tens B.w) x‖ ^ 2 := by
    rw [hk, EuclideanSpace.norm_sq_eq, Complex.re_sum]
    simp only [vv]
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [e2]
  exact GlobalTheory.T.deepPoint_bound_cuspidalIsometricIntertwinerFamily B Cg n₀ d p q b c x B.D T Fr hn hq hC hc hx hFr hT3 hT6

end GlobalTheory.DeepKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointKernelBoundOfPointwiseBoundStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deepPointKernelBound_of_pointwiseBound : PtBound → (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) → GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound := by
  first | exact @GlobalTheory.DeepKernel.deep_kernel_bound_of_ptBound | exact GlobalTheory.DeepKernel.deep_kernel_bound_of_ptBound | (intros; apply GlobalTheory.DeepKernel.deep_kernel_bound_of_ptBound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBound
open MeasureTheory NumberField Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.DeepRegion

theorem one_le_f (I : AutInst) : 1 ≤ I.f := by
  show 0 < Module.finrank ℚ I.F
  exact Module.finrank_pos

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  have hd : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
    have h0 : discr I.E ≠ 0 := discr_ne_zero I.E
    have : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs h0
    exact_mod_cast this
  exact Real.one_le_rpow hd (by positivity)

theorem deepBound (hV : GlobalTheory.FlagMeas.AbsoluteVolume) (hK : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound) :
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound := by
  intro Cg hCg
  refine ⟨8, ?_⟩
  intro B d p q b hq hH
  obtain ⟨hDS, hSig, hn0, hqn, hrd, hf, hb, hbb, hlam, hg1, hgb, hg0p, hg0, hsplit, hgap⟩ := id hH
  have hgc : ∀ v, ∃ c : ℝ, 0 < c ∧ IsGauge (B.I.ε v) c := fun v => by
    obtain ⟨c, hc, hc', -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)
    exact ⟨c, hc, hc'⟩
  choose c hc0 hc using hgc
  have hn8 : 8 ≤ B.I.n := hn0
  have hf1 : 1 ≤ B.I.f := one_le_f B.I
  have hrd1 : 1 ≤ B.I.rd := one_le_rd B.I
  have hnR : (8 : ℝ) ≤ B.I.n := by exact_mod_cast hn8
  have hfR : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf1
  have hgR : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b := ⟨_, rfl⟩
  have a1 : (8 : ℝ) ≤ B.I.n * B.I.f := by nlinarith
  have a2 : (8 : ℝ) ≤ B.I.n * B.I.f * B.g := by nlinarith
  have a3 : (16 : ℝ) ≤ B.I.n * B.I.f * B.g * b := by nlinarith
  have hXe : X = B.I.rd * (B.I.n * B.I.f * B.g * b) := by rw [hX]; ring
  have hX16 : 16 ≤ X := by rw [hXe]; nlinarith
  have hXrd : B.I.rd ≤ X := by rw [hXe]; nlinarith
  have hXf : 2 * B.I.f * B.I.rd ≤ X := by
    have : 2 * (B.I.f : ℝ) ≤ B.I.n * B.I.f * B.g * b := by nlinarith
    rw [hXe]; nlinarith
  have hXsq : 2 * B.I.f * B.I.rd ≤ X ^ 2 := by nlinarith
  have hVol := hV B.I p q (by first | exact hSig | exact fun v => hSig v) hqn hn8 X (by linarith) hXrd hXsq
    c B.μf (by first | exact hc | exact fun v => ⟨hc0 v, hc v⟩ | exact fun v => ⟨hc v, hc0 v⟩)
  obtain ⟨hKs, hKg0, hKsT⟩ := GlobalTheory.CongIndex.measure_Kset_le B.I B.μf B.g hg1
  obtain ⟨hcov, -⟩ := GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter B.I B.μf B.fund Set.univ B.fund_spec MeasurableSet.univ
    (fun _ _ _ _ => trivial)
  rw [Set.univ_inter] at hcov
  change ENNReal.ofReal (∏ v, c v) * _ / B.μf B.I.Kset ≤ _ at hVol
  rw [hcov] at hVol
  set N : ℕ := B.I.n ^ 2 * B.I.f with hN
  set P : ℝ := ∏ v, c v with hP
  have hP0 : 0 < P := Finset.prod_pos fun v _ => hc0 v
  have hKgT : B.μf (B.I.Kg B.g) ≠ ⊤ :=
    ne_top_of_le_ne_top hKsT.ne (measure_mono fun x hx => hx.1)
  set kR : ℝ := (B.μf (B.I.Kg B.g)).toReal with hkR
  have hkR0 : 0 < kR := ENNReal.toReal_pos hKg0.ne' hKgT
  have hX0 : 0 < X := by linarith
  have hg0' : (0 : ℝ) < B.g := by linarith
  have hm0 : B.μf B.I.Kset ≠ 0 := (lt_of_lt_of_le hKg0 (measure_mono fun x hx => hx.1)).ne'

  have hF : B.I.muA B.μf B.fund ≤ ENNReal.ofReal (X ^ N * (B.g : ℝ) ^ (2 * N) * kR / P) := by
    have h1 : ENNReal.ofReal P * B.I.muA B.μf B.fund ≤ ENNReal.ofReal (X ^ N) * B.μf B.I.Kset :=
      (ENNReal.div_le_iff hm0 hKsT.ne).1 hVol
    have h2 : B.μf B.I.Kset ≤ ENNReal.ofReal ((B.g : ℝ) ^ (2 * N) * kR) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hKgT, ENNReal.ofReal_pow hg0'.le,
        ENNReal.ofReal_natCast]
      exact hKs
    have h3 : ENNReal.ofReal P * B.I.muA B.μf B.fund ≤
        ENNReal.ofReal (X ^ N * ((B.g : ℝ) ^ (2 * N) * kR)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      exact h1.trans (by gcongr)
    rw [ENNReal.ofReal_div_of_pos hP0, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hP0))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm, ← mul_assoc]
    simpa [mul_assoc] using h3

  set Kc : ℝ := Real.exp (-(N : ℝ)) / ((B.g : ℝ) ^ (2 * N) * X ^ N) * B.D * P / kR with hKc
  have hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b,
      ENNReal.ofReal (kern B.I (phe B d) x x).re ≤ ENNReal.ofReal Kc := by
    intro x hx
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, Set.mem_setOf_eq] at hx
    apply ENNReal.ofReal_le_ofReal
    have hτ0 : 0 < least B.I x :=
      ((GlobalTheory.T.canonicalLatticeFiltration_size_properties B.I x 1 one_pos).2.2.2.2.2.2.2.2 (by omega)).1
    have hτle : least B.I x ≤ ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b)⁻¹ ^ (11 * q) := hx.2.le
    have hk := hK Cg 8 B d p q b c x hCg le_rfl hq hH hc hx.2
    have he := (GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn8 hf1 hq hqn
      hrd1 hb hgR hτ0 hτle).2
    have hN' : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B = N := rfl
    have hst : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * N + N) =
        √(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe
      have : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) = B.I.n * √(B.I.n : ℝ) := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by positivity), Real.rpow_one]
      rw [this]; push_cast; ring
    rw [hN', hst] at hk
    rw [hX] at hKc
    have hA : ((2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * √(B.I.f : ℝ) *
          (√(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ))) ^
            (16 * q * N) *
          (6 * (√(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
            3 * ((8 * q * N + N : ℕ) : ℝ))) ^ N *
          Real.exp B.I.f * (17 * √(B.I.n : ℝ) / least B.I x ^ 2) ^ (2 * N)) *
          ((B.g : ℝ) ^ (2 * N) * ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b) ^ N) ≤
          Real.exp (-(N : ℝ)) := by
      rw [show 16 * q * N = 2 * (8 * q * N) by ring]
      refine le_of_eq_of_le ?_ he
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh]
      ring
    have hD : (0 : ℝ) ≤ B.D := Nat.cast_nonneg _
    refine hk.trans ?_
    rw [hKc]
    have hpos : 0 < (B.g : ℝ) ^ (2 * N) * ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b) ^ N := by
      rw [← hX]; positivity
    gcongr
    rw [le_div_iff₀ hpos]
    exact hA
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b, ENNReal.ofReal (kern B.I (phe B d) x x).re ∂(B.I.muA B.μf)
      ≤ ∫⁻ _ in GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b, ENNReal.ofReal Kc ∂(B.I.muA B.μf) := by
        first
          | exact setLIntegral_mono measurable_const hpt
          | exact lintegral_mono_ae ((ae_restrict_iff' (by
              simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet]; exact (measurableSet_eq_fun_of_countable
                measurable_const measurable_const))).2 (Filter.Eventually.of_forall hpt))
    _ = ENNReal.ofReal Kc * B.I.muA B.μf (GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal Kc * B.I.muA B.μf B.fund := by
        gcongr
        intro x hx
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, Set.mem_setOf_eq] at hx
        exact hx.1
    _ ≤ ENNReal.ofReal Kc * ENNReal.ofReal (X ^ N * (B.g : ℝ) ^ (2 * N) * kR / P) := by gcongr
    _ = ENNReal.ofReal ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) := by
        rw [← ENNReal.ofReal_mul (by rw [hKc]; positivity)]
        congr 1
        rw [hKc, hN]
        push_cast
        field_simp

end GlobalTheory.DeepRegion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBoundStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deepRegion_kernelDiagonal_bound : GlobalTheory.FlagMeas.AbsoluteVolume → GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound → GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound := by
  first | exact @GlobalTheory.DeepRegion.deepBound | exact GlobalTheory.DeepRegion.deepBound | (intros; apply GlobalTheory.DeepRegion.deepBound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagRareOfNonzeroFlagBound
open MeasureTheory Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FlagRareProof

theorem flagRare_of_nonzeroFlagBound : GlobalTheory.FlagMeas.NonzeroFlagBound → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare := by
  intro h
  refine ⟨⌈Real.exp 15⌉₊, ?_⟩
  intro B p q hsig hn hq hrd hf

  have hn' : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 hn
  have hn1 : 1 ≤ B.I.n := by
    have : 0 < ⌈Real.exp 15⌉₊ := Nat.ceil_pos.2 (Real.exp_pos 15)
    omega
  have hlog : 15 ≤ Real.log B.I.n := by
    have := Real.log_le_log (Real.exp_pos 15) hn'
    rwa [Real.log_exp] at this
  have key := h B.I B.μf B.fund B.fund_spec p q hsig hlog hq hrd hf

  have hset : {x | least B.I x < 1 / 2} = {x | stepLt B.I x (1 / 2) ≠ ⊥} := by
    ext x
    have hx := ((GlobalTheory.CountSteps.steps B.I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn1).2.2
    simp only [Set.mem_ofPred_eq, ne_eq, hx, not_le]
  have hnf : 0 ≤ (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  rw [prob, hset, Formalism.MainNotions.S.AutInst.vol, ← ENNReal.toReal_div]
  calc _ ≤ Real.exp (-(1 / 3 * (B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
        ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le key
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.FlagRareProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FarTermsModerateRegionOfFlagBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapThresholdPaysFarTerms
open Matrix Finset Real

namespace GlobalTheory

private theorem log_le_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h1 : Real.log (Real.sqrt x / 2) ≤ Real.sqrt x / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (Real.sqrt x / 2) = Real.log (Real.sqrt x) - Real.log 2 :=
    Real.log_div hs.ne' (by norm_num)
  have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← hx2]
    rw [Real.log_pow]
    push_cast
    ring
  have h4 := Real.log_two_lt_d9
  linarith


set_option maxHeartbeats 800000 in
theorem gap_threshold_pays_far_terms : ∀ (Cg : ℝ) (n f q : ℕ) (rd g b : ℝ) (h t : ℝ), 0 ≤ Cg → 3 ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ g → g ≤ b ^ Cg → 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h → ((n : ℝ) * f * rd * g * b)⁻¹ ^ (11 * q) ≤ t → t ≤ 1 / 2 → let ep : ℝ := 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2); 64 * (n : ℝ) ^ 2 ≤ h * ep ∧ 1 ≤ h * ep ^ 2 / 16 ∧ (3 * Real.sqrt n / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-(h * ep ^ 2 / 16))) ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := by
  intro Cg n f q rd g b h t hCg hn hf hq hqn hrd hlogf hb hg1 hgb hh ht1 _ht2 ep
  have hep : ep = 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) := rfl
  clear_value ep
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hqnR : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hf0 : (f : ℝ) ≠ 0 := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hfpos : (0 : ℝ) < f := by linarith
  set s := Real.sqrt (n : ℝ) with hs_def
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith)
  have hsn : s ≤ n := by nlinarith
  have hqs : (q : ℝ) ≤ s := (Real.le_sqrt (by positivity) (by linarith)).2 hqnR
  set ℓ := Real.log (b * rd) with hℓ_def
  have hbrd : 2 ≤ b * rd := le_trans hb (le_mul_of_one_le_right (by linarith) hrd)
  have hℓ : 0.69 ≤ ℓ := by
    have e1 := Real.log_le_log (by norm_num) hbrd
    have e2 := Real.log_two_gt_d9
    linarith
  have hlogb : Real.log b ≤ ℓ := Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith) hrd)
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hKl : 2.76 ≤ (Cg + 4) * ℓ := by nlinarith [mul_nonneg hCg (by linarith : (0 : ℝ) ≤ ℓ)]

  have hX : 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ ≤ h * ep ^ 2 / 16 := by
    have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep ^ 2 / 16
        = 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ := by
      rw [hep]
      field_simp
      norm_num
    rw [← e]
    have := mul_le_mul_of_nonneg_right hh (sq_nonneg ep)
    linarith
  have hn3f : 1 ≤ (n : ℝ) ^ 3 * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hfR
  refine ⟨?_, ?_, ?_⟩
  · have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep
        = 800000000 * ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) := by
      rw [hep]
      field_simp
      norm_num
    have hep0 : 0 ≤ ep := by rw [hep]; positivity
    have h1 := mul_le_mul_of_nonneg_right hh hep0
    have hn11 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hf3 : (1 : ℝ) ≤ (f : ℝ) ^ 3 := one_le_pow₀ hfR
    have hP : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 * f ^ 3 :=
      le_trans hn11 (le_mul_of_one_le_right (by positivity) hf3)
    have h2 : 2.76 * (n : ℝ) ^ 2 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) :=
      mul_le_mul hKl hP (by positivity) (by linarith)
    have hz : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    linarith
  · have h2 : 2.76 * 1 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 3 * f) :=
      mul_le_mul hKl hn3f (by norm_num) (by linarith)
    linarith
  · set X := h * ep ^ 2 / 16 with hX_def
    set M := (n : ℝ) * f * rd * g * b with hM_def
    have hgpos : 0 < g := by linarith
    have hMpos : 0 < M := by
      have : (0 : ℝ) < rd := by linarith
      have : (0 : ℝ) < b := by linarith
      positivity
    set Lb := s + s + Cg * ℓ + ℓ with hLb_def
    have hLb0 : 0 ≤ Lb := by
      have : 0 ≤ Cg * ℓ := mul_nonneg hCg (by linarith)
      linarith

    have hnexp : (n : ℝ) ≤ Real.exp s := by
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 (log_le_sqrt_of_one_le _ (by linarith))
    have hfexp : (f : ℝ) ≤ Real.exp s := by
      calc (f : ℝ) = Real.exp (Real.log f) := (Real.exp_log hfpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 hlogf
    have hgexp : g ≤ Real.exp (Cg * ℓ) := by
      calc g ≤ b ^ Cg := hgb
        _ = Real.exp (Real.log b * Cg) := Real.rpow_def_of_pos (by linarith) Cg
        _ ≤ Real.exp (Cg * ℓ) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_right hlogb hCg
          linarith
    have hbrdexp : b * rd = Real.exp ℓ := (Real.exp_log (by linarith)).symm
    have hMle : M ≤ Real.exp Lb := by
      have e1 : M = (n : ℝ) * f * g * (b * rd) := by rw [hM_def]; ring
      have e2 : Real.exp Lb = Real.exp s * Real.exp s * Real.exp (Cg * ℓ) * Real.exp ℓ := by
        rw [hLb_def, Real.exp_add, Real.exp_add, Real.exp_add]
      rw [e1, e2, hbrdexp]
      have a1 : (n : ℝ) * f ≤ Real.exp s * Real.exp s :=
        mul_le_mul hnexp hfexp (by positivity) (by positivity)
      have a2 : (n : ℝ) * f * g ≤ Real.exp s * Real.exp s * Real.exp (Cg * ℓ) :=
        mul_le_mul a1 hgexp (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right a2 (by positivity)

    have htpos : 0 < t := lt_of_lt_of_le (pow_pos (inv_pos.2 hMpos) _) ht1
    have hinvt : t⁻¹ ≤ Real.exp (11 * s * Lb) := by
      rw [inv_pow] at ht1
      have a1 : t⁻¹ ≤ M ^ (11 * q) := inv_le_of_inv_le₀ (pow_pos hMpos _) ht1
      have a2 : M ^ (11 * q) ≤ Real.exp Lb ^ (11 * q) := pow_le_pow_left₀ hMpos.le hMle _
      have a3 : Real.exp Lb ^ (11 * q) = Real.exp (((11 * q : ℕ) : ℝ) * Lb) :=
        (Real.exp_nat_mul Lb (11 * q)).symm
      have a4 : ((11 * q : ℕ) : ℝ) * Lb ≤ 11 * s * Lb := by
        push_cast
        have : 11 * (q : ℝ) ≤ 11 * s := by linarith
        exact mul_le_mul_of_nonneg_right this hLb0
      calc t⁻¹ ≤ M ^ (11 * q) := a1
        _ ≤ Real.exp Lb ^ (11 * q) := a2
        _ = Real.exp (((11 * q : ℕ) : ℝ) * Lb) := a3
        _ ≤ Real.exp (11 * s * Lb) := Real.exp_le_exp.2 a4

    have hA : 3 * s / t ^ 2 ≤ Real.exp (2 + s + 22 * s * Lb) := by
      have e1 : 3 * s / t ^ 2 = 3 * s * (t⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
      have e2 : Real.exp (2 + s + 22 * s * Lb)
          = Real.exp 2 * Real.exp s * (Real.exp (11 * s * Lb)) ^ 2 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [e1, e2]
      have b1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp 2
        linarith
      have b2 : s ≤ Real.exp s := by
        have := Real.add_one_le_exp s
        linarith
      have b3 : (t⁻¹) ^ 2 ≤ (Real.exp (11 * s * Lb)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinvt 2
      have b4 : 3 * s ≤ Real.exp 2 * Real.exp s :=
        mul_le_mul b1 b2 (by linarith) (by positivity)
      exact mul_le_mul b4 b3 (by positivity) (by positivity)
    have hpow : (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) hA _

    have hsmall : 2 * (f : ℝ) * 3 ^ f ≤ Real.exp (4 * f) := by
      have c1 : 2 * (f : ℝ) ≤ Real.exp (2 * f) := by
        have := Real.add_one_le_exp (2 * (f : ℝ))
        linarith
      have c2 : (3 : ℝ) ^ f ≤ Real.exp (f * 2) := by
        rw [Real.exp_nat_mul]
        have : (3 : ℝ) ≤ Real.exp 2 := by
          have := Real.add_one_le_exp 2
          linarith
        exact pow_le_pow_left₀ (by norm_num) this f
      have e : Real.exp (4 * f) = Real.exp (2 * f) * Real.exp (f * 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      exact mul_le_mul c1 c2 (by positivity) (by positivity)

    have hexp : ((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)
        ≤ -((n : ℝ) ^ 2 * f) := by
      push_cast
      have hP0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f := by positivity
      have hKl0 : 0 ≤ (Cg + 1) * ℓ := mul_nonneg (by linarith) (by linarith)
      have k1 : (n : ℝ) ^ 2 * f * s * ((Cg + 1) * ℓ) ≤ (n : ℝ) ^ 2 * f * n * ((Cg + 1) * ℓ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsn hP0) hKl0
      have k2 : (n : ℝ) ^ 2 * f * s ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hsn hP0
      have k3 : (f : ℝ) ≤ (n : ℝ) ^ 2 * f :=
        le_mul_of_one_le_left hfpos.le (one_le_pow₀ (by linarith))
      have k4 : (n : ℝ) ^ 2 * f * 3 ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hnR hP0
      have k5 : (n : ℝ) ^ 2 * f * n * 107 ≤ (n : ℝ) ^ 2 * f * n * (156 * ℓ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have k6 : 0 ≤ (n : ℝ) ^ 2 * f * n * (Cg * ℓ) :=
        mul_nonneg (by positivity) (mul_nonneg hCg (by linarith))
      have k7 : (n : ℝ) ^ 2 * f * s ^ 2 = (n : ℝ) ^ 2 * f * n := by rw [hs2]
      have k8 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f * n := by positivity
      rw [hLb_def]
      linarith
    calc (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-X))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb))
            * (Real.exp (4 * f) * Real.exp (-X)) := by
          apply mul_le_mul hpow (mul_le_mul_of_nonneg_right hsmall (by positivity))
            (by positivity) (by positivity)
      _ = Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := Real.exp_le_exp.2 hexp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FarTermsModerateRegionOfFlagBound
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Deep

theorem farModerate_e_one_nonneg (B : RowsAut) : 0 ≤ (B.e 1).re := by
  obtain ⟨-, -, -, hpos, -⟩ := B.e_adm
  have h := hpos 1 (fun _ => 1) (fun _ => 1)
  simp at h
  simpa using (Complex.le_def.1 h).1

private theorem epN_pos_and_le_inv_sqrt_and_mul_le_log_two (n f q : ℕ) (hn : 8 ≤ n) (hf : 1 ≤ f) (hq : 1 ≤ q)
    (hqn : q ^ 2 ≤ n) :
    0 < 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ∧
      1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / Real.sqrt (2 * (q : ℝ)) ∧
      2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) ≤ Real.log 2 := by
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
    exact_mod_cast this
  have hD : 0 < (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by positivity
  have hn8 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hf2 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := one_le_pow₀ hf'
  have hnD : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by nlinarith
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · have hs : Real.sqrt (2 * (q : ℝ)) ≤ 2 * q :=
      calc Real.sqrt (2 * (q : ℝ)) ≤ Real.sqrt ((2 * (q : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * q := Real.sqrt_sq (by linarith)
    have hspos : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by linarith)
    calc 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / (2 * q) := by
          rw [div_le_div_iff₀ hD (by linarith)]
          nlinarith
      _ ≤ 1 / Real.sqrt (2 * (q : ℝ)) := one_div_le_one_div_of_le hspos hs
  · have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h1 : (n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 := (div_le_one hD).2 hnD
    have h2 : 2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) =
        2 / 10 ^ 6 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) := by ring
    rw [h2]
    linarith

theorem farModerate_of_farBound :
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.FarBound → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate := by
  intro hFM hFB Cg hCg
  refine ⟨8, fun B d p q b hq hCH => ?_⟩
  obtain ⟨-, hrd, hf1, -, -, h2q, -, hmin, hdpos, -, htpos, htq, h, hh, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl hCH
  obtain ⟨hDS, hSig, hn0, hqn, -, hlf, hb2, -, -, hg1, hgb, -, -, -, -⟩ := hCH
  have htq' : tauStar B q b < 1 / 2 := (htq hq).1
  have he1 : 0 ≤ (B.e 1).re := farModerate_e_one_nonneg B
  have hK : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hdpos.le he1
  obtain ⟨hep0, hepq, heplog⟩ := epN_pos_and_le_inv_sqrt_and_mul_le_log_two B.I.n B.I.f q hn0 hf1 hq hqn
  obtain ⟨hA, hB, hC⟩ := GlobalTheory.gap_threshold_pays_far_terms Cg B.I.n B.I.f q B.I.rd (B.g : ℝ) b h
    (tauStar B q b) hCg (by omega) hf1 hq hqn hrd hlf hb2 (Nat.one_le_cast.2 hg1) hgb hh.ge le_rfl htq'.le
  obtain ⟨-, -, hfin, -⟩ := hFM B.I B.μf B.fund B.fund_spec p q hSig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  have hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ≤
      ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) := by
    intro x hx
    obtain ⟨hs, hsum⟩ := hFB B d p q h (epN B) hDS hSig hmin.symm hq hgap hep0 hepq heplog hA hB h120 x
    have hx1 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x = ENNReal.ofReal
        (∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
      simp only [ofReal_norm]
      rfl
    have hlat : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x ≤
        (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) := by
      have ht1 : tauStar B q b ≤ tau1 B.I x := le_min htq'.le hx.2
      unfold GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos htpos 2)
        (pow_le_pow_left₀ htpos.le ht1 2)
    have hC0 : 0 ≤ 2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)) := by positivity
    rw [hx1]
    apply ENNReal.ofReal_le_ofReal
    calc ∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖
        ≤ (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) := hsum
      _ ≤ (∏ v, d v) * (B.e 1).re *
            (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlat hK) hC0
      _ = (∏ v, d v) * (B.e 1).re *
            ((3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)))) := by ring
      _ ≤ (∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) :=
          mul_le_mul_of_nonneg_left hC hK
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ∂(B.I.muA B.μf)
      ≤ ∫⁻ _ in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b,
          ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))
          ∂(B.I.muA B.μf) := setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf B.fund := mul_le_mul_of_nonneg_left (measure_mono fun x hx => hx.1) (by simp)
    _ = ENNReal.ofReal (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d) := by
      rw [← ENNReal.ofReal_toReal hfin.ne,
        ← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le)]
      congr 1
      show _ = Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) *
        ((∏ v, d v) * ((B.I.muA B.μf) B.fund).toReal * (B.e 1).re)
      ring

end GlobalTheory.Deep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FarTermsModerateRegionOfFlagBoundStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.farTermsModerateRegion_of_flagBound : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.FarBound → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate := by
  first | exact @GlobalTheory.Deep.farModerate_of_farBound | exact GlobalTheory.Deep.farModerate_of_farBound | (intros; apply GlobalTheory.Deep.farModerate_of_farBound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountFinal

theorem countingTheorem_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hV
  have hDec : GlobalTheory.DSId.DecGap := GlobalTheory.T.lowestKType_decayGap_of_compressionFormulaGap GlobalTheory.T.lowestKType_compressionFormula_of_strictLowestKType
  have hPt : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hDec
  have hAbs : GlobalTheory.FlagMeas.AbsoluteVolume := GlobalTheory.T.hermAbsoluteVolumeBound_of_volume_ratio_induction hV
  have hFM : GlobalTheory.FlagMeas.FlagMeasureBound := GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio hV
  have hFin := GlobalTheory.T.finiteDimensional_rowsSpace_discreteSeriesCount hDec hAbs
  have hNear := GlobalTheory.NearMod.nearModerate hFM GlobalTheory.T.flag_explicit_constant_le_exp_neg_half GlobalTheory.NearElement.near_unipotent hPt
  have hFar := GlobalTheory.T.farTermsModerateRegion_of_flagBound hFM (GlobalTheory.FarTerms.farBound_of_ptBound hPt)
  have hRare := GlobalTheory.FlagRareProof.flagRare_of_nonzeroFlagBound (GlobalTheory.T.nonzeroFlagProbabilityBound_of_volumeRatioInduction hV)
  have hDeep := GlobalTheory.T.deepRegion_kernelDiagonal_bound hAbs (GlobalTheory.T.deepPointKernelBound_of_pointwiseBound hPt hFin)
  exact GlobalTheory.T.discreteSeries_counting_of_finite_and_bounds hFin hFM hPt hNear hFar hRare hDeep

end GlobalTheory.CountFinal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRatStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAutomorphicCounting_of_compactDualVolumeRatio : GlobalTheory.FlagMeas.VolumeStep → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  first | exact @GlobalTheory.CountFinal.countingTheorem_of_volumeStep | exact GlobalTheory.CountFinal.countingTheorem_of_volumeStep | (intros; apply GlobalTheory.CountFinal.countingTheorem_of_volumeStep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingUnbundled
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingUnbundled
open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CountBridge

theorem fdegOf_eq_of_isFdeg {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (μ : Measure (Formalism.REAL.UJ ε))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (hd : IsFdeg μ σ d) (w : H) (hw : ‖w‖ = 1) :
    fdegOf μ σ w = d := by
  obtain ⟨hpos, h⟩ := hd
  have h2 := (h w w w w).2
  have h3 : (fun g => coefOn (ε := ε) σ w w g * star (coefOn σ w w g)) =
      fun g => (((‖coefOn (ε := ε) σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h3, integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hw] at h2
  have h4 : ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂μ = 1 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    simp
  unfold fdegOf
  rw [h4, hw]
  simp

theorem le_exp_of_log_le {x y : ℝ} (h : Real.log x ≤ y) : x ≤ Real.exp y :=
  (Real.le_exp_log x).trans (Real.exp_le_exp.mpr h)

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  apply Real.one_le_rpow
  · have h : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (discr_ne_zero I.E)
    exact_mod_cast h
  · positivity

theorem count_unbundled : GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀, ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ), (n₁ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧ Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ ∀ P : Ideal (𝓞 I.E), P.IsMaximal → ((g₀ : 𝓞 I.E) ∈ P) → Ideal.absNorm P = g₀ ∧ (g₀ : 𝓞 I.E) ∉ P ^ 2) → ((∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧ I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re) → (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h → Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) → Real.log (Real.log b) ≤ 1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) → |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e| ≤ Real.exp (-(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e := by
  intro hT A
  obtain ⟨n₀, hn₀⟩ := hT A
  refine ⟨n₀, max 0 (8 * 10 ^ 14 * (A + 4)), le_max_left _ _, ?_⟩
  intro n₁ hn₁ C hC I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h
    ⟨hn, ⟨p, q, hpq, hq⟩, hb, hrd, hHC, hlam, hadm, hg, hgb, hpr, hg₀, hsplit⟩
    ⟨hDS, hlow, htens, hhaar, hfund, hR, hRe⟩ hgap hh hf hbb
  let B : RowsAut :=
    { I := I, μf := μf, haar := hhaar, fund := fund, fund_spec := hfund, lam := lam, H := H, σ := σ,
      w := w, Hs := Hs, σs := σs, tens := tens, tens_spec := htens, R := R, R_spec := hR, g := g,
      g₀ := g₀, e := e, e_adm := hadm, Re := Re, Re_spec := hRe }
  have hfd : ∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) := by
    intro v
    obtain ⟨_, hnt, hU, hirr, hsq, -⟩ := hDS v
    obtain ⟨d, hd⟩ := GlobalTheory.schur_orthogonality_unitary I.n (I.ε v) (H v) (σ v) hU hirr hsq
    rw [fdegOf_eq_of_isFdeg _ _ d hd _ (hlow v).1]
    exact hd
  have hlog : 0 ≤ Real.log (b * I.rd) := by
    apply Real.log_nonneg
    have := one_le_rd I
    nlinarith
  have hC' : 8 * 10 ^ 14 * (A + 4) ≤ C := (le_max_right _ _).trans hC
  have hH : GlobalTheory.Count.CountHyp B A n₀ (fun v => fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) p q b := by
    refine ⟨fun v => ⟨hHC v, hDS v, hlow v, hfd v⟩, hpq, le_trans hn₁ hn, hq, le_exp_of_log_le hrd, hf, hb,
      le_exp_of_log_le hbb, hlam, hg, hgb, hpr, hg₀, GlobalTheory.T.ncard_primesOver_eq_finrank_of_unramified_split I.E g₀ hpr hsplit, ?_⟩
    intro v a a' haa
    refine le_trans ?_ (hgap v a a' haa)
    refine le_trans ?_ hh
    show 8 * 10 ^ 14 * (A + 4) * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ _
    gcongr
  have hres := (hn₀ B _ p q b hH).2
  have he : -(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) =
      -(1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) := by ring
  rw [he]
  exact hres

end GlobalTheory.CountBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingUnbundledStatement
open MeasureTheory NumberField Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAutomorphicCounting_unbundled : GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀, ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ), (n₁ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧ Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ ∀ P : Ideal (𝓞 I.E), P.IsMaximal → ((g₀ : 𝓞 I.E) ∈ P) → Ideal.absNorm P = g₀ ∧ (g₀ : 𝓞 I.E) ∉ P ^ 2) → ((∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧ I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re) → (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h → Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) → Real.log (Real.log b) ≤ 1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) → |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e| ≤ Real.exp (-(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e := by
  first | exact @GlobalTheory.CountBridge.count_unbundled | exact GlobalTheory.CountBridge.count_unbundled | (intros; apply GlobalTheory.CountBridge.count_unbundled <;> assumption)
end
end

open Formalism.MainNotions.PlaceDegreeData

namespace GlobalTheory.CountBridge

theorem count_typed_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀,
      ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.PlaceDegreeData.PointsLemma D n₁ A C (1 / 16) (1 / 16) := by
  intro hV A
  obtain ⟨n₀, C₀, hC₀, hcount⟩ := GlobalTheory.T.unitaryAutomorphicCounting_unbundled (GlobalTheory.T.unitaryAutomorphicCounting_of_compactDualVolumeRatio hV) A
  refine ⟨n₀, C₀, hC₀, fun n₁ hn₁ C hC _D => ?_⟩
  intro I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h hSet hData
  exact hcount n₁ hn₁ C hC I b lam g g₀ e H σ w Hs σs tens μf fund R Re h hSet hData

end GlobalTheory.CountBridge
