module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuLineNormEq
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuFrameExists

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRegAboveWeight
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def RegAboveWeight.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    ∃ t₂ : ℝ, 0 < t₂ ∧ ∃ N : Set ((Σ k, ι k) → ℂ), IsPtsNull (mCoordIdeal D.y) D.n N ∧
      ∀ t : ℝ, 0 < t → t ≤ t₂ → ∀ z ∈ mcPts (mCoordIdeal D.y), z ∉ N →
        phMu X.H z ≤ Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjSmoothAlong
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ProjSmoothAlong.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D) (g : M.Xc → ℝ),
    M.atlas.Smooth g → SmoothAlong (mcPts (mCoordIdeal D.y)) (fun z => g (M.proj z))

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBdPtsNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def BdPtsNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBoundaryNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def BoundaryNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSemipos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem NbarSemipos.proof (h : NbarChartSemipos.Statement) : NbarSemipos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hp _
  obtain ⟨c, hc, hX⟩ := h II Ψ K ι Ω E D O Lt X
  have hpc : 0 < (p : ℝ) * c := mul_pos (by exact_mod_cast hp) hc
  have hlim : Tendsto (fun t => (q : ℝ) * (4 * X.S.Cη * X.S.e1 t)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (X.S_tied.e1_tendsto_zero.const_mul (4 * X.S.Cη)).const_mul (q : ℝ)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t) := by
    filter_upwards [X.S.eventually_chartLevi X.S_tied, hlim.eventually (eventually_le_nhds hpc)] with t ht hq
    exact hX B p q t _ ht.1 ht.2 hq
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hall
  exact ⟨u, hu, fun t ht0 ht1 => hsub ⟨ht0, ht1⟩⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVertFactorSmooth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def VertFactorSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ), p ∈ D.S →
    (∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      D.vertFactor p (torusSmul c z) = (∏ k, ‖c k‖ ^ D.vdeg p k) * D.vertFactor p z) ∧
    SmoothAlong (mcPts (mCoordIdeal D.y)) (D.vertFactor p)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsOmNVbInt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def OmNVbInt.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    1 ≤ p → p ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ),
      IsPtsIntegrable (mCoordIdeal D.y) (X.omN B p q t) (fun z => X.Cd.cuspWeight z / 2)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ChartVel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

def IsChartVel (M : CxModel P d) (e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)) (z w : (Σ k, ι k) → ℂ)
    (v : Fin d → ℂ) : Prop :=
  ∃ γ : ℂ → (Σ k, ι k) → ℂ, γ 0 = z ∧ HasDerivAt γ w 0 ∧
    (∀ᶠ s in 𝓝 (0 : ℂ), DifferentiableAt ℂ γ s ∧ γ s ∈ mcPts P) ∧
    HasDerivAt (fun s => e (M.proj (γ s))) v 0

namespace Line

open GroundTheory.Heights₂.Heights (CP)

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTpIntegrandLimit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def TpIntegrandLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    1 ≤ q → ∃ t₂ : ℝ, 0 < t₂ ∧ ∀ t : ℝ, 0 < t → t ≤ t₂ →
      ∃ (N : Set ((Σ k, ι k) → ℂ)) (C t'₀ : ℝ), 0 < t'₀ ∧ IsPtsNull (mCoordIdeal D.y) D.n N ∧
        (∀ t' : ℝ, 0 < t' → t' < t'₀ →
          (∀ z ∈ mcPts (mCoordIdeal D.y), |X.wSt B p q t t' z| ≤ C) ∧
          ContinuousOn (X.wSt B p q t t') (mcPts (mCoordIdeal D.y) \ N)) ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), z ∉ N →
          Tendsto (fun t' => X.wSt B p q t t' z) (𝓝[>] 0)
            (𝓝 (cuspCorr X.H X.Cd z - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z))))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsMonoSemipos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def PtsMonoSemipos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (r : ℝ) (g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ) (N : Set ((Σ k, ι k) → ℂ)),
    IsArithVar P (e + 1) → IsSemipositiveH P L → 0 < r → IsPtsNull P e N →
    (∀ z ∈ mcPts P, z ∉ N → g₁ z ≤ g₂ z) →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₁ →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₂ →
    ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₁ ≤
      ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₂

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitT
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem StokesLimitT.proof (hG : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement)
    (hNs : NbarSemipos.Statement) (hTop : StokesLimitTTop.Statement) (hVb : StokesLimitTVb.Statement) :
    StokesLimitT.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hAr hp hpq
  refine ⟨tendsto_nhds_limUnder (hTop II Ψ K ι Ω E D O Lt X B p q hII hAr hp hpq),
    tendsto_nhds_limUnder (hVb II Ψ K ι Ω E D O Lt X B p q hp hpq), ?_⟩
  obtain ⟨t₁, ht₁, hN⟩ := hNs II Ψ K ι Ω E D O Lt X B p q hp hpq

  have ha : ∀ t : ℝ, (X.NbarQ B p q t).a = (X.NbarQ B p q t₁).a := by
    intro t
    simp only [ComponentSetting.NbarQ, smoothRep_a]
    rfl
  have hconst : ∀ᶠ t in 𝓝[>] (0 : ℝ), X.degN B p q t₁ = X.degN B p q t := by
    filter_upwards [Ioc_mem_nhdsGT ht₁] with t ht
    unfold ComponentSetting.degN
    rw [hG K ι Ω D.y D.n _ D.arith (hN t ht.1 ht.2).1, hG K ι Ω D.y D.n _ D.arith (hN t₁ ht₁ le_rfl).1, ha t]
  exact tendsto_nhds_limUnder ⟨_, tendsto_const_nhds.congr' hconst⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuMeasureLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem ptsIntegral_div_two {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral (e := e) P φ (fun z => g z / 2) = ptsIntegral (e := e) P φ g / 2 := by
  classical
  let m : ℝ ≃+ ℝ :=
    { toFun := fun x => x / 2, invFun := fun x => 2 * x, left_inv := fun x => by ring,
      right_inv := fun x => by ring, map_add' := fun x y => add_div x y 2 }
  have hhalf : ∀ (s : Set (((k : K) → ι k) → ℂ)) (F : (((k : K) → ι k) → ℂ) → ℝ),
      ∑ᶠ w ∈ s, F w / 2 = (∑ᶠ w ∈ s, F w) / 2 := by
    intro s F
    show ∑ᶠ w, ∑ᶠ (_ : w ∈ s), m (F w) = m (∑ᶠ w, ∑ᶠ (_ : w ∈ s), F w)
    rw [m.map_finsum]
    congr 1
    funext w
    rw [m.map_finsum]
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_div]
    congr 1
    funext y
    have hs : ∀ w, sheetDensity P hΨ.choose φ (fun z => g z / 2) y w =
        sheetDensity P hΨ.choose φ g y w / 2 := by
      intro w
      unfold sheetDensity
      split_ifs <;> ring
    simp only [hs]
    exact hhalf _ _
  · simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTopNMixed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

namespace ComponentSetting

variable (X : ComponentSetting D O Lt)

def mixN (B k : ℕ) (t : ℝ) : ℝ :=
  II K ι (mCoordIdeal D.y) (D.n + 1) fun j => if (j : ℕ) < k then muReg X.H X.S B t else D.A'

end ComponentSetting

def TopNMixedExpand.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    IsIntersectionSystem II → 1 ≤ p → p ≤ q →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), X.topN B p q t =
        ∑ k ∈ Finset.range (D.n + 2),
          ((D.n + 1).choose k : ℝ) * ((p : ℝ) / q) ^ (D.n + 1 - k) * X.mixN B k t

def TopNMixedLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      ∀ k : ℕ, k ≤ D.n → ∃ L : ℝ, Tendsto (X.mixN B k) (𝓝[>] 0) (𝓝 L)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRatioFieldSpan
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace RatioFieldSpan

variable {F M : Type} [Field F] [Field M] [Algebra F M]

theorem div_mem_adjoin {I : Type} (u : I → M) (v : M) {x : M}
    (hx : x ∈ Submodule.span F (Set.range u)) :
    x / v ∈ IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    exact IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_div]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, mul_div_assoc]
    exact mul_mem (IntermediateField.algebraMap_mem _ a) hx

theorem adjoin_le {I J : Type} (u : I → M) (w : J → M) (v v' : M)
    (hw : ∀ j, w j ∈ Submodule.span F (Set.range u)) (hv' : v' ∈ Submodule.span F (Set.range u))
    (hv : v ≠ 0) (hv'0 : v' ≠ 0) :
    IntermediateField.adjoin F (Set.range fun j => w j / v') ≤
      IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  have h1 := div_mem_adjoin (F := F) u v (hw j)
  have h2 := div_mem_adjoin (F := F) u v hv'
  have key : w j / v' = (w j / v) / (v' / v) := by
    field_simp
  show w j / v' ∈ IntermediateField.adjoin F (Set.range fun i => u i / v)
  rw [key]
  exact div_mem h1 h2

theorem full : RatioFieldSpan.Statement := by
  intro F M _ _ _ I J u w v v' hspan hv hv' hv0 hv'0
  apply le_antisymm
  · apply adjoin_le w u v' v
    · intro i
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [← hspan]; exact hv
    · exact hv'0
    · exact hv0
  · apply adjoin_le u w v v'
    · intro j
      rw [hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    · exact hv'
    · exact hv0
    · exact hv'0

end RatioFieldSpan

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitEps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace StokesLimitEps

open Matrix

theorem coeff_tendsto {N : ℕ} (c : ℕ → ℝ → ℝ) (f : ℕ → ℝ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ), f q t = ∑ i ∈ Finset.range N, c i t * (1 / (q : ℝ)) ^ i)
    (hg : ∀ q : ℕ, 1 ≤ q → Tendsto (f q) (𝓝[>] 0) (𝓝 (g q))) :
    ∃ ℓ : ℕ → ℝ, (∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i))) ∧
      ∀ q : ℕ, 1 ≤ q → g q = ∑ i ∈ Finset.range N, ℓ i * (1 / (q : ℝ)) ^ i := by

  let x : Fin N → ℝ := fun j => 1 / (((j : ℕ) + 1 : ℕ) : ℝ)
  have hinj : Function.Injective x := by
    intro j k h
    simp only [x, one_div, _root_.inv_inj, Nat.cast_inj] at h
    exact Fin.ext (by omega)
  have hdet : IsUnit (Matrix.vandermonde x).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    exact hinj
  let F : ℝ → Fin N → ℝ := fun t j => f ((j : ℕ) + 1) t

  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun i : Fin N => c i t) = (Matrix.vandermonde x)⁻¹ *ᵥ F t := by
    filter_upwards [Filter.eventually_all.2 fun j : Fin N => hf ((j : ℕ) + 1) (by omega)] with t ht
    have hval : F t = Matrix.vandermonde x *ᵥ fun i : Fin N => c i t := by
      funext j
      simp only [F, ht j, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, x]
      rw [← Fin.sum_univ_eq_sum_range (fun i => c i t * (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) ^ i)]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hF : Tendsto F (𝓝[>] 0) (𝓝 fun j : Fin N => g ((j : ℕ) + 1)) :=
    tendsto_pi_nhds.2 fun j => hg _ (by omega)
  have hC : Tendsto (fun t => fun i : Fin N => c i t) (𝓝[>] 0)
      (𝓝 ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1))) :=
    (((continuous_const.matrix_mulVec continuous_id).tendsto _).comp hF).congr' (hev.mono fun t ht => ht.symm)
  let ℓ : ℕ → ℝ := fun i => if h : i < N then
    ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1)) ⟨i, h⟩ else 0
  have hℓ : ∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i)) := by
    intro i hi
    simpa only [ℓ, dif_pos hi] using tendsto_pi_nhds.1 hC ⟨i, hi⟩
  refine ⟨ℓ, hℓ, fun q hq => tendsto_nhds_unique (hg q hq) ?_⟩
  refine Tendsto.congr' ((hf q hq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun i hi => (hℓ i (Finset.mem_range.1 hi)).mul_const _

theorem tendsto_const_coeff {N : ℕ} (ℓ : ℕ → ℝ) (hN : 1 ≤ N) :
    Tendsto (fun m : ℕ => ∑ i ∈ Finset.range N, ℓ i * (1 / ((m + 1 : ℕ) : ℝ)) ^ i) atTop (𝓝 (ℓ 0)) := by
  have h0 : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hs := tendsto_finsetSum (Finset.range N) fun i _ => (h0.pow i).const_mul (ℓ i)
  have e : ∑ i ∈ Finset.range N, ℓ i * (0 : ℝ) ^ i = ℓ 0 := by
    rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [zero_pow hb])
      (fun h => absurd (Finset.mem_range.2 hN) h)]
    simp
  rwa [e] at hs

end StokesLimitEps

theorem StokesLimitEps.proof (hT : StokesLimitT.Statement) (hTop : TopNPoly.Statement)
    (hOm : OmNPoly.Statement) (hMu : MuMeasureLimit.Statement) : StokesLimitEps.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII hAr
  have hTq := fun q (hq : 1 ≤ q) => hT II Ψ K ι Ω E D O Lt X B 1 q hII hAr le_rfl hq
  obtain ⟨c, hc0, hc⟩ := hTop II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨v, d, hv0, hd0, hvd⟩ := hOm II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨hmuV, hmuD⟩ := hMu II Ψ K ι Ω E D O Lt X B hII hAr
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto c (fun q => X.topN B 1 q) (X.topNLim B 1) hc
      fun q hq => (hTq q hq).1
    have h0 : ℓ 0 = arLim X.H X.S B := by
      obtain ⟨L, hL⟩ := hAr
      have e1 : arLim X.H X.S B = L := by unfold arLim; exact hL.limUnder_eq
      have h := hℓ 0 (by omega)
      rw [hc0] at h
      rw [e1]; exact tendsto_nhds_unique h hL
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 2) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto v (fun q => X.Vb B 1 q) (X.VbLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.1) fun q hq => (hTq q hq).2.1
    have h0 : ℓ 0 = meanU X.H X.Cd * degMu X.H / 2 := by
      have h := hℓ 0 (by omega)
      rw [hv0] at h
      exact tendsto_nhds_unique h hmuV
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto d (fun q => X.degN B 1 q) (X.degNLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.2) fun q hq => (hTq q hq).2.2
    have h0 : ℓ 0 = degMu X.H := by
      have h := hℓ 0 (by omega)
      rw [hd0] at h
      exact tendsto_nhds_unique h hmuD
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVerticalTwistGenDeg
section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PVerticalGenericDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.HilbertSamuel

namespace VerticalGenericDeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} {ι : K → Type}

theorem map_mem_map_iff {W : Ideal (MRing ι)} (hW : W.IsPrime) (hh : IsHorizontal W) (x : MRing ι) :
    MvPolynomial.map (Int.castRingHom ℚ) x ∈ W.map (MvPolynomial.map (Int.castRingHom ℚ)) ↔ x ∈ W := by
  classical
  let S : Submonoid (MRing ι) := (nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))
  have : IsLocalization S (MRingOver ℚ ι) := MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  have hφ : algebraMap (MRing ι) (MRingOver ℚ ι) = MvPolynomial.map (Int.castRingHom ℚ) := by
    show MvPolynomial.map (algebraMap ℤ ℚ) = _
    rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]
  have hdisj : Disjoint (S : Set (MRing ι)) W := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmW
    have h0 : m ∈ W.comap (C : ℤ →+* MRing ι) := hmW
    rw [hh, Ideal.mem_bot] at h0
    exact zero_notMem_nonZeroDivisors (h0 ▸ hm)
  have h := IsLocalization.under_map_of_isPrime_disjoint S (MRingOver ℚ ι) hW hdisj
  constructor
  · intro hx
    rw [← h]
    show algebraMap (MRing ι) (MRingOver ℚ ι) x ∈ Ideal.map (algebraMap (MRing ι) (MRingOver ℚ ι)) W
    rw [hφ]
    exact hx
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

theorem isMultiHomog_map [DecidableEq K] {x : MRing ι} {e : K → ℕ} (h : NumbersDVR.IsMultiHomog x e) :
    NumbersDVR.IsMultiHomog (MvPolynomial.map (Int.castRingHom ℚ) x) e := by
  intro d hd
  apply h
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

end VerticalGenericDeg

end GroundTheory.Heights₂.Heights.NineStatements
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVerticalTwistGenDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel

def VerticalTwistGenDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (a : K → ℤ)
    (s : Finset ℕ) (b : ℕ → K → ℤ) (f g : ℕ → MRing ι),
    IsArithVar P (d + 1) → (∀ p ∈ s, p.Prime ∧ IsVerticalDivisorAt P p (b p) (f p) (g p)) →
    genDeg P d (a + ∑ p ∈ s, b p) = genDeg P d a

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.HilbertSamuel

namespace VerticalTwistGenDeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem intNum_snoc_eq_zero {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n p : ℕ} {b : K → ℤ} {f g : MRing ι}
    (hP : IsArithVar P (n + 1 + 1)) (hp : p.Prime) (hV : IsVerticalDivisorAt P p b f g)
    (L : Fin n → K → ℤ) :
    NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ)))
      (Fin.snoc (α := fun _ => K → ℤ) L b) = 0 := by
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφ
  have hPN : NumbersDVR.IsMultiProjPrime P := (Bridge.isMultiProjPrime_iff P).mpr hP.2.1
  have : P.IsPrime := hPN.isPrime
  have hPh : IsHorizontal P := hP.2.2.1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpP : (C (p : ℤ) : MRing ι) ∉ P := by
    intro h
    have h0 : (p : ℤ) ∈ P.comap (C : ℤ →+* MRing ι) := h
    rw [hPh, Ideal.mem_bot] at h0
    exact hp0 h0
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  have hfN : NumbersDVR.IsMultiHomog f bf := (Bridge.isMultiHomog_iff f bf).mpr hf
  have hgN : NumbersDVR.IsMultiHomog g bg := (Bridge.isMultiHomog_iff g bg).mpr hg

  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_fibre P ‹_› le_rfl hP.2.1.2.2 hpP
  obtain ⟨u', v', e, e', hu', hv', hdeg, hu'P, hv'P, huv'⟩ :=
    NumbersDVR.exists_form_pair hPN.multiHomog le_rfl hfN hgN hV.num_not_mem hV.den_not_mem hu hv huv

  have hkey : ∀ W' : Ideal (MRingOver ℚ ι), W'.IsPrime → P.map φ ≤ W' → NumbersDVR.IsRelevant W' →
      NumbersDVR.divCycle (P.map φ) (φ v') W' = NumbersDVR.divCycle (P.map φ) (φ u') W' := by
    intro W' hW' hle hrel
    have hPle : P ≤ W'.comap φ := fun x hx => hle (Ideal.mem_map_of_mem φ hx)
    have hrel' : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (W'.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel k
      refine ⟨i, fun h => hi ?_⟩
      have h' : φ (X ⟨k, i⟩) ∈ W' := h
      rwa [hφ, map_X] at h'
    have hpW' : (C (p : ℤ) : MRing ι) ∉ W'.comap φ := by
      intro h
      have hu : IsUnit (φ (C (p : ℤ))) := by
        rw [hφ, map_C]
        exact (isUnit_iff_ne_zero.mpr (by simpa using hp0)).map C
      exact hW'.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    obtain ⟨s, t, hs, ht, hst⟩ := hV.unit_off_fibre _ (Ideal.comap_isPrime φ W') hPle hrel' hpW'
    have h1 : g * (s * v' - t * u') ∈ P := by
      have e1 : g * (s * v' - t * u') = u' * (s * f - t * g) - s * (u' * f - v' * g) := by ring
      rw [e1]
      exact P.sub_mem (P.mul_mem_left _ hst) (P.mul_mem_left _ huv')
    have h2 : s * v' - t * u' ∈ P := (‹P.IsPrime›.mem_or_mem h1).resolve_left hV.den_not_mem
    have h3 : φ s * φ v' - φ t * φ u' ∈ P.map φ := by
      rw [← map_mul, ← map_mul, ← map_sub]
      exact Ideal.mem_map_of_mem φ h2
    have hs' : φ s ∉ W' := hs
    have ht' : φ t ∉ W' := ht
    exact NumbersDVR.divCycle_eq_of_mul_sub_mem hs' ht' h3
  have hrat : NumbersDVR.ratDiv (P.map φ) (φ v') (φ u') = 0 := by
    funext W'
    show NumbersDVR.divCycle _ _ W' - NumbersDVR.divCycle _ _ W' = 0
    by_cases h1 : NumbersDVR.divCycle (P.map φ) (φ v') W' = 0
    · by_cases h2 : NumbersDVR.divCycle (P.map φ) (φ u') W' = 0
      · rw [h1, h2, sub_zero]
      · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h2
        rw [hkey W' a1 a2 a3, sub_self]
    · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h1
      rw [hkey W' a1 a2 a3, sub_self]

  have hX : IsProjVarF (P.map φ) (n + 1) := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map φ) := (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hv'Q : φ v' ∉ P.map φ := fun h => hv'P ((NineStatements.VerticalGenericDeg.map_mem_map_iff ‹_› hPh v').mp h)
  have hu'Q : φ u' ∉ P.map φ := fun h => hu'P ((NineStatements.VerticalGenericDeg.map_mem_map_iff ‹_› hPh u').mp h)
  have hab : ∀ k, (e' k : ℤ) - e k = b k := by
    intro k
    have h1 : (e' k : ℤ) + bg k = e k + bf k := by exact_mod_cast congrFun hdeg k
    have h2 : (bf k : ℤ) - bg k = b k := congrFun hb k
    rw [← h2]
    linarith
  have hR := NumbersDVR.IntNumRatSection.proof FieldNumbers.CutRational.full ℚ K ι n (P.map φ) hXN hX.2
    L b (φ v') (φ u') e' e (NineStatements.VerticalGenericDeg.isMultiHomog_map hv')
    (NineStatements.VerticalGenericDeg.isMultiHomog_map hu') hv'Q hu'Q hab
  rw [hrat] at hR
  rw [hR]
  simp [NumbersDVR.cycEval]

end VerticalTwistGenDeg

theorem VerticalTwistGenDeg.proof : VerticalTwistGenDeg.Statement := by
  intro K _ ι _ P d a s b f g hP hs
  classical
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφ
  obtain _ | n := d
  · unfold genDeg
    congr 1
    funext i
    exact i.elim0
  have hX : IsProjVarF (P.map φ) (n + 1) := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map φ) := (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hd : FieldNumbers.relDim (P.map φ) = (n + 1 : ℕ) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hX.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set F := intNumMultilinear (P.map φ) (n + 1) hXN.multiHomog hXN.relevant hd with hF

  have hposition : ∀ p ∈ s, ∀ (bs : Fin (n + 1) → K → ℤ) (i : Fin (n + 1)), bs i = b p → F bs = 0 := by
    intro p hps bs i hi
    obtain ⟨hp, hV⟩ := hs p hps
    have h := FieldNumbers.IntNumSymm.full ℚ K ι (P.map φ) (n + 1) bs (Equiv.swap i (Fin.last n))
    rw [hF, intNumMultilinear_apply, ← h]
    have e1 : bs ∘ Equiv.swap i (Fin.last n) = Fin.snoc (α := fun _ => K → ℤ)
        (fun j => bs (Equiv.swap i (Fin.last n) (Fin.castSucc j))) (b p) := by
      funext j
      induction j using Fin.lastCases with
      | last => simp [hi]
      | cast j => simp
    rw [e1]
    exact VerticalTwistGenDeg.intNum_snoc_eq_zero hP hp hV _

  have hB : ∀ (bs : Fin (n + 1) → K → ℤ) (i : Fin (n + 1)), bs i = ∑ p ∈ s, b p → F bs = 0 := by
    intro bs i hi
    have e2 : bs = Function.update bs i (∑ p ∈ s, b p) := by rw [← hi, Function.update_eq_self]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2, ← MultilinearMap.toLinearMap_apply, map_sum]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [MultilinearMap.toLinearMap_apply]
    exact hposition p hp _ i (Function.update_self _ _ _)
  have hg : ∀ c, genDeg P (n + 1) c = F (fun _ => c) := fun c => by
    rw [hF, intNumMultilinear_apply, genDeg]
  rw [hg, hg, show (fun _ : Fin (n + 1) => a + ∑ p ∈ s, b p) =
    (fun _ => a) + (fun _ => ∑ p ∈ s, b p) from rfl, F.map_add_univ,
    Finset.sum_eq_single Finset.univ]
  · rw [Finset.piecewise_univ]
  · intro S _ hS
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra h
      exact hS (Finset.eq_univ_iff_forall.2 fun i => not_not.1 (not_exists.1 h i))
    exact hB _ i (by simp [Finset.piecewise, hi])
  · intro h
    exact absurd (Finset.mem_univ _) h

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ContDiffAtSqrtQuotNormSq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped Matrix ComplexOrder

namespace MuWeightChartSmooth

section Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} {x : F}

theorem contDiffAt_det {m : Type*} [Fintype m] [DecidableEq m] {M : F → Matrix m m ℂ}
    (hM : ∀ i j, ContDiffAt ℝ n (fun w => M w i j) x) : ContDiffAt ℝ n (fun w => (M w).det) x := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hM _ _)

theorem contDiffAt_star {f : F → ℂ} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun w => star (f w)) x :=
  (Complex.conjCLE.contDiff.contDiffAt).comp x hf

theorem contDiffAt_zpow_of_ne {f : F → ℝ} (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ n (fun w => f w ^ m) x := by
  rcases m with m | m
  · simpa using hf.pow m
  · simp only [zpow_negSucc]
    exact (hf.pow (m + 1)).fun_inv (pow_ne_zero _ h0)

theorem contDiffAt_sandwich {m : Type*} [Fintype m] {A B : F → Matrix m m ℂ}
    (hA : ∀ i j, ContDiffAt ℝ n (fun w => A w i j) x) (hB : ∀ i j, ContDiffAt ℝ n (fun w => B w i j) x)
    (i j : m) : ContDiffAt ℝ n (fun w => ((A w)ᴴ * B w * A w) i j) x := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiffAt.sum fun k _ =>
    (ContDiffAt.sum fun l _ => (contDiffAt_star (hA l i)).mul (hB l k)).mul (hA k j)

end Calculus

section Chart

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]


end Chart

end MuWeightChartSmooth

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
