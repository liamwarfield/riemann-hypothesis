module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.BRegWeightLevi
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {a : K → ℤ}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

theorem BoundedRegularisationSetting.eventually_closedBall_subset (S : BoundedRegularisationSetting M Xo a w) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.B.mid j),
      closedBall (S.B.chart j x) t ⊆ (S.B.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.B.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.B.chart j '' closure (S.B.mid j)) :=
    hc.image_of_continuousOn ((S.B.chart j).continuousOn.mono (S.B.closure_mid j))
  have hsub : S.B.chart j '' closure (S.B.mid j) ⊆ (S.B.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.B.chart j).map_source (S.B.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.B.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem BoundedRegularisationSetting.eventually_chartLevi (S : BoundedRegularisationSetting M Xo a w) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.bregWeight t) ∧
      ∀ k : Fin S.B.N, ∀ x ∈ S.B.mid k, ∀ v : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖v‖ ^ 2 ≤
          levi (S.B.chartFun (S.bregWeight t) k) (S.B.chart k x) v := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc d M.atlas S.B S.ρ S.η S.Cη t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PhiISemipositive
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree Metric
open ReciprocityTheory.AnForm.A (IsPsh)
open scoped Matrix ComplexOrder

section Gram

variable {k : ℕ}

variable {ρ m : Type} [Fintype ρ] [Fintype m]

end Gram

section Psh

variable {d : ℕ}

theorem isPsh_congr' {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (h : Set.EqOn φ ψ U)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in nhdsWithin z U, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h hxU]
  · have hs : Set.EqOn (fun ζ : ℂ => φ (z + ζ • w)) (fun ζ => ψ (z + ζ • w)) (sphere 0 |(1 : ℝ)|) :=
      fun ζ hζ => h (hd ζ (by simp at hζ; rw [hζ]))
    obtain ⟨h1, h2⟩ := hφ.2 z w hd
    refine ⟨(circleIntegrable_congr hs).1 h1, ?_⟩
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    rw [← Real.circleAverage_congr_sphere hs, ← h hz]
    exact h2

theorem isPsh_add_re_add_const {U : Set (Fin d → ℂ)} (hU : IsOpen U) {φ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ)
    {G : (Fin d → ℂ) → ℂ} (hG : DifferentiableOn ℂ G U) (c : ℝ) :
    IsPsh U (fun w => φ w + (G w).re + c) := by
  have hcont : ContinuousOn (fun w => (G w).re) U := Complex.continuous_re.comp_continuousOn hG.continuousOn
  refine ⟨(hφ.1.add hcont.upperSemicontinuousOn).add upperSemicontinuousOn_const, fun z w hd => ?_⟩
  obtain ⟨hint, hle⟩ := hφ.2 z w hd
  have hmap : Continuous fun ζ : ℂ => z + ζ • w := continuous_const.add (continuous_id.smul continuous_const)
  have hdiff : DifferentiableOn ℂ (fun ζ : ℂ => G (z + ζ • w)) (closedBall 0 1) := by
    intro ζ hζ
    have hζU : z + ζ • w ∈ U := hd ζ (by simpa using hζ)
    have hGa : DifferentiableAt ℂ G (z + ζ • w) := hG.differentiableAt (hU.mem_nhds hζU)
    have hl : DifferentiableAt ℂ (fun ζ : ℂ => z + ζ • w) ζ :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const w)
    exact (hGa.comp ζ hl).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun ζ : ℂ => G (z + ζ • w)) (ball 0 |(1 : ℝ)|) := by
    rw [abs_one]
    exact hdiff.diffContOnCl_ball subset_rfl
  have hmean : Real.circleAverage (fun ζ : ℂ => G (z + ζ • w)) 0 1 = G z := by
    have := hdc.circleAverage
    simpa using this
  have hcs : ContinuousOn (fun ζ : ℂ => G (z + ζ • w)) (sphere 0 1) :=
    hdiff.continuousOn.mono sphere_subset_closedBall
  have hciG : CircleIntegrable (fun ζ : ℂ => G (z + ζ • w)) 0 1 := hcs.circleIntegrable zero_le_one
  have hciR : CircleIntegrable (fun ζ : ℂ => (G (z + ζ • w)).re) 0 1 :=
    (Complex.continuous_re.comp_continuousOn hcs).circleIntegrable zero_le_one
  have hre : Real.circleAverage (fun ζ : ℂ => (G (z + ζ • w)).re) 0 1 = (G z).re := by
    have := ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hciG
    rw [hmean] at this
    simpa [Function.comp_def] using this
  have hci2 : CircleIntegrable (fun ζ : ℂ => φ (z + ζ • w) + (G (z + ζ • w)).re) 0 1 := hint.add hciR
  refine ⟨hci2.add (circleIntegrable_const c 0 1), ?_⟩
  have e1 := Real.circleAverage_fun_add hci2 (circleIntegrable_const c 0 1)
  have e2 := Real.circleAverage_fun_add hint hciR
  show φ z + (G z).re + c ≤ Real.circleAverage (fun ζ : ℂ => φ (z + ζ • w) + (G (z + ζ • w)).re + c) 0 1
  rw [e1, e2, hre, Real.circleAverage_const]
  linarith

end Psh

section Hodge

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

end Hodge

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CardZBasisEqMulFinrank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights.LowerBoundFree
  Module Matrix
open scoped Matrix ComplexConjugate Kronecker

section Tower

variable {Em : Type} [Field Em] [NumberField Em]

def towerZBasis {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) :
    Basis (Fin ρ × (Em →+* ℂ)) ℤ (Submodule.span (𝓞 Em) (Set.range v)) :=
  ((RingOfIntegers.basis Em).smulTower' (Basis.span hv)).reindex
    (Equiv.prodCongr (Equiv.refl _) (equivReindex Em).symm)

theorem towerZBasis_apply {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) (p : Fin ρ × (Em →+* ℂ)) :
    (towerZBasis hv p : M) = RingOfIntegers.basis Em (equivReindex Em p.2) • v p.1 := by
  simp [towerZBasis, Basis.smulTower'_apply, Basis.span_apply]


end Tower

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)



end FullerData

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.EigenLatDifferent
section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.TorusIndex
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

section Torus

variable {Em : Type} [Field Em] [NumberField Em] {K : Type} [Field K] [NumberField K] {N : ℕ}

def baseChangeLat (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 Em) (Fin N → Em)) :
    Submodule (𝓞 K) ((Em →+* K) → Fin N → K) :=
  Submodule.span (𝓞 K) ((fun v σ a => σ (v a)) '' (I : Set (Fin N → Em)))


open Classical in
def eigenLat (I : Submodule (𝓞 Em) (Fin N → Em)) (s : Em →+* K) : Submodule (𝓞 K) (Fin N → K) :=
  (baseChangeLat K I).comap (LinearMap.single (𝓞 K) (fun _ : Em →+* K => Fin N → K) s)

def familyLat (s : Em →+* K) {ρ : ℕ} (v : Fin ρ → Fin N → Em) : Submodule (𝓞 K) (Fin N → K) :=
  Submodule.span (𝓞 K) (Set.range fun a i => s (v a i))

def genIndex {M : Type*} [AddCommGroup M] (P Q : AddSubgroup M) : ℝ :=
  (Q.relIndex P : ℝ) / (P.relIndex Q : ℝ)

def familyIndex (I : Submodule (𝓞 Em) (Fin N → Em)) {ρ : ℕ} (v : Fin ρ → Fin N → Em) : ℕ :=
  (Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup

end Torus

def TorusIndex.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ),
    (∀ σ : Em →+* ℂ, ∃ t : Em →+* K, ι.comp t = σ) →
    ∀ (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)) (ρ : ℕ) (v : Fin ρ → Fin N → Em), IsNzFamily I ρ v →
    ∀ s : Em →+* K,
      genIndex (eigenLat I s).toAddSubgroup (familyLat s v).toAddSubgroup =
        ((familyIndex I v : ℝ) / |(discr Em : ℝ)| ^ ρ) ^ ((Module.finrank ℚ K : ℝ) / Module.finrank ℚ Em)

namespace Gauss

open Gauss

theorem split (ι σ : Em →+* ℂ) : ∃ t : Em →+* Em, ι.comp t = σ := by
  have hcc : (ι.comp (cc : Em →+* Em)) ζ = -ι ζ := by
    rw [RingHom.comp_apply]
    change ι (cc ζ) = -ι ζ
    rw [cc_ζ, map_neg]
  rcases emb_ζ σ with h | h <;> rcases emb_ζ ι with h0 | h0
  · exact ⟨RingHom.id _, ringHom_ext (by rw [RingHom.comp_id, h, h0])⟩
  · exact ⟨_, ringHom_ext (by rw [hcc, h, h0, neg_neg])⟩
  · exact ⟨_, ringHom_ext (by rw [hcc, h, h0])⟩
  · exact ⟨RingHom.id _, ringHom_ext (by rw [RingHom.comp_id, h, h0])⟩

def isoVec : Fin 2 → Em := fun _ => 1

def isoLine : Submodule (𝓞 Em) (Fin 2 → Em) := Submodule.span (𝓞 Em) {isoVec}

def isoFam : Fin 1 → Fin 2 → Em := fun _ => isoVec

theorem span_isoFam : Submodule.span (𝓞 Em) (Set.range isoFam) = isoLine := by
  show Submodule.span (𝓞 Em) (Set.range fun _ : Fin 1 => isoVec) = isoLine
  rw [Set.range_const]
  rfl

theorem isoFam_nz : IsNzFamily isoLine 1 isoFam := by
  refine ⟨le_rfl, fun _ => Submodule.subset_span rfl, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 ?_
    intro h
    have := congrFun h 0
    simp [isoFam, isoVec] at this
  · rw [span_isoFam, AddSubgroup.relIndex_self]
    exact one_ne_zero

end Gauss

end GroundTheory.Heights₂.Heights.NineStatements
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section DiffLat

variable {Em : Type} [Field Em] [NumberField Em] {K : Type} [Field K] [NumberField K] {N : ℕ}

def diffLat (s : Em →+* K) (I : Submodule (𝓞 Em) (Fin N → Em)) : Submodule (𝓞 K) (Fin N → K) :=
  Submodule.span (𝓞 K) ((fun u i => s (u i)) ''
    {u | ∃ x ∈ differentIdeal ℤ (𝓞 Em), ∃ y ∈ I, u = (x : Em) • y})

end DiffLat

def EigenLatDifferent.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ),
    (∀ σ : Em →+* ℂ, ∃ t : Em →+* K, ι.comp t = σ) →
    ∀ (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)), I.FG → ∀ s : Em →+* K,
      eigenLat I s = diffLat s I

end GroundTheory.Heights₂.Heights.NineStatements
end
end
