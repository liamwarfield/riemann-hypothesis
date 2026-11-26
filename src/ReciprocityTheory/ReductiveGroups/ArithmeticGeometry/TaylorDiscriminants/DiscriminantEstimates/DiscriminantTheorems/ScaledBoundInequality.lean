module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.ScaledBoundInequality
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne
namespace ReciprocityTheory.ChartRestriction.G.TB

open ComplexConjugate

def SchwarzBallSt : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (u : E → ℂ) (ρ M : ℝ),
    0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : E) ρ, ‖u z - u 0‖ ≤ M) →
      ∀ z ∈ Metric.ball (0 : E) ρ, ‖u z - u 0‖ ≤ M * ‖z‖ / ρ

def EBasisSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    [Module ℚ W] [IsScalarTower ℚ E W] (ι : Type) [Fintype ι] (v : ι → W),
    LinearIndependent ℚ v → Fintype.card ι = Module.finrank ℚ E * Module.finrank E W →
      ∃ s : Finset ι, s.card = Module.finrank E W ∧ LinearIndependent E (fun i : s => v i) ∧
        Submodule.span E (Set.range fun i : s => v i) = ⊤

end ReciprocityTheory.ChartRestriction.G.TB
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.EBasis
namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem eBasis : ReciprocityTheory.ChartRestriction.G.TB.EBasisSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.EBasisSt
  intro E _ _ W _ _ _ _ _ ι _ v hv hcard
  classical
  haveI : FiniteDimensional ℚ W := Module.Finite.trans E W
  have hinj : Function.Injective v := hv.injective
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, hcard, Module.finrank_mul_finrank]
  have hspanE : Submodule.span E (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range v) := by rw [hspanQ]; trivial
    exact Submodule.span_le_restrictScalars ℚ E (Set.range v) hx
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent E (Set.range v)
  let s : Finset ι := Finset.univ.filter (fun i => v i ∈ b)
  have hrange : Set.range (fun i : s => v i) = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (Finset.mem_filter.mp i.2).2
    · intro hx
      obtain ⟨i, rfl⟩ := hbsub hx
      exact ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩
  have hli : LinearIndependent E (fun i : s => v i) := by
    let f : s → b := fun i => ⟨v i, (Finset.mem_filter.mp i.2).2⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact hinj (congrArg Subtype.val hij)
    exact hbli.comp f hf
  have hspan : Submodule.span E (Set.range fun i : s => v i) = ⊤ := by
    rw [hrange, hbspan, hspanE]
  refine ⟨s, ?_, hli, hspan⟩
  have hfr := finrank_span_eq_card hli
  rw [hspan, finrank_top, Fintype.card_coe] at hfr
  exact hfr.symm

end PI.UnitaryGroupMassFormula.TBNum
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.Schwarz
namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem schwarzBall : ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt
  intro E _ _ u ρ M hρ hu hM z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.mp hz
  have hmaps : Set.MapsTo (fun w : ℂ => w • z) (Metric.ball 0 (ρ / ‖z‖)) (Metric.ball (0 : E) ρ) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_smul]
    rw [lt_div_iff₀ hzpos] at hw
    exact hw
  have hg : DifferentiableOn ℂ (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖)) :=
    hu.comp (differentiable_id.smul_const z).differentiableOn hmaps
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (ρ / ‖z‖) := by
    rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hzpos, one_mul]
    exact hzρ
  have hmap2 : Set.MapsTo (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖))
      (Metric.closedBall (u ((0 : ℂ) • z)) M) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm, zero_smul]
    exact hM _ (hmaps hw)
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmap2 h1
  simp only [one_smul, zero_smul, dist_eq_norm, sub_zero, norm_one, mul_one] at hS
  rw [div_div_eq_mul_div] at hS
  exact hS

end PI.UnitaryGroupMassFormula.TBNum
end

theorem schwarz_ball_bound : ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt := PI.UnitaryGroupMassFormula.TBNum.schwarzBall
theorem euclidean_basis_exists : ReciprocityTheory.ChartRestriction.G.TB.EBasisSt := PI.UnitaryGroupMassFormula.TBNum.eBasis
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBDisc
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.UniformDiscreteness.FgOfUnifDiscrete
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.RatIntUnifDiscrete
namespace ReciprocityTheory.ChartRestriction.G.TB

open NumberField

structure NormFam (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] where
  N : (K →+* ℂ) → V → ℝ
  nonneg : ∀ σ v, 0 ≤ N σ v
  eq_zero : ∀ σ v, N σ v = 0 → v = 0
  smul : ∀ σ (a : K) v, N σ (a • v) = ‖σ a‖ * N σ v
  add : ∀ σ v w, N σ (v + w) ≤ N σ v + N σ w

section Defs

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V]

def ProdLower (Nf : NormFam K V) (M : Submodule (𝓞 K) V) (A : ℝ) : Prop :=
  ∀ f ∈ M, f ≠ 0 → -A ≤ ∑ σ : K →+* ℂ, Real.log (Nf.N σ f)

def UnifDiscrete (Nf : NormFam K V) (M : Submodule (𝓞 K) V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ f ∈ M, (∀ σ, Nf.N σ f < ε) → f = 0

end Defs

def DiscOfProdLowerSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (Nf : NormFam K V) (M : Submodule (𝓞 K) V) (A : ℝ),
    ProdLower Nf M A → UnifDiscrete Nf M

def FGOfDiscSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (Nf : NormFam K V) (M : Submodule (𝓞 K) V),
    UnifDiscrete Nf M → M.FG

def IsLatticeOfDiscSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (Nf : NormFam K V) (M : Submodule (𝓞 K) V),
    UnifDiscrete Nf M → Submodule.span K (M : Set V) = ⊤ → Submodule.IsLattice K M

theorem rat_emb_apply (σ : ℚ →+* ℂ) (q : ℚ) : σ q = (q : ℂ) := eq_ratCast σ q

noncomputable def ratNormFam : NormFam ℚ ℚ where
  N σ v := ‖σ v‖
  nonneg _ _ := norm_nonneg _
  eq_zero σ v h := by simpa using h
  smul σ a v := by rw [smul_eq_mul, map_mul, norm_mul]
  add σ v w := by rw [map_add (f := _)]; exact norm_add_le _ _

noncomputable def ratInt : Submodule (𝓞 ℚ) ℚ := Submodule.span (𝓞 ℚ) {1}

theorem mem_ratInt {f : ℚ} (hf : f ∈ ratInt) : ∃ n : ℤ, f = n := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have hi : IsIntegral ℤ (a : ℚ) := RingOfIntegers.isIntegral_coe a
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  refine ⟨n, ?_⟩
  rw [Algebra.smul_def, mul_one]
  simpa using hn.symm

theorem ratInt_prodLower : ProdLower ratNormFam ratInt 0 := by
  intro f hf hf0
  obtain ⟨n, rfl⟩ := mem_ratInt hf
  have hn : n ≠ 0 := by exact_mod_cast hf0
  rw [neg_zero]
  refine Finset.sum_nonneg fun σ _ => Real.log_nonneg ?_
  show 1 ≤ ‖σ (n : ℚ)‖
  rw [rat_emb_apply, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hn

theorem ratInt_unifDiscrete : UnifDiscrete ratNormFam ratInt := by
  refine ⟨1, one_pos, fun f hf hsmall => ?_⟩
  obtain ⟨n, rfl⟩ := mem_ratInt hf
  have h := hsmall (Rat.castHom ℂ)
  change ‖(Rat.castHom ℂ) (n : ℚ)‖ < 1 at h
  rw [rat_emb_apply, Rat.cast_intCast, Complex.norm_intCast] at h
  have h' : |n| < 1 := by exact_mod_cast h
  have : n = 0 := by rwa [Int.abs_lt_one_iff] at h'
  simp [this]

theorem ratInt_span : Submodule.span ℚ (ratInt : Set ℚ) = ⊤ := by
  have h1 : (1 : ℚ) ∈ ratInt := Submodule.subset_span (Set.mem_singleton 1)
  rw [Submodule.eq_top_iff']
  intro x
  have := Submodule.smul_mem (Submodule.span ℚ (ratInt : Set ℚ)) x (Submodule.subset_span h1)
  simpa using this

end ReciprocityTheory.ChartRestriction.G.TB
end

namespace PI.UnitaryGroupMassFormula.TBDisc

open NumberField ReciprocityTheory.ChartRestriction.G.TB

theorem discOfProdLower : DiscOfProdLowerSt := by
  intro K _ _ V _ _ _ Nf M A h
  refine ⟨Real.exp (-|A|), Real.exp_pos _, fun f hf hs => ?_⟩
  by_contra hne
  have hA := h f hf hne
  have hpos : ∀ σ, 0 < Nf.N σ f := fun σ =>
    lt_of_le_of_ne (Nf.nonneg σ f) (fun h0 => hne (Nf.eq_zero σ f h0.symm))
  have hlt : ∑ σ : K →+* ℂ, Real.log (Nf.N σ f) < ∑ _σ : K →+* ℂ, (-|A|) := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun σ _ => ?_)
    have := Real.log_lt_log (hpos σ) (hs σ)
    rwa [Real.log_exp] at this
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  have hc : (1 : ℝ) ≤ (Fintype.card (K →+* ℂ) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1 : (Fintype.card (K →+* ℂ) : ℝ) * (-|A|) ≤ -|A| := by
    nlinarith [abs_nonneg A]
  linarith [le_abs_self A]

section FG

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

theorem normFam_zero (Nf : NormFam K V) (σ : K →+* ℂ) : Nf.N σ 0 = 0 := by
  have h := Nf.smul σ 0 0
  simpa using h

theorem normFam_sum_le (Nf : NormFam K V) (σ : K →+* ℂ) {ι : Type*} (s : Finset ι)
    (g : ι → V) : Nf.N σ (∑ i ∈ s, g i) ≤ ∑ i ∈ s, Nf.N σ (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [normFam_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Nf.add σ _ _).trans (by linarith)

variable [FiniteDimensional K V]

noncomputable def coordMap : V →+ ((K →+* ℂ) → Fin (Module.finrank K V) → ℂ) where
  toFun v σ i := σ ((Module.finBasis K V).repr v i)
  map_zero' := by ext; simp
  map_add' v w := by ext; simp

theorem norm_le_coord (Nf : NormFam K V) (σ : K →+* ℂ) (v : V) :
    Nf.N σ v ≤ ‖coordMap (K := K) v‖ * ∑ i, Nf.N σ (Module.finBasis K V i) := by
  have hv : v = ∑ i, (Module.finBasis K V).repr v i • Module.finBasis K V i :=
    ((Module.finBasis K V).sum_repr v).symm
  have hle : ∀ i, ‖σ ((Module.finBasis K V).repr v i)‖ ≤ ‖coordMap (K := K) v‖ := fun i =>
    (norm_le_pi_norm (coordMap (K := K) v σ) i).trans (norm_le_pi_norm (coordMap (K := K) v) σ)
  calc Nf.N σ v = Nf.N σ (∑ i, (Module.finBasis K V).repr v i • Module.finBasis K V i) := by
        conv_lhs => rw [hv]
    _ ≤ ∑ i, Nf.N σ ((Module.finBasis K V).repr v i • Module.finBasis K V i) := normFam_sum_le Nf σ _ _
    _ = ∑ i, ‖σ ((Module.finBasis K V).repr v i)‖ * Nf.N σ (Module.finBasis K V i) := by
        simp only [Nf.smul]
    _ ≤ ∑ i, ‖coordMap (K := K) v‖ * Nf.N σ (Module.finBasis K V i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (Nf.nonneg _ _)
    _ = ‖coordMap (K := K) v‖ * ∑ i, Nf.N σ (Module.finBasis K V i) := by rw [Finset.mul_sum]

theorem fg_of_unifDiscrete [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nf : NormFam K V)
    (M : Submodule (𝓞 K) V) (hM : UnifDiscrete Nf M) : M.FG := by
  obtain ⟨ε, hε, hsmall⟩ := hM
  set C : ℝ := ∑ σ : K →+* ℂ, ∑ i, Nf.N σ (Module.finBasis K V i) + 1 with hC
  have hS : ∀ σ, ∑ i, Nf.N σ (Module.finBasis K V i) ≤ C - 1 := fun σ => by
    rw [hC, add_sub_cancel_right]
    exact Finset.single_le_sum (f := fun σ => ∑ i, Nf.N σ (Module.finBasis K V i))
      (fun τ _ => Finset.sum_nonneg (fun i _ => Nf.nonneg _ _)) (Finset.mem_univ σ)
  have hCpos : 0 < C := by
    have : 0 ≤ C - 1 :=
      (Finset.sum_nonneg (fun i _ => Nf.nonneg _ _)).trans (hS (Classical.arbitrary _))
    linarith
  have hδ : 0 < ε / C := div_pos hε hCpos
  have key : ∀ f ∈ M, ‖coordMap (K := K) f‖ < ε / C → f = 0 := by
    intro f hf hlt
    refine hsmall f hf (fun σ => ?_)
    have h1 := norm_le_coord Nf σ f
    have h2 : ‖coordMap (K := K) f‖ * ∑ i, Nf.N σ (Module.finBasis K V i) ≤
        ‖coordMap (K := K) f‖ * C :=
      mul_le_mul_of_nonneg_left (by linarith [hS σ]) (norm_nonneg _)
    have h3 : ‖coordMap (K := K) f‖ * C < ε := by
      rwa [lt_div_iff₀ hCpos] at hlt
    linarith
  let P : Submodule ℤ V := M.restrictScalars ℤ
  let Ψ : P →ₗ[ℤ] ((K →+* ℂ) → Fin (Module.finrank K V) → ℂ) :=
    (coordMap (K := K) (V := V)).toIntLinearMap.comp P.subtype
  have hΨ : ∀ x : P, ‖Ψ x‖ < ε / C → x = 0 := fun x hx => Subtype.ext (key x x.2 hx)
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    have : x - y = 0 := hΨ _ (by rw [map_sub, hxy, sub_self, norm_zero]; exact hδ)
    exact sub_eq_zero.mp this
  have : DiscreteTopology (LinearMap.range Ψ) := by
    refine discreteTopology_iff_isOpen_singleton.mpr (fun z => Metric.isOpen_singleton_iff.mpr
      ⟨ε / C, hδ, fun y hy => ?_⟩)
    obtain ⟨_, ⟨x, rfl⟩⟩ := z
    obtain ⟨_, ⟨x', rfl⟩⟩ := y
    rw [Subtype.dist_eq, dist_eq_norm, ← map_sub] at hy
    have := hΨ _ hy
    rw [sub_eq_zero] at this
    subst this
    rfl
  have : Module.Finite ℤ P := Module.Finite.equiv (LinearEquiv.ofInjective Ψ hinj).symm
  obtain ⟨s, hs⟩ : P.FG := Module.Finite.iff_fg.mp inferInstance
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    have : x ∈ P := by rw [← hs]; exact Submodule.subset_span hx
    exact this
  · intro x hx
    have hxP : x ∈ P := hx
    rw [← hs] at hxP
    exact Submodule.span_le_restrictScalars ℤ (𝓞 K) (s : Set V) hxP

end FG

theorem fGOfDisc : FGOfDiscSt := fun _ _ _ _ _ _ _ _ _ Nf M hM => fg_of_unifDiscrete Nf M hM

end PI.UnitaryGroupMassFormula.TBDisc
end

theorem discriminant_of_product_lower : ReciprocityTheory.ChartRestriction.G.TB.DiscOfProdLowerSt :=
  PI.UnitaryGroupMassFormula.TBDisc.discOfProdLower

theorem formalGroup_of_discriminant : ReciprocityTheory.ChartRestriction.G.TB.FGOfDiscSt :=
  PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc
end
