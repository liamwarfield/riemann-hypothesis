module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScaledIntegralHermitianInOpenSubgroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScaledIntegralHermitianInOpenSubgroup
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open Topology

theorem exists_den {F : Type} [Field F] [NumberField F] (y : F) :
    ∃ D : ℕ, 0 < D ∧ ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y := by
  have hal : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨z, hz, hint⟩ := hal.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_⟩
  have hint' : IsIntegral ℤ ((z.natAbs : F) * y) := by
    rcases Int.natAbs_eq z with h | h
    · have : ((z.natAbs : F) * y) = z • y := by
        rw [zsmul_eq_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rwa [this]
    · have : ((z.natAbs : F) * y) = -(z • y) := by
        rw [zsmul_eq_mul, ← neg_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rw [this]
      exact hint.neg
  exact ⟨IsIntegralClosure.mk' (𝓞 F) _ hint', IsIntegralClosure.algebraMap_mk' _ _ _⟩

theorem exists_common_den {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (y : ι → F) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y i := by
  choose D hD r hr using fun i => exists_den (y i)
  refine ⟨∏ i, D i, Finset.prod_pos fun i _ => hD i, fun i => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  refine ⟨(m : 𝓞 F) * r i, ?_⟩
  rw [hm, map_mul, hr, map_natCast]
  push_cast
  ring

theorem coords_den {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (o : 𝓞 E) (k : Fin d), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = (D : F) * b.repr (algebraMap (𝓞 E) E o) k := by
  let e := RingOfIntegers.basis E
  obtain ⟨D, hD, h⟩ := exists_common_den (F := F)
    (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d => b.repr (algebraMap (𝓞 E) E (e p.1)) p.2)
  refine ⟨D, hD, fun o k => ?_⟩
  choose r hr using h
  refine ⟨∑ i, (e.repr o i) • r (i, k), ?_⟩
  have ho : algebraMap (𝓞 E) E o = ∑ i, (e.repr o i) • algebraMap (𝓞 E) E (e i) := by
    conv_lhs => rw [← e.sum_repr o]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ho, map_sum, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, Finsupp.smul_apply, hr (i, k)]
  simp only [zsmul_eq_mul]
  ring

theorem nhds_unif {ι Y : Type} [Finite ι] [TopologicalSpace Y] (y0 : Y) (W : Set (ι → Y))
    (hW : W ∈ 𝓝 (fun _ => y0)) : ∃ V ∈ 𝓝 y0, ∀ y : ι → Y, (∀ i, y i ∈ V) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr ht, fun y hy => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hy i) i

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open Topology

theorem exists_smul_mem_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  intro F E _ _ _ _ _ σ hcm n U hU t ht
  obtain ⟨-, hSC, hT2, -, -, -, hF, hN, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : SecondCountableTopology (Af F) := hSC
  haveI : T2Space (Af F) := hT2
  haveI : LocallyCompactSpace (Af F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).1
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Af F)
  let b := Module.finBasis F E
  have hh := hH _ b
  set h := hh.homeomorph with hdef
  have happ : ∀ (y : Af F ⊗[F] E) k, h y k = (Algebra.TensorProduct.basis (Af F) b).repr y k :=
    fun _ _ => rfl
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.mp hU
  let G : (Fin n × Fin n × Fin (Module.finrank F E) → Af F) →
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun x a c => h.symm (fun k => x (a, c, k))
  have hG : Continuous G := by
    refine continuous_matrix fun a c => ?_
    exact h.symm.continuous.comp (continuous_pi fun k => continuous_apply _)
  have hG0 : G (fun _ => 0) = 0 := by
    ext a c
    apply h.injective
    show h (h.symm _) = h 0
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    simp
  have h0 : (0 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ U' := by
    have h1 : (0 : HermR (Af F) σ n) ∈ (U : Set (HermR (Af F) σ n)) := U.zero_mem
    rw [← hU'] at h1
    exact h1
  have hW : G ⁻¹' U' ∈ 𝓝 (fun _ => (0 : Af F)) :=
    (hU'o.preimage hG).mem_nhds (by rw [Set.mem_preimage, hG0]; exact h0)
  obtain ⟨V, hV, hVW⟩ := nhds_unif _ _ hW
  obtain ⟨N, hNpos, hNV⟩ := hN V hV
  obtain ⟨D₁, hD₁, p, hp⟩ := exists_den (t⁻¹)
  obtain ⟨D₂, hD₂, hco⟩ := coords_den b
  refine ⟨D₁ * D₂ * N, by positivity, fun c hc => ?_⟩
  let y : Fin n × Fin n × Fin (Module.finrank F E) → Af F := fun q =>
    algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 q.1 q.2.1) q.2.2)
  have hy : ∀ q, y q ∈ V := by
    rintro ⟨a, a', k⟩
    obtain ⟨o, ho⟩ := hc a a'
    obtain ⟨r, hr⟩ := hco o k
    have hval : b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k
        = (N : F) * (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) := by
      have : (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a')
          = (((D₁ * D₂ * N : ℕ) : F) / t) • algebraMap (𝓞 E) E o := by
        rw [ho]; rfl
      rw [this, map_smul, Finsupp.smul_apply, hp, hr, smul_eq_mul, div_eq_mul_inv]
      push_cast
      ring
    have hmem : algebraMap F (Af F) (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) ∈
        GlobalTheory.CompanionTheory.SW.Core.Oh F := (hF _).mpr ⟨p * r, by simp⟩
    have := hNV _ hmem
    show algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k) ∈ V
    rw [hval, map_mul, map_natCast]
    exact this
  have hGy : G y ∈ U' := hVW y hy
  have heq : G y = (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 := by
    ext a a'
    apply h.injective
    show h (h.symm _) = _
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    show y (a, a', k) = _
    have hentry : (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 a a' =
        (1 : Af F) ⊗ₜ[F] (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') := rfl
    rw [hentry, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, one_smul, Finsupp.mapRange_apply]
    rfl
  have hfin : hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c) ∈ (U : Set (HermR (Af F) σ n)) := by
    rw [← hU']
    show _ ∈ U'
    rw [← heq]
    exact hGy
  exact hfin

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScaledIntegralHermitianInOpenSubgroupStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_integral_hermitian_in_open_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitLists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitLists
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

section LimLists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem limL_allLeaves_strip (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    ∀ {N : ℕ} (t : Tr E N), t.strip.AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_shift (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) (z : ℂ) :
    ∀ {N : ℕ} (t : Tr E N), (t.shift z).AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z' => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_mono {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (h : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact h _ _
  | node t₁ t₂ i₁ i₂ => exact fun a => ⟨i₁ a.1, i₂ a.2⟩

theorem limL_disc_shift (z : ℂ) : ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Disc → (t.shift z).Disc := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr h
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

theorem limL_good_shift {z : ℂ} (hz : z.re = 0) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Good → (t.shift z).Good := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr ⟨h.1, h.2.1, by simp [h.2.2, hz]⟩
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

def LimDiscBody (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ))
    (K : Subgroup (GL (Fin M) (Af E))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ [MeasurableSpace (GA E M)] [BorelSpace (GA E M)] (μ : Measure (GA E M)) [μ.IsHaarMeasure] (R : ℝ), 0 < M →
  ReproAll E →
  ∀ V : ℕ → Submodule ℂ (Sm E M), (∀ k, IsDiscrete (V k)) → (∀ k, HasType K W (V k)) → (∀ k, InfBdd R (V k)) →
  ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (t₀ : Tr E M), StrictMono φ ∧ t₀.Good ∧ (∀ k, (t k).Disc) ∧
    (∀ k, (t k).strip = t₀.strip) ∧
    t₀.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (t₀.twists.getD i 0))) ∧
    ∀ k, Emb (V (φ k)) (· ∈ (t k).space)

theorem limL_exists_haar (M : ℕ) : ∃ (_ : MeasurableSpace (GA E M)) (_ : BorelSpace (GA E M)) (μ : Measure (GA E M)),
    μ.IsHaarMeasure := by
  letI : MeasurableSpace (GA E M) := borel _
  haveI : BorelSpace (GA E M) := ⟨rfl⟩
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E M
  exact ⟨_, inferInstance, Measure.haar, inferInstance⟩

theorem limL_lim_one (hS : ConvStrip) (hSh : ConvShift) (hC : ConvComp) (hT : TwShift) {M : ℕ} (hM : 0 < M)
    {W : Submodule ℂ (Kinf E M → ℂ)} {K : Subgroup (GL (Fin M) (Af E))}
    {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hB : LimDiscBody E M W K Ω Θ) (V : ℕ → Submodule ℂ (Sm E M)) (z : ℕ → ℂ) (R : ℝ) (hR : ReproAll E)
    (hD : ∀ k, IsDiscrete (V k)) (hz : ∀ k, (z k).re = 0) (hTy : ∀ k, HasType K W (V k))
    (hI : ∀ k, InfBdd R (V k)) (hzR : ∀ k, ‖z k‖ ≤ R) :
    ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (s : Tr E M), StrictMono φ ∧ Conv t s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧ (∀ k, (t k).Disc) ∧
      ∀ k, Emb (tw (V (φ k)) (z (φ k))) (· ∈ (t k).space) := by
  obtain ⟨_, _, μ, _⟩ := limL_exists_haar (E := E) M
  obtain ⟨φ, tt, t₀, hφ, hG, hDt, hst, hL, htw, hE⟩ := hB μ R hM hR V hD hTy hI
  obtain ⟨z₀, hz₀, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded (x := fun k => z (φ k))
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)) (fun k => by simpa using hzR (φ k))
  have hre : z₀.re = 0 := by
    have h1 : Tendsto (fun k => (z (φ (ψ k))).re) atTop (𝓝 z₀.re) :=
      (Complex.continuous_re.tendsto z₀).comp hlim
    simp only [hz, ] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  have hpos : t₀.AllLeaves (fun M _ => 0 < M) := limL_allLeaves_mono (fun _ _ h => h.1) hL
  have hposk : ∀ k, (tt k).AllLeaves (fun M _ => 0 < M) := fun k => by
    rw [← limL_allLeaves_strip, hst k, limL_allLeaves_strip]
    exact hpos
  have hconv : Conv tt t₀ := (hS E M tt t₀).2 ⟨hst, htw⟩
  have hconv' : Conv (fun k => (tt (ψ k)).shift (z (φ (ψ k)))) (t₀.shift z₀) :=
    hSh E M _ t₀ _ z₀ (hC E M tt t₀ ψ hconv hψ) hlim
  have hL' : (t₀.shift z₀).AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) :=
    (limL_allLeaves_shift _ _ _).2 hL
  exact ⟨fun k => φ (ψ k), fun k => (tt (ψ k)).shift (z (φ (ψ k))), t₀.shift z₀, hφ.comp hψ, hconv',
    red_of_leaves hL', limL_good_shift hre hpos hG, hL', fun k => limL_disc_shift _ (hposk _) (hDt _),
    fun k => hT E M _ _ _ (hD _).stable (hE _)⟩

end LimLists

theorem limLists : ConvStrip → ConvShift → ConvComp → LimLists := by
  intro hS hSh hC h5 hT E _ _ _ N Ωs hΩs
  have h1 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)),
      ∃ Ω : ∀ M' : ℕ, Set (Submodule ℂ (Kinf E M' → ℂ)), KTypes E Ω ∧
        (FiniteDimensional ℂ W → ∀ K : Subgroup (GL (Fin M) (Af E)), IsOpen (K : Set (GL (Fin M) (Af E))) →
          ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧ LimDiscBody E M W K Ω Θ) := by
    intro M W
    by_cases hW : FiniteDimensional ℂ W
    · obtain ⟨Ω, hΩ, h⟩ := h5 E M W hW
      exact ⟨Ω, hΩ, fun _ K hK => h K hK⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, by simp⟩, fun h => absurd h hW⟩
  choose Om hOm hOm' using h1
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, Om M W M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ => (hOm M W M').1, ?_⟩
    intro W' hW'
    simp only [Set.mem_iUnion] at hW'
    obtain ⟨M, _, W, _, h⟩ := hW'
    exact (hOm M W M').2 W' h
  intro Θs hΘs
  have h2 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)) (K : Subgroup (GL (Fin M) (Af E))),
      ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧
        (FiniteDimensional ℂ W → IsOpen (K : Set (GL (Fin M) (Af E))) → LimDiscBody E M W K (Om M W) Θ) := by
    intro M W K
    by_cases h : FiniteDimensional ℂ W ∧ IsOpen (K : Set (GL (Fin M) (Af E)))
    · obtain ⟨Θ, hΘ, hb⟩ := hOm' M W h.1 K h.2
      exact ⟨Θ, hΘ, fun _ _ => hb⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, fun _ hk => False.elim hk⟩,
        fun a b => absurd ⟨a, b⟩ h⟩
  choose Th hTh hTh' using h2
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, ⋃ K ∈ Θs M, Th M W K M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ =>
      (hΘs M).1.biUnion fun K _ => (hTh M W K M').1, ?_⟩
    intro K' hK'
    simp only [Set.mem_iUnion] at hK'
    obtain ⟨M, _, W, _, K, _, h⟩ := hK'
    exact (hTh M W K M').2 K' h
  intro M hM hMN V z R hR hD hz hTy hI hzR
  choose Kk hKk Wk hWk hty using hTy
  have hfin : (Θs M ×ˢ Ωs M).Finite := (hΘs M).1.prod (hΩs M).1
  haveI := hfin.to_subtype
  obtain ⟨⟨⟨K, W⟩, hKW⟩, hinf⟩ := Finite.exists_infinite_fiber
    (fun k : ℕ => (⟨(Kk k, Wk k), hKk k, hWk k⟩ : ↥(Θs M ×ˢ Ωs M)))
  have hfr : ∃ᶠ k in atTop, Kk k = K ∧ Wk k = W := by
    refine Nat.frequently_atTop_iff_infinite.2 ((Set.infinite_coe_iff.1 hinf).mono ?_)
    intro k hk
    have h := congrArg Subtype.val (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hk))
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨a, ha, hak⟩ := extraction_of_frequently_atTop hfr
  have hK : K ∈ Θs M := hKW.1
  have hW : W ∈ Ωs M := hKW.2
  have hbody : LimDiscBody E M W K (Om M W) (Th M W K) := hTh' M W K ((hΩs M).2 W hW) ((hΘs M).2 K hK)
  have htyp : ∀ k, HasType K W (V (a k)) := fun k => by
    have h := hty (a k)
    rwa [(hak k).1, (hak k).2] at h
  obtain ⟨φ, t, s, hφ, hc, hr, hg, hl, hd, he⟩ := limL_lim_one hS hSh hC hT hM hbody (fun k => V (a k))
    (fun k => z (a k)) R hR (fun k => hD _) (fun k => hz _) htyp (fun k => hI _) (fun k => hzR _)
  refine ⟨fun k => a (φ k), t, s, ha.comp hφ, hc, hr, hg, limL_allLeaves_mono ?_ hl, hd, he⟩
  rintro M' V' ⟨-, K'', hK'', W'', hW'', h⟩
  refine Or.inr ⟨K'', ?_, W'', ?_, h⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, K, hK, hK''⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, hW''⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitListsStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_lists : GlobalTheory.CompanionTheory.EGlue.ConvStrip → GlobalTheory.CompanionTheory.EGlue.ConvShift → GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimLists := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.limLists | exact GlobalTheory.CompanionTheory.EGlue.limLists | (intros; apply GlobalTheory.CompanionTheory.EGlue.limLists <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FubiniFourierHermitianIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FubiniFourierHermitianIntegral
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Abstract

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]

theorem fubini_unimod {dy : Measure Y} {dx : Measure X} [SFinite dy] [SFinite dx] {f : Y → ℂ} {g : X → ℂ}
    (hf : Integrable f dy) (hg : Integrable g dx) {u : Y → X → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (dy.prod dx)) (hn : ∀ y x, ‖u y x‖ = 1) :
    ∫ y, f y * ∫ x, g x * u y x ∂dx ∂dy = ∫ x, g x * ∫ y, f y * u y x ∂dy ∂dx := by
  have h0 : Integrable (fun z : Y × X => f z.1 * g z.2) (dy.prod dx) := hf.mul_prod hg
  have hint : Integrable (Function.uncurry fun y x => f y * (g x * u y x)) (dy.prod dx) := by
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine (h0.aestronglyMeasurable.mul hu).congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hn, mul_one, le_refl]
  have hL : ∀ y, f y * ∫ x, g x * u y x ∂dx = ∫ x, f y * (g x * u y x) ∂dx := fun y =>
    (integral_const_mul _ _).symm
  have hR : ∀ x, g x * ∫ y, f y * u y x ∂dy = ∫ y, f y * (g x * u y x) ∂dy := fun x => by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL, hR]
  exact integral_integral_swap hint

end Abstract

section Pair

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem pairHerm_sub (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S A B : HermR R σ n) :
    pairHerm R σ n S (A - B) = pairHerm R σ n S A - pairHerm R σ n S B := by
  simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]

theorem half_trace_mul_eq_pairHerm (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (G : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem half_trace_mul_eq_pairHerm' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((G : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  rw [Matrix.trace_mul_comm]
  exact half_trace_mul_eq_pairHerm R σ S G

theorem continuous_pairHerm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [Module.Finite F E] (σ : E →ₐ[F] E) (n : ℕ) :
    Continuous fun z : HermR R σ n × HermR R σ n => pairHerm R σ n z.1 z.2 := by
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing R
  unfold pairHerm
  refine continuous_const.mul ((GlobalTheory.CompanionTheory.SW.TopK.continuous_trace R).comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
    ((continuous_subtype_val.comp continuous_snd).matrix_elem b a)

end Pair

section Cm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_pairHerm_gramH_sub (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (hg : Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) (c : HermR R σ n) :
    Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2 - c) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hp := continuous_pairHerm (F := F) (E := E) R σ n
  have hgH : Continuous fun x : Fin n → Fin M → R ⊗[F] E => gramH hCM hJ R x :=
    Continuous.subtype_mk hg _
  have m1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, gramH hCM hJ R z.2) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst (hgH.comp continuous_snd)
  have m2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, c) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst continuous_const
  have h1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2) := by
    have h := hp.comp m1
    exact h
  have h2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) => pairHerm R σ n z.1 c := by
    have h := hp.comp m2
    exact h
  have := h1.sub h2
  refine this.congr fun z => ?_
  exact (pairHerm_sub R σ z.1 _ c).symm

end Cm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem chiT_eq (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c) (y : HermR (AF F) σ n) :
    chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := by
  rw [← half_trace_mul_eq_pairHerm' (AF F) σ y (hermOf (AF F) σ T hT)]
  rfl

theorem psi_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x))) * chiT σ ψ T y =
    ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) := by
  have h2 : algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) :=
    half_trace_mul_eq_pairHerm (AF F) σ y (gramH hCM hJ (AF F) x)
  rw [h2, chiT_eq σ ψ T hT, ← AddChar.map_add_eq_mul, pairHerm_sub, sub_eq_add_neg]

theorem starN_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) :
    GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y =
      ∫ x, Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := by
  rw [GlobalTheory.CompanionTheory.SiegelND.starN, ← integral_mul_const]
  congr 1
  funext x
  rw [mul_assoc, psi_mul_chiT hCM hJ ψ T hT]

end Adelic

end GlobalTheory.CompanionTheory.SiegelND.Coef

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN_fouH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) (hCM : IsCMExt F E σ), ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)), SFinite dx → SFinite db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ) db → (∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T) ∧ ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ M J hJ n hCM ψ hψ dx db _ _ Φ hΦ τ hTh hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨hψc, hψn, -⟩ := hψ
  have hpc := continuous_pairHerm_gramH_sub (AF F) hCM hJ (hg n M J) (hermOf (AF F) σ T hT)
  refine ⟨?_, ?_⟩
  · have hp := continuous_pairHerm (F := F) (E := E) (AF F) σ n
    have m : Continuous fun y : HermR (AF F) σ n =>
        ((y, hermOf (AF F) σ T hT) : HermR (AF F) σ n × HermR (AF F) σ n) :=
      Continuous.prodMk continuous_id continuous_const
    have h1 := (hp.comp m).neg
    have h2 := hψc.comp h1
    have : GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T =
        fun y => ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := funext (chiT_eq σ ψ T hT)
    rw [this]
    exact h2
  · have hmeas : AEStronglyMeasurable (Function.uncurry fun (y : HermR (AF F) σ n)
        (x : Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT))) (db.prod dx) :=
      (hψc.comp hpc).aestronglyMeasurable
    have key := fubini_unimod hTh hΦ hmeas (fun y x => hψn _)
    have hL : ∀ y, fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y) =
        fouH σ ψ db τ y * ∫ x, Φ x *
          ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := fun y => by
      rw [starN_mul_chiT hCM hJ ψ dx Φ T hT y]
    have hR : ∀ x, ∫ y, fouH σ ψ db τ y *
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂db =
        τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) := fun x => by
      rw [hinv, neg_sub]
    simp_rw [hL]
    rw [key]
    simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FubiniFourierHermitianIntegralStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubini_fourier_hermitian_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) (hCM : IsCMExt F E σ), ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)), SFinite dx → SFinite db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ) db → (∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T) ∧ ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∂dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN_fouH | exact GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN_fouH | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN_fouH <;> assumption)
end
end
