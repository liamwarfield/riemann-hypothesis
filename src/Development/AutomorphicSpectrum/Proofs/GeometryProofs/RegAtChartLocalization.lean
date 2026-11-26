module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PPshLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompat
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chart_regAt_localisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v :=
  PositivityTheory.HtPt.Ma.regat_loc

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalizationStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_chart_localization : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation | exact GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation | (intros; apply GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem regAt_isLocalRing (q : Cpt ξ) : IsLocalRing (regAt ξ q) :=
  IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective

theorem not_inFibre_of_isUnit {q : Cpt ξ} {p : ℕ} (h : IsUnit (p : regAt ξ q)) : ¬ InFibre ξ p q := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  have e : (p : Ω) * (v : Ω) = 1 := by
    have := congrArg (Subtype.val) hv
    simpa using this
  have hp : (p : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one e
  have hreg : (p : Ω) ∈ regAt ξ q := natCast_mem (regAt ξ q) p
  have hinv : (p : Ω)⁻¹ ∈ regAt ξ q := by
    rw [eq_comm.1 (eq_inv_of_mul_eq_one_right e)]
    exact v.2
  exact not_not.2 ⟨hp, hreg, hinv⟩

theorem inFibre_unique {q : Cpt ξ} {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (h : InFibre ξ p q)
    (h' : InFibre ξ p' q) : p' = p := by
  by_contra hne
  haveI := regAt_isLocalRing (ξ := ξ) q
  have hc : IsCoprime (p : ℤ) (p' : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hp').2 (Ne.symm hne))
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (regAt ξ q))
  simp only [eq_intCast, Int.cast_natCast] at hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with hu | hu
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h'

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePoint
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chart_prime_point : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) :=
  @PositivityTheory.HtPt.Ma.prime_pt

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePointStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_prime_existsUnique_point : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chart_prime_point | exact GlobalTheory.CompanionTheory.Ar.chart_prime_point | (intros; apply GlobalTheory.CompanionTheory.Ar.chart_prime_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem mem_btOrder_iff_mem_btSet : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U :=
  PositivityTheory.HtPt.Twhopf.mem_order

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSetStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_btOrder_iff_btSet : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal
namespace GlobalTheory.CompanionTheory.AnForm.PshLocal

open Filter Topology ReciprocityTheory.AnForm.A

theorem isPsh_mono {n : ℕ} {V W : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (hWV : W ⊆ V)
    (h : IsPsh V φ) : IsPsh W φ := by
  unfold ReciprocityTheory.AnForm.A.IsPsh at h ⊢
  obtain ⟨hu, hm⟩ := h
  exact ⟨hu.mono hWV, fun z w hzw => hm z w fun ζ hζ => hWV (hzw ζ hζ)⟩

theorem isPsh_of_locally :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ), IsOpen U →
      (∀ z ∈ U, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) →
      ReciprocityTheory.AnForm.A.IsPsh U φ := by
  intro n U φ hU hloc
  have hloc' : ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ IsPsh W φ := by
    intro p hp
    obtain ⟨V, hV, hpV, hψ⟩ := hloc p hp
    exact ⟨V ∩ U, hV.inter hU, ⟨hpV, hp⟩, Set.inter_subset_right, isPsh_mono Set.inter_subset_left hψ⟩
  have hlocg : ∀ k : ℕ, ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
      IsPsh W (fun x => max (φ x) (-(k : ℝ))) := by
    intro k p hp
    obtain ⟨W, hW, hpW, hWU, hψ⟩ := hloc' p hp
    exact ⟨W, hW, hpW, hWU, GroundTheory.Heights₂.Heights.NineStatements.PshLocal.isPsh_max hψ _⟩
  have husc := GroundTheory.Heights₂.Heights.NineStatements.PshLocal.usc hloc'
  unfold ReciprocityTheory.AnForm.A.IsPsh
  refine ⟨husc, ?_⟩
  intro z w hzw
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))
  let F : ℝ → ℝ := fun θ => φ (z + circleMap 0 1 θ • w)
  let f : ℕ → ℝ → ℝ := fun k θ => max (F θ) (-(k : ℝ))
  have hcore : ∀ k : ℕ, IntervalIntegrable (f k) MeasureTheory.volume 0 (2 * Real.pi) ∧
      max (φ z) (-(k : ℝ)) ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f k θ := fun k =>
    GroundTheory.Heights₂.Heights.NineStatements.PshLocal.core hU (hlocg k) z w hzw (c := -(k : ℝ))
      (fun θ => le_max_right _ _)
  have hint : ∀ k, MeasureTheory.Integrable (f k) μ := fun k =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mp (hcore k).1
  have hanti : ∀ θ, Antitone fun k : ℕ => f k θ := by
    intro θ
    refine antitone_nat_of_succ_le fun k => ?_
    show max (F θ) (-(((k + 1 : ℕ)) : ℝ)) ≤ max (F θ) (-(k : ℝ))
    push_cast
    exact max_le_max le_rfl (by linarith)
  have htend : ∀ θ, Tendsto (fun k : ℕ => f k θ) atTop (𝓝 (F θ)) := by
    intro θ
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈-F θ⌉₊) fun k hk => ?_
    have hc := Nat.le_ceil (-F θ)
    have hk' : ((⌈-F θ⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    exact max_eq_left (by linarith)
  have hlow : ∀ k : ℕ, 2 * Real.pi * φ z ≤ ∫ θ, f k θ ∂μ := by
    intro k
    have h1 := le_trans (le_max_left (φ z) (-(k : ℝ))) (hcore k).2
    rw [intervalIntegral.integral_of_le h2π] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 h2π
    rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at h3
  have hFmeas : MeasureTheory.AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hint k).aestronglyMeasurable)
      (Filter.Eventually.of_forall htend)
  have hGnn : ∀ (k : ℕ) θ, 0 ≤ f 0 θ - f k θ := fun k θ => sub_nonneg.mpr (hanti θ (Nat.zero_le k))
  have hFle : ∀ θ, F θ ≤ f 0 θ := fun θ => le_max_left _ _
  have hGint : MeasureTheory.Integrable (fun θ => f 0 θ - F θ) μ := by
    refine ⟨(hint 0).aestronglyMeasurable.sub hFmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun θ => sub_nonneg.mpr (hFle θ))]
    have hlim : ∀ θ, Tendsto (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop
        (𝓝 (ENNReal.ofReal (f 0 θ - F θ))) :=
      fun θ => (ENNReal.continuous_ofReal.tendsto _).comp ((htend θ).const_sub _)
    have hterm : ∀ k : ℕ, ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ ≤
        ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) := by
      intro k
      have e := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun θ => f 0 θ - f k θ)
        ((hint 0).sub (hint k)) (Filter.Eventually.of_forall (hGnn k))
      rw [← e, MeasureTheory.integral_sub (hint 0) (hint k)]
      exact ENNReal.ofReal_le_ofReal (by linarith [hlow k])
    calc ∫⁻ θ, ENNReal.ofReal (f 0 θ - F θ) ∂μ
        = ∫⁻ θ, liminf (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop ∂μ := by
          congr 1
          funext θ
          exact ((hlim θ).liminf_eq).symm
      _ ≤ liminf (fun k : ℕ => ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ) atTop :=
          MeasureTheory.lintegral_liminf_le' fun k => ((hint 0).sub (hint k)).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) :=
          Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hterm)
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hFint : MeasureTheory.Integrable F μ :=
    ((hint 0).sub hGint).congr (Filter.Eventually.of_forall fun θ => by simp)
  have hlimI := MeasureTheory.integral_tendsto_of_tendsto_of_antitone hint hFint
    (Filter.Eventually.of_forall hanti) (Filter.Eventually.of_forall htend)
  have hge : 2 * Real.pi * φ z ≤ ∫ θ, F θ ∂μ := ge_of_tendsto' hlimI hlow
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mpr hFint, ?_⟩
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le h2π]
  have h4 := mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr h2π)
  rwa [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul] at h4

end GlobalTheory.CompanionTheory.AnForm.PshLocal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocalStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plurisubharmonic_local : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ), IsOpen U → (∀ z ∈ U, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) → ReciprocityTheory.AnForm.A.IsPsh U φ := by
  first | exact @GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally | exact GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally | (intros; apply GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFraction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFraction
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_local_mono_frac : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) :=
  @PositivityTheory.HtPt.Ma.reg_local

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFractionStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_local_order_fraction : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac | exact GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeClosure
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeClosure
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem coh_vb_images_sums_multiples : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (L L' : Lat ξ E) (T : Set (Cpt ξ)), (∀ r V, L.IsVBOn T r V → L.IsCohOn T) ∧ (∀ φ : E →ₗ[Ω] E', L.IsCohOn T → (L.map φ).IsCohOn T) ∧ (L.IsCohOn T → L'.IsCohOn T → Lat.IsCohOn (fun p => L p ⊔ L' p : Lat ξ E) T) ∧ (∀ (r : ℕ) (V : Submodule Ω E) (a : Ω), a ≠ 0 → L.IsVBOn T r V → (L.scale a).IsVBOn T r V) ∧ (∀ (r : ℕ) (V : Submodule Ω E), L.IsCohOn T → (∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) → L.IsVBOn T r V) :=
  @PositivityTheory.HtPt.Mc.coh_ops

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeClosureStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_lattice_closure : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (L L' : Lat ξ E) (T : Set (Cpt ξ)), (∀ r V, L.IsVBOn T r V → L.IsCohOn T) ∧ (∀ φ : E →ₗ[Ω] E', L.IsCohOn T → (L.map φ).IsCohOn T) ∧ (L.IsCohOn T → L'.IsCohOn T → Lat.IsCohOn (fun p => L p ⊔ L' p : Lat ξ E) T) ∧ (∀ (r : ℕ) (V : Submodule Ω E) (a : Ω), a ≠ 0 → L.IsVBOn T r V → (L.scale a).IsVBOn T r V) ∧ (∀ (r : ℕ) (V : Submodule Ω E), L.IsCohOn T → (∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) → L.IsVBOn T r V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coh_vb_images_sums_multiples | exact GlobalTheory.CompanionTheory.Ar.coh_vb_images_sums_multiples | (intros; apply GlobalTheory.CompanionTheory.Ar.coh_vb_images_sums_multiples <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem exists_isFinite_open_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  refine ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart f, fun x hx => ?_⟩
  exact GlobalTheory.mem_finitePart_of_eq_closedPoint f x hx

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePartStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselian_quasi_finite_finite_part : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian | exact GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoords
noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChartSmooth

open GlobalTheory.CompanionTheory.Ar.ChartFin

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem mem_adjoin_iff {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q) (T : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {U : X.Opens}
    (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (h : genPt ξ ∈ U) (a : Ω) :
    a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ ∃ s : Γ(X, U), ChartFin.secVal ξ U h s = a := by
  rw [T.ring c hc a]
  constructor
  · intro H
    refine exists_secVal hall T.gen.inj U h a fun q hq => ?_
    obtain ⟨h', hi⟩ := (hU q).1 hq
    exact H _ hi
  · rintro ⟨s, rfl⟩ p hp
    have hq : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
    exact ⟨_, genMap_germ ξ h hq p.2 s⟩

theorem exists_secEquiv {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q) (T : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {U : X.Opens}
    (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (h : genPt ξ ∈ U) :
    ∃ E : Γ(X, U) ≃+* Algebra.adjoin o (Set.range fun j => x j / x c),
      ∀ s, ((E s : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) = ChartFin.secVal ξ U h s := by
  have hm : ∀ s, ChartFin.secVal ξ U h s ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := fun s =>
    (mem_adjoin_iff hall T hc hU h _).2 ⟨s, rfl⟩
  refine ⟨RingEquiv.ofBijective ((ChartFin.secVal ξ U h).codRestrict _ hm) ⟨fun a b e => ?_, fun r => ?_⟩, fun _ => rfl⟩
  · exact secVal_injective hall T.gen.inj U h (congrArg Subtype.val e)
  · obtain ⟨s, hs⟩ := (mem_adjoin_iff hall T hc hU h r).1 r.2
    exact ⟨s, Subtype.ext hs⟩

variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω']

theorem inChart_map {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} {κ κ' : Type} {x : κ → Ω} {x' : κ' → Ω'} (hall : ∀ q : X, genPt ξ ⤳ q)
    (T : CoordTie ℤ ξ x) (T' : CoordTie ℤ ξ' x') (hd : Dominates ξ' ξ f i) {c : κ} {c' : κ'} (hc : x c ≠ 0)
    (hc' : x' c' ≠ 0) (hi : ∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'))
    (p' : Cpt ξ') (hp' : InChart ξ' x' c' p') : InChart ξ x c ⟨f p'.1, hall _⟩ := by
  obtain ⟨h, hreg, hunit⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd p'
  obtain ⟨d, hd0, hdr⟩ := T.cover ⟨f p'.1, h⟩
  have ha0 : x c / x d ≠ 0 := div_ne_zero hc hd0
  have hinv : (i (x c / x d))⁻¹ ∈ regAt ξ' p' := by
    rw [← map_inv₀, inv_div]
    exact (T'.ring c' hc' _).1 (hi d) p' hp'
  have hu := hunit T'.gen _ (hdr c) ⟨(map_ne_zero i).2 ha0, hreg _ (hdr c), hinv⟩
  refine ⟨hc, fun j => ?_⟩
  have e : x j / x c = x j / x d * (x c / x d)⁻¹ := by
    field_simp
  rw [e]
  exact mul_mem (hdr j) hu.2.2

theorem smooth_chartRing (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (i : Ω₀ →+* Ω) (κ κ' : Type) (x : κ → Ω₀) (x' : κ' → Ω) :
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ x → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → Smooth f → ∀ (c : κ) (c' : κ'), x c ≠ 0 → x' c' ≠ 0 →
    (∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) →
    ∃ φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'),
      (∀ a, ((φ a : Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) : Ω) = i a) ∧ φ.Smooth := by
  intro hall hall' T T' hd hsm c c' hc hc' hi
  obtain ⟨U, hUa, hUm⟩ := T.affine c hc
  obtain ⟨U', hU'a, hU'm⟩ := T'.affine c' hc'
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt T.gen hc⟩
  have hg' : genPt ξ' ∈ U' := (hU'm _).2 ⟨specializes_rfl, inChart_genPt T'.gen hc'⟩
  have hle : U' ≤ f ⁻¹ᵁ U := by
    intro q hq
    obtain ⟨h, hin⟩ := (hU'm q).1 hq
    exact (hUm (f q)).2 ⟨hall _, inChart_map hall T T' hd hc hc' hi ⟨q, h⟩ hin⟩
  obtain ⟨E, hE⟩ := exists_secEquiv hall T hc hUm hg
  obtain ⟨E', hE'⟩ := exists_secEquiv hall' T' hc' hU'm hg'
  have hs : (f.appLE U U' hle).hom.Smooth := Smooth.smooth_appLE (f := f) hUa hU'a hle
  have hval : ∀ s, ChartFin.secVal ξ' U' hg' ((f.appLE U U' hle).hom s) = i (ChartFin.secVal ξ U hg s) := by
    intro s
    have h2 : genPt ξ' ∈ f ⁻¹ᵁ U := hle hg'
    rw [← secVal_app hd U hg h2 s, ← secVal_res ξ' (homOfLE hle) hg' h2 ((f.app U).hom s)]
    rfl
  refine ⟨(E'.toRingHom.comp (f.appLE U U' hle).hom).comp E.symm.toRingHom, fun a => ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := E.surjective a
    simp only [RingHom.comp_apply]
    have : E.symm.toRingHom (E s) = s := E.symm_apply_apply s
    rw [this]
    exact (hE' _).trans ((hval s).trans (congrArg i (hE s).symm))
  · have hr := RingHom.Smooth.propertyIsLocal.respectsIso
    exact hr.2 _ E.symm (hr.1 _ E' hs)

end GlobalTheory.CompanionTheory.Ar.ChartSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoordsStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_smooth_map_coords : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (i : Ω₀ →+* Ω) (κ κ' : Type) (x : κ → Ω₀) (x' : κ' → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ x → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → Smooth f → ∀ (c : κ) (c' : κ'), x c ≠ 0 → x' c' ≠ 0 →
    (∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) →
    ∃ φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'),
      (∀ a, ((φ a : Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) : Ω) = i a) ∧ φ.Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing | exact GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueLatOfChartBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TieVB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

noncomputable def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq t) = secVal ξ U h t := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have e2 : X.presheaf.germ U q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e)
  exact congrArg (fun f => f.hom t) e2

theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · intro hs
    have hu := hs.map (genMap ξ q)
    refine ⟨hu.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := hs
    refine ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).1, ?_⟩
    have : genMap ξ q u.1 * genMap ξ q (u⁻¹ : (X.presheaf.stalk q.1)ˣ).1 = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact eq_inv_of_mul_eq_one_right this
  · rintro ⟨h0, -, ⟨s', hs'⟩⟩
    have : s * s' = 1 := hi (by rw [map_mul, hs', map_one, mul_inv_cancel₀ h0])
    exact IsUnit.of_mul_eq_one _ this

theorem mem_basicOpen_iff (hg : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (t : Γ(X, U)) : q.1 ∈ X.basicOpen t ↔ unitAt ξ q (secVal ξ U h t) := by
  rw [Scheme.mem_basicOpen X t q.1 hq, isUnit_iff_unitAt (hg.inj q), genMap_germ U h q hq]

theorem unitAt_mul {p : Cpt ξ} {s t : Ω} (hs : unitAt ξ p s) (ht : unitAt ξ p t) : unitAt ξ p (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, mul_mem hs.2.1 ht.2.1, by rw [mul_inv]; exact mul_mem hs.2.2 ht.2.2⟩

theorem unitAt_one (p : Cpt ξ) : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp [one_mem]⟩

theorem regAt_genPt (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) := by
  obtain ⟨s, rfl⟩ := hg.bij.2 a
  refine ⟨s, ?_⟩
  unfold genMap
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  erw [Category.id_comp]
  rfl

section Chart

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

theorem exists_chart (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ (U : X.Opens) (h : genPt ξ ∈ U), IsAffineOpen U ∧ (∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q) ∧
      (∀ q : X, q ∈ U → genPt ξ ⤳ q) ∧
      Function.Injective (secVal ξ U h) ∧
      ∀ a : Ω, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ a ∈ (secVal ξ U h).range := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have h : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc, fun c' => regAt_genPt hT.gen _⟩
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h2, _⟩ := (hmem q).1 hq
    exact h2
  have hUq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun hq => by obtain ⟨_, h2⟩ := (hmem q.1).1 hq; exact h2, fun hq => (hmem q.1).2 ⟨q.2, hq⟩⟩
  obtain ⟨hinj, hran⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hT.gen U h hsp
  refine ⟨U, h, hU, hUq, hsp, hinj, fun a => ?_⟩
  rw [hT.ring c hc a]
  refine Iff.trans ?_ (hran a).symm
  exact forall_congr' fun q => (by rw [hUq q])

theorem exists_point (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) (P : Ideal (chartRing o x c)) (hP : P.IsPrime) :
    ∃ p : Cpt ξ, InChart ξ x c p ∧ ∀ s : chartRing o x c, s ∈ P ↔ ¬ unitAt ξ p s := by
  obtain ⟨U, h, hU, hUq, hsp, -, hran⟩ := exists_chart hT hc
  let φ : Γ(X, U) →+* chartRing o x c :=
    (secVal ξ U h).codRestrict (chartRing o x c) fun t => (hran _).2 ⟨t, rfl⟩
  let y : PrimeSpectrum Γ(X, U) := ⟨P.comap φ, inferInstance⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this
  let q : Cpt ξ := ⟨_, hsp _ hyU⟩
  refine ⟨q, (hUq q).1 hyU, fun s => ?_⟩
  obtain ⟨t, ht⟩ := (hran s).1 s.2
  have hst : s = φ t := Subtype.ext ht.symm
  have key : q.1 ∈ X.basicOpen t ↔ t ∉ P.comap φ := by
    show y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen t ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  have h2 := mem_basicOpen_iff hT.gen U h q hyU t
  have h3 : (s : Ω) = secVal ξ U h t := ht.symm
  rw [h3, ← h2, key, hst, Ideal.mem_comap, not_not]

theorem exists_den (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) : ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s * a ∈ chartRing o x c :=
  (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ x hT c p hp a).1 ha

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_den_span (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) (M : AddSubgroup E)
    (hM : ∀ a ∈ chartRing o x c, ∀ e ∈ M, a • e ∈ M) {e : E}
    (he : e ∈ Submodule.span (regAt ξ p) (M : Set E)) :
    ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s • e ∈ M := by
  induction he using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_mem _, unitAt_one p, by simpa using hv⟩
  | zero => exact ⟨1, one_mem _, unitAt_one p, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htM⟩ := hv
    refine ⟨s * t, mul_mem hs ht, unitAt_mul hsu htu, ?_⟩
    have h1 : (s * t) • (u + v) = t • s • u + s • t • v := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [h1]
    exact add_mem (hM t ht _ hsM) (hM s hs _ htM)
  | smul r u _ hu =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htr⟩ := exists_den hT hp r.2
    refine ⟨t * s, mul_mem ht hs, unitAt_mul htu hsu, ?_⟩
    have h1 : (t * s) • r • u = (t * (r : Ω)) • s • u := by
      rw [Subring.smul_def, smul_smul, smul_smul]
      congr 1
      ring
    rw [h1]
    exact hM _ htr _ hsM

end Chart

section Bundle

variable {κ : Type} {x : κ → Ω} {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

end Bundle

end GlobalTheory.CompanionTheory.Ar.TieVB

namespace GlobalTheory.CompanionTheory.Ar

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin
namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]

def latOn (D : HTChart A K c p R N (Module.Dual K Li)) (V : Submodule K Li) (t : K) (B : Subring K) : Set Li :=
  {e | e ∈ V ∧ ∀ w ∈ D.om', t * w e ∈ B}

def IsLocIn (A : Type) {K : Type} [CommRing A] [Field K] [Algebra A K] (B : Subring K) : Prop :=
  (∀ a : A, algebraMap A K a ∈ B) ∧
    ∀ b ∈ B, ∃ u a : A, algebraMap A K u ≠ 0 ∧ (algebraMap A K u)⁻¹ ∈ B ∧ algebraMap A K u * b = algebraMap A K a

end
end GlobalTheory.CompanionTheory.Ar.Flat.HTL

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem exists_extend_lin {A K V W : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W]
    (M : Submodule A V) (g : M →ₗ[A] W) : ∃ G : V →ₗ[K] W, ∀ z : M, G z = g z := by
  classical
  obtain ⟨b, hbM, -, hsp, hli⟩ := exists_linearIndepOn_id_extension (K := K) (s := ∅) (t := (M : Set V)) (by simp) (by simp)
  let bb := Basis.extend hli
  let f : V → W := fun x => if h : x ∈ M then g ⟨x, h⟩ else 0
  let G : V →ₗ[K] W := bb.constr K fun i => f i.1
  have hGb : ∀ x ∈ b, G x = f x := fun x hx => by
    have hx' : x ∈ hli.extend (Set.subset_univ b) := hli.subset_extend _ hx
    have := bb.constr_basis K (fun i => f i.1) ⟨x, hx'⟩
    simpa [bb, G, Basis.extend_apply_self] using this
  have hG : ∀ x (hx : x ∈ Submodule.span A b) (h : x ∈ M), G x = g ⟨x, h⟩ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro h
      rw [hGb x hx]
      simp [f, h]
    | zero =>
      intro h
      have : (⟨0, h⟩ : M) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have h2 : y ∈ M := Submodule.span_le.2 hbM hy
      have : (⟨x + y, h⟩ : M) = ⟨x, h1⟩ + ⟨y, h2⟩ := rfl
      rw [map_add (f := _), ihx h1, ihy h2, this, map_add (f := _)]
    | smul a x hx ih =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have : (⟨a • x, h⟩ : M) = a • ⟨x, h1⟩ := rfl
      rw [this, g.map_smul, ← ih h1, LinearMap.map_smul_of_tower]
  have hden : ∀ v ∈ Submodule.span K b, ∃ a : A, algebraMap A K a ≠ 0 ∧ a • v ∈ Submodule.span A b := by
    intro v hv
    have hinj := IsFractionRing.injective A K
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simp, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨a', ha', hy⟩ := hy
      refine ⟨a * a', by rw [map_mul]; exact mul_ne_zero ha ha', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul r x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) r
      have hv0 : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hv)
      refine ⟨v * a, by rw [map_mul]; exact mul_ne_zero hv0 ha, ?_⟩
      have : (v * a) • (algebraMap A K u / algebraMap A K v) • x = u • a • x := by
        rw [← algebraMap_smul K (v * a), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact Submodule.smul_mem _ _ hx
  refine ⟨G, fun z => ?_⟩
  obtain ⟨a, ha, haz⟩ := hden z (hsp z.2)
  have h1 := hG _ haz (M.smul_mem a z.2)
  have h2 : (⟨a • (z : V), M.smul_mem a z.2⟩ : M) = a • z := rfl
  rw [h2, g.map_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul K a (G (z : V)), ← algebraMap_smul K a (g z)] at h1
  exact smul_right_injective W ha h1

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]
  (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li)

theorem eigProj_dual (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w = w ∘ₗ eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ := by
  ext v
  simp [eigProj, LinearMap.sum_apply, hact]

theorem eigProj_apply (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w e = w e := by
  rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
  congr 1
  have h1 : ∀ a : 𝓞 E, ρ (RingOfIntegers.mapRingEquiv c a) e = σ (a : E) • e := fun a => by
    rw [LatBasic.mem_eigSp.1 he]
    simp [hc]
  have h2 : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ e = e := by
    apply LatBasic.eigProj_of_mem
    rw [LatBasic.mem_eigSp]
    exact fun a => h1 a
  exact h2

theorem exists_vec [IsDomain A] [IsFractionRing A K] (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (g : Module.Dual A (D.omHT σ)) :
    ∃ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom), ∀ z : D.omHT σ,
      (z : Module.Dual K Li) e = algebraMap A K (g z) := by
  let U : Submodule K (Module.Dual K Li) := Submodule.span K (D.om : Set _)
  haveI : Module.Finite K U := by
    obtain ⟨S, hS⟩ := D.om_lat.fg
    have : U = Submodule.span K (S : Set _) := by
      dsimp [U]
      rw [← hS, Submodule.span_span_of_tower]
    rw [this]
    exact Module.Finite.span_of_finite K S.finite_toSet
  let T := U.map (eigProj D.ρΩ σ)
  haveI : Module.Finite K T := Module.Finite.iff_fg.mpr (Submodule.FG.map (eigProj D.ρΩ σ) (Module.Finite.iff_fg.mp (show Module.Finite K U from inferInstance)))
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) (D.omHT σ) ((Algebra.linearMap A K) ∘ₗ g)
  let B : Li →ₗ[K] Module.Dual K T := T.subtype.dualMap.comp (Module.Dual.eval K Li)
  have hB : Function.Injective B.flip := by
    intro x y h
    apply Subtype.ext
    ext v
    exact LinearMap.congr_fun h v
  obtain ⟨v, hv⟩ := (LinearMap.flip_injective_iff₂.mp hB) (G.comp T.subtype)
  have hv' : ∀ w ∈ T, w v = G w := by
    intro w hw
    exact LinearMap.congr_fun hv ⟨w, hw⟩
  have hom : D.om' ≤ D.om := by
    rw [HTChart.om', sup_le_iff]
    constructor
    · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr D.h_mem)
    · rintro _ ⟨x, hx, rfl⟩
      exact D.om.smul_mem _ hx
  refine ⟨eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v, ?_, ?_⟩
  · have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
    rw [LatBasic.mem_eigSp] at h ⊢
    intro a
    have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      apply RingOfIntegers.ext
      simp [hc]
    have := h (RingOfIntegers.mapRingEquiv c a)
    simpa [hinv] using this
  · intro z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ σ w = (z : Module.Dual K Li) := hz
    have he : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
      have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
      rw [LatBasic.mem_eigSp] at h ⊢
      intro a
      have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
        apply RingOfIntegers.ext
        simp [hc]
      have := h (RingOfIntegers.mapRingEquiv c a)
      simpa [hinv] using this
    rw [← hz', eigProj_apply D ρ hc hact σ he w]
    have h2 : w (eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v) = (eigProj D.ρΩ σ w) v := by
      rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
    have hzT : (z : Module.Dual K Li) ∈ T := by
      rw [← hz']
      exact ⟨w, Submodule.subset_span (hom hw), rfl⟩
    rw [h2, hz', hv' _ hzT, hG z]
    rfl

end Chart

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartUnitBasicOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartUnitBasicOpen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chRing_basicOpen_basis : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U :=
  @PositivityTheory.HtPt.Ma.basic

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartUnitBasicOpenStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_unit_basic_open : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis | exact GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCentreChart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCentreChart
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem join_points_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' :=
  @PositivityTheory.HtPt.Mb.join_charts

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCentreChartStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_coords_centre_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.join_points_charts | exact GlobalTheory.CompanionTheory.Ar.join_points_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.join_points_charts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeBasisPullbackDominant
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeBasisPullbackDominant
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem Lat.pull_isFrameAt_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (E E' : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω' E'] (j : E →+ E'), Dominates ξ' ξ f i → (∀ (a : Ω) (e : E), j (a • e) = i a • j e) → ∀ (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), LinearIndependent Ω' (fun k => j (b k)) → L.IsFrameAt b ⟨f p'.1, h⟩ → (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) p' := by
  intro X Ω _ ξ X' Ω' _ ξ' f i E E' _ _ _ _ j hD hj L r b p' h hli hb
  obtain ⟨h', hreg, -⟩ := pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hD p'
  refine ⟨hli, ?_⟩
  rw [Lat.pull_apply L hD]
  have hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b) := hb.2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b) := by
      rw [← hL]; exact he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun k => ⟨i (c k), hreg _ (c k).2⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => (hj (c k) (b k)).symm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨b k, ?_, rfl⟩
    show b k ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set E)
    rw [hL]
    exact Submodule.subset_span ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeBasisPullbackDominantStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_pullback_dominant : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (E E' : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω' E'] (j : E →+ E'), Dominates ξ' ξ f i → (∀ (a : Ω) (e : E), j (a • e) = i a • j e) → ∀ (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), LinearIndependent Ω' (fun k => j (b k)) → L.IsFrameAt b ⟨f p'.1, h⟩ → (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Lat.pull_isFrameAt_comp | exact GlobalTheory.CompanionTheory.Ar.Flat.Lat.pull_isFrameAt_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Lat.pull_isFrameAt_comp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvr
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NormalSchemeHeightOneStalkDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem normal_scheme_height_one_stalk_dvr : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) := by
  intro X _ hn p hd
  obtain ⟨h1, h2⟩ := hn p
  refine ⟨h1, ?_⟩
  have hnf : ¬ IsField (X.presheaf.stalk p) := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hd
    exact zero_ne_one hd
  have hk : Ring.KrullDimLE 1 (X.presheaf.stalk p) := Ring.krullDimLE_iff.2 (by rw [hd]; rfl)
  have hd1 : Ring.DimensionLEOne (X.presheaf.stalk p) :=
    ⟨fun hne hp => Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk _ hne hp⟩
  have hdd : IsDedekindDomain (X.presheaf.stalk p) := {}
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk p) hnf).out 3 1).1 hdd

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem stalk_isDiscreteValuationRing_of_dim_one : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) :=
  @PositivityTheory.UnitarySelfGeneration.normal_scheme_height_one_stalk_dvr

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_codim_one_stalk_dvr : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one | exact GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one | (intros; apply GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one <;> assumption)
end
end
