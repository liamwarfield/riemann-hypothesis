module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PeterssonLiftSmulMeasure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedThetaCoefficientEqIsotropicIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.SmoothUnitary

open GlobalTheory.PRep

section

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def stab (π : G →* (H →L[ℂ] H)) (v : H) : Subgroup G := GlobalTheory.DoubleCosetSetoid.clmStabilizer π v

theorem inner_map_map_of_norm {π : G →* (H →L[ℂ] H)} (hπ : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (x y : H) :
    ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(π g : H →ₗ[ℂ] H), hπ g⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

theorem exists_mean (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) (K : Subgroup G) (w : H)
    (hf : (Set.range fun k : K => π (k : G) w).Finite) :
    ∃ m ∈ Submodule.span ℂ (Set.range fun k : K => π (k : G) w), (∀ k ∈ K, π k m = m) ∧
      ∀ u : H, (∀ k ∈ K, π k u = u) → ⟪u, m⟫_ℂ = ⟪u, w⟫_ℂ := by
  classical
  set O := hf.toFinset with hO
  have hmem : ∀ z, z ∈ O ↔ ∃ k : K, π (k : G) w = z := fun z => by simp [O]
  have hw : w ∈ O := (hmem w).2 ⟨1, by simp⟩
  have hc : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w, hw⟩)
  refine ⟨(O.card : ℂ)⁻¹ • ∑ z ∈ O, z, ?_, fun k hk => ?_, fun u hu => ?_⟩
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun z hz => Submodule.subset_span ?_)
    obtain ⟨k, rfl⟩ := (hmem z).1 hz
    exact ⟨k, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_smul, map_sum]
      congr 1
      refine Finset.sum_nbij' (fun z => π k z) (fun z => π k⁻¹ z) (fun z hz => ?_) (fun z hz => ?_)
        (fun z _ => ?_) (fun z _ => ?_) (fun z _ => rfl)
      · obtain ⟨k', rfl⟩ := (hmem z).1 hz
        exact (hmem _).2 ⟨⟨k, hk⟩ * k', by simp⟩
      · obtain ⟨k', rfl⟩ := (hmem z).1 hz
        exact (hmem _).2 ⟨⟨k, hk⟩⁻¹ * k', by simp⟩
      · simp [← ContinuousLinearMap.mul_apply, ← map_mul]
      · simp [← ContinuousLinearMap.mul_apply, ← map_mul]
  · have h1 : ∀ z ∈ O, ⟪u, z⟫_ℂ = ⟪u, w⟫_ℂ := fun z hz => by
      obtain ⟨k, rfl⟩ := (hmem z).1 hz
      rw [← inner_map_map_of_norm hπ k u w, hu k k.2]
    rw [inner_smul_right, inner_sum, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hc, one_mul]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_compactOpen_subset [NonarchimedeanGroup G] [LocallyCompactSpace G] {U : Set G}
    (hU : U ∈ nhds (1 : G)) : ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨C, hC, hCU, hCc⟩ := local_compact_nhds hU
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean C hC
  exact ⟨V.toSubgroup, V.isOpen, hCc.of_isClosed_subset V.isClosed hV, hV.trans hCU⟩

theorem finite_orbit (π : G →* (H →L[ℂ] H)) {K : Subgroup G} (hK : IsCompact (K : Set G)) {w : H}
    (hw : IsOpen (stab π w : Set G)) : (Set.range fun k : K => π (k : G) w).Finite := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI := Subgroup.quotient_finite_of_isOpen ((stab π w).subgroupOf K) (hw.preimage continuous_subtype_val)
  refine (Set.finite_range (fun q : K ⧸ (stab π w).subgroupOf K => π ((q.out : K) : G) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨QuotientGroup.mk k, ?_⟩
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul ((stab π w).subgroupOf K) k
  have h2 : π ((s : K) : G) w = w := Subgroup.mem_subgroupOf.1 s.2
  simp only [hs, Subgroup.coe_mul, map_mul, ContinuousLinearMap.mul_apply, h2]

end

theorem exists_fixed_ne_zero : ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) → ∀ (K : Subgroup G) (x : H), x ≠ 0 →
      (∀ k ∈ K, ‖π k x - x‖ ≤ ‖x‖ / 2) → ∃ y : H, y ≠ 0 ∧ ∀ k ∈ K, π k y = y := by
  intro G _ H _ _ _ π hπ K x hx hK
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  set O : Set H := Set.range fun k : K => π (k : G) x
  set C : Set H := closure (convexHull ℝ O)
  have hconv : Convex ℝ C := (convex_convexHull ℝ O).closure
  have hxC : x ∈ C := subset_closure (subset_convexHull ℝ O ⟨1, by simp⟩)
  have hball : C ⊆ Metric.closedBall x (‖x‖ / 2) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall
    rintro _ ⟨k, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hK k k.2
  have hinv : ∀ k ∈ K, ∀ z ∈ C, π k z ∈ C := by
    intro k hk z hz
    let T : H →L[ℝ] H := (π k).restrictScalars ℝ
    have hO : T '' O ⊆ O := by
      rintro _ ⟨_, ⟨k', rfl⟩, rfl⟩
      exact ⟨⟨k, hk⟩ * k', by simp [T]⟩
    have h1 : T '' convexHull ℝ O ⊆ convexHull ℝ O := by
      have e := (T : H →ₗ[ℝ] H).image_convexHull O
      change (T : H →ₗ[ℝ] H) '' convexHull ℝ O ⊆ _
      rw [e]
      exact convexHull_min ((show (T : H →ₗ[ℝ] H) '' O ⊆ O from hO).trans (subset_convexHull ℝ O)) (convex_convexHull ℝ O)
    have h2 : T '' C ⊆ C := (image_closure_subset_closure_image T.continuous).trans (closure_mono h1)
    exact h2 ⟨z, hz, rfl⟩
  obtain ⟨y, hyC, hy⟩ := exists_norm_eq_iInf_of_complete_convex ⟨x, hxC⟩ isClosed_closure.isComplete hconv 0
  have hmin : ∀ z ∈ C, ‖y‖ ≤ ‖z‖ := fun z hz => by
    have := ciInf_le (f := fun w : C => ‖(0 : H) - (w : H)‖) ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨z, hz⟩ : C)
    simp only [zero_sub, norm_neg] at hy this
    rw [← hy] at this
    exact this
  refine ⟨y, fun h0 => ?_, fun k hk => ?_⟩
  · have h1 := hball (h0 ▸ hyC)
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at h1
    have := norm_pos_iff.2 hx
    linarith
  · set z := π k y
    have hz : z ∈ C := hinv k hk y hyC
    have hzn : ‖z‖ = ‖y‖ := hπ k y
    have hmid : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z ∈ C := hconv hyC hz (by norm_num) (by norm_num) (by norm_num)
    have h3 := hmin _ hmid
    have h4 : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z = (1 / 2 : ℝ) • (y + z) := by rw [smul_add]
    rw [h4, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h3
    have hp := parallelogram_law_with_norm ℂ y z
    rw [hzn] at hp
    have h5 : ‖y - z‖ * ‖y - z‖ ≤ 0 := by nlinarith [norm_nonneg (y + z), norm_nonneg y]
    have h6 : ‖y - z‖ = 0 := by nlinarith [norm_nonneg (y - z)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h6)).symm

theorem isIrreducible_isAdmissible_smRep : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsIrrUnitary π →
    (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional ℂ (fixed (toRep π) K)) →
      (smRep π).IsIrreducible ∧ IsAdmissible (smRep π) := by
  intro G _ _ _ _ _ H _ _ π hπ hfin
  have hc := hπ.complete
  have hu := hπ.unitary
  have memF : ∀ (K : Subgroup G) (u : H), u ∈ fixed (toRep π) K ↔ ∀ k ∈ K, π k u = u := fun K u => by
    change (∀ k : K, toRep π k u = ((1 : K →* ℂˣ) k : ℂ) • u) ↔ _
    simp
  have memV : ∀ v : H, v ∈ smoothPart (toRep π) ↔ IsOpen (stab π v : Set G) := fun v => Iff.rfl
  refine ⟨?_, isSmooth_smoothRep (toRep π), fun K hKo hKc => ?_⟩
  swap
  · haveI := hfin K hKo hKc
    let f : fixed (smRep π) K →ₗ[ℂ] fixed (toRep π) K :=
      { toFun := fun v => ⟨(v : smoothPart (toRep π)).1, (memF K _).2 fun k hk => by
            have h : smRep π k (v : smoothPart (toRep π)) = v := by simpa using v.2 ⟨k, hk⟩
            exact congrArg Subtype.val h⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_injective f fun a b e => by
      have := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext this)
  have hex : ∃ y : H, y ≠ 0 ∧ y ∈ smoothPart (toRep π) := by
    have := hπ.irred.1
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hx2 : 0 < ‖x‖ / 2 := by have := norm_pos_iff.2 hx; positivity
    have hU : {g : G | ‖π g x - x‖ < ‖x‖ / 2} ∈ nhds (1 : G) := by
      have hcont : Continuous fun g => ‖π g x - x‖ := ((hu.continuous_apply x).sub continuous_const).norm
      exact (isOpen_lt hcont continuous_const).mem_nhds (by simpa using hx2)
    obtain ⟨K, hKo, -, hKU⟩ := exists_compactOpen_subset hU
    obtain ⟨y, hy, hyK⟩ := exists_fixed_ne_zero G H π hu.norm_apply K x hx (fun k hk => (hKU hk).le)
    exact ⟨y, hy, (memV y).2 (Subgroup.isOpen_mono (H₁ := K) (fun k hk => hyK k hk) hKo)⟩
  obtain ⟨y, hy0, hy⟩ := hex
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => hy0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1
    (show (⟨y, hy⟩ : smoothPart (toRep π)) ∈ (⊥ : Subrepresentation (smRep π)).toSubmodule from
      e ▸ Submodule.mem_top)))⟩, eq_bot_or_eq_top := fun S => ?_ }
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  let V := smoothPart (toRep π)
  let W' : Submodule ℂ H := S.toSubmodule.map V.subtype
  have hWst : ∀ g, ∀ w ∈ W', π g w ∈ W' := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨smRep π g w, S.apply_mem_toSubmodule g hw, rfl⟩
  have hWV : ∀ w ∈ W', w ∈ V := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hcl : W'.topologicalClosure = ⊤ := by
    refine (hπ.irred.2 _ ⟨W'.isClosed_topologicalClosure, fun g v hv => ?_⟩).resolve_left ?_
    · exact Submodule.topologicalClosure_minimal W' (t := W'.topologicalClosure.comap (π g : H →ₗ[ℂ] H))
        (fun w hw => W'.le_topologicalClosure (hWst g w hw))
        (W'.isClosed_topologicalClosure.preimage (π g).continuous) hv
    · intro e
      have hS' : S.toSubmodule ≠ ⊥ := fun e' => hS (Subrepresentation.ext e')
      obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hS'
      have h1 : (w : H) ∈ W'.topologicalClosure := W'.le_topologicalClosure ⟨w, hw, rfl⟩
      rw [e, Submodule.mem_bot] at h1
      exact hw0 (Subtype.ext h1)
  have key : ∀ v ∈ V, v ∈ W' := by
    intro v hv
    obtain ⟨K, hKo, hKc, hKv⟩ := exists_compactOpen_subset (((memV v).1 hv).mem_nhds (one_mem (stab π v)))
    haveI := hfin K hKo hKc
    let M : Submodule ℂ H := W' ⊓ fixed (toRep π) K
    haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le inf_le_right
    have hvF : v ∈ fixed (toRep π) K := (memF K v).2 fun k hk => hKv hk
    have huF : v - M.starProjection v ∈ fixed (toRep π) K :=
      Submodule.sub_mem _ hvF (Submodule.mem_inf.1 (M.starProjection_apply_mem v)).2
    have huM := M.sub_starProjection_mem_orthogonal v
    have horth : ∀ w ∈ W', ⟪v - M.starProjection v, w⟫_ℂ = 0 := by
      intro w hw
      obtain ⟨m, hm, hmK, hmu⟩ := exists_mean π hu.norm_apply K w (finite_orbit π hKc ((memV w).1 (hWV w hw)))
      have hmW : m ∈ W' := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hWst k w hw) hm
      rw [← hmu _ ((memF K _).1 huF)]
      exact (Submodule.mem_orthogonal' _ _).1 huM m ⟨hmW, (memF K m).2 hmK⟩
    have hu0 : v - M.starProjection v = 0 := by
      have hle : W'.topologicalClosure ≤ LinearMap.ker (innerₛₗ ℂ (v - M.starProjection v)) :=
        Submodule.topologicalClosure_minimal _ (fun w hw => horth w hw)
          (ContinuousLinearMap.isClosed_ker (innerSL ℂ (v - M.starProjection v)))
      have h1 := hle (hcl ▸ Submodule.mem_top : v - M.starProjection v ∈ W'.topologicalClosure)
      exact inner_self_eq_zero.1 h1
    have hvM : v ∈ M := (sub_eq_zero.1 hu0).symm ▸ M.starProjection_apply_mem v
    exact hvM.1
  refine Subrepresentation.ext (eq_top_iff.2 fun v _ => ?_)
  obtain ⟨w, hw, e⟩ := key v.1 v.2
  exact (Subtype.ext e : w = v) ▸ hw

end GlobalTheory.SmoothUnitary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissibleStatement
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_irreducible_smooth_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NonarchimedeanGroup G] [LocallyCompactSpace G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : G →* (H →L[ℂ] H)), IsIrrUnitary π → (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional ℂ (fixed (toRep π) K)) → (smRep π).IsIrreducible ∧ IsAdmissible (smRep π) := by
  first | exact @GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep | exact GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep | (intros; apply GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorEqOffPlaceMulAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorEqOffPlaceMulAtPlace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.OffOp

section General

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group A] [TopologicalSpace A]
  [IsTopologicalGroup A]

def splitEquiv (ι : A →* G) (π : G →* A) (hπι : ∀ a, π (ι a) = a) (hc : ∀ a g, π g = 1 → Commute (ι a) g) :
    π.ker × A ≃* G where
  toFun p := p.1 * ι p.2
  invFun g := (⟨g * (ι (π g))⁻¹, by simp [MonoidHom.mem_ker, hπι]⟩, π g)
  left_inv p := by
    have h : π p.1 = 1 := p.1.2
    ext <;> simp [hπι, h]
  right_inv g := by simp
  map_mul' p q := by
    have := (hc p.2 q.1 q.1.2).eq
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_assoc]
    rw [← mul_assoc (q.1 : G), ← this, mul_assoc]

variable [T2Space A] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem exists_op (ι : A →* G) (π : G →* A) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ a, π (ι a) = a)
    (hc : ∀ a g, π g = 1 → Commute (ι a) g) (μ : Measure A) [μ.IsHaarMeasure] (ν : Measure G) [ν.IsHaarMeasure]
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (hσ : GlobalTheory.PRep.IsSmooth σ)
    {φ : G → ℂ} (hφ : φ ∈ GlobalTheory.SplitWeil.SB G) :
    ∃ H : W →ₗ[ℂ] W, (∀ g x, H (σ (ι g) x) = σ (ι g) (H x)) ∧
      (∀ x, ∀ k ∈ leftStabilizer φ, π k = 1 → σ k (H x) = H x) ∧
      ∀ f ∈ GlobalTheory.SplitWeil.SB A, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ (σ.comp ι) f B →
        ∀ Ψ : G → ℂ, (∀ h a, π h = 1 → Ψ (h * ι a) = φ h * f a) → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ Ψ (H ∘ₗ B) := by
  classical
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hNc : IsClosed (π.ker : Set G) := by
    have hset : (π.ker : Set G) = π ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hNc.locallyCompactSpace
  let e : π.ker × A ≃ₜ* G :=
    { splitEquiv ι π hπι hc with
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (hι.comp continuous_snd)
      continuous_invFun := by
        refine Continuous.prodMk ?_ hπ
        exact (continuous_id.mul (hι.comp hπ).inv).subtype_mk _ }
  have he : ∀ p : π.ker × A, e p = (p.1 : G) * ι p.2 := fun p => rfl
  let μN : Measure π.ker := Measure.haar
  let P : Measure (π.ker × A) := μN.prod μ
  have hE : MeasurableEmbedding e := e.toHomeomorph.isClosedEmbedding.measurableEmbedding
  haveI : (P.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P e
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • P.map e := ⟨_, Measure.isMulLeftInvariant_eq_smul ν (P.map e)⟩
  let σN : Representation ℂ π.ker W := σ.comp π.ker.subtype
  have hσN : GlobalTheory.PRep.IsSmooth σN := fun x => (hσ x).preimage continuous_subtype_val
  let φN : π.ker → ℂ := fun h => φ h
  have hφN1 : IsLocallyConstant φN := hφ'.1.comp_continuous continuous_subtype_val
  have hφN2 : HasCompactSupport φN := hφ'.2.comp_isClosedEmbedding hNc.isClosedEmbedding_subtypeVal
  let T : W →ₗ[ℂ] W := smoothOp σN μN φN
  have hT : ∀ (l : Module.Dual ℂ W) (y : W), l (T y) = ∫ h, φN h * l (σN h y) ∂μN := by
    intro l y
    simpa [smul_eq_mul] using hσN.map_smoothOp (μ := μN) hφN1 hφN2 l y
  refine ⟨((c : ℝ) : ℂ) • T, ?_, ?_, ?_⟩
  · intro g x
    simp only [LinearMap.smul_apply, map_smul]
    congr 1
    refine (hσN.map_smoothOp_of_intertwining (μ := μN) hσN hφN1 hφN2 (σ (ι g)) (fun h y => ?_) x).symm
    show σ (ι g) (σ h y) = σ h (σ (ι g) y)
    rw [← mul_apply_eq_comp, ← map_mul, (hc g h h.2).eq, map_mul, mul_apply_eq_comp]
  · intro x k hk hk1
    have hmem := hσN.smoothOp_mem_fixed (μ := μN) hφN1 hφN2
      (K := (leftStabilizer φ).comap π.ker.subtype) (fun k' hk' g => hk' g) x
    have hfix := (mem_fixed.1 hmem) ⟨k, MonoidHom.mem_ker.2 hk1⟩ hk
    simp only [LinearMap.smul_apply, map_smul]
    congr 1
  · intro f hf B hB Ψ hΨ v l
    have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
    let F : π.ker × A → ℂ := fun p => φN p.1 * f p.2 * l (σ (e p) v)
    have hFe : ∀ p, Ψ (e p) * l (σ (e p) v) = F p := by
      intro p
      show Ψ (e p) * l (σ (e p) v) = φ p.1 * f p.2 * l (σ (e p) v)
      rw [he p, hΨ _ _ p.1.2]
    have hFlc : IsLocallyConstant F := by
      have h1 : IsLocallyConstant fun p : π.ker × A => φN p.1 := hφN1.comp_continuous continuous_fst
      have h2 : IsLocallyConstant fun p : π.ker × A => f p.2 := hf'.1.comp_continuous continuous_snd
      have h3 : IsLocallyConstant fun p : π.ker × A => l (σ (e p) v) :=
        ((hσ.isLocallyConstant_orbit v).comp_continuous e.continuous).comp l
      exact (h1.mul h2).mul h3
    have hFcs : HasCompactSupport F := by
      refine IsCompact.of_isClosed_subset (IsCompact.prod hφN2 hf'.2) (isClosed_tsupport F) ?_
      refine closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
      intro p hp
      refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
      · intro h0
        apply hp
        show φN p.1 * f p.2 * l (σ (e p) v) = 0
        rw [h0, zero_mul, zero_mul]
      · intro h0
        apply hp
        show φN p.1 * f p.2 * l (σ (e p) v) = 0
        rw [h0, mul_zero, zero_mul]
    have hFi : Integrable F P := hFlc.continuous.integrable_of_hasCompactSupport hFcs
    refine ⟨?_, ?_⟩
    · rw [hν]
      refine Integrable.smul_measure_nnreal ?_
      rw [hE.integrable_map_iff]
      exact hFi.congr (Filter.Eventually.of_forall fun p => (hFe p).symm)
    · have hin : ∀ a, ∫ h, F (h, a) ∂μN = f a * l (T (σ (ι a) v)) := by
        intro a
        rw [hT, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        show φN h * f a * l (σ (e (h, a)) v) = f a * (φN h * l (σ h (σ (ι a) v)))
        rw [he, map_mul, mul_apply_eq_comp]
        ring
      have hB2 := (hB v (l ∘ₗ T)).2
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply] at hB2
      rw [hν, integral_smul_nnreal_measure, hE.integral_map,
        integral_congr_ae (Filter.Eventually.of_forall hFe), integral_prod_symm F hFi,
        show (fun a => ∫ h, F (h, a) ∂μN) = fun a => f a * l (T (σ (ι a) v)) from funext hin, ← hB2]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, NNReal.smul_def,
        Complex.real_smul]

end General

variable {D : D7}

local instance (V : HSp D) : Submodule.IsFullLattice D.host.E (frameLat V) :=
  GlobalTheory.AdelicU.SelfDual.isLattice_frameLat V

theorem isFinFamily_update {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (u : HeightOneSpectrum (𝓞 D.host.F))
    {f : GLoc D.sp.cm.sig V.gram u → ℂ} (hf : f ∈ CcLoc D.sp.cm.sig V.gram u) :
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) (Function.update ff u f) := by
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v = u
    · subst hv
      simpa using hf
    · rw [Function.update_of_ne hv]
      exact hff.1 v
  · filter_upwards [hff.2, Filter.eventually_cofinite_ne u] with v hv hne
    rw [Function.update_of_ne hne]
    exact hv

theorem finite_mulSupport {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (g : GfC V) :
    (Function.mulSupport fun v => ff v (finLoc V v g)).Finite := by
  have hev := GlobalTheory.AdelicU.eventually_proj_mem_stabLoc (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V)
    (g := (g : GA D V))
  refine (Filter.eventually_cofinite.1 (hff.2.and hev)).subset fun v hv => ?_
  rintro ⟨h1, h2⟩
  apply hv
  show ff v (proj D.sp.cm.sig V.gram v (g : GA D V)) = 1
  rw [h1]
  exact (Set.indicator_of_mem h2 1).trans rfl

theorem finFn_update_mul {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (u : HeightOneSpectrum (𝓞 D.host.F))
    {f : GLoc D.sp.cm.sig V.gram u → ℂ} (hf : f ∈ CcLoc D.sp.cm.sig V.gram u) (h : GfC V) (a : Gv V u)
    (hh : finLoc V u h = 1) :
    finFn V (Function.update ff u f) (h * locFin V u a) =
      finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u)) h * f a := by
  have hu : unitLoc D.sp.cm.sig V.gram (frameLat V) u ∈ CcLoc D.sp.cm.sig V.gram u := unitLoc_mem u
  have m1 := finite_mulSupport (isFinFamily_update hff u hf) (h * locFin V u a)
  have m2 := finite_mulSupport (isFinFamily_update hff u hu) h
  have hfin : ∀ (ff' : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (g : GfC V),
      finFn V ff' g = ∏ᶠ v, ff' v (finLoc V v g) := fun _ _ => rfl
  have hloc : ∀ v, finLoc V v (locFin V u a) = proj D.sp.cm.sig V.gram v (emb D.sp.cm.sig V.gram u a) :=
    fun _ => rfl
  rw [hfin, hfin, ← mul_finprod_cond_ne u m1, ← mul_finprod_cond_ne u m2]
  have hoff : (∏ᶠ (v) (_ : v ≠ u), Function.update ff u f v (finLoc V v (h * locFin V u a))) =
      ∏ᶠ (v) (_ : v ≠ u), Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u) v (finLoc V v h) := by
    refine finprod_congr fun v => finprod_congr fun hv => ?_
    rw [Function.update_of_ne hv, Function.update_of_ne hv, map_mul, hloc, proj_emb_ne D.sp.cm.sig V.gram hv, mul_one]
  rw [hoff, Function.update_self, Function.update_self, map_mul, hh, hloc, proj_emb_self, one_mul]
  have h1 : unitLoc D.sp.cm.sig V.gram (frameLat V) u 1 = 1 :=
    (Set.indicator_of_mem (one_mem _) 1).trans rfl
  rw [h1, one_mul, mul_comm]

theorem exists_offOp : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ (H : W →ₗ[ℂ] W) (K : Subgroup (GfC V)), IsOpen (K : Set (GfC V)) ∧ (∀ g x, H (σ (locFin V u g) x) = σ (locFin V u g) (H x)) ∧ (∀ x, ∀ k ∈ K, finLoc V u k = 1 → σ k (H x) = H x) ∧ ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (μf u) (σ.comp (locFin V u)) f B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (Function.update ff u f)) (H ∘ₗ B) := by
  intro D V u μf hμf hK ν hν W _ _ σ hσ ff hff
  haveI := hμf u
  haveI : LocallyCompactSpace (GfC V) := GlobalTheory.AdelicU.locallyCompactSpace_finPts D.sp.cm.sig V.gram
  haveI : ν.IsHaarMeasure := hν.1
  have hu : unitLoc D.sp.cm.sig V.gram (frameLat V) u ∈ CcLoc D.sp.cm.sig V.gram u := unitLoc_mem u
  have hfam := isFinFamily_update hff u hu
  have hφ := (GlobalTheory.TrConv.conv_finFn D V μf hμf hK ν hν _ _ hfam hfam).2.2
  have hφ' : IsLocallyConstant (finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u))) ∧
      HasCompactSupport (finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u))) := hφ
  have hι : Continuous (locFin V u) := continuous_induced_rng.2 (continuous_emb D.sp.cm.sig V.gram u)
  have hπ : Continuous (finLoc V u) := (continuous_proj D.sp.cm.sig V.gram u).comp continuous_subtype_val
  have hπι : ∀ a, finLoc V u (locFin V u a) = a := fun a => proj_emb_self D.sp.cm.sig V.gram u a
  have hc : ∀ a g, finLoc V u g = 1 → Commute (locFin V u a) g := fun a g hg =>
    Subtype.ext (commute_emb D.sp.cm.sig V.gram a hg).eq
  obtain ⟨H, h1, h2, h3⟩ := exists_op (locFin V u) (finLoc V u) hι hπ hπι hc (μf u) ν σ hσ hφ
  exact ⟨H, leftStabilizer _, isOpen_leftStabilizer hφ'.1 hφ'.2, h1, h2,
    fun f hf B hB => h3 f hf B hB _ fun h a hh => finFn_update_mul hff u hf h a hh⟩

end GlobalTheory.OffOp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorEqOffPlaceMulAtPlaceStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureTensorOperator_eq_offPlace_mul_atPlace : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ (H : W →ₗ[ℂ] W) (K : Subgroup (GfC V)), IsOpen (K : Set (GfC V)) ∧ (∀ g x, H (σ (locFin V u g) x) = σ (locFin V u g) (H x)) ∧ (∀ x, ∀ k ∈ K, finLoc V u k = 1 → σ k (H x) = H x) ∧ ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (μf u) (σ.comp (locFin V u)) f B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (Function.update ff u f)) (H ∘ₗ B) := by
  first | exact @GlobalTheory.OffOp.exists_offOp | exact GlobalTheory.OffOp.exists_offOp | (intros; apply GlobalTheory.OffOp.exists_offOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionIntertwinesWeilUpToCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionIntertwinesWeilUpToCharacter
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerRestrictScalar

theorem integral_unitary_mul : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)), ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ, ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν = ∫ y, Φ y ∂ν :=
  GlobalTheory.T.integral_leftMul_unitaryMatrix_addHaar

theorem coef_unfold : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ ν : Measure (Mx D W.rank r), ν.IsAddHaarMeasure ∧ ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ x : WO V' W, ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 F) w * star (res V V' W C B μ 𝓨 G w) ∂μ' = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) F w * star (G w) ∂μV) ∂ν :=
  GlobalTheory.T.restrictedTheta_coefficient_eq_isotropic_integral

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem exists_fd (S T : HSp D) :
    ∃ (m : Measure (WO S T)) (F : Set (WO S T)), m.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL T S) F m := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

theorem integrable_prod (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    Integrable (fun x => f x * star (g x)) (μ.restrict 𝓕) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  have hcont : Continuous fun x => f x * star (g x) := hf.cont.mul hg.cont.star
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hγ w]
  exact hC _ h

theorem heisO_smul (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem mt_one' (S : HSp D) : Formalism.L2.Theta.mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem mt_mul' (S : HSp D) (h k : GA D S) :
    Formalism.L2.Theta.mt S (h * k) = Formalism.L2.Theta.mt S h * Formalism.L2.Theta.mt S k := by
  simp [Formalism.L2.Theta.mt]

theorem actO_one_mul (S T : HSp D) (h k : GA D T) (x : WO S T) :
    actO S T 1 h (actO S T 1 k x) = actO S T 1 (h * k) x := by
  simp [actO, mt_one', mt_mul', Matrix.mul_assoc]

theorem actO_one_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  simp [actO, mt_one']

theorem actO_iso_mid (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (k : GA D W) (y : Mx D W.rank r) (x : WO V' W) :
    actO V W 1 k (isoPart V W C y + midPart V V' W B x) =
      isoPart V W C (HMul.hMul (Formalism.L2.Theta.mt W k) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) +
        midPart V V' W B (actO V' W 1 k x) := by
  simp [actO, isoPart, midPart, mt_one', Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem move (S T : HSp D) {χS χT : (AE D)ˣ →* Circle} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hω : IsWeilDatumO ψ S T χS χT ω) (h : GA D T) (w : WO S T) (P : WO S T → ℂ) (hP : IsThetaFunO ψ S T P) :
    heisO ψ S T w (ω (1, h) P) = ω (1, h) (heisO ψ S T (actO S T 1 h⁻¹ w) P) := by
  rw [hω.om_heis 1 h _ P hP, actO_one_mul, mul_inv_cancel, actO_one_one]

theorem inv_apply (S T : HSp D) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D T)
    (z : WO S T → ℂ) : ω (1, h⁻¹) (ω (1, h) z) = z := by
  have e : ((1 : GA D S), h⁻¹) * ((1 : GA D S), h) = 1 := Prod.ext (by simp) (by simp)
  rw [← Module.End.mul_apply, ← map_mul, e, map_one, Module.End.one_apply]

theorem per_h {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    {χS χT χS' χT' : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)} (hω : IsWeilDatumO ψ V W χS χT ω)
    (hω' : IsWeilDatumO ψ V' W χS' χT' ω') {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨) (h : GA D W) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ V W f →
      res V V' W C B μ 𝓨 (ω (1, h) f) = c • ω' (1, h) (res V V' W C B μ 𝓨 f) := by
  have hψ := hω.std
  obtain ⟨hR, f₀, hf₀, hR0⟩ := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ
  have thV := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1
  have thV' := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V' W).1
  obtain ⟨μV, 𝓕V, hμV, h𝓕V⟩ := exists_fd (D := D) V W
  obtain ⟨μ', 𝓕', hμ', h𝓕'⟩ := exists_fd (D := D) V' W
  obtain ⟨ν, hν, hMC⟩ := coef_unfold D V V' W r C B hs ψ hψ μ 𝓨 hμ μV 𝓕V hμV h𝓕V μ' 𝓕' hμ' h𝓕'
  have hU : ∀ P Q, IsThetaFunO ψ V W P → IsThetaFunO ψ V W Q →
      ∫ w in 𝓕V, ω (1, h) P w * star (ω (1, h) Q w) ∂μV = ∫ w in 𝓕V, P w * star (Q w) ∂μV :=
    fun P Q hP hQ => GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ V W μV 𝓕V hμV h𝓕V (ω (1, h)) (hω.om_pres _)
      (hω.om_unit μV 𝓕V hμV h𝓕V _) P Q hP hQ
  have hU' : ∀ P Q, IsThetaFunO ψ V' W P → IsThetaFunO ψ V' W Q →
      ∫ w in 𝓕', ω' (1, h) P w * star (ω' (1, h) Q w) ∂μ' = ∫ w in 𝓕', P w * star (Q w) ∂μ' :=
    fun P Q hP hQ => GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ V' W μ' 𝓕' hμ' h𝓕' (ω' (1, h)) (hω'.om_pres _)
      (hω'.om_unit μ' 𝓕' hμ' h𝓕' _) P Q hP hQ

  have hpair : ∀ f g, IsThetaFunO ψ V W f → IsThetaFunO ψ V W g → ∀ x : WO V' W,
      ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 (ω (1, h) f)) w *
          star (res V V' W C B μ 𝓨 (ω (1, h) g) w) ∂μ' =
        ∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f)) w *
          star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ' := by
    intro f g hf hg x
    have hf1 := hω.om_pres (1, h) f hf
    have hg1 := hω.om_pres (1, h) g hg
    have hRf := (hR f hf).2.1
    have hRg := (hR g hg).2.1
    calc _ = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) (ω (1, h) f) w *
            star (ω (1, h) g w) ∂μV) ∂ν := hMC _ _ hf1 hg1 x
      _ = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹)
              (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) +
              midPart V V' W B (actO V' W 1 h⁻¹ x)) f w * star (g w) ∂μV) ∂ν := by
          refine congrArg (fun Φ : Mx D W.rank r → ℂ => ∫ y, Φ y ∂ν) (funext fun y => ?_)
          rw [move V W hω h _ f hf, actO_iso_mid, hU _ _ (thV _ f hf) hg]
      _ = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B (actO V' W 1 h⁻¹ x)) f w *
            star (g w) ∂μV) ∂ν :=
          integral_unitary_mul D W r h⁻¹ ν hν (fun y => ∫ w in 𝓕V, heisO ψ V W
            (isoPart V W C y + midPart V V' W B (actO V' W 1 h⁻¹ x)) f w * star (g w) ∂μV)
      _ = ∫ w in 𝓕', heisO ψ V' W (actO V' W 1 h⁻¹ x) (res V V' W C B μ 𝓨 f) w *
            star (res V V' W C B μ 𝓨 g w) ∂μ' := (hMC f g hf hg _).symm
      _ = ∫ w in 𝓕', ω' (1, h) (heisO ψ V' W (actO V' W 1 h⁻¹ x) (res V V' W C B μ 𝓨 f)) w *
            star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ' := (hU' _ _ (thV' _ _ hRf) hRg).symm
      _ = _ := by rw [move V' W hω' h x _ hRf]
  have hcoef : ∀ f, IsThetaFunO ψ V W f → ∃ c : ℂ, ‖c‖ = 1 ∧
      res V V' W C B μ 𝓨 (ω (1, h) f) = c • ω' (1, h) (res V V' W C B μ 𝓨 f) := fun f hf =>
    GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq D ψ hψ V' W μ' 𝓕' hμ' h𝓕'
      (ω' (1, h) (res V V' W C B μ 𝓨 f)) (res V V' W C B μ 𝓨 (ω (1, h) f))
      (hω'.om_pres _ _ (hR f hf).2.1) (hR _ (hω.om_pres _ f hf)).2.1 (fun w => hpair f f hf hf w)
  have hv0t : IsThetaFunO ψ V' W (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) := hω'.om_pres _ _ (hR f₀ hf₀).2.1
  have hv0 : ω' (1, h) (res V V' W C B μ 𝓨 f₀) ≠ 0 := fun h0 => hR0 (by
    rw [← inv_apply V' W ω' h (res V V' W C B μ 𝓨 f₀), h0, map_zero])
  obtain ⟨c, hc, hu0⟩ := hcoef f₀ hf₀
  have hdiag : ∃ x, ∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
      star (ω' (1, h) (res V V' W C B μ 𝓨 f₀) w) ∂μ' ≠ 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨c', -, h'⟩ := GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq D ψ hψ V' W μ' 𝓕' hμ' h𝓕'
      0 (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) GlobalTheory.WeilVacMove.isTheta_zero hv0t (fun w => by
        rw [hne w]
        simp [heisO])
    exact hv0 (by rw [h', smul_zero])
  have hA : ∀ g, IsThetaFunO ψ V W g → (∃ x, ∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
      star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ' ≠ 0) →
      res V V' W C B μ 𝓨 (ω (1, h) g) = c • ω' (1, h) (res V V' W C B μ 𝓨 g) := by
    rintro g hg ⟨x, hx⟩
    obtain ⟨cg, hcg, hug⟩ := hcoef g hg
    have e := hpair f₀ g hf₀ hg x
    rw [hu0, hug, heisO_smul] at e
    have e2 : (∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
        star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ') * (c * star cg) =
        (∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
        star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ') * 1 := by
      rw [mul_one, ← integral_mul_const]
      refine Eq.trans ?_ e
      refine congrArg (fun Φ : WO V' W → ℂ => ∫ w in 𝓕', Φ w ∂μ') (funext fun w => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, star_mul']
      ring
    have e3 : c * star cg = 1 := mul_left_cancel₀ hx e2
    have hcg2 : cg * star cg = 1 := by
      rw [Complex.star_def, Complex.mul_conj', hcg]
      simp
    have : cg = c := by
      calc cg = cg * (c * star cg) := by rw [e3, mul_one]
        _ = c * (cg * star cg) := by ring
        _ = c := by rw [hcg2, mul_one]
    rw [hug, this]
  refine ⟨c, hc, fun g hg => ?_⟩
  by_cases hx : ∃ x, ∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
      star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ' ≠ 0
  · exact hA g hg hx
  · push_neg at hx
    obtain ⟨x₁, hx₁⟩ := hdiag
    have hRadd : ∀ a b, IsThetaFunO ψ V W a → IsThetaFunO ψ V W b →
        res V V' W C B μ 𝓨 (a + b) = res V V' W C B μ 𝓨 a + res V V' W C B μ 𝓨 b := fun a b ha hb => by
      funext z
      simp only [res, Pi.add_apply]
      exact integral_add ((hR a ha).1 z) ((hR b hb).1 z)
    have hv' : ω' (1, h) (res V V' W C B μ 𝓨 (f₀ + g)) =
        ω' (1, h) (res V V' W C B μ 𝓨 f₀) + ω' (1, h) (res V V' W C B μ 𝓨 g) := by
      rw [hRadd _ _ hf₀ hg, map_add (f := _)]
    have hu' : res V V' W C B μ 𝓨 (ω (1, h) (f₀ + g)) =
        res V V' W C B μ 𝓨 (ω (1, h) f₀) + res V V' W C B μ 𝓨 (ω (1, h) g) := by
      rw [map_add (f := _), hRadd _ _ (hω.om_pres _ _ hf₀) (hω.om_pres _ _ hg)]
    have hvg : IsThetaFunO ψ V' W (ω' (1, h) (res V V' W C B μ 𝓨 g)) := hω'.om_pres _ _ (hR g hg).2.1
    have key := hA (f₀ + g) (GlobalTheory.WeilVacMove.isTheta_add hf₀ hg) ⟨x₁, by
      rw [hv']
      simp only [Pi.add_apply, star_add, mul_add]
      rw [integral_add (integrable_prod hψ μ' 𝓕' hμ' h𝓕' (thV' x₁ _ hv0t) hv0t)
        (integrable_prod hψ μ' 𝓕' hμ' h𝓕' (thV' x₁ _ hv0t) hvg), hx x₁, add_zero]
      exact hx₁⟩
    rw [hu', hv', hu0, smul_add] at key
    exact add_left_cancel key

theorem main : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ c : GA D W →* Circle, ∀ h f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs ψ χS χT χS' χT' ω ω' hω hω' μ 𝓨 hμ
  have P := fun h => per_h hs hω hω' hμ h
  obtain ⟨-, f₀, hf₀, hR0⟩ := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hω.std μ 𝓨 hμ
  let c : GA D W → ℂ := fun h => Classical.choose (P h)
  have hc1 : ∀ h, ‖c h‖ = 1 := fun h => (Classical.choose_spec (P h)).1
  have hc : ∀ h f, IsThetaFunO ψ V W f →
      res V V' W C B μ 𝓨 (ω (1, h) f) = c h • ω' (1, h) (res V V' W C B μ 𝓨 f) :=
    fun h => (Classical.choose_spec (P h)).2
  have uniq : ∀ h (a b : ℂ), a • ω' (1, h) (res V V' W C B μ 𝓨 f₀) = b • ω' (1, h) (res V V' W C B μ 𝓨 f₀) →
      a = b := fun h a b e => by
    by_contra hab
    have hz : (a - b) • ω' (1, h) (res V V' W C B μ 𝓨 f₀) = 0 := by rw [sub_smul, e, sub_self]
    rcases smul_eq_zero.1 hz with h1 | h1
    · exact hab (sub_eq_zero.1 h1)
    · exact hR0 (by rw [← inv_apply V' W ω' h (res V V' W C B μ 𝓨 f₀), h1, map_zero])
  let cc : GA D W → Circle := fun h => ⟨c h, by simp [Submonoid.unitSphere, hc1 h]⟩
  have hcc : ∀ h, ((cc h : Circle) : ℂ) = c h := fun h => rfl
  refine ⟨{ toFun := cc, map_one' := ?_, map_mul' := ?_ }, fun h f hf => ?_⟩
  · apply Circle.ext
    rw [hcc, Circle.coe_one]
    apply uniq 1
    rw [← hc 1 f₀ hf₀, one_smul]
    show res V V' W C B μ 𝓨 (ω 1 f₀) = ω' 1 (res V V' W C B μ 𝓨 f₀)
    rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply]
  · intro h k
    apply Circle.ext
    rw [hcc, Circle.coe_mul, hcc, hcc]
    apply uniq (h * k)
    have e1 : ω (1, h * k) = ω (1, h) * ω (1, k) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
    have e1' : ω' (1, h * k) = ω' (1, h) * ω' (1, k) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [← hc (h * k) f₀ hf₀, e1, Module.End.mul_apply, hc h _ (hω.om_pres _ _ hf₀), hc k _ hf₀, map_smul,
      smul_smul, e1', Module.End.mul_apply]
  · exact hc h f hf

end GlobalTheory.TowerRestrictScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionIntertwinesWeilUpToCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittTowerRestriction_intertwines_weil_upToCharacter : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ c : GA D W →* Circle, ∀ h f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (res V V' W C B μ 𝓨 f) := by
  first | exact @GlobalTheory.TowerRestrictScalar.main | exact GlobalTheory.TowerRestrictScalar.main | (intros; apply GlobalTheory.TowerRestrictScalar.main <;> assumption)
end
end
