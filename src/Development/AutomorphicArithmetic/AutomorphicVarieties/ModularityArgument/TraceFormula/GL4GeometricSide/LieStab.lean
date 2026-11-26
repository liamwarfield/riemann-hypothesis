module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SkewExp
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.LieStab
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open Matrix

private theorem flow {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (c : ℝ → S) (hc : ∀ t, HasDerivAt c (D (c t)) t) :
    c 1 = NormedSpace.exp D (c 0) := by
  have hψ : ∀ t : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • D) (c u)) 0 t := by
    intro t
    have he := (hasDerivAt_exp_smul_const (𝕂 := ℝ) D (1 - t)).comp_const_sub 1 t
    have h := he.clm_apply (hc t)
    convert h using 1
    simp [ContinuousLinearMap.mul_apply]
  have hconst := is_const_of_deriv_eq_zero
    (fun u => (hψ u).differentiableAt) (fun u => (hψ u).deriv) 1 0
  simpa using hconst

private theorem exp_mem {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (M : Submodule ℝ S) (hM : IsClosed (M : Set S)) (hD : ∀ y ∈ M, D y ∈ M)
    {x : S} (hx : x ∈ M) : NormedSpace.exp D x ∈ M := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) D
  have hs2 := (ContinuousLinearMap.apply ℝ S x).hasSum hs
  have hpow : ∀ m : ℕ, (D ^ m) x ∈ M := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      exact hD _ ih
  refine hM.mem_of_tendsto hs2 (Filter.Eventually.of_forall fun s => ?_)
  refine M.sum_mem fun m _ => ?_
  simpa using M.smul_mem _ (hpow m)

private theorem lift {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {S : Submodule ℂ V}
    {c : ℝ → S} {d : S} {t : ℝ} (h : HasDerivAt (fun s => (c s : V)) (d : V) t) : HasDerivAt c d t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  exact (Asymptotics.isLittleO_norm_left).1 h.norm_left

variable {n : ℕ}

private def curve (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (t : ℝ) : Un n :=
  ⟨NormedSpace.exp ((t : ℂ) • X), (UpperTheory.RealTr.skewExp n).1 _ (by
    rw [conjTranspose_smul, hX]; simp)⟩

private theorem curve_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    curve X hX (s + t) = curve X hX s * curve X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]

private theorem curve_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) : curve X hX 0 = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
  simp

end UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open UpperTheory.V.Z.GSp4Splitting.LieStabilizer in
theorem UpperTheory.V.Z.GSp4Splitting.lieStab :
    LieStab := by
  intro n V _ _ σ Kf hder N hN k x hx
  obtain ⟨X, hX, hXk⟩ := (UpperTheory.RealTr.skewExp n).2 k
  obtain ⟨S, hfd, hxS, hσS, hKS, hd⟩ := hder.2 x
  haveI : FiniteDimensional ℂ S := hfd
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : Module.End ℂ V := ∑ a, ∑ b, X a b • Kf a b
  have hLapp : ∀ w, L w = ∑ a, ∑ b, X a b • Kf a b w := by
    intro w
    simp [L, LinearMap.sum_apply]
  have hLS : ∀ w ∈ S, L w ∈ S := by
    intro w hw
    rw [hLapp]
    exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hKS a b w hw)
  have hLN : ∀ w ∈ N, L w ∈ N := by
    intro w hw
    rw [hLapp]
    exact N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (hN a b w hw)
  let Dc : S →L[ℂ] S := LinearMap.toContinuousLinearMap (L.restrict hLS)
  let D : S →L[ℝ] S := Dc.restrictScalars ℝ
  have hDapp : ∀ w : S, ((D w : S) : V) = L w := fun w => rfl
  let γ := curve X hX
  let c : ℝ → S := fun t => ⟨σ (γ t) x, hσS _ _ hxS⟩
  have hc : ∀ t, HasDerivAt c (D (c t)) t := by
    intro t
    apply lift
    have h0 : HasDerivAt (fun s : ℝ => σ (γ s) (c t : V)) (L (c t : V)) (t - t) := by
      rw [sub_self, hLapp]
      exact hd X γ (fun _ => rfl) _ (c t).2
    have h1 := h0.comp_sub_const t t
    convert h1 using 1
    funext s
    have : γ s = γ (s - t) * γ t := by
      rw [← curve_add, sub_add_cancel]
    show σ (γ s) x = σ (γ (s - t)) (σ (γ t) x)
    rw [this, map_mul, Module.End.mul_apply]
    exact hDapp _
  have h1 := flow D c hc
  let M : Submodule ℂ S := N.comap S.subtype
  have hMc : IsClosed (M : Set S) := Submodule.closed_of_finiteDimensional M
  have hc0 : c 0 ∈ M.restrictScalars ℝ := by
    show σ (γ 0) x ∈ N
    have : γ 0 = 1 := curve_zero X hX
    rw [this, map_one]
    exact hx
  have h2 := exp_mem D (M.restrictScalars ℝ) hMc (fun y hy => hLN _ hy) hc0
  rw [← h1] at h2
  have hk : γ 1 = k := by
    apply Subtype.ext
    show NormedSpace.exp (((1 : ℝ) : ℂ) • X) = k.1
    simpa using hXk
  have h3 : σ (γ 1) x ∈ N := h2
  rwa [hk] at h3
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.HeckeMem
noncomputable section

open MeasureTheory Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private def cos (U : Subgroup G) (a : G) : Set G := {y | a⁻¹ * y ∈ U}

private theorem cos_self (U : Subgroup G) (a : G) : a ∈ cos U a := by
  simp [cos, U.one_mem]

private theorem isOpen_cos {U : Subgroup G} (hU : IsOpen (U : Set G)) (a : G) : IsOpen (cos U a) :=
  hU.preimage (continuous_const.mul continuous_id)

private theorem exists_reps {U : Subgroup G} (hU : IsOpen (U : Set G)) {C : Set G} (hC : IsCompact C) :
    ∃ s : Finset G, (∀ a ∈ s, ∀ b ∈ s, ∀ y, y ∈ cos U a → y ∈ cos U b → a = b) ∧
      C ⊆ ⋃ a ∈ s, cos U a := by
  classical
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun g => cos U g)
    (fun g _ => (isOpen_cos hU g).mem_nhds (cos_self U g))
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ U))).image Quotient.out, ?_, ?_⟩
  · intro a ha b hb y hya hyb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hb
    have hab : (Quotient.out q)⁻¹ * Quotient.out q' ∈ U := by
      have := U.mul_mem hya (U.inv_mem hyb)
      simpa [mul_assoc] using this
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ U) = QuotientGroup.mk (Quotient.out q') :=
      QuotientGroup.eq.2 hab
    have e : q = q' := by
      simpa [QuotientGroup.out_eq'] using this
    rw [e]
  · intro y hy
    obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hr : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk g : G ⧸ U)) : G ⧸ U) = QuotientGroup.mk g :=
      QuotientGroup.out_eq' _
    have hgr : (Quotient.out (QuotientGroup.mk g : G ⧸ U))⁻¹ * g ∈ U := QuotientGroup.eq.1 hr
    refine Set.mem_iUnion₂.2 ⟨Quotient.out (QuotientGroup.mk g : G ⧸ U),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hg), ?_⟩
    have := U.mul_mem hgr hyg
    simpa [cos, mul_assoc] using this

private theorem integral_eq_sum (μ : Measure G) [μ.IsMulLeftInvariant] {U : Subgroup G} (hU : IsOpen (U : Set G))
    (hfin : μ (U : Set G) ≠ ⊤) {h : G → ℂ} (hc : HasCompactSupport h) (hinv : ∀ g, ∀ k ∈ U, h (g * k) = h g) :
    ∃ s : Finset G, ∀ f : G → ℂ, (∀ g, ∀ k ∈ U, f (g * k) = f g) →
      ∫ y, h y * f y ∂μ = ∑ a ∈ s, (h a * (μ.real (U : Set G) : ℂ)) * f a := by
  classical
  obtain ⟨s, hdis, hcov⟩ := exists_reps hU hc.isCompact
  refine ⟨s, fun f hf => ?_⟩
  have hmeas : ∀ a, μ (cos U a) = μ (U : Set G) := fun a => measure_preimage_mul μ a⁻¹ (U : Set G)
  have hval : ∀ a y, y ∈ cos U a → h y * f y = h a * f a := by
    intro a y hy
    have e : y = a * (a⁻¹ * y) := by group
    rw [e, hinv a _ hy, hf a _ hy]
  have hsum : (fun y => h y * f y) = fun y => ∑ a ∈ s, (cos U a).indicator (fun _ => h a * f a) y := by
    funext y
    by_cases hy : ∃ a ∈ s, y ∈ cos U a
    · obtain ⟨a, ha, hya⟩ := hy
      rw [Finset.sum_eq_single a, Set.indicator_of_mem hya, hval a y hya]
      · intro b hb hba
        exact Set.indicator_of_notMem (fun hyb => hba (hdis b hb a ha y hyb hya)) _
      · exact fun h' => (h' ha).elim
    · have hy0 : h y = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => hy ?_
        obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.1 (hcov hmem)
        exact ⟨a, ha, hya⟩
      rw [hy0, zero_mul]
      exact (Finset.sum_eq_zero fun a ha => Set.indicator_of_notMem (fun hya => hy ⟨a, ha, hya⟩) _).symm
  rw [hsum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_indicator_const _ (isOpen_cos hU a).measurableSet]
    simp only [Measure.real, hmeas a, Complex.real_smul]
    ring
  · intro a _
    refine (integrable_indicator_iff (isOpen_cos hU a).measurableSet).2 ?_
    exact integrableOn_const (by rw [hmeas a]; exact hfin)

end Abs

theorem heckeMem : HeckeMem := by
  intro E _ _ _ n π K hKo hKc _ _ μf _ h hh ψ
  let St : Subgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | finRep E n k ψ.1 = ψ.1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSt : IsOpen (St : Set (GL (Fin n) (Af E))) := (π.cusp ψ.1 ψ.2).1.level
  have hU : IsOpen ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) := hKo.inter hSt
  have hfin : μf ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt hKc.measure_lt_top).ne
  obtain ⟨s, hs⟩ := integral_eq_sum μf hU hfin hh.1 (fun g k hk => by
    simpa using hh.2 1 K.one_mem k hk.1 g)
  let c : GL (Fin n) (Af E) → ℂ := fun a => h a * (μf.real ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) : ℂ)
  have hmem : ∑ g ∈ s, c g • finRep E n g ψ.1 ∈ π.V :=
    Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (π.stable (.fin g) ψ.1 ψ.2)
  have hop : (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 = heckeOp μf h ψ.1.1 := by
    funext x
    have hinv := hs (fun g => ψ.1.1 (x * finGL E n g)) (fun g k hk => by
      have e := congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (show finRep E n k ψ.1 = ψ.1 from hk.2)
      have e' : ψ.1.1 (x * finGL E n g * finGL E n k) = ψ.1.1 (x * finGL E n g) := e
      simpa [mul_assoc] using e')
    rw [heckeOp, hinv]
    simp [c, Submodule.coe_sum, Finset.sum_apply]
    rfl
  refine ⟨s, c, ⟨_, hmem⟩, rfl, hop, fun k hk => ?_⟩
  refine Subtype.ext (funext fun x => ?_)
  change (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 (x * finGL E n k) = (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 x
  rw [hop]
  have e := integral_mul_left_eq_self (μ := μf) (fun g => h g * ψ.1.1 (x * finGL E n g)) k
  simp only [heckeOp]
  rw [← e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have e2 : h (k * g) = h g := by simpa using hh.2 k hk 1 K.one_mem g
  simp [e2, map_mul, mul_assoc]

end UpperTheory.V.Z.GSp4Splitting
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ProjEx
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Un n →* (V →ₗ[ℂ] V)} {E : KMod n}

private theorem sig_inv (k : Un n) (y : V) : σ k (σ k⁻¹ y) = y := by
  have h : σ k * σ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact LinearMap.congr_fun h y

private theorem inner_sig (hσ : IsK σ) (k : Un n) (c y : V) : ⟪c, σ k y⟫_ℂ = ⟪σ k⁻¹ c, y⟫_ℂ := by
  have h := hσ.iso k (σ k⁻¹ c) y
  rw [sig_inv] at h
  exact h

private theorem range_mem (t : invA σ E) (ξ : E.V →L[ℂ] ℂ) : t.1 ξ ∈ isoSp σ E :=
  (le_iSup (fun t : invA σ E => LinearMap.range t.1) t) ⟨ξ, rfl⟩

private theorem iso_le {W : Submodule ℂ V} (h : ∀ (t : invA σ E) ξ, t.1 ξ ∈ W) : isoSp σ E ≤ W := by
  refine iSup_le fun t => ?_
  rintro _ ⟨ξ, rfl⟩
  exact h t ξ

private theorem map_iso (B : V →ₗ[ℂ] V) (hB : ∀ k x, B (σ k x) = σ k (B x)) {x : V}
    (hx : x ∈ isoSp σ E) : B x ∈ isoSp σ E := by
  have h : isoSp σ E ≤ (isoSp σ E).comap B := by
    refine iso_le fun t ξ => ?_
    have ht : B.comp t.1 ∈ invA σ E := fun k ξ => by
      simp only [LinearMap.comp_apply]
      rw [t.2 k ξ, hB]
    exact range_mem ⟨_, ht⟩ ξ
  exact h hx

private theorem iso_stable (k : Un n) {x : V} (hx : x ∈ isoSp σ E) : σ k x ∈ isoSp σ E := by
  have h : isoSp σ E ≤ (isoSp σ E).comap (σ k) := by
    refine iso_le fun t ξ => ?_
    show σ k (t.1 ξ) ∈ isoSp σ E
    rw [← t.2 k ξ]
    exact range_mem t _
  exact h hx

private theorem orth_stable (hσ : IsK σ) {K : Submodule ℂ V} (hK : ∀ k, ∀ x ∈ K, σ k x ∈ K)
    (k : Un n) {y : V} (hy : y ∈ Kᗮ) : σ k y ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro c hc
  rw [inner_sig hσ]
  exact hy _ (hK _ _ hc)

private theorem proj_comm (hσ : IsK σ) (K : Submodule ℂ V) [K.HasOrthogonalProjection]
    (hK : ∀ k, ∀ x ∈ K, σ k x ∈ K) (k : Un n) (x : V) :
    K.starProjection (σ k x) = σ k (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal (hK _ _ (K.starProjection_apply_mem x)) ?_
  rw [← map_sub]
  exact orth_stable hσ hK k (K.sub_starProjection_mem_orthogonal x)

private theorem core (hσ : IsK σ) (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (hS : ∀ k, ∀ x ∈ S, σ k x ∈ S) {x : V} (hx : x ∈ S) :
    ∃ u ∈ S ⊓ isoSp σ E, x - u ∈ (isoSp σ E)ᗮ := by
  let D : Submodule ℂ V := S ⊓ isoSp σ E
  haveI : FiniteDimensional ℂ D := Submodule.finiteDimensional_inf_left S _
  haveI : CompleteSpace D := FiniteDimensional.complete ℂ D
  let C : Submodule ℂ V := S ⊓ Dᗮ
  haveI : FiniteDimensional ℂ C := Submodule.finiteDimensional_inf_left S _
  haveI : CompleteSpace C := FiniteDimensional.complete ℂ C
  have hD : ∀ k, ∀ x ∈ D, σ k x ∈ D := fun k x hx => ⟨hS k x hx.1, iso_stable k hx.2⟩
  have hC : ∀ k, ∀ x ∈ C, σ k x ∈ C := fun k x hx => ⟨hS k x hx.1, orth_stable hσ hD k hx.2⟩
  have hu : D.starProjection x ∈ D := D.starProjection_apply_mem x
  refine ⟨D.starProjection x, hu, ?_⟩
  have hc : x - D.starProjection x ∈ C := ⟨S.sub_mem hx hu.1, D.sub_starProjection_mem_orthogonal x⟩
  have hIC : isoSp σ E ≤ Cᗮ := by
    intro y hy
    have h1 : C.starProjection y ∈ isoSp σ E :=
      map_iso (C.starProjection : V →ₗ[ℂ] V) (fun k z => proj_comm hσ C hC k z) hy
    have h2 : C.starProjection y ∈ C := C.starProjection_apply_mem y
    have h3 : C.starProjection y ∈ D := ⟨h2.1, h1⟩
    have h0 : C.starProjection y = 0 := by
      have h4 : C.starProjection y ∈ D ⊓ Dᗮ := ⟨h3, h2.2⟩
      rw [D.inf_orthogonal_eq_bot] at h4
      exact (Submodule.mem_bot ℂ).1 h4
    exact (Submodule.starProjection_apply_eq_zero_iff C).1 h0
  rw [Submodule.mem_orthogonal]
  intro y hy
  have h := (Submodule.mem_orthogonal _ _).1 (hIC hy) _ hc
  rw [← inner_conj_symm, h, map_zero]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.projEx :
    ProjEx := by
  intro n V _ _ σ hσ E
  haveI : (isoSp σ E).HasOrthogonalProjection := ⟨fun v => by
    obtain ⟨S, hfd, hx, hS⟩ := hσ.fin v
    haveI := hfd
    obtain ⟨u, hu, hv⟩ := core (E := E) hσ S hS hx
    exact ⟨u, hu.2, hv⟩⟩
  have hIs : ∀ k, ∀ x ∈ isoSp σ E, σ k x ∈ isoSp σ E := fun k x hx => iso_stable k hx
  refine ⟨((isoSp σ E).starProjection : V →ₗ[ℂ] V), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact Submodule.inner_starProjection_left_eq_right _ x y
  · intro x
    exact (isoSp σ E).starProjection_apply_mem x
  · intro x hx
    exact (Submodule.starProjection_eq_self_iff).2 hx
  · intro k
    ext x
    exact proj_comm hσ _ hIs k x
  · rintro B ⟨B', hadj, hcomm⟩
    have hB : ∀ x ∈ isoSp σ E, B x ∈ isoSp σ E := fun x hx =>
      map_iso B (fun k z => LinearMap.congr_fun (hcomm k).1 z) hx
    have hB' : ∀ x ∈ isoSp σ E, B' x ∈ isoSp σ E := fun x hx =>
      map_iso B' (fun k z => LinearMap.congr_fun (hcomm k).2 z) hx
    ext x
    show (isoSp σ E).starProjection (B x) = B ((isoSp σ E).starProjection x)
    refine Submodule.eq_starProjection_of_mem_orthogonal (hB _ ((isoSp σ E).starProjection_apply_mem x)) ?_
    rw [← map_sub, Submodule.mem_orthogonal]
    intro c hc
    have h := (Submodule.mem_orthogonal _ _).1 ((isoSp σ E).sub_starProjection_mem_orthogonal x) (B' c) (hB' c hc)
    rw [← inner_conj_symm, hadj, ← inner_conj_symm, h, map_zero, map_zero]
  · intro N hN x hx
    obtain ⟨S, hfd, hxS, hS⟩ := hσ.fin x
    haveI := hfd
    haveI : FiniteDimensional ℂ (S ⊓ N : Submodule ℂ V) := Submodule.finiteDimensional_inf_left S N
    obtain ⟨u, hu, hv⟩ := core (E := E) hσ (S ⊓ N) (fun k y hy => ⟨hS k y hy.1, hN k y hy.2⟩) ⟨hxS, hx⟩
    have he : (isoSp σ E).starProjection x = u := Submodule.eq_starProjection_of_mem_orthogonal hu.2 hv
    show (isoSp σ E).starProjection x ∈ N
    rw [he]
    exact hu.1.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlComm
noncomputable section

open NumberField Matrix MeasureTheory Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GKCoh GlobalTheory.WigAlg
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.GSp4Splitting

section Sum

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_sum (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) {S : Set G} (hS : IsCompact S) :
    ∃ (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : G ⧸ K → ℂ), ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) →
      (∀ g, g ∉ S → F g = 0) → ∫ g, F g ∂μ = ∑ x ∈ T, c x * F (r x) :=
  _root_.UpperTheory.Reformulated.B.Qg3.exists_sum μ K hKo hKc hS

end Sum

section Ops

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem atW_val (w v : InfinitePlace E) (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    atW w X a b v = (if v = w then X else 1) a b := by
  simp only [atW]
  split_ifs <;> rfl

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem of_atW_mul (w w' v : InfinitePlace E) (X Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' Y)) a b v =
      ((if v = w then X else 1) * (if v = w' then Y else 1)) a b := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, atW_val]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem of_atW_inv (w : InfinitePlace E) {X Y : Matrix (Fin n) (Fin n) ℂ} (h : X * Y = 1) :
    (Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w Y) = 1 := by
  ext a b v
  rw [of_atW_mul]
  by_cases hv : v = w
  · simp only [if_pos hv, h]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  · simp only [if_neg hv, mul_one]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl

private def yAt (w : InfinitePlace E) (k : Un n) : GL (Fin n) (Cinf E) where
  val := Matrix.of (atW w k.1)
  inv := Matrix.of (atW w (star k.1))
  val_inv := of_atW_inv w (Unitary.mul_star_self_of_mem k.2)
  inv_val := of_atW_inv w (Unitary.star_mul_self_of_mem k.2)

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem yAt_comm {w w' : InfinitePlace E} (h : w ≠ w') (k k' : Un n) : yAt w k * yAt w' k' = yAt w' k' * yAt w k := by
  apply Units.ext
  ext a b v
  show ((Matrix.of (atW w k.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' k'.1)) a b v =
    ((Matrix.of (atW w' k'.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w k.1)) a b v
  rw [of_atW_mul, of_atW_mul]
  by_cases h1 : v = w
  · have h2 : v ≠ w' := h1 ▸ h
    simp [h1, h]
  · simp [h1]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem coord_atW {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (X : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n) : coord τ (atW w X a b) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [PositivityTheory.Rg.Cz.J.coord_eq, atW_val, if_neg h, Matrix.one_apply]
  split_ifs <;> simp

private theorem commute_rt_Eop {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (k : Un n) (a b : Fin n) :
    Commute (Eop τ a b) (rt E n (infGL E n (yAt w k))) := by
  have e := GlobalTheory.CapAdInv.rt_Eop (yAt w k) τ a b
  have c1 : ∀ p q, coord τ ((yAt w k).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q := coord_atW h k.1
  have c2 : ∀ p q, coord τ (((yAt w k)⁻¹ : GL (Fin n) (Cinf E)).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q :=
    coord_atW h (star k.1)
  simp only [c1, c2, Matrix.one_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  exact e.symm

private theorem commute_Eop_fin (τ : E →+* ℂ) (a b : Fin n) (g : GL (Fin n) (Af E)) :
    Commute (Eop τ a b) (finRep E n g) := by
  have hl : ∀ x, Commute (lieS E n a b x) (finRep E n g) := fun x => by
    rw [lieS_apply]
    exact lie_rt_fin _ g
  have e : Eop τ a b = (1 / 2 : ℂ) • (lieS E n a b (atEmb τ 1) - Complex.I • lieS E n a b (atEmb τ Complex.I)) := by
    rw [lieS_atEmb_one, lieS_atEmb_I, smul_smul, Complex.I_mul_I]
    module
  rw [e]
  exact ((hl _).sub_left ((hl _).smul_left _)).smul_left _

private theorem commute_rt_fin (y : GL (Fin n) (Cinf E)) (g : GL (Fin n) (Af E)) :
    Commute (rt E n (infGL E n y)) (finRep E n g) := by
  show rt E n (infGL E n y) * rt E n (finGL E n g) = rt E n (finGL E n g) * rt E n (infGL E n y)
  rw [← map_mul, ← map_mul, infGL_comm]

private theorem exists_op [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (K : Subgroup (GL (Fin n) (Af E)))
    (hKo : IsOpen (K : Set (GL (Fin n) (Af E)))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    {h : GL (Fin n) (Af E) → ℂ} (hh : IsHeckeF K h) :
    ∃ A : Module.End ℂ (Sm E n), (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧
      ∀ ψ : Sm E n, (∀ k ∈ K, finRep E n k ψ = ψ) → heckeOp μf h ψ.1 = (A ψ).1 := by
  obtain ⟨T, r, c, H⟩ := exists_sum μf K hKo hKc hh.1
  refine ⟨∑ x ∈ T, (c x * h (r x)) • finRep E n (r x), fun B hB => ?_, fun ψ hψ => ?_⟩
  · exact Commute.sum_left _ _ _ fun x _ => ((hB _).symm).smul_left _
  · funext x
    have e := H (fun g => h g * ψ.1 (x * finGL E n g)) (fun g k hk => ?_) (fun g hg => ?_)
    · refine e.trans ?_
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [mul_assoc]
      rfl
    · have e1 : h (g * k) = h g := by simpa using hh.2 1 K.one_mem k hk g
      have e2 : ψ.1 (x * finGL E n g * finGL E n k) = ψ.1 (x * finGL E n g) :=
        congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hψ k hk)
      simp only [e1, map_mul, ← mul_assoc, e2]
    · simp [image_eq_zero_of_notMem_tsupport hg]

end Ops

theorem rlComm : RlComm := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D
  let ι : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hinj : Function.Injective ι := π.V.injective_subtype.comp D.inj
  have lift : ∀ (A B : Module.End ℂ D.U) (A' B' : Module.End ℂ (Sm E n)), (∀ u, ι (A u) = A' (ι u)) →
      (∀ u, ι (B u) = B' (ι u)) → Commute A' B' → Commute A B := fun A B A' B' hA hB hc =>
    LinearMap.ext fun u => hinj <| by
      have := LinearMap.congr_fun hc.eq (ι u)
      simp only [Module.End.mul_apply] at this ⊢
      rw [hA, hB, hB, hA, this]
  have h1 : ∀ w a b u, ι (D.E1 w a b u) = Eop w.embedding a b (ι u) := fun w a b u => D.hE1 w a b u
  have h2 : ∀ w a b u, ι (D.E2 w a b u) = (-Eop (ComplexEmbedding.conjugate w.embedding) b a) (ι u) :=
    fun w a b u => D.hE2 w a b u
  have h3 : ∀ w k u, ι (D.σ w k u) = rt E n (infGL E n (yAt w k)) (ι u) := fun w k u =>
    Subtype.ext <| funext fun g => (D.hσ w k u g).trans (chart_val _ g (yAt w k))
  have h4 : ∀ h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}, ∃ A : Module.End ℂ (Sm E n),
      (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧ ∀ u, ι (D.R h u) = A (ι u) := fun h => by
    obtain ⟨A, hA, hA'⟩ := exists_op μf K hKo hKc h.2
    exact ⟨A, hA, fun u => Subtype.ext ((D.hR h u).trans (hA' _ ((D.rng (D.i u)).1 ⟨u, rfl⟩)))⟩
  have mk1 : ∀ w : InfinitePlace E, InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding
  have mk2 : ∀ w : InfinitePlace E, InfinitePlace.mk (ComplexEmbedding.conjugate w.embedding) = w := fun w => by
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have ne : ∀ {τ τ' : E →+* ℂ}, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → τ ≠ τ' := fun h e => h (e ▸ rfl)
  refine ⟨fun i j hij a b => ⟨fun c d => ⟨?_, ?_, ?_⟩, fun k => ⟨?_, ?_⟩⟩, fun i j hij k k' => ?_, fun h i => ⟨fun a b => ⟨?_, ?_⟩, fun k => ?_⟩⟩
  · exact lift _ _ _ _ (h1 i a b) (h1 j c d) (Eop_comm (ne (by rwa [mk1, mk1])) a b c d)
  · exact lift _ _ _ _ (h1 i a b) (h2 j c d) (Commute.neg_right (Eop_comm (ne (by rwa [mk1, mk2])) a b d c))
  · exact lift _ _ _ _ (h2 i a b) (h2 j c d) (Commute.neg_left (Commute.neg_right (Eop_comm (ne (by rwa [mk2, mk2])) b a d c)))
  · exact lift _ _ _ _ (h1 i a b) (h3 j k) (commute_rt_Eop (by rwa [mk1]) k a b)
  · exact lift _ _ _ _ (h2 i a b) (h3 j k) (Commute.neg_left (commute_rt_Eop (by rwa [mk2]) k b a))
  · refine (lift _ _ _ _ (h3 i k) (h3 j k') ?_).eq
    show rt E n (infGL E n (yAt i k)) * rt E n (infGL E n (yAt j k')) = rt E n (infGL E n (yAt j k')) * rt E n (infGL E n (yAt i k))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, yAt_comm hij]
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h1 i a b) (hA _ fun g => commute_Eop_fin _ a b g)
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h2 i a b) (hA _ fun g => Commute.neg_left (commute_Eop_fin _ b a g))
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h3 i k) (hA _ fun g => commute_rt_fin _ g)

end UpperTheory.V.Z.GSp4Splitting
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ThetaFixedGlobalCharacter
noncomputable section

open NumberField MeasureTheory Matrix Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB (thetaA)
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

private theorem trace_range {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (i : U →ₗ[ℂ] V) (B : V →ₗ[ℂ] U) (F : Submodule ℂ U) [FiniteDimensional ℂ F] (hB : ∀ v, B v ∈ F) :
    FiniteDimensional ℂ (LinearMap.range (i ∘ₗ B)) ∧
      trOn F (B ∘ₗ i) = LinearMap.trace ℂ (LinearMap.range (i ∘ₗ B))
        ((i ∘ₗ B).restrict fun x _ => LinearMap.mem_range_self (i ∘ₗ B) x) := by
  have hle : LinearMap.range B ≤ F := by
    rintro _ ⟨v, rfl⟩
    exact hB v
  haveI : FiniteDimensional ℂ (LinearMap.range B) := Submodule.finiteDimensional_of_le hle
  haveI hfin : FiniteDimensional ℂ (LinearMap.range (i ∘ₗ B)) := by
    rw [LinearMap.range_comp]
    infer_instance
  refine ⟨hfin, ?_⟩
  let a : LinearMap.range (i ∘ₗ B) →ₗ[ℂ] LinearMap.range B := B.rangeRestrict ∘ₗ (LinearMap.range (i ∘ₗ B)).subtype
  let b : LinearMap.range B →ₗ[ℂ] LinearMap.range (i ∘ₗ B) :=
    (i ∘ₗ (LinearMap.range B).subtype).codRestrict _ (by
      rintro ⟨_, v, rfl⟩
      exact ⟨v, rfl⟩)
  let p : F →ₗ[ℂ] LinearMap.range B := B.rangeRestrict ∘ₗ i ∘ₗ F.subtype
  have h0 : ∀ x ∈ F, (B ∘ₗ i) x ∈ F := fun x _ => hB _
  have e1 : (B ∘ₗ i).restrict h0 = Submodule.inclusion hle ∘ₗ p := by
    ext x
    rfl
  have e2 : p ∘ₗ Submodule.inclusion hle = a ∘ₗ b := by
    ext x
    rfl
  have e3 : b ∘ₗ a = (i ∘ₗ B).restrict fun x _ => LinearMap.mem_range_self (i ∘ₗ B) x := by
    ext x
    rfl
  rw [trOn, dif_pos h0, e1, LinearMap.trace_comp_comm', e2, LinearMap.trace_comp_comm', e3]

private theorem trOn_smul {U : Type} [AddCommGroup U] [Module ℂ U] (F : Submodule ℂ U) (c : ℂ) (f : U →ₗ[ℂ] U)
    (hf : ∀ x ∈ F, f x ∈ F) : trOn F (c • f) = c * trOn F f := by
  have h : ∀ x ∈ F, (c • f) x ∈ F := fun x hx => F.smul_mem c (hf x hx)
  have e : (c • f).restrict h = c • f.restrict hf := by
    ext x
    rfl
  rw [trOn, trOn, dif_pos h, dif_pos hf, e, map_smul, smul_eq_mul]

section Conc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem exists_theta (π : CuspSub E n) (hθ : ThetaFix π) :
    ∃ t : π.V →ₗ[ℂ] π.V, ∀ ψ g, (t ψ).1.1 g = ψ.1.1 (thetaA E n g) := by
  choose f hf hfe using hθ.2
  refine ⟨⟨⟨fun ψ => ⟨f ψ.1 ψ.2, hf ψ.1 ψ.2⟩, fun a b => ?_⟩, fun c a => ?_⟩, fun ψ g => hfe ψ.1 ψ.2 g⟩
  · refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    change (f (a + b).1 (a + b).2).1 g = (f a.1 a.2).1 g + (f b.1 b.2).1 g
    rw [hfe, hfe, hfe]
    rfl
  · refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    change (f (c • a).1 (c • a).2).1 g = c * (f a.1 a.2).1 g
    rw [hfe, hfe]
    rfl

private theorem integrable_hecke (π : CuspSub E n) {K : Subgroup (GL (Fin n) (Af E))}
    (hKo : IsOpen (K : Set (GL (Fin n) (Af E)))) [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] {h : GL (Fin n) (Af E) → ℂ} (hh : IsHeckeF K h) (ψ : π.V)
    (x : GA E n) : Integrable (fun g => h g * ψ.1.1 (x * finGL E n g)) μf := by
  refine Continuous.integrable_of_hasCompactSupport ?_ hh.1.mul_right
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_)
  have hS : IsOpen {k | finRep E n k ψ.1 = ψ.1} := (π.cusp ψ.1 ψ.2).1.level
  have ho : IsOpen ((fun y => g⁻¹ * y) ⁻¹' ((K : Set (GL (Fin n) (Af E))) ∩ {k | finRep E n k ψ.1 = ψ.1})) :=
    (hKo.inter hS).preimage (continuous_const.mul continuous_id)
  filter_upwards [ho.mem_nhds (x := g) (by simp [K.one_mem])] with y hy
  have e1 : h y = h g := by simpa using hh.2 1 K.one_mem _ hy.1 g
  have e2 : ψ.1.1 (x * finGL E n g * finGL E n (g⁻¹ * y)) = ψ.1.1 (x * finGL E n g) :=
    congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (show finRep E n (g⁻¹ * y) ψ.1 = ψ.1 from hy.2)
  rw [mul_assoc, ← map_mul, mul_inv_cancel_left] at e2
  rw [e1, e2]

private theorem exists_hecke (hM : HeckeMem) (π : CuspSub E n) {K : Subgroup (GL (Fin n) (Af E))}
    (hKo : IsOpen (K : Set (GL (Fin n) (Af E)))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (D : Rl π K μf) {h : GL (Fin n) (Af E) → ℂ} (hh : IsHeckeF K h) :
    ∃ S : π.V →ₗ[ℂ] D.U, ∀ ψ, (D.i (S ψ)).1.1 = heckeOp μf h ψ.1.1 := by
  have hex : ∀ ψ : π.V, ∃ u, (D.i u).1.1 = heckeOp μf h ψ.1.1 := fun ψ => by
    obtain ⟨-, -, ψ', -, h1, h2⟩ := hM E n π K hKo hKc μf h hh ψ
    obtain ⟨u, rfl⟩ := (D.rng ψ').2 h2
    exact ⟨u, h1⟩
  choose f hf using hex
  refine ⟨⟨⟨f, fun a b => D.inj ?_⟩, fun c a => D.inj ?_⟩, hf⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [map_add (f := _)]
    change (D.i (f (a + b))).1.1 x = (D.i (f a)).1.1 x + (D.i (f b)).1.1 x
    rw [hf, hf, hf, heckeOp, heckeOp, heckeOp,
      ← integral_add (integrable_hecke π hKo μf hh a x) (integrable_hecke π hKo μf hh b x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_add (h g) (a.1.1 _) (b.1.1 _)
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [map_smul]
    change (D.i (f (c • a))).1.1 x = c * (D.i (f a)).1.1 x
    rw [hf, hf, heckeOp, heckeOp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_left_comm (h g) c (a.1.1 _)

end Conc

end UpperTheory.V.Z.GSp4Splitting

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH in
theorem UpperTheory.V.Z.GSp4Splitting.exists_global_hecke_theta_lift :
    AvgEx → AbsGlob → LowIso → HeckeMem → RlEx → RlPair → RlChar → RlK → RlTheta → RlComm → RlHecke → RlSimple → RlFin → RlLow → OpForm → ThetaFixedGlobalCharacter := by
  intro hAvg hAbs hLow hM hEx hPair hChar hK hTh hComm hHk hSim hFin hRL hOp
  intro E _ _ _ n hn π hreg hθ lam hlam hch K hKo hKc hKθ hfix _ _ μC _ _ _ μf _ μ _
  classical
  obtain ⟨D⟩ := hEx E n hn π hθ K hKo hKc hKθ μf
  replace hPair := hPair E n hn π hθ K hKo hKc hKθ μf D
  replace hChar := hChar E n hn π hθ K hKo hKc hKθ μf D
  replace hK := hK E n hn π hθ K hKo hKc hKθ μf D
  obtain ⟨hsq, hiso, hT⟩ := hTh E n hn π hθ K hKo hKc hKθ μf D
  obtain ⟨hc1, hc2, hc3⟩ := hComm E n hn π hθ K hKo hKc hKθ μf D
  obtain ⟨hadj, htw⟩ := hHk E n hn π hθ K hKo hKc hKθ μf D
  replace hSim := hSim E n hn π hθ K hKo hKc hKθ μf D
  replace hFin := hFin E n hn π hθ K hKo hKc hKθ μf D fun w => lefE n (lam w)
  replace hRL := hRL E n hn π hθ K hKo hKc hKθ μf D hreg
  replace hOp := hOp E n hn π hθ K hKo hKc hKθ μf D lam hch
  have hnt : Nontrivial D.U := by
    obtain ⟨ψ, hψ, hψ0, hψK⟩ := hfix
    obtain ⟨u, hu⟩ := (D.rng ⟨ψ, hψ⟩).2 hψK
    refine nontrivial_of_ne u 0 fun h0 => hψ0 ?_
    rw [h0, map_zero] at hu
    exact (congrArg Subtype.val hu).symm
  letI : MeasurableSpace (Un n) := borel _
  haveI : BorelSpace (Un n) := ⟨rfl⟩
  let ν : Measure (Un n) := Measure.haarMeasure ⊤
  have hν : ν Set.univ = 1 := Measure.haarMeasure_self (K₀ := ⊤)
  have hloc : ∀ w, IsLoc (infOf (lam w)) (D.E1 w) (D.E2 w) (D.σ w) D.Θ := fun w =>
    ⟨hPair w, (hChar w (lam w) (hch w)).1, (hChar w (lam w) (hch w)).2, (hK w).2, (hK w).1, hsq, hiso, (hT w).1, (hT w).2⟩
  choose P hP using fun w => hAvg n ν D.U (D.σ w) (hK w).1 (lefE n (lam w)) (lefT n (lam w))
  obtain ⟨Y, c₁, hc₁, hYf, hY0, hYR, hYΘ, hYs, hPF, htr⟩ := hAbs n (InfinitePlace E) lam hlam (fun w => lefE n (lam w))
    (fun w => lefT n (lam w)) (fun w => isLefK_model (lam w) (hlam w)) ν hν D.U D.E1 D.E2 D.σ D.Θ P _ D.R hloc hP hc1 hc2 hc3
    hadj (fun h => (htw h).imp fun _ h' => h'.2) hsq hSim hnt hFin
    (fun w => hLow n (lam w) (hlam w) _ _ (isLefK_model (lam w) (hlam w)) D.U _ _ _ _ (hloc w)
      (hRL hnt w (lam w) (hlam w) (hch w)))
  obtain ⟨c₂, hc₂, hop⟩ := hOp ν hν μC μ P hP
  let j : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hj : Function.Injective j := Subtype.val_injective.comp D.inj
  let e : Y ≃ₗ[ℂ] Y.map j := Submodule.equivMapOfInjective j hj Y
  have he : ∀ y : Y, ((e y : Y.map j) : Sm E n) = (D.i y).1 := fun _ => rfl
  let ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ (Y.map j) := fun h =>
    if hh : IsHeckeF K h then e.conj ((D.R ⟨h, hh⟩).restrict (hYR ⟨h, hh⟩)) else 0
  have hρ : ∀ h (hh : IsHeckeF K h), ρ h = e.conj ((D.R ⟨h, hh⟩).restrict (hYR ⟨h, hh⟩)) := fun h hh => dif_pos hh
  have hmul : ∀ f g : Module.End ℂ Y, e.conj f * e.conj g = e.conj (f * g) := fun f g => (e.conj_comp g f).symm
  refine ⟨Y.map j, ρ, e.conj (D.Θ.restrict hYΘ), c₂ * c₁, ?_, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_,
    mul_ne_zero hc₂ hc₁, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact (D.i u).2
  · intro h0
    refine hY0 ((Submodule.eq_bot_iff _).2 fun y hy => hj ?_)
    rw [map_zero]
    exact (Submodule.eq_bot_iff _).1 h0 _ ⟨y, hy, rfl⟩
  · rintro _ ⟨u, -, rfl⟩
    exact (D.rng (D.i u)).1 ⟨u, rfl⟩
  · intro h hh y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [hρ h hh, LinearEquiv.conj_apply_apply, e.symm_apply_apply, he, he]
    exact D.hR ⟨h, hh⟩ y
  · intro W hW
    rcases hYs ((W.comap e.toLinearMap).map Y.subtype) (Submodule.map_subtype_le _ _) (by
      rintro ⟨h, hh⟩ _ ⟨y, hy, rfl⟩
      refine ⟨(D.R ⟨h, hh⟩).restrict (hYR ⟨h, hh⟩) y, ?_, rfl⟩
      have := hW h hh (e y) hy
      rwa [hρ h hh, LinearEquiv.conj_apply_apply, e.symm_apply_apply] at this) with h0 | h1
    · refine Or.inl ((Submodule.eq_bot_iff _).2 fun y hy => ?_)
      obtain ⟨y, rfl⟩ := e.surjective y
      have : (y : D.U) = 0 := (Submodule.eq_bot_iff _).1 h0 _ ⟨y, hy, rfl⟩
      rw [show y = 0 from Subtype.ext this, e.map_zero]
    · refine Or.inr (Submodule.eq_top_iff'.2 fun y => ?_)
      obtain ⟨y, rfl⟩ := e.surjective y
      obtain ⟨z, hz, hzy⟩ : (y : D.U) ∈ (W.comap e.toLinearMap).map Y.subtype := h1.symm ▸ y.2
      rw [← show z = y from Subtype.ext hzy]
      exact hz
  · rw [hmul]
    have : D.Θ.restrict hYΘ * D.Θ.restrict hYΘ = 1 :=
      LinearMap.ext fun y => Subtype.ext (LinearMap.congr_fun hsq y.1)
    rw [this]
    exact e.conj_id
  · intro h hh
    obtain ⟨⟨h', hh'⟩, rfl, hc⟩ := htw ⟨h, hh⟩
    rw [hρ h hh, hρ _ hh', hmul, hmul]
    exact congrArg e.conj (LinearMap.ext fun y => Subtype.ext (LinearMap.congr_fun hc y.1))
  · intro k val T hk h hh
    obtain ⟨t, ht⟩ := exists_theta π hθ
    obtain ⟨S, hS⟩ := exists_hecke hM π hKo hKc μf D hh
    set Q : Module.End ℂ D.U := ((univ : Finset (InfinitePlace E)).toList.map P).prod with hQ
    set a : ℂ := c₂ * ∏ w, val w (infOf (lam w)) with ha
    haveI := hFin
    obtain ⟨hf, htrL⟩ := trace_range D.i (a • (Q ∘ₗ S ∘ₗ t)) (⨅ w, isoSp (D.σ w) (lefE n (lam w)))
      fun v => Submodule.smul_mem _ _ (hPF _)
    refine ⟨D.i ∘ₗ (a • (Q ∘ₗ S ∘ₗ t)), fun ψ x => ?_, hf, ?_⟩
    · have h1 := hop k val T hk h hh (t ψ) (S (t ψ)) (hS _) x
      simp only [ht] at h1
      rw [h1, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
      rfl
    · have h2 : (a • (Q ∘ₗ S ∘ₗ t)) ∘ₗ D.i = a • (Q * D.R ⟨h, hh⟩ * D.Θ) := by
        refine LinearMap.ext fun u => ?_
        have h3 : t (D.i u) = D.i (D.Θ u) := Subtype.ext (Subtype.ext (funext fun g => by rw [ht, D.hΘ]))
        have h4 : S (D.i (D.Θ u)) = D.R ⟨h, hh⟩ (D.Θ u) := D.inj (Subtype.ext (Subtype.ext (by rw [hS, D.hR])))
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.mul_apply, h3, h4]
      have h5 : ∀ y ∈ Y, (D.R ⟨h, hh⟩ * D.Θ) y ∈ Y := fun y hy => hYR _ _ (hYΘ y hy)
      have h6 : LinearMap.trace ℂ (Y.map j) (ρ h * e.conj (D.Θ.restrict hYΘ)) = trOn Y (D.R ⟨h, hh⟩ * D.Θ) := by
        rw [hρ h hh, hmul, LinearMap.trace_conj', trOn, dif_pos h5]
        rfl
      rw [← htrL, h2, trOn_smul _ a (Q * D.R ⟨h, hh⟩ * D.Θ) (fun x _ => hPF _), htr, h6, ha]
      ring
end
end
