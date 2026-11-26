module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

abbrev ProjIdx (K : Type) [Field K] [NumberField K] (i : ℕ) : Type :=
  Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin i

abbrev projBlocks (K : Type) [Field K] [NumberField K] (i : ℕ) : Unit → Type := fun _ => ProjIdx K i

abbrev ProjField (K : Type) [Field K] (i : ℕ) : Type := FractionRing (MvPolynomial (Fin i) K)


open scoped Classical in
def embComp {K : Type} [Field K] [NumberField K] {i : ℕ} (σ : K →+* ℂ) (z : ProjIdx K i → ℂ) :
    Fin i → ℂ :=
  by
    classical
    exact fun j => ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single σ 1) m * z (m, j)

def latticeNormSq {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i)
    (z : ProjIdx K i → ℂ) : ℝ :=
  ∑ σ : K →+* ℂ, (star (embComp σ z) ⬝ᵥ (F.metric σ *ᵥ embComp σ z)).re

theorem latticeNormSq_term_nonneg {K : Type} [Field K] [NumberField K] {i : ℕ}
    (F : HermLattice K i) (σ : K →+* ℂ) (w : Fin i → ℂ) :
    0 ≤ (star w ⬝ᵥ (F.metric σ *ᵥ w)).re := by
  by_cases hw : w = 0
  · simp [hw]
  · exact ((Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hw)).1).le

theorem embComp_smul {K : Type} [Field K] [NumberField K] {i : ℕ} (σ : K →+* ℂ) (c : ℂ)
    (z : ProjIdx K i → ℂ) : embComp σ (c • z) = c • embComp σ z := by
  funext j
  simp only [embComp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring


open scoped Classical in
theorem sum_emb_embComp {K : Type} [Field K] [NumberField K] {i : ℕ} (z : ProjIdx K i → ℂ)
    (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (j : Fin i) :
    ∑ σ : K →+* ℂ, σ (integralBasis K m) * embComp σ z j = z (m, j) := by
  classical
  set b := canonicalEmbedding.latticeBasis K
  have hb : b m = ∑ σ : K →+* ℂ, σ (integralBasis K m) • (Pi.single σ 1 : (K →+* ℂ) → ℂ) := by
    funext τ
    simp [b, canonicalEmbedding.latticeBasis_apply, canonicalEmbedding.apply_at, Pi.single_apply]
  have hr : ∀ m' , (if m = m' then (1 : ℂ) else 0) =
      ∑ σ : K →+* ℂ, σ (integralBasis K m) * b.repr (Pi.single σ 1) m' := by
    intro m'
    have := congrArg (fun v => b.repr v m') hb
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.repr_self, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at this
    rw [← this, Finsupp.single_apply]
  have hs : ∀ m', ∑ σ : K →+* ℂ, σ (integralBasis K m) * (b.repr (Pi.single σ 1) m' * z (m', j)) =
      (if m = m' then (1 : ℂ) else 0) * z (m', j) := by
    intro m'
    rw [hr m', Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by ring
  calc ∑ σ : K →+* ℂ, σ (integralBasis K m) * embComp σ z j
      = ∑ σ : K →+* ℂ, ∑ m', σ (integralBasis K m) * (b.repr (Pi.single σ 1) m' * z (m', j)) := by
        simp only [embComp, Finset.mul_sum]; rfl
    _ = ∑ m', ∑ σ : K →+* ℂ, σ (integralBasis K m) * (b.repr (Pi.single σ 1) m' * z (m', j)) :=
        Finset.sum_comm
    _ = ∑ m', (if m = m' then (1 : ℂ) else 0) * z (m', j) := Finset.sum_congr rfl fun m' _ => hs m'
    _ = z (m, j) := by simp

def latticeLine {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    HermLine (projBlocks K i) where
  a := fun _ => 1
  h z := Real.sqrt (latticeNormSq F fun q => z ⟨(), q⟩)
  pos z hz := by
    apply Real.sqrt_pos.mpr
    obtain ⟨⟨m, j⟩, hmj⟩ := hz ()
    have hσ : ∃ σ : K →+* ℂ, embComp σ (fun q => z ⟨(), q⟩) ≠ 0 := by
      by_contra h
      push Not at h
      apply hmj
      rw [← sum_emb_embComp (fun q => z ⟨(), q⟩) m j]
      simp [h]
    obtain ⟨σ, hσ⟩ := hσ
    have hpos : 0 < (star (embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ
        (F.metric σ *ᵥ embComp σ fun q => z ⟨(), q⟩)).re :=
      (Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hσ)).1
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun σ =>
      (star (embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ (F.metric σ *ᵥ embComp σ fun q => z ⟨(), q⟩)).re)
      (fun σ _ => latticeNormSq_term_nonneg F σ _) (Finset.mem_univ σ))
  smul c z hc := by
    have hz : (fun q => (fun p : Σ _ : Unit, ProjIdx K i => c p.1 * z p) ⟨(), q⟩) =
        c () • fun q => z ⟨(), q⟩ := by
      funext q; rfl
    simp only [hz, latticeNormSq, embComp_smul, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    have : ∀ σ : K →+* ℂ, (star (c () • embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ
        (F.metric σ *ᵥ (c () • embComp σ fun q => z ⟨(), q⟩))).re =
        ‖c ()‖ ^ 2 * (star (embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ
          (F.metric σ *ᵥ embComp σ fun q => z ⟨(), q⟩)).re := by
      intro σ
      rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul,
        Complex.normSq_eq_norm_sq]
    simp only [this, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

def LineOfLargeDegreeFromZ.Statement : Prop :=
  SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement → LineOfLargeDegree.Statement

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPtsIntegralZeroLowerNE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory

noncomputable section

namespace PtsIntegralZeroLowerNEAux

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem rel_of_mk_eq {W : Ideal (MRing ι)} {a b : mcPts W}
    (h : (Quot.mk _ a : McClasses W) = Quot.mk _ b) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (b : (Σ k, ι k) → ℂ) = fun p => c p.1 * (a : (Σ k, ι k) → ℂ) p := by
  have hg := Quot.eqvGen_exact h
  clear h
  induction hg with
  | rel x y hxy => exact hxy
  | refl x => exact ⟨1, fun _ => one_ne_zero, by funext p; simp⟩
  | symm x y _ ih =>
    obtain ⟨c, hc, e⟩ := ih
    refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
    funext p
    rw [e]
    field_simp [hc p.1]
  | trans x y w _ _ ih1 ih2 =>
    obtain ⟨c, hc, e⟩ := ih1
    obtain ⟨d, hd, e'⟩ := ih2
    refine ⟨fun k => d k * c k, fun k => mul_ne_zero (hd k) (hc k), ?_⟩
    funext p
    rw [e', e]
    ring

theorem maDensity_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (z : Fin 0 → ℂ) : maDensity φ z = 1 := by
  simp [maDensity, mixedDisc, Matrix.det_fin_zero]

theorem integral_fin_zero (F : (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : ∫ y', F y' = F y := by
  rw [Measure.volume_pi_eq_dirac y, integral_dirac]


omit [∀ k, Fintype (ι k)] in
theorem segre_ne_zero {W : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts W) : segre z ≠ 0 := by
  intro h0
  choose p hp using hz.1
  have h := congrFun h0 p
  simp only [segre, Pi.zero_apply] at h
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => hp k) h

theorem exists_goodProj {W : Ideal (MRing ι)} (hfin : Finite (McClasses W)) :
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj W Ψ := by
  classical
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun q : McClasses W => segre (q.out : (Σ k, ι k) → ℂ)) (fun q => segre_ne_zero q.out.2)
  refine ⟨LinearMap.pi fun _ => f, fun z hz h => ?_⟩
  obtain ⟨c, hc, e⟩ := rel_of_mk_eq (Quot.out_eq (Quot.mk _ ⟨z, hz⟩ : McClasses W))
  have e' : z = fun p => c p.1 * ((Quot.mk _ ⟨z, hz⟩ : McClasses W).out : (Σ k, ι k) → ℂ) p := e
  have h0 := congrFun h 0
  rw [LinearMap.pi_apply, Pi.zero_apply, e', segre_smul, map_smul, smul_eq_mul] at h0
  exact hf _ ((mul_eq_zero.mp h0).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => hc k))

theorem bij_fibre [Nonempty K] {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (hΨ : IsGoodProj W Ψ) (y : Fin 0 → ℂ) :
    ∃ M : McClasses W → ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y, Function.Bijective M := by
  classical
  set a : ((Σ k, ι k) → ℂ) → ℂ := fun z => Ψ (segre z) 0 with ha_def
  have ha : ∀ z ∈ mcPts W, a z ≠ 0 := fun z hz h0 =>
    hΨ z hz (funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h0)
  set N : ((Σ k, ι k) → ℂ) → (((k : K) → ι k) → ℂ) := fun z => (a z)⁻¹ • segre z with hN
  have hNmem : ∀ z (hz : z ∈ mcPts W), N z ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y := by
    intro z hz
    obtain ⟨k0⟩ := ‹Nonempty K›
    let u : K → ℂ := Pi.mulSingle k0 (a z)⁻¹
    have hu : ∀ k, u k ≠ 0 := fun k => by
      by_cases hk : k = k0
      · subst hk; simp [u, ha z hz]
      · simp [u, Pi.mulSingle_eq_of_ne hk]
    refine ⟨fun p => u p.1 * z p, mcPts_smul hW u hu hz, ?_, ?_⟩
    · rw [segre_smul]
      simp [u, N]
    · funext i
      rw [Fin.fin_one_eq_zero i]
      simp [N, a, ha z hz]
  have hNrel : ∀ z z' : mcPts W, (∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (z' : (Σ k, ι k) → ℂ) = fun p => c p.1 * (z : (Σ k, ι k) → ℂ) p) → N z = N z' := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ ⟨c, hc, e⟩
    simp only at e
    subst e
    have hpc : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
    simp only [N, a, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    field_simp [hpc, ha z hz]
  let M : McClasses W → ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y :=
    Quot.lift (fun z => ⟨N z, hNmem z z.2⟩) (fun z z' h => Subtype.ext (hNrel z z' h))
  refine ⟨M, ?_, ?_⟩
  · intro q q'
    induction q using Quot.ind with | mk z => ?_
    induction q' using Quot.ind with | mk z' => ?_
    intro h
    have h' : N z = N z' := congrArg Subtype.val h
    have hs : segre (z : (Σ k, ι k) → ℂ) = (a z * (a z')⁻¹) • segre (z' : (Σ k, ι k) → ℂ) := by
      have := congrArg (fun v => a z • v) h'
      simp only [N, smul_smul] at this
      rw [mul_inv_cancel₀ (ha z z.2), one_smul] at this
      exact this
    obtain ⟨c, hc, e⟩ :=
      sameOrbit_of_segre z'.2.1 _ (mul_ne_zero (ha z z.2) (inv_ne_zero (ha z' z'.2))) hs
    exact (Quot.sound ⟨c, hc, e⟩).symm
  · rintro ⟨w, z, hz, rfl, hw⟩
    refine ⟨Quot.mk _ ⟨z, hz⟩, Subtype.ext ?_⟩
    show N z = segre z
    have h1 : a z = 1 := by
      show Ψ (segre z) 0 = 1
      rw [hw]
      rfl
    simp [N, h1]


omit [∀ k, Fintype (ι k)] in
theorem density_ge {W : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ} {g : ((Σ k, ι k) → ℂ) → ℝ} {c : ℝ}
    (hc : ∀ z ∈ mcPts W, c ≤ g z) {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre W Ψ y) :
    c ≤ sheetDensity W Ψ φ g y w := by
  classical
  obtain ⟨z, hz, rfl, hΨz⟩ := hw
  have hex : ∃ γ, IsSheet W Ψ y (segre z) γ :=
    ⟨fun _ => z, rfl, Filter.Eventually.of_forall fun y' =>
      ⟨differentiableAt_const _, hz, by rw [Subsingleton.elim y' y]; exact hΨz⟩⟩
  unfold sheetDensity
  rw [dite_eq_left hex, maDensity_zero, mul_one]
  exact hc _ hex.choose_spec.2.self_of_nhds.2.1

end PtsIntegralZeroLowerNEAux


open PtsIntegralZeroLowerNEAux in
theorem PtsIntegralZeroLowerNE.proof : PtsIntegralZeroLowerNE.Statement := by
  intro K _ _ ι _ W φ g c hW hfin _ hc
  classical
  obtain ⟨Ψ0, hΨ0⟩ := exists_goodProj hfin
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj W Ψ := ⟨Ψ0, hΨ0⟩
  unfold ptsIntegral
  rw [dite_eq_left hex]
  have hΨ : IsGoodProj W hex.choose := hex.choose_spec
  let y : Fin 0 → ℂ := fun i => i.elim0
  unfold ptsIntegralAt
  rw [integral_fin_zero _ y]
  obtain ⟨M, hM⟩ := bij_fibre hW hex.choose hΨ y
  have := hfin
  have : Finite (ReciprocityTheory.ChartRestriction.G.Geo.fibre W hex.choose y) := Finite.of_surjective M hM.2
  have hF : (ReciprocityTheory.ChartRestriction.G.Geo.fibre W hex.choose y).Finite := Set.toFinite _
  have hcard : degC W = hF.toFinset.card := by
    rw [← Nat.card_eq_card_finite_toFinset hF, ← Nat.card_eq_of_bijective M hM]
    rfl
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, hcard]
  have h := Finset.card_nsmul_le_sum hF.toFinset (fun w => sheetDensity W hex.choose φ g y w) c
    (fun w hw => density_ge hc ((Set.Finite.mem_toFinset hF).mp hw))
  rw [nsmul_eq_mul] at h
  linarith

end

end GroundTheory.Heights₂.Heights
end
