module

public import Formalism.PeriodIntegrals.VolFromSW
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.IsPositiveDefiniteMatrixCoefficientOfMemAlgA
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.InstCompactUG
noncomputable section

namespace PI.UnitaryGroupMassFormula.PolyCoef

open MeasureTheory Matrix

abbrev UG (N : ℕ) := ↥(Matrix.unitaryGroup (Fin N) ℂ)

lemma isCompact_UG (N : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
  have hc : IsClosed ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
    have : ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) =
        {g | star g * g = 1} ∩ {g | g * star g = 1} := by
      ext g; exact Unitary.mem_iff
    rw [this]
    exact (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  have hb : IsCompact (Set.pi Set.univ fun _ : Fin N =>
      Set.pi Set.univ fun _ : Fin N => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hb.of_isClosed_subset hc ?_
  intro g hg i _ j _
  simpa using entry_norm_bound_of_unitary hg i j

instance instCompactUG (N : ℕ) : CompactSpace (UG N) :=
  isCompact_iff_compactSpace.mp (isCompact_UG N)

instance instMeasUG (N : ℕ) : MeasurableSpace (UG N) := borel _

instance instBorelUG (N : ℕ) : BorelSpace (UG N) := ⟨rfl⟩

def ent {N : ℕ} (g : UG N) : Fin N × Fin N → ℂ := fun ij => (g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2

def IsPD {N : ℕ} (f : UG N → ℂ) : Prop :=
  ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ),
    ∀ g : UG N, f g * (g : Matrix (Fin N) (Fin N) ℂ).det ^ k = MvPolynomial.eval (ent g) P

def detP (N : ℕ) : MvPolynomial (Fin N × Fin N) ℂ := (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).det

lemma mapX_eval {N : ℕ} (g : UG N) :
    (MvPolynomial.eval (ent g)).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ) =
      (g : Matrix (Fin N) (Fin N) ℂ) :=
  Matrix.mvPolynomialX_mapMatrix_eval (g : Matrix (Fin N) (Fin N) ℂ)

lemma eval_detP {N : ℕ} (g : UG N) :
    MvPolynomial.eval (ent g) (detP N) = (g : Matrix (Fin N) (Fin N) ℂ).det := by
  unfold detP
  rw [RingHom.map_det, mapX_eval]

lemma IsPD.const {N : ℕ} (c : ℂ) : IsPD (fun _ : UG N => c) :=
  ⟨0, MvPolynomial.C c, fun g => by simp⟩

lemma IsPD.add {N : ℕ} {f f' : UG N → ℂ} (hf : IsPD f) (hf' : IsPD f') : IsPD (fun g => f g + f' g) := by
  obtain ⟨k, P, hP⟩ := hf
  obtain ⟨k', P', hP'⟩ := hf'
  refine ⟨k + k', P * detP N ^ k' + P' * detP N ^ k, fun g => ?_⟩
  simp only [map_add (f := _), map_mul, map_pow, eval_detP, ← hP g, ← hP' g]
  ring

lemma IsPD.mul {N : ℕ} {f f' : UG N → ℂ} (hf : IsPD f) (hf' : IsPD f') : IsPD (fun g => f g * f' g) := by
  obtain ⟨k, P, hP⟩ := hf
  obtain ⟨k', P', hP'⟩ := hf'
  refine ⟨k + k', P * P', fun g => ?_⟩
  simp only [map_mul, ← hP g, ← hP' g]
  ring

lemma IsPD.sum {N : ℕ} {ι : Type*} (s : Finset ι) {F : ι → UG N → ℂ} (hF : ∀ i ∈ s, IsPD (F i)) :
    IsPD (fun g => ∑ i ∈ s, F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (IsPD.const (N := N) 0)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

lemma IsPD.entry {N : ℕ} (i j : Fin N) : IsPD (fun g : UG N => (g : Matrix (Fin N) (Fin N) ℂ) i j) :=
  ⟨0, MvPolynomial.X (i, j), fun g => by simp [ent]⟩

lemma adjugate_eq {N : ℕ} (g : UG N) :
    (g : Matrix (Fin N) (Fin N) ℂ).adjugate =
      (g : Matrix (Fin N) (Fin N) ℂ).det • star (g : Matrix (Fin N) (Fin N) ℂ) := by
  have h1 : star (g : Matrix (Fin N) (Fin N) ℂ) * (g : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self g
  calc (g : Matrix (Fin N) (Fin N) ℂ).adjugate
      = (star (g : Matrix (Fin N) (Fin N) ℂ) * (g : Matrix (Fin N) (Fin N) ℂ)) *
          (g : Matrix (Fin N) (Fin N) ℂ).adjugate := by rw [h1, Matrix.one_mul]
    _ = star (g : Matrix (Fin N) (Fin N) ℂ) * ((g : Matrix (Fin N) (Fin N) ℂ) *
          (g : Matrix (Fin N) (Fin N) ℂ).adjugate) := by rw [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]

lemma IsPD.conjEntry {N : ℕ} (i j : Fin N) :
    IsPD (fun g : UG N => star ((g : Matrix (Fin N) (Fin N) ℂ) i j)) := by
  refine ⟨1, (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).adjugate j i, fun g => ?_⟩
  have h : MvPolynomial.eval (ent g) ((Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).adjugate j i) =
      ((MvPolynomial.eval (ent g)).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).adjugate) j i := rfl
  rw [h, RingHom.map_adjugate, mapX_eval, adjugate_eq]
  show star ((g : Matrix (Fin N) (Fin N) ℂ) i j) * (g : Matrix (Fin N) (Fin N) ℂ).det ^ 1 = _
  simp [Matrix.star_apply, mul_comm]

def coordC {N : ℕ} (i j : Fin N) : C(UG N, ℂ) :=
  ⟨fun g => (g : Matrix (Fin N) (Fin N) ℂ) i j,
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)⟩

def algA (N : ℕ) : StarSubalgebra ℂ C(UG N, ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range fun ij : Fin N × Fin N => coordC ij.1 ij.2)

lemma algA_dense (N : ℕ) (F : C(UG N, ℂ)) {ε : ℝ} (hε : 0 < ε) : ∃ f ∈ algA N, ‖F - f‖ < ε := by
  have hsep : (algA N).SeparatesPoints := by
    intro x y hxy
    have hne : (x : Matrix (Fin N) (Fin N) ℂ) ≠ y := fun h => hxy (Subtype.ext h)
    obtain ⟨i, j, hij⟩ : ∃ i j, (x : Matrix (Fin N) (Fin N) ℂ) i j ≠ (y : Matrix (Fin N) (Fin N) ℂ) i j := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hne (Matrix.ext hcon)
    refine ⟨coordC i j, ⟨coordC i j, StarAlgebra.subset_adjoin ℂ _ ⟨(i, j), rfl⟩, rfl⟩, hij⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (algA N) hsep
  have hF : F ∈ closure ((algA N : Set C(UG N, ℂ))) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]; trivial
  obtain ⟨f, hf, hd⟩ := Metric.mem_closure_iff.mp hF ε hε
  exact ⟨f, hf, by rwa [dist_eq_norm] at hd⟩

def Sep {N : ℕ} (f : UG N → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → UG N → ℂ), (∀ i, IsPD (a i)) ∧ (∀ i, Continuous (b i)) ∧
    ∀ h y : UG N, f (h⁻¹ * y) = ∑ i, a i h * b i y

lemma Sep.const {N : ℕ} (c : ℂ) : Sep (fun _ : UG N => c) :=
  ⟨Unit, inferInstance, fun _ _ => c, fun _ _ => 1, fun _ => IsPD.const c, fun _ => continuous_const,
    fun h y => by simp⟩

lemma Sep.add {N : ℕ} {f f' : UG N → ℂ} (hf : Sep f) (hf' : Sep f') : Sep (fun g => f g + f' g) := by
  obtain ⟨ι, _, a, b, ha, hb, he⟩ := hf
  obtain ⟨ι', _, a', b', ha', hb', he'⟩ := hf'
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim b b', ?_, ?_, fun h y => ?_⟩
  · rintro (i | i); exacts [ha i, ha' i]
  · rintro (i | i); exacts [hb i, hb' i]
  · simp [Fintype.sum_sum_type, he, he']

lemma Sep.mul {N : ℕ} {f f' : UG N → ℂ} (hf : Sep f) (hf' : Sep f') : Sep (fun g => f g * f' g) := by
  obtain ⟨ι, _, a, b, ha, hb, he⟩ := hf
  obtain ⟨ι', _, a', b', ha', hb', he'⟩ := hf'
  refine ⟨ι × ι', inferInstance, fun p g => a p.1 g * a' p.2 g, fun p g => b p.1 g * b' p.2 g,
    fun p => (ha p.1).mul (ha' p.2), fun p => (hb p.1).mul (hb' p.2), fun h y => ?_⟩
  show f (h⁻¹ * y) * f' (h⁻¹ * y) = ∑ p : ι × ι', (a p.1 h * a' p.2 h) * (b p.1 y * b' p.2 y)
  rw [he, he', Fintype.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma Sep.coord {N : ℕ} (i j : Fin N) : Sep (fun g : UG N => (g : Matrix (Fin N) (Fin N) ℂ) i j) := by
  refine ⟨Fin N, inferInstance, fun k h => star ((h : Matrix (Fin N) (Fin N) ℂ) k i),
    fun k y => (y : Matrix (Fin N) (Fin N) ℂ) k j, fun k => IsPD.conjEntry k i,
    fun k => (coordC k j).continuous, fun h y => ?_⟩
  show (star (h : Matrix (Fin N) (Fin N) ℂ) * (y : Matrix (Fin N) (Fin N) ℂ)) i j = _
  rw [Matrix.mul_apply]
  simp [Matrix.star_apply]

lemma Sep.conjCoord {N : ℕ} (i j : Fin N) :
    Sep (fun g : UG N => star ((g : Matrix (Fin N) (Fin N) ℂ) i j)) := by
  refine ⟨Fin N, inferInstance, fun k h => (h : Matrix (Fin N) (Fin N) ℂ) k i,
    fun k y => star ((y : Matrix (Fin N) (Fin N) ℂ) k j), fun k => IsPD.entry k i,
    fun k => (coordC k j).continuous.star, fun h y => ?_⟩
  show star ((star (h : Matrix (Fin N) (Fin N) ℂ) * (y : Matrix (Fin N) (Fin N) ℂ)) i j) = _
  rw [Matrix.mul_apply]
  simp [Matrix.star_apply]

lemma sep_of_mem {N : ℕ} {f : C(UG N, ℂ)} (hf : f ∈ algA N) : Sep (⇑f) := by
  letI : Star (Set C(UG N, ℂ)) := Set.star
  have hf' : f ∈ Algebra.adjoin ℂ ((Set.range fun ij : Fin N × Fin N => coordC ij.1 ij.2) ∪
      star (Set.range fun ij : Fin N × Fin N => coordC ij.1 ij.2)) := by
    rw [← StarAlgebra.adjoin_toSubalgebra]; exact hf
  clear hf
  induction hf' using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨⟨i, j⟩, rfl⟩ | hx
    · exact Sep.coord i j
    · obtain ⟨⟨i, j⟩, hij⟩ := (Set.mem_star.mp hx)
      have : x = star (coordC i j) := by rw [show coordC i j = star x from hij, star_star]
      subst this
      exact Sep.conjCoord i j
  | algebraMap r => exact Sep.const r
  | add x y _ _ hx hy => exact Sep.add hx hy
  | mul x y _ _ hx hy => exact Sep.mul hx hy

end PI.UnitaryGroupMassFormula.PolyCoef
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.PolyCoef

open MeasureTheory PI.UpqRep
open scoped InnerProductSpace

lemma Jm_allPos (N : ℕ) : Jm (allPos N) = 1 := by
  simp [Jm, allPos]

lemma mem_Kset_iff {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) :
    g ∈ Kset (allPos N) ↔ g ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  simp [Kset, Jm_allPos]

lemma memK {N : ℕ} (g : UG N) : (g : Matrix (Fin N) (Fin N) ℂ) ∈ Kset (allPos N) :=
  (mem_Kset_iff _).mpr g.2

abbrev muU (N : ℕ) : Measure (UG N) := Measure.haar

section

variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}

def orb (hst : IsKStableOn (allPos N) σ S) (u : S) : UG N → S :=
  fun x => ⟨σ x u, hst _ (memK x) _ u.2⟩

lemma orb_cont (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S) (u : S) :
    Continuous (orb hst u) := by
  refine Continuous.subtype_mk ?_ _
  exact (hrep.2.2 (u : H)).comp_continuous continuous_subtype_val fun x => memK x

lemma integrable_cont {E : Type*} [NormedAddCommGroup E] {F : UG N → E} (hF : Continuous F) :
    Integrable F (muU N) :=
  hF.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

def T (hst : IsKStableOn (allPos N) σ S) (f : C(UG N, ℂ)) (u : S) : S :=
  ∫ x, f x • orb hst u x ∂(muU N)

lemma inner_sigma_T_eq_integral_mul_inner [FiniteDimensional ℂ S] (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S)
    (f : C(UG N, ℂ)) (u : S) (w : H) (h : UG N) :
    ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ =
      ∫ x, f x * ⟪w, σ ((h * x : UG N) : Matrix (Fin N) (Fin N) ℂ) u⟫_ℂ ∂(muU N) := by
  have hint : Integrable (fun x => f x • orb hst u x) (muU N) :=
    integrable_cont (f.continuous.smul (orb_cont hrep hst u))
  unfold T
  have hL := ((innerSL ℂ w).comp ((σ (h : Matrix (Fin N) (Fin N) ℂ)).comp S.subtypeL)).integral_comp_comm hint
  refine hL.symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hmul : σ ((h * x : UG N) : Matrix (Fin N) (Fin N) ℂ) = (σ h).comp (σ x) :=
    hrep.1.2 _ (memK h) _ (memK x)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Submodule.subtypeL_apply, orb,
    Submodule.coe_smul, map_smul, inner_smul_right, hmul, smul_eq_mul]
  try rfl

lemma isPositiveDefinite_matrix_coefficient_of_mem_algA [FiniteDimensional ℂ S] (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S)
    {f : C(UG N, ℂ)} (hf : f ∈ algA N) (u : S) (w : H) :
    IsPD (fun h : UG N => ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ) := by
  obtain ⟨ι, _, a, b, ha, hb, hab⟩ := sep_of_mem hf
  have hcont : Continuous (fun y : UG N => ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ) :=
    continuous_const.inner (continuous_subtype_val.comp (orb_cont hrep hst u))
  have hfun : ∀ h : UG N, ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ = ∑ i, a i h *
      ∫ y, b i y * ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ ∂(muU N) := by
    intro h
    rw [inner_sigma_T_eq_integral_mul_inner hrep hst f u w h]
    have hsh := integral_mul_left_eq_self (μ := muU N)
      (fun y => f (h⁻¹ * y) * ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ) h
    simp only [inv_mul_cancel_left] at hsh
    rw [hsh]
    simp_rw [hab h, Finset.sum_mul]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    · intro i _
      exact integrable_cont ((continuous_const.mul (hb i)).mul hcont)
  have e : (fun h : UG N => ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ) = fun h => ∑ i, a i h *
      ∫ y, b i y * ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ ∂(muU N) := funext hfun
  rw [e]
  exact IsPD.sum _ fun i _ => (ha i).mul (IsPD.const _)


variable (σ S) in
def Ugood : Submodule ℂ S where
  carrier := {u | ∀ w : H, IsPD (fun h : UG N => ⟪w, σ h (u : H)⟫_ℂ)}
  add_mem' := by
    intro u v hu hv w
    simpa [map_add (f := _), inner_add_right] using (hu w).add (hv w)
  zero_mem' := by
    intro w
    simpa using IsPD.const (N := N) 0
  smul_mem' := by
    intro c u hu w
    simpa [map_smul, inner_smul_right] using (IsPD.const c).mul (hu w)

theorem Ugood_eq_top (hrep : IsURepOn (Kset (allPos N)) σ) (hfin : FiniteDimensional ℂ S)
    (hst : IsKStableOn (allPos N) σ S) : Ugood (σ := σ) (S := S) = ⊤ := by
  haveI := hfin
  by_contra hne
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  let φC : S →L[ℂ] ℂ := LinearMap.toContinuousLinearMap φ
  apply hφ0
  ext u
  let g : UG N → ℂ := fun x => φC (orb hst u x)
  have hg : Continuous g := φC.continuous.comp (orb_cont hrep hst u)
  have hA : ∀ f ∈ algA N, ∫ x, f x * g x ∂(muU N) = 0 := by
    intro f hf
    have hmem : T hst f u ∈ Ugood (σ := σ) (S := S) :=
      fun w => isPositiveDefinite_matrix_coefficient_of_mem_algA hrep hst hf u w
    have h0 : φ (T hst f u) = 0 := LinearMap.mem_ker.mp (hle hmem)
    have hint : Integrable (fun x => f x • orb hst u x) (muU N) :=
      integrable_cont (f.continuous.smul (orb_cont hrep hst u))
    have hc := φC.integral_comp_comm hint
    rw [← h0]
    refine Eq.trans ?_ hc
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [g, φC, map_smul, smul_eq_mul]
  have hall : ∀ F : C(UG N, ℂ), ∫ x, F x * g x ∂(muU N) = 0 := by
    intro F
    have hM0 : 0 ≤ ∫ x, ‖g x‖ ∂(muU N) := integral_nonneg fun x => norm_nonneg _
    have hbound : ∀ ε > 0, ‖∫ x, F x * g x ∂(muU N)‖ ≤ ε * ∫ x, ‖g x‖ ∂(muU N) := by
      intro ε hε
      obtain ⟨f, hf, hfF⟩ := algA_dense N F hε
      have hsplit : ∫ x, F x * g x ∂(muU N) = ∫ x, (F - f) x * g x ∂(muU N) := by
        have h1 : ∫ x, (F - f) x * g x ∂(muU N) =
            ∫ x, F x * g x ∂(muU N) - ∫ x, f x * g x ∂(muU N) := by
          have hi1 : Integrable (fun x => F x * g x) (muU N) := integrable_cont (F.continuous.mul hg)
          have hi2 : Integrable (fun x => f x * g x) (muU N) := integrable_cont (f.continuous.mul hg)
          rw [← integral_sub hi1 hi2]
          congr 1
          funext x
          simp [sub_mul]
        rw [h1, hA f hf, sub_zero]
      rw [hsplit]
      calc ‖∫ x, (F - f) x * g x ∂(muU N)‖ ≤ ∫ x, ‖(F - f) x * g x‖ ∂(muU N) :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, ε * ‖g x‖ ∂(muU N) := by
          refine integral_mono (integrable_cont (((F - f).continuous.mul hg).norm))
            (integrable_cont (continuous_const.mul hg.norm)) fun x => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right ((ContinuousMap.norm_coe_le_norm (F - f) x).trans hfF.le)
            (norm_nonneg _)
        _ = ε * ∫ x, ‖g x‖ ∂(muU N) := integral_const_mul _ _
    by_contra hne0
    have hpos : 0 < ‖∫ x, F x * g x ∂(muU N)‖ := norm_pos_iff.mpr hne0
    set I := ‖∫ x, F x * g x ∂(muU N)‖
    set M := ∫ x, ‖g x‖ ∂(muU N)
    have h3 := hbound (I / (M + 1)) (div_pos hpos (by linarith))
    have hlt : I / (M + 1) * M < I := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hF := hall ⟨fun x => star (g x), continuous_star.comp hg⟩
  have hcn : Continuous fun x => Complex.normSq (g x) := Complex.continuous_normSq.comp hg
  have hF' : ∫ x, Complex.normSq (g x) ∂(muU N) = 0 := by
    have h4 : ∫ x, ((Complex.normSq (g x) : ℝ) : ℂ) ∂(muU N) = 0 := by
      rw [← hF]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact Complex.normSq_eq_conj_mul_self
    rw [integral_complex_ofReal] at h4
    exact_mod_cast h4
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (g x))
    (integrable_cont hcn)).mp hF'
  have heq : (fun x => Complex.normSq (g x)) = fun _ => (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq (muU N) hcn continuous_const).mp hae
  have h1 : Complex.normSq (g 1) = 0 := congrFun heq 1
  rw [Complex.normSq_eq_zero] at h1
  have horb : orb hst u 1 = u := by
    apply Subtype.ext
    simp [orb, hrep.1.1]
  simp only [g, horb] at h1
  simpa [φC] using h1

end

theorem polyCoef : PI.PolyCoef := by
  intro N H _ _ σ S hrep hfin hst v hv w
  have hgood : (⟨v, hv⟩ : S) ∈ Ugood (σ := σ) (S := S) := by
    rw [Ugood_eq_top hrep hfin hst]
    trivial
  obtain ⟨k, P, hP⟩ := hgood w
  refine ⟨k, P, fun g hg => ?_⟩
  exact hP ⟨g, (mem_Kset_iff g).mp hg⟩

end PI.UnitaryGroupMassFormula.PolyCoef
end
end

theorem polynomial_coefficients : PI.PolyCoef := PI.UnitaryGroupMassFormula.PolyCoef.polyCoef
