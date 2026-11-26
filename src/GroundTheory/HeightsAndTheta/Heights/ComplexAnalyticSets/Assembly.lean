module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PClosedPointChartField
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeRadialIntegral
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLeadBlockGaussTail
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreeGeoNum
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjChowNonzero
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjSecDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjSecDomain
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartFreeParAlgIndep
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PEmultiplicityOrd
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartFinite
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartIncOrd
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartResidueDegree
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PDehomogOrd
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBundleRadicalAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffBoundaryBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteFibreCentredEquation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreSectionsCovering
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGradDensSheetBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalGraphProjectionMass
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedCoverCycles
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJacobianRankGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolySublevel
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatLocalRegularElement
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermCompletionEquiv
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotientMinimalPrimeAddOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeChartGram
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConePolar

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric

open MvPolynomial Matrix

noncomputable section

def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ := fun ij => A ij.1 ij.2

def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  bind₁ (fun ij : Fin d × Fin n => ∑ l, C (F (s ij.1) l) * X (l, ij.2)) p

theorem eval_rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p := by
  change eval₂Hom (RingHom.id ℂ) (entries U) (bind₁ _ p) = eval₂Hom (RingHom.id ℂ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  simp [entries, Matrix.mul_apply]

theorem exists_rows_eq {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by
  refine ⟨star F * Matrix.of (Function.extend s (fun i => A i) 0), ?_⟩
  rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hF, Matrix.one_mul]
  ext i j
  simp [hs.extend_apply]

theorem rowsPoly_ne_zero {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]

theorem proof (hO : FiniteProjectionsContainOpen.Statement) (hU : UnitaryZariskiDense.Statement) :
    FiniteProjectionsGeneric.Statement := by
  classical
  intro n d J hJ hd
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hsub⟩ := hO n d J hJ hd
  have hA₀' := hA₀
  rw [hS] at hA₀'
  obtain ⟨p, hpS, hp⟩ := hA₀'
  have good : ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (entries A) p ≠ 0 → IsFiniteProjection J A :=
    fun A hA => hsub (by rw [hS]; exact ⟨p, hpS, hA⟩)
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  refine ⟨⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hsub⟩, fun D hD hcl => ?_, fun m F => ?_⟩
  · obtain ⟨U, hUu, hUp⟩ := hU n (rowsPoly 1 (Fin.castLE hdn) p)
      (rowsPoly_ne_zero (one_mem _) (Fin.castLE_injective hdn) hp)
    have hUp' : eval (entries (U.submatrix (Fin.castLE hdn) id)) p ≠ 0 := by
      have := eval_rowsPoly 1 (Fin.castLE hdn) p U
      rw [Matrix.one_mul] at this
      exact this ▸ hUp
    have hAo : U.submatrix (Fin.castLE hdn) id ∈ orthoRows d n := by
      show _ * _ = _
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hUu,
        submatrix_one _ (Fin.castLE_injective hdn)]
    have hopen : IsOpen {B : Matrix (Fin d) (Fin n) ℂ | eval (entries B) p ≠ 0} :=
      isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp
        (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)) continuous_const
    obtain ⟨B, hBp, hBD⟩ := mem_closure_iff.mp (hcl hAo) _ hopen hUp'
    exact ⟨B, hBD, good B hBp⟩
  · have hQ : (∏ ks : Fin m × (Fin d ↪ Fin n), rowsPoly (F ks.1 : Matrix (Fin n) (Fin n) ℂ) ks.2 p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ks _ => rowsPoly_ne_zero (F ks.1).2 ks.2.injective hp
    obtain ⟨U, hUu, hUQ⟩ := hU n _ hQ
    refine ⟨U, hUu, fun k s => good _ ?_⟩
    rw [map_prod] at hUQ
    have := Finset.prod_ne_zero_iff.mp hUQ (k, s) (Finset.mem_univ _)
    change eval (entries U) (rowsPoly _ _ p) ≠ 0 at this
    rwa [eval_rowsPoly] at this

end

end GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteCoverPuncturedPolydisc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Complex
open scoped Real

noncomputable section

namespace FiniteCoverPuncturedPolydisc

variable {e : ℕ}

def strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) : Set (Fin (e + 1) → ℂ) :=
  {u | (u 0).re < Real.log ρ ∧ ∀ i, i ≠ 0 → dist (u i) (c i) < ρ}

theorem convex_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) : Convex ℝ (strip c ρ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, fun i hi => ?_⟩
  · have := convex_halfSpace_re_lt (r := Real.log ρ) hx.1 hy.1 ha hb hab
    simpa using this
  · have := convex_ball (c i) ρ (hx.2 i hi) (hy.2 i hi) ha hb hab
    simpa [Metric.mem_ball] using this

theorem isOpen_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) : IsOpen (strip c ρ) := by
  have h1 : IsOpen {u : Fin (e + 1) → ℂ | (u 0).re < Real.log ρ} :=
    isOpen_lt (continuous_re.comp (continuous_apply 0)) continuous_const
  have h2 : IsOpen {u : Fin (e + 1) → ℂ | ∀ i, i ≠ 0 → dist (u i) (c i) < ρ} := by
    have : {u : Fin (e + 1) → ℂ | ∀ i, i ≠ 0 → dist (u i) (c i) < ρ} =
        ⋂ i ∈ ({0}ᶜ : Finset (Fin (e + 1))), {u | dist (u i) (c i) < ρ} := by
      ext u; simp
    rw [this]
    exact isOpen_biInter_finset fun i _ =>
      isOpen_lt ((continuous_apply i).dist continuous_const) continuous_const
  exact h1.inter h2

theorem base_mem_strip (c : Fin (e + 1) → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Function.update c 0 ((Real.log ρ - 1 : ℝ) : ℂ) ∈ strip c ρ := by
  refine ⟨by simp, fun i hi => ?_⟩
  simp [Function.update_of_ne hi, hρ]

instance simplyConnected_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) [Fact (0 < ρ)] :
    SimplyConnectedSpace (strip c ρ) := by
  have := (convex_strip c ρ).contractibleSpace ⟨_, base_mem_strip c (Fact.out : 0 < ρ)⟩
  infer_instance

instance locPathConnected_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) :
    LocallyPathConnectedSpace (strip c ρ) :=
  (isOpen_strip c ρ).locallyPathConnectedSpace

def shift (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k : ℤ) (u : strip c ρ) : strip c ρ :=
  ⟨Function.update u.1 0 (u.1 0 + k * (2 * π * I)), by
    refine ⟨by simpa using u.2.1, fun i hi => ?_⟩
    rw [Function.update_of_ne hi]
    exact u.2.2 i hi⟩

theorem shift_val (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k : ℤ) (u : strip c ρ) :
    (shift c ρ k u).1 = Function.update u.1 0 (u.1 0 + k * (2 * π * I)) := rfl

theorem continuous_shift (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k : ℤ) : Continuous (shift c ρ k) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.update 0
    (((continuous_apply 0).comp continuous_subtype_val).add continuous_const)

theorem shift_shift (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k l : ℤ) (u : strip c ρ) :
    shift c ρ k (shift c ρ l u) = shift c ρ (k + l) u := by
  apply Subtype.ext
  simp only [shift_val, Function.update_self, Function.update_idem]
  congr 1
  push_cast; ring

theorem shift_zero (c : Fin (e + 1) → ℂ) (ρ : ℝ) (u : strip c ρ) : shift c ρ 0 u = u := by
  apply Subtype.ext
  simp [shift_val]

variable {c : Fin (e + 1) → ℂ} {r : ℝ}

theorem expMap_mem (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (u : strip c ρ) :
    Function.update u.1 0 (exp (u.1 0)) ∈ Metric.ball c r ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0} := by
  refine ⟨?_, by simp [exp_ne_zero]⟩
  rw [Metric.mem_ball, dist_pi_lt_iff (hρ.trans_le hρr)]
  intro i
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [Function.update_self, hc, dist_zero_right, norm_exp]
    calc Real.exp (u.1 0).re < Real.exp (Real.log ρ) := Real.exp_lt_exp.2 u.2.1
      _ = ρ := Real.exp_log hρ
      _ ≤ r := hρr
  · rw [Function.update_of_ne hi]
    exact (u.2.2 i hi).trans_le hρr

def expMap (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    C(strip c ρ, ↥(Metric.ball c r ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})) where
  toFun u := ⟨Function.update u.1 0 (exp (u.1 0)), expMap_mem hc hρ hρr u⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.update 0 (((continuous_apply 0).comp continuous_subtype_val).cexp)

theorem expMap_val (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (u : strip c ρ) :
    ((expMap hc hρ hρr u : _) : Fin (e + 1) → ℂ) = Function.update u.1 0 (exp (u.1 0)) := rfl

theorem expMap_shift (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (k : ℤ) (u : strip c ρ) :
    expMap hc hρ hρr (shift c ρ k u) = expMap hc hρ hρr u := by
  apply Subtype.ext
  rw [expMap_val, expMap_val, shift_val]
  simp only [Function.update_self, Function.update_idem, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

theorem mem_strip_of_exp (hc : c 0 = 0) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {t : Fin (e + 1) → ℂ}
    (ht : t ∈ Metric.ball c ρ) {w : ℂ} (hw : exp w = t 0) {k : ℕ} (hk : 1 ≤ k) :
    Function.update t 0 (k * w) ∈ strip c ρ := by
  have ht0 : t 0 ≠ 0 := hw ▸ exp_ne_zero w
  have hnorm : ‖t 0‖ < ρ := by
    have := (dist_le_pi_dist t c 0).trans_lt ht
    simpa [hc] using this
  have hre : w.re = Real.log ‖t 0‖ := by rw [← hw, norm_exp, Real.log_exp]
  have hlog : Real.log ‖t 0‖ < Real.log ρ := Real.log_lt_log (norm_pos_iff.2 ht0) hnorm
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [Function.update_self, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, hre]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hk') (hlog.trans_le hlogρ).le]
  · rw [Function.update_of_ne hi]
    exact (dist_le_pi_dist t c i).trans_lt ht

end FiniteCoverPuncturedPolydisc


open FiniteCoverPuncturedPolydisc in
theorem FiniteCoverPuncturedPolydisc.proof : FiniteCoverPuncturedPolydisc.Statement := by
  intro e N c r Y _ p hr hc hcov hfib
  classical
  obtain ⟨ρ, hρ0, hρr, hρ1⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ρ ≤ 1 :=
    ⟨min r 1, lt_min hr one_pos, min_le_left _ _, min_le_right _ _⟩
  have : Fact (0 < ρ) := ⟨hρ0⟩
  let E := expMap hc hρ0 hρr
  let u₀ : strip c ρ := ⟨_, base_mem_strip c hρ0⟩

  have hlift : ∀ (a : strip c ρ) (y : Y), p y = E a →
      ∃ G : C(strip c ρ, Y), G a = y ∧ p ∘ G = E :=
    fun a y h => (hcov.existsUnique_continuousMap_lifts E a y h).exists
  have huniq : ∀ G₁ G₂ : C(strip c ρ, Y), p ∘ G₁ = E → p ∘ G₂ = E → ∀ a, G₁ a = G₂ a → G₁ = G₂ :=
    fun G₁ G₂ h1 h2 a ha => ContinuousMap.ext
      (congrFun (hcov.eq_of_comp_eq G₁.continuous G₂.continuous (h1.trans h2.symm) a ha))

  let F : Set Y := p ⁻¹' {E u₀}
  have hFfin : F.Finite := Set.finite_of_encard_eq_coe (hfib (E u₀))
  have : Finite F := hFfin.to_subtype
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Nat.card F = N := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hfib]
    simp
  let L : F → C(strip c ρ, Y) := fun y => Classical.choose (hlift u₀ y.1 y.2)
  have hL0 : ∀ y : F, L y u₀ = y.1 := fun y => (Classical.choose_spec (hlift u₀ y.1 y.2)).1
  have hLp : ∀ y : F, p ∘ L y = E := fun y => (Classical.choose_spec (hlift u₀ y.1 y.2)).2
  have hLp' : ∀ y : F, ∀ a, p (L y a) = E a := fun y a => congrFun (hLp y) a
  have hLinj : ∀ y y' : F, ∀ a, L y a = L y' a → y = y' := by
    intro y y' a h
    have := huniq (L y) (L y') (hLp y) (hLp y') a h
    apply Subtype.ext
    rw [← hL0 y, ← hL0 y', this]
  have hfibre : ∀ a (y : Y), p y = E a → ∃ y' : F, L y' a = y := by
    intro a y h
    obtain ⟨G, hGa, hGp⟩ := hlift a y h
    have hG0 : G u₀ ∈ F := by
      show p (G u₀) ∈ ({E u₀} : Set _)
      rw [← Function.comp_apply (f := p), hGp]
      rfl
    refine ⟨⟨G u₀, hG0⟩, ?_⟩
    have := huniq G (L ⟨G u₀, hG0⟩) hGp (hLp _) u₀ (hL0 ⟨G u₀, hG0⟩).symm
    rw [← this, hGa]
  have hEshift : ∀ k a, E (shift c ρ k a) = E a := expMap_shift hc hρ0 hρr

  have hs_mem : ∀ y : F, L y (shift c ρ 1 u₀) ∈ F := by
    intro y
    show p _ ∈ ({E u₀} : Set _)
    rw [hLp', hEshift]
    rfl
  let s : F → F := fun y => ⟨_, hs_mem y⟩
  have hLs : ∀ y : F, ∀ a, L y (shift c ρ 1 a) = L (s y) a := by
    intro y a
    have := huniq ((L y).comp ⟨shift c ρ 1, continuous_shift c ρ 1⟩) (L (s y))
      (by funext a; simp [hLp', hEshift]) (hLp _) u₀ (by rw [hL0]; rfl)
    exact DFunLike.congr_fun this a
  have hs_inj : Function.Injective s := by
    intro y y' h
    apply hLinj y y' u₀
    have e1 : shift c ρ 1 (shift c ρ (-1) u₀) = u₀ := by
      rw [shift_shift]
      simp [shift_zero]
    rw [← e1, hLs, hLs, h]
  let σ : Equiv.Perm F := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hs_inj)
  have hσ : ∀ y, σ y = s y := fun y => rfl
  have hLσ : ∀ k : ℤ, ∀ y : F, ∀ a, L y (shift c ρ k a) = L ((σ ^ k) y) a := by
    intro k
    induction k using Int.induction_on with
    | zero => intro y a; simp [shift_zero]
    | succ k ih =>
      intro y a
      conv_lhs => rw [show ((k : ℤ) + 1) = 1 + k by ring, ← shift_shift c ρ 1 k]
      rw [hLs, ih, zpow_add_one, Equiv.Perm.mul_apply, hσ]
    | pred k ih =>
      intro y a
      have hy : y = s (σ⁻¹ y) := by rw [← hσ]; simp
      conv_lhs => rw [hy]
      rw [← hLs, shift_shift, show (1 : ℤ) + (-↑k - 1) = -↑k by ring, ih, zpow_sub_one,
        Equiv.Perm.mul_apply]

  let Q := MulAction.orbitRel.Quotient (Subgroup.zpowers σ) F
  letI : Fintype Q := Fintype.ofFinite Q
  let m := Nat.card Q
  let eQ : Fin m ≃ Q := (Finite.equivFin Q).symm
  let rep : Fin m → F := fun b => (eQ b).out
  let ord : Fin m → ℕ := fun b => Function.minimalPeriod (σ • ·) (rep b)
  have hper : ∀ b (k : ℤ), (σ ^ k) (rep b) = rep b ↔ (ord b : ℤ) ∣ k := by
    intro b k
    rw [← Equiv.Perm.smul_def]
    exact MulAction.zpow_smul_eq_iff_minimalPeriod_dvd
  have hord : ∀ b, 1 ≤ ord b := by
    intro b
    have : Finite (MulAction.orbit (Subgroup.zpowers σ) (rep b)) := Subtype.finite
    exact Nat.one_le_iff_ne_zero.2 (NeZero.ne (Function.minimalPeriod (σ • ·) (rep b)))
  have hsame : ∀ b b' (k : ℤ), rep b = (σ ^ k) (rep b') → b = b' := by
    intro b b' k h
    apply eQ.injective
    rw [← Quotient.out_eq (eQ b), ← Quotient.out_eq (eQ b')]
    apply Quotient.sound
    show MulAction.orbitRel _ _ (rep b) (rep b')
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨σ ^ k, Subgroup.zpow_mem_zpowers σ k⟩, h.symm⟩
  have hrep : ∀ y : F, ∃ b, ∃ k : ℤ, y = (σ ^ k) (rep b) := by
    intro y
    refine ⟨eQ.symm ⟦y⟧, ?_⟩
    have h1 : rep (eQ.symm ⟦y⟧) = (⟦y⟧ : Q).out := by simp [rep]
    have h2 := Quotient.mk_out (s := MulAction.orbitRel (Subgroup.zpowers σ) F) y
    have h3 : (⟦y⟧ : Q).out ∈ MulAction.orbit (Subgroup.zpowers σ) y := by
      rw [← MulAction.orbitRel_apply]; exact h2
    obtain ⟨⟨g, hg⟩, hgy⟩ := MulAction.mem_orbit_iff.1 h3
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨-j, ?_⟩
    rw [h1, ← hgy]
    simp [zpow_neg, Equiv.Perm.smul_def]
  have hsum : ∑ b, ord b = N := by
    rw [← hcardF]
    have h1 : ∑ b, ord b = ∑ q : Q, Function.minimalPeriod (σ • ·) q.out :=
      Equiv.sum_comp eQ (fun q => Function.minimalPeriod (σ • ·) q.out)
    have h2 : ∀ q : Q, Function.minimalPeriod (σ • ·) q.out =
        Nat.card (MulAction.orbit (Subgroup.zpowers σ) q.out) := by
      intro q
      rw [MulAction.minimalPeriod_eq_card, Nat.card_eq_fintype_card]
    rw [h1, Finset.sum_congr rfl (fun q _ => h2 q),
      Nat.card_congr (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers σ) F), Nat.card_sigma]

  have hpt : ∀ b (t : ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})) (w : ℂ), exp w = t.1 0 →
      Function.update t.1 0 (ord b * w) ∈ strip c ρ :=
    fun b t w hw => mem_strip_of_exp hc hρ0 hρ1 t.2.1 hw (hord b)
  let ψ : Fin m → ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}) → Y :=
    fun b t => L (rep b) ⟨_, hpt b t (log (t.1 0)) (exp_log t.2.2)⟩
  have hψw : ∀ b t w (hw : exp w = t.1 0), ψ b t = L (rep b) ⟨_, hpt b t w hw⟩ := by
    intro b t w hw
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 (hw.trans (exp_log t.2.2).symm)
    have hsh : (⟨_, hpt b t w hw⟩ : strip c ρ) =
        shift c ρ (ord b * n) ⟨_, hpt b t (log (t.1 0)) (exp_log t.2.2)⟩ := by
      apply Subtype.ext
      simp only [shift_val, Function.update_self, Function.update_idem, hn]
      congr 1
      push_cast
      ring
    rw [hsh, hLσ, (hper b _).2 (dvd_mul_right _ _)]
  have hψcont : ∀ b, Continuous (ψ b) := by
    intro b
    rw [continuous_iff_continuousAt]
    intro t₁
    have hz : t₁.1 0 ≠ 0 := t₁.2.2
    have hw : ∀ t : ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}),
        exp (log (t₁.1 0) + log (t.1 0 / t₁.1 0)) = t.1 0 := by
      intro t
      rw [exp_add, exp_log hz, exp_log (div_ne_zero t.2.2 hz)]
      field_simp
    have heq : ψ b = fun t => L (rep b) ⟨_, hpt b t _ (hw t)⟩ := funext fun t => hψw b t _ (hw t)
    rw [heq]
    apply (L (rep b)).continuous.continuousAt.comp
    rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
    apply continuousAt_subtype_val.update 0
    apply continuousAt_const.mul
    apply continuousAt_const.add
    apply ContinuousAt.clog
    · exact (((continuous_apply 0).comp continuous_subtype_val).div_const _).continuousAt
    · simp [div_self hz]
  have hpψ : ∀ b t, ((p (ψ b t) : Fin (e + 1) → ℂ)) = Function.update t.1 0 (t.1 0 ^ ord b) := by
    intro b t
    show ((p (L (rep b) _) : Fin (e + 1) → ℂ)) = _
    rw [hLp', expMap_val]
    simp only [Function.update_self, Function.update_idem, exp_nat_mul, exp_log t.2.2]
  have hrest : ∀ b b' t t', ψ b t = ψ b' t' → (∀ i, i ≠ 0 → t.1 i = t'.1 i) ∧
      t.1 0 ^ ord b = t'.1 0 ^ ord b' := by
    intro b b' t t' h
    have hp := congrArg (fun y => ((p y : Fin (e + 1) → ℂ))) h
    simp only [hpψ] at hp
    refine ⟨fun i hi => ?_, by simpa using congrFun hp 0⟩
    have := congrFun hp i
    simpa [Function.update_of_ne hi] using this

  have hmeet : ∀ b b' t t', ψ b t = ψ b' t' → ∃ n : ℤ,
      (ord b' : ℂ) * log (t'.1 0) = ord b * log (t.1 0) + n * (2 * π * I) ∧
      rep b = (σ ^ n) (rep b') := by
    intro b b' t t' h
    obtain ⟨hr', h0⟩ := hrest b b' t t' h
    have hexp : exp (ord b' * log (t'.1 0)) = exp (ord b * log (t.1 0)) := by
      rw [exp_nat_mul, exp_nat_mul, exp_log t.2.2, exp_log t'.2.2, h0]
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hexp
    refine ⟨n, hn, ?_⟩
    have hsh : (⟨_, hpt b' t' (log (t'.1 0)) (exp_log t'.2.2)⟩ : strip c ρ) =
        shift c ρ n ⟨_, hpt b t (log (t.1 0)) (exp_log t.2.2)⟩ := by
      apply Subtype.ext
      funext i
      rcases eq_or_ne i 0 with rfl | hi
      · simp [shift_val, hn]
      · simp [shift_val, Function.update_of_ne hi, hr' i hi]
    have h2 : ψ b' t' = L ((σ ^ n) (rep b')) ⟨_, hpt b t _ (exp_log t.2.2)⟩ := by
      show L (rep b') _ = _
      rw [hsh, hLσ]
    exact hLinj (rep b) ((σ ^ n) (rep b')) _ (h.trans h2)
  have hψinj : ∀ b, Function.Injective (ψ b) := by
    intro b t t' h
    obtain ⟨hr', -⟩ := hrest b b t t' h
    obtain ⟨n, hn, h3⟩ := hmeet b b t t' h
    obtain ⟨j, hj⟩ := (hper b n).1 h3.symm
    have hm0 : (ord b : ℂ) ≠ 0 := by
      have : ord b ≠ 0 := Nat.one_le_iff_ne_zero.1 (hord b)
      exact_mod_cast this
    have hlog : log (t'.1 0) = log (t.1 0) + j * (2 * π * I) := by
      apply mul_left_cancel₀ hm0
      rw [hn, hj]
      push_cast
      ring
    apply Subtype.ext
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · rw [← exp_log t.2.2, ← exp_log t'.2.2, hlog, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
    · exact hr' i hi
  have hψdisj : ∀ b b', b ≠ b' → ∀ t t', ψ b t ≠ ψ b' t' := by
    intro b b' hbb t t' h
    obtain ⟨n, -, h3⟩ := hmeet b b' t t' h
    exact hbb (hsame b b' n h3)
  have hcover : ∀ y, dist ((p y : Fin (e + 1) → ℂ)) c < ρ ^ N → ∃ b t, ψ b t = y := by
    intro y hy
    have hs0 : (p y : Fin (e + 1) → ℂ) 0 ≠ 0 := (p y).2.2
    have hN : N ≠ 0 := by
      intro hN0
      have := hfib (p y)
      rw [hN0, Nat.cast_zero, Set.encard_eq_zero] at this
      exact (Set.eq_empty_iff_forall_notMem.1 this) y rfl
    have hρN : ρ ^ N ≤ ρ := pow_le_of_le_one hρ0.le hρ1 hN
    have hsball : (p y : Fin (e + 1) → ℂ) ∈ Metric.ball c ρ := Metric.mem_ball.2 (hy.trans_le hρN)
    let a : strip c ρ := ⟨_, mem_strip_of_exp hc hρ0 hρ1 hsball (exp_log hs0) le_rfl⟩
    have hEa : p y = E a := by
      apply Subtype.ext
      rw [expMap_val]
      simp [a, exp_log hs0]
    obtain ⟨y', hy'⟩ := hfibre a y hEa
    obtain ⟨b, k, hk⟩ := hrep y'
    have hm1 := hord b
    have hm0 : (ord b : ℂ) ≠ 0 := by
      have : ord b ≠ 0 := Nat.one_le_iff_ne_zero.1 hm1
      exact_mod_cast this
    let w : ℂ := (log ((p y : Fin (e + 1) → ℂ) 0) + k * (2 * π * I)) / ord b
    have hmw : (ord b : ℂ) * w = log ((p y : Fin (e + 1) → ℂ) 0) + k * (2 * π * I) := by
      simp only [w]
      field_simp
    let t : Fin (e + 1) → ℂ := Function.update (p y : Fin (e + 1) → ℂ) 0 (exp w)
    have hmN : ord b ≤ N :=
      hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    have ht : t ∈ Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0} := by
      refine ⟨?_, by simp [t, exp_ne_zero]⟩
      rw [Metric.mem_ball, dist_pi_lt_iff hρ0]
      intro i
      rcases eq_or_ne i 0 with rfl | hi
      · simp only [t, Function.update_self, hc, dist_zero_right, norm_exp]
        have hre : (ord b : ℝ) * w.re = Real.log ‖(p y : Fin (e + 1) → ℂ) 0‖ := by
          have := congrArg re hmw
          simpa [mul_re, log_re] using this
        have hsn : ‖(p y : Fin (e + 1) → ℂ) 0‖ < ρ ^ N := by
          simpa [hc] using (dist_le_pi_dist _ c 0).trans_lt hy
        have hl : Real.log ‖(p y : Fin (e + 1) → ℂ) 0‖ < N * Real.log ρ := by
          rw [← Real.log_pow]
          exact Real.log_lt_log (norm_pos_iff.2 hs0) hsn
        have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
        have hmpos : (0 : ℝ) < ord b := by exact_mod_cast hm1
        have hmN' : (ord b : ℝ) ≤ N := by exact_mod_cast hmN
        have hlt : w.re < Real.log ρ := by
          by_contra hcon
          replace hcon := not_lt.1 hcon
          nlinarith [mul_le_mul_of_nonpos_right hmN' hlogρ, mul_le_mul_of_nonneg_left hcon hmpos.le]
        calc Real.exp w.re < Real.exp (Real.log ρ) := Real.exp_lt_exp.2 hlt
          _ = ρ := Real.exp_log hρ0
      · simp only [t, Function.update_of_ne hi]
        exact ((dist_le_pi_dist _ c i).trans_lt hy).trans_le hρN
    refine ⟨b, ⟨t, ht⟩, ?_⟩
    have hwt : exp w = (⟨t, ht⟩ : ↥(Metric.ball c ρ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})).1 0 := by
      simp [t]
    rw [hψw b ⟨t, ht⟩ w hwt]
    have hsh : (⟨_, hpt b ⟨t, ht⟩ w hwt⟩ : strip c ρ) = shift c ρ k a := by
      apply Subtype.ext
      simp only [shift_val, a, t, Function.update_idem, Function.update_self, hmw, Nat.cast_one,
        one_mul]
    rw [hsh, hLσ, ← hk, hy']
  exact ⟨m, ord, ρ, ψ, hρ0, hρ1, hsum, hord, hψcont, hpψ, hψinj, hψdisj, hcover⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem AffineChartTrdeg.full : GroundTheory.Heights₂.Heights.AffineChartTrdeg.Statement :=
  GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof

theorem AreaGraphPiece.full : GroundTheory.Heights₂.Heights.AreaGraphPiece.Statement :=
  GroundTheory.Heights₂.Heights.AreaGraphPiece.proof

theorem AreaGraphPartition.full : GroundTheory.Heights₂.Heights.AreaGraphPartition.Statement :=
  GroundTheory.Heights₂.Heights.AreaGraphPartition.proof

theorem GraphJacContinuous.full : GroundTheory.Heights₂.Heights.GraphJacContinuous.Statement :=
  GroundTheory.Heights₂.Heights.GraphJacContinuous.proof

theorem AreaGraphBound.full : GroundTheory.Heights₂.Heights.AreaGraphBound.Statement :=
  GroundTheory.Heights₂.Heights.AreaGraphBound.proof GroundTheory.Heights₂.Heights.AreaGraphPiece.full GroundTheory.Heights₂.Heights.AreaGraphPartition.full GroundTheory.Heights₂.Heights.GraphJacContinuous.full

theorem AreaGraph.full : GroundTheory.Heights₂.Heights.AreaGraph.Statement :=
  GroundTheory.Heights₂.Heights.AreaGraph.proof GroundTheory.Heights₂.Heights.AreaGraphBound.full

theorem AreaMultiplicity.full : GroundTheory.Heights₂.Heights.AreaMultiplicity.Statement :=
  GroundTheory.Heights₂.Heights.AreaMultiplicity.proof

theorem ChartChoice.full : GroundTheory.Heights₂.Heights.ChartChoice.Statement :=
  GroundTheory.Heights₂.Heights.ChartChoice.proof GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full

theorem ChartDehomog.full : GroundTheory.Heights₂.Heights.ChartDehomog.Statement :=
  GroundTheory.Heights₂.Heights.ChartDehomog.proof

theorem ChartFinite.full : GroundTheory.Heights₂.Heights.ChartFinite.Statement :=
  GroundTheory.Heights₂.Heights.ChartFinite.proof

theorem ChartFirstGroupDvd.full : GroundTheory.Heights₂.Heights.ChartFirstGroupDvd.Statement :=
  GroundTheory.Heights₂.Heights.ChartFirstGroupDvd.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full

theorem IncIdealBelow.full : GroundTheory.Heights₂.Heights.IncIdealBelow.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealBelow.proof GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full

theorem ChartFirstGroupPrime.full : GroundTheory.Heights₂.Heights.ChartFirstGroupPrime.Statement :=
  GroundTheory.Heights₂.Heights.ChartFirstGroupPrime.proof GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.IncIdealBelow.full

theorem ChartHomogenise.full : GroundTheory.Heights₂.Heights.ChartHomogenise.Statement :=
  GroundTheory.Heights₂.Heights.ChartHomogenise.proof

theorem ChartIncDomain.full : GroundTheory.Heights₂.Heights.ChartIncDomain.Statement :=
  GroundTheory.Heights₂.Heights.ChartIncDomain.proof

theorem ChartIncOrd.full : GroundTheory.Heights₂.Heights.ChartIncOrd.Statement :=
  GroundTheory.Heights₂.Heights.ChartIncOrd.proof GroundTheory.Heights₂.Heights.OrdPolynomialLocalization.full

theorem ChartKernel.full : GroundTheory.Heights₂.Heights.ChartKernel.Statement :=
  GroundTheory.Heights₂.Heights.ChartKernel.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full GroundTheory.Heights₂.Heights.ChartIncDomain.full

theorem SpecFirstMemIncIdeal.full : GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.Statement :=
  GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.proof

theorem LengthFiniteAlgebra.full : GroundTheory.Heights₂.Heights.LengthFiniteAlgebra.Statement :=
  GroundTheory.Heights₂.Heights.LengthFiniteAlgebra.proof

theorem IncIdealDim.full : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.full

theorem ConeDimOfChowForm.full : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof GroundTheory.Heights₂.Heights.IncIdealDim.full GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem ComponentOfIncIdeal.full : GroundTheory.Heights₂.Heights.ComponentOfIncIdeal.Statement :=
  GroundTheory.Heights₂.Heights.ComponentOfIncIdeal.proof GroundTheory.Heights₂.Heights.IncIdealDim.full GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.ConeDimComponent.full

theorem ChartMaxIdeals.full : GroundTheory.Heights₂.Heights.ChartMaxIdeals.Statement :=
  GroundTheory.Heights₂.Heights.ChartMaxIdeals.proof GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ConeDimComponent.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartIncDomain.full GroundTheory.Heights₂.Heights.ChartKernel.full GroundTheory.Heights₂.Heights.ChartHomogenise.full GroundTheory.Heights₂.Heights.ChartDehomog.full GroundTheory.Heights₂.Heights.ComponentOfIncIdeal.full

theorem ChowFormExists.full : GroundTheory.Heights₂.Heights.ChowFormExists.Statement :=
  GroundTheory.Heights₂.Heights.ChowFormExists.proof GroundTheory.Heights₂.Heights.IncIdealDim.full GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem DehomogOrd.full : GroundTheory.Heights₂.Heights.DehomogOrd.Statement :=
  GroundTheory.Heights₂.Heights.DehomogOrd.proof GroundTheory.Heights₂.Heights.OrdPolynomialLocalization.full

theorem LocalMultOrd.full : GroundTheory.Heights₂.Heights.LocalMultOrd.Statement :=
  GroundTheory.Heights₂.Heights.LocalMultOrd.proof

theorem ChartLocalOrder.full : GroundTheory.Heights₂.Heights.ChartLocalOrder.Statement :=
  GroundTheory.Heights₂.Heights.ChartLocalOrder.proof GroundTheory.Heights₂.Heights.ChartIncDomain.full GroundTheory.Heights₂.Heights.ChartKernel.full GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ConeDimComponent.full GroundTheory.Heights₂.Heights.ChowFormExists.full GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.ChartIncOrd.full GroundTheory.Heights₂.Heights.DehomogOrd.full GroundTheory.Heights₂.Heights.LocalMultOrd.full

theorem ChartResidueDegree.full : GroundTheory.Heights₂.Heights.ChartResidueDegree.Statement :=
  GroundTheory.Heights₂.Heights.ChartResidueDegree.proof GroundTheory.Heights₂.Heights.ChowFormBirational.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartKernel.full GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ConeDimComponent.full GroundTheory.Heights₂.Heights.ChowFormExists.full GroundTheory.Heights₂.Heights.IncidenceGeneric.full GroundTheory.Heights₂.Heights.ChartLocalOrder.full

theorem ChartLength.full : GroundTheory.Heights₂.Heights.ChartLength.Statement :=
  GroundTheory.Heights₂.Heights.ChartLength.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.LengthFiniteAlgebra.full GroundTheory.Heights₂.Heights.ChartMaxIdeals.full GroundTheory.Heights₂.Heights.ChartLocalOrder.full GroundTheory.Heights₂.Heights.ChartResidueDegree.full

theorem ChartLocDomain.full : GroundTheory.Heights₂.Heights.ChartLocDomain.Statement :=
  GroundTheory.Heights₂.Heights.ChartLocDomain.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.ChartIncDomain.full GroundTheory.Heights₂.Heights.ChartKernel.full

theorem SheetComass.full : GroundTheory.Heights₂.Heights.SheetComass.Statement :=
  GroundTheory.Heights₂.Heights.SheetComass.proof

theorem SheetImageArea.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.SheetImageArea.Statement :=
  GroundTheory.Heights₂.Heights.SheetImageArea.proof hSheetImageAreaSet

theorem SheetAreaCompare.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.SheetAreaCompare.Statement :=
  GroundTheory.Heights₂.Heights.SheetAreaCompare.proof (GroundTheory.Heights₂.Heights.SheetImageArea.of_open hSheetImageAreaSet)

theorem ChartMassCompare.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.ChartMassCompare.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompare.proof GroundTheory.Heights₂.Heights.SheetComass.full (GroundTheory.Heights₂.Heights.SheetAreaCompare.of_open hSheetImageAreaSet)

theorem ComplexSets.ConeAvoidsFinite.full : GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof

theorem ComplexSets.FiniteProjHomInjective.full : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.proof

theorem ComplexSets.ConeAvoidsOpen.full : GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.proof

theorem ComplexSets.LeadIdealDim.full : GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.proof

theorem ComplexSets.LinearFormCut.full : GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.proof

theorem ComplexSets.HomogDimZeroPow.full : GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.proof

theorem ComplexSets.ConeAvoidsExists.full : GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.proof GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.full GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.full GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.full

theorem ComplexSets.FiniteProjectionsContainOpen.full : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.full GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.full GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.full GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.full

theorem ComplexSets.UnitaryZariskiDense.full : GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.proof

theorem ComplexSets.GenericProjectionFinite.full : GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.proof GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.full GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.full

theorem ComplexSets.FibreBound.full : GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof

theorem ComplexSets.PrimitiveElementFibres.full : GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof

theorem ComplexSets.DiscriminantCover.full : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.full

theorem NullSmaller.full : GroundTheory.Heights₂.Heights.NullSmaller.Statement :=
  GroundTheory.Heights₂.Heights.NullSmaller.proof

theorem FrameJacobianSum.full : GroundTheory.Heights₂.Heights.FrameJacobianSum.Statement :=
  GroundTheory.Heights₂.Heights.FrameJacobianSum.proof

theorem GraphAreaHolomorphic.full : GroundTheory.Heights₂.Heights.GraphAreaHolomorphic.Statement :=
  GroundTheory.Heights₂.Heights.GraphAreaHolomorphic.proof GroundTheory.Heights₂.Heights.AreaGraph.full

theorem ProjectionFormula.full : GroundTheory.Heights₂.Heights.ProjectionFormula.Statement :=
  GroundTheory.Heights₂.Heights.ProjectionFormula.proof GroundTheory.Heights₂.Heights.AreaMultiplicity.full GroundTheory.Heights₂.Heights.FrameJacobianSum.full GroundTheory.Heights₂.Heights.GraphAreaHolomorphic.full

theorem LocalGraphMass.full : GroundTheory.Heights₂.Heights.LocalGraphMass.Statement :=
  GroundTheory.Heights₂.Heights.LocalGraphMass.proof GroundTheory.Heights₂.Heights.ProjectionFormula.full

theorem MassFinite.full : GroundTheory.Heights₂.Heights.MassFinite.Statement :=
  GroundTheory.Heights₂.Heights.MassFinite.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.full GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.NullSmaller.full GroundTheory.Heights₂.Heights.LocalGraphMass.full

theorem ChartMassCompact.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.ChartMassCompact.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompact.proof (GroundTheory.Heights₂.Heights.ChartMassCompare.of_open hSheetImageAreaSet) GroundTheory.Heights₂.Heights.MassFinite.full

theorem LocalizationPrimeDVR.full : GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.Statement :=
  GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.proof

theorem NormFormEval.full : GroundTheory.Heights₂.Heights.NormFormEval.Statement :=
  GroundTheory.Heights₂.Heights.NormFormEval.proof

theorem NormFormEmbeddings.full : GroundTheory.Heights₂.Heights.NormFormEmbeddings.Statement :=
  GroundTheory.Heights₂.Heights.NormFormEmbeddings.proof GroundTheory.Heights₂.Heights.NormFormEval.full

theorem LinearFormPrime.full : GroundTheory.Heights₂.Heights.LinearFormPrime.Statement :=
  GroundTheory.Heights₂.Heights.LinearFormPrime.proof

theorem MapDvdDescent.full : GroundTheory.Heights₂.Heights.MapDvdDescent.Statement :=
  GroundTheory.Heights₂.Heights.MapDvdDescent.proof

theorem NormFormDvd.full : GroundTheory.Heights₂.Heights.NormFormDvd.Statement :=
  GroundTheory.Heights₂.Heights.NormFormDvd.proof GroundTheory.Heights₂.Heights.NormFormEmbeddings.full GroundTheory.Heights₂.Heights.LinearFormPrime.full GroundTheory.Heights₂.Heights.MapDvdDescent.full

theorem PrimeMapFractionRing.full : GroundTheory.Heights₂.Heights.PrimeMapFractionRing.Statement :=
  GroundTheory.Heights₂.Heights.PrimeMapFractionRing.proof

theorem NormOfDividedForm.full : GroundTheory.Heights₂.Heights.NormOfDividedForm.Statement :=
  GroundTheory.Heights₂.Heights.NormOfDividedForm.proof GroundTheory.Heights₂.Heights.NormFormEval.full GroundTheory.Heights₂.Heights.NormFormDvd.full GroundTheory.Heights₂.Heights.PrimeMapFractionRing.full

theorem ChartNorm.full : GroundTheory.Heights₂.Heights.ChartNorm.Statement :=
  GroundTheory.Heights₂.Heights.ChartNorm.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartLocDomain.full GroundTheory.Heights₂.Heights.ChartFirstGroupPrime.full GroundTheory.Heights₂.Heights.ChartFirstGroupDvd.full GroundTheory.Heights₂.Heights.NormOfDividedForm.full

theorem ChowFormDimLe.full : GroundTheory.Heights₂.Heights.ChowFormDimLe.Statement :=
  GroundTheory.Heights₂.Heights.ChowFormDimLe.proof

theorem SpecFirstNe.full : GroundTheory.Heights₂.Heights.SpecFirstNe.Statement :=
  GroundTheory.Heights₂.Heights.SpecFirstNe.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.ChartLocDomain.full GroundTheory.Heights₂.Heights.ChartNorm.full

theorem EmultiplicityOrd.full : GroundTheory.Heights₂.Heights.EmultiplicityOrd.Statement :=
  GroundTheory.Heights₂.Heights.EmultiplicityOrd.proof GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.full

theorem SectionOrder.full : GroundTheory.Heights₂.Heights.SectionOrder.Statement :=
  GroundTheory.Heights₂.Heights.SectionOrder.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.ChartChoice.full GroundTheory.Heights₂.Heights.SpecFirstNe.full GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.full GroundTheory.Heights₂.Heights.EmultiplicityOrd.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartLocDomain.full GroundTheory.Heights₂.Heights.ChartNorm.full GroundTheory.Heights₂.Heights.ChartLength.full GroundTheory.Heights₂.Heights.LengthQuotientDet.full

theorem ChowFormSection.full : GroundTheory.Heights₂.Heights.ChowFormSection.Statement :=
  GroundTheory.Heights₂.Heights.ChowFormSection.proof GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ConeDimComponent.full GroundTheory.Heights₂.Heights.ChowFormExists.full GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.SectionOrder.full

theorem ComplexSets.FiniteProjectionsGeneric.full : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric.proof GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.full GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.full

theorem IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof

theorem SheetOnlyNull.full : GroundTheory.Heights₂.Heights.SheetOnlyNull.Statement :=
  GroundTheory.Heights₂.Heights.SheetOnlyNull.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full

theorem PosPartLocal.full : GroundTheory.Heights₂.Heights.PosPartLocal.Statement :=
  GroundTheory.Heights₂.Heights.PosPartLocal.proof

theorem PosPartSplit.full : GroundTheory.Heights₂.Heights.PosPartSplit.Statement :=
  GroundTheory.Heights₂.Heights.PosPartSplit.proof

theorem PosPartIndep.full : GroundTheory.Heights₂.Heights.PosPartIndep.Statement :=
  GroundTheory.Heights₂.Heights.PosPartIndep.proof GroundTheory.Heights₂.Heights.SheetOnlyNull.full GroundTheory.Heights₂.Heights.PosPartLocal.full GroundTheory.Heights₂.Heights.PosPartSplit.full

theorem IntegralIndep.full : GroundTheory.Heights₂.Heights.IntegralIndep.Statement :=
  GroundTheory.Heights₂.Heights.IntegralIndep.proof GroundTheory.Heights₂.Heights.PosPartIndep.full

theorem StokesOffDiscriminant.full : GroundTheory.Heights₂.Heights.StokesOffDiscriminant.Statement :=
  GroundTheory.Heights₂.Heights.StokesOffDiscriminant.proof

theorem CutOffShape.full : GroundTheory.Heights₂.Heights.CutOffShape.Statement :=
  GroundTheory.Heights₂.Heights.CutOffShape.proof

theorem TubeFormCompare.full : GroundTheory.Heights₂.Heights.TubeFormCompare.Statement :=
  GroundTheory.Heights₂.Heights.TubeFormCompare.proof

theorem CutOffTube.of_open (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.CutOffTube.Statement :=
  GroundTheory.Heights₂.Heights.CutOffTube.proof GroundTheory.Heights₂.Heights.TubeFormCompare.full hTubeEuclMass

theorem HessCCompPluri.full : GroundTheory.Heights₂.Heights.HessCCompPluri.Statement :=
  GroundTheory.Heights₂.Heights.HessCCompPluri.proof

theorem LogLogCutHess.full : GroundTheory.Heights₂.Heights.LogLogCutHess.Statement :=
  GroundTheory.Heights₂.Heights.LogLogCutHess.proof GroundTheory.Heights₂.Heights.HessCCompPluri.full

theorem CutOffGradient.full : GroundTheory.Heights₂.Heights.CutOffGradient.Statement :=
  GroundTheory.Heights₂.Heights.CutOffGradient.proof GroundTheory.Heights₂.Heights.LogLogCutHess.full

theorem CutOff.of_open (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.CutOff.Statement :=
  GroundTheory.Heights₂.Heights.CutOff.proof GroundTheory.Heights₂.Heights.CutOffShape.full (GroundTheory.Heights₂.Heights.CutOffTube.of_open hTubeEuclMass) GroundTheory.Heights₂.Heights.CutOffGradient.full

theorem CutOffDominated.full : GroundTheory.Heights₂.Heights.CutOffDominated.Statement :=
  GroundTheory.Heights₂.Heights.CutOffDominated.proof

theorem MaDensLeibniz.full : GroundTheory.Heights₂.Heights.MaDensLeibniz.Statement :=
  GroundTheory.Heights₂.Heights.MaDensLeibniz.proof

theorem EnergyDensNonneg.full : GroundTheory.Heights₂.Heights.EnergyDensNonneg.Statement :=
  GroundTheory.Heights₂.Heights.EnergyDensNonneg.proof

theorem GradDensSheetBound.full : GroundTheory.Heights₂.Heights.GradDensSheetBound.Statement :=
  GroundTheory.Heights₂.Heights.GradDensSheetBound.proof

theorem CutOffBoundaryBound.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.CutOffBoundaryBound.Statement :=
  GroundTheory.Heights₂.Heights.CutOffBoundaryBound.proof (GroundTheory.Heights₂.Heights.ChartMassCompact.of_open hSheetImageAreaSet) GroundTheory.Heights₂.Heights.MaDensLeibniz.full GroundTheory.Heights₂.Heights.EnergyDensNonneg.full GroundTheory.Heights₂.Heights.GradDensSheetBound.full

theorem CutOffLimit.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.CutOffLimit.Statement :=
  GroundTheory.Heights₂.Heights.CutOffLimit.proof (GroundTheory.Heights₂.Heights.CutOff.of_open hTubeEuclMass) (GroundTheory.Heights₂.Heights.ChartMassCompact.of_open hSheetImageAreaSet) GroundTheory.Heights₂.Heights.CutOffDominated.full (GroundTheory.Heights₂.Heights.CutOffBoundaryBound.of_open hSheetImageAreaSet)

theorem StokesOnVariety.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.StokesOnVariety.Statement :=
  GroundTheory.Heights₂.Heights.StokesOnVariety.proof GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.StokesOffDiscriminant.full (GroundTheory.Heights₂.Heights.CutOffLimit.of_open hSheetImageAreaSet hTubeEuclMass)

theorem SheetSumMeasurable.full : GroundTheory.Heights₂.Heights.SheetSumMeasurable.Statement :=
  GroundTheory.Heights₂.Heights.SheetSumMeasurable.proof

theorem LocalGraphProjectionMass.full : GroundTheory.Heights₂.Heights.LocalGraphProjectionMass.Statement :=
  GroundTheory.Heights₂.Heights.LocalGraphProjectionMass.proof GroundTheory.Heights₂.Heights.ProjectionFormula.full

theorem VarietyProjectionMass.full : GroundTheory.Heights₂.Heights.VarietyProjectionMass.Statement :=
  GroundTheory.Heights₂.Heights.VarietyProjectionMass.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.LocalGraphProjectionMass.full

theorem IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.proof

theorem VarietySlabMeasure.full : GroundTheory.Heights₂.Heights.VarietySlabMeasure.Statement :=
  GroundTheory.Heights₂.Heights.VarietySlabMeasure.proof GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric.full GroundTheory.Heights₂.Heights.VarietyProjectionMass.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.full

theorem VarSlabMeasure.full : GroundTheory.Heights₂.Heights.VarSlabMeasure.Statement :=
  GroundTheory.Heights₂.Heights.VarSlabMeasure.proof GroundTheory.Heights₂.Heights.VarietySlabMeasure.full

theorem ConeSlabBound.full : GroundTheory.Heights₂.Heights.ConeSlabBound.Statement :=
  GroundTheory.Heights₂.Heights.ConeSlabBound.proof GroundTheory.Heights₂.Heights.VarietySlabMeasure.full

theorem ZeroLocusDimH.full : GroundTheory.Heights₂.Heights.ZeroLocusDimH.Statement :=
  GroundTheory.Heights₂.Heights.ZeroLocusDimH.proof

theorem ConeHyperplaneNull.full : GroundTheory.Heights₂.Heights.ConeHyperplaneNull.Statement :=
  GroundTheory.Heights₂.Heights.ConeHyperplaneNull.proof GroundTheory.Heights₂.Heights.ZeroLocusDimH.full GroundTheory.Heights₂.Heights.ChowFormDimLe.full

theorem ImplicitCurve.full : GroundTheory.Heights₂.Heights.ImplicitCurve.Statement :=
  GroundTheory.Heights₂.Heights.ImplicitCurve.proof

theorem SliceMatricesOpen.full : GroundTheory.Heights₂.Heights.SliceMatricesOpen.Statement :=
  GroundTheory.Heights₂.Heights.SliceMatricesOpen.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.FibreSectionsCovering.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreSectionsCovering.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreSectionsCovering.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full

theorem IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreSectionsCovering.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc.full

theorem IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full

theorem IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full

theorem ConeAreaFormula.of_open (hConeGraphCover : GroundTheory.Heights₂.Heights.ConeGraphCover.Statement) (hGraphAreaFibre : GroundTheory.Heights₂.Heights.GraphAreaFibre.Statement) :
    GroundTheory.Heights₂.Heights.ConeAreaFormula.Statement :=
  GroundTheory.Heights₂.Heights.ConeAreaFormula.proof hConeGraphCover hGraphAreaFibre

theorem ConeLocalMass.of_open (hConeFiniteFibreDim : GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.Statement) :
    GroundTheory.Heights₂.Heights.ConeLocalMass.Statement :=
  GroundTheory.Heights₂.Heights.ConeLocalMass.proof hConeFiniteFibreDim GroundTheory.Heights₂.Heights.MassFinite.full GroundTheory.Heights₂.Heights.NullSmaller.full

theorem ConeTangentAverage.of_open (hConeFiniteFibreDim : GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.Statement) (hConeJacMeasurable : GroundTheory.Heights₂.Heights.ConeJacMeasurable.Statement) (hConeTangentDim : GroundTheory.Heights₂.Heights.ConeTangentDim.Statement) (hTangentGaussInvariant : GroundTheory.Heights₂.Heights.TangentGaussInvariant.Statement) :
    GroundTheory.Heights₂.Heights.ConeTangentAverage.Statement :=
  GroundTheory.Heights₂.Heights.ConeTangentAverage.proof (GroundTheory.Heights₂.Heights.ConeLocalMass.of_open hConeFiniteFibreDim) hConeJacMeasurable hConeTangentDim hTangentGaussInvariant

theorem ConeRadialIntegral.full : GroundTheory.Heights₂.Heights.ConeRadialIntegral.Statement :=
  GroundTheory.Heights₂.Heights.ConeRadialIntegral.proof

theorem LeadPlaneJac.full : GroundTheory.Heights₂.Heights.LeadPlaneJac.Statement :=
  GroundTheory.Heights₂.Heights.LeadPlaneJac.proof

theorem LeadBlockGaussTail.full : GroundTheory.Heights₂.Heights.LeadBlockGaussTail.Statement :=
  GroundTheory.Heights₂.Heights.LeadBlockGaussTail.proof

theorem TangentGaussMoment.full : GroundTheory.Heights₂.Heights.TangentGaussMoment.Statement :=
  GroundTheory.Heights₂.Heights.TangentGaussMoment.proof GroundTheory.Heights₂.Heights.LeadPlaneJac.full GroundTheory.Heights₂.Heights.LeadBlockGaussTail.full

theorem ConeFibreAverage.of_open (hConeFiniteFibreDim : GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.Statement) (hConeGraphCover : GroundTheory.Heights₂.Heights.ConeGraphCover.Statement) (hConeJacMeasurable : GroundTheory.Heights₂.Heights.ConeJacMeasurable.Statement) (hConeTangentDim : GroundTheory.Heights₂.Heights.ConeTangentDim.Statement) (hGraphAreaFibre : GroundTheory.Heights₂.Heights.GraphAreaFibre.Statement) (hTangentGaussInvariant : GroundTheory.Heights₂.Heights.TangentGaussInvariant.Statement) :
    GroundTheory.Heights₂.Heights.ConeFibreAverage.Statement :=
  GroundTheory.Heights₂.Heights.ConeFibreAverage.proof (GroundTheory.Heights₂.Heights.ConeAreaFormula.of_open hConeGraphCover hGraphAreaFibre) (GroundTheory.Heights₂.Heights.ConeTangentAverage.of_open hConeFiniteFibreDim hConeJacMeasurable hConeTangentDim hTangentGaussInvariant) GroundTheory.Heights₂.Heights.ConeRadialIntegral.full GroundTheory.Heights₂.Heights.TangentGaussMoment.full

theorem ProjSecDegree.full : GroundTheory.Heights₂.Heights.ProjSecDegree.Statement :=
  GroundTheory.Heights₂.Heights.ProjSecDegree.proof

theorem ProjSecDomain.full : GroundTheory.Heights₂.Heights.ProjSecDomain.Statement :=
  GroundTheory.Heights₂.Heights.ProjSecDomain.proof

theorem ProjChowNonzero.full : GroundTheory.Heights₂.Heights.ProjChowNonzero.Statement :=
  GroundTheory.Heights₂.Heights.ProjChowNonzero.proof

theorem SecDegreeLe.full : GroundTheory.Heights₂.Heights.SecDegreeLe.Statement :=
  GroundTheory.Heights₂.Heights.SecDegreeLe.proof

theorem SecFiniteUnit.full : GroundTheory.Heights₂.Heights.SecFiniteUnit.Statement :=
  GroundTheory.Heights₂.Heights.SecFiniteUnit.proof

theorem SecRankSpecialize.full : GroundTheory.Heights₂.Heights.SecRankSpecialize.Statement :=
  GroundTheory.Heights₂.Heights.SecRankSpecialize.proof

theorem SecDegreeGe.full : GroundTheory.Heights₂.Heights.SecDegreeGe.Statement :=
  GroundTheory.Heights₂.Heights.SecDegreeGe.proof GroundTheory.Heights₂.Heights.SecFiniteUnit.full GroundTheory.Heights₂.Heights.SecRankSpecialize.full

theorem ProjDegreeChow.full : GroundTheory.Heights₂.Heights.ProjDegreeChow.Statement :=
  GroundTheory.Heights₂.Heights.ProjDegreeChow.proof GroundTheory.Heights₂.Heights.ProjSecDegree.full GroundTheory.Heights₂.Heights.ProjSecDomain.full GroundTheory.Heights₂.Heights.ProjChowNonzero.full GroundTheory.Heights₂.Heights.SecDegreeLe.full GroundTheory.Heights₂.Heights.SecDegreeGe.full

theorem ConeFibreDegree.full : GroundTheory.Heights₂.Heights.ConeFibreDegree.Statement :=
  GroundTheory.Heights₂.Heights.ConeFibreDegree.proof GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.ProjDegreeChow.full

theorem ConeMassOfFibre.of_open (hConeFiniteFibreDim : GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.Statement) (hConeGraphCover : GroundTheory.Heights₂.Heights.ConeGraphCover.Statement) (hConeJacMeasurable : GroundTheory.Heights₂.Heights.ConeJacMeasurable.Statement) (hConeTangentDim : GroundTheory.Heights₂.Heights.ConeTangentDim.Statement) (hGraphAreaFibre : GroundTheory.Heights₂.Heights.GraphAreaFibre.Statement) (hTangentGaussInvariant : GroundTheory.Heights₂.Heights.TangentGaussInvariant.Statement) :
    GroundTheory.Heights₂.Heights.ConeMassOfFibre.Statement :=
  GroundTheory.Heights₂.Heights.ConeMassOfFibre.proof (GroundTheory.Heights₂.Heights.ConeFibreAverage.of_open hConeFiniteFibreDim hConeGraphCover hConeJacMeasurable hConeTangentDim hGraphAreaFibre hTangentGaussInvariant)

end GroundTheory.Heights₂.Heights
