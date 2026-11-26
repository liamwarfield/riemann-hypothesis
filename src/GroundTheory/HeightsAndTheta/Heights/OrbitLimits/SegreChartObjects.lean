module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StokesObjects
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.POrderIdealIndexExtension
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing mcPts segre PBlk)

section Chart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def segreChartSet (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def segreChartIdeal (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (segreChartSet P σ i)

def segreChartComponents (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Finset (Ideal (MvPolynomial (Fin m) ℂ)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) ℂ)
    (segreChartIdeal P σ i)).toFinset

omit [∀ k, Fintype (ι k)] in
theorem mem_segreChartComponents {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} :
    J ∈ segreChartComponents P σ i ↔ J ∈ (segreChartIdeal P σ i).minimalPrimes :=
  Set.Finite.mem_toFinset _


omit [∀ k, Fintype (ι k)] in
theorem chart_coord_eq_one {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i)
    {x : Fin m → ℂ} (hx : x ∈ ComplexSets.zeroSet J) : x (σ.symm i) = 1 := by
  have hle : segreChartIdeal P σ i ≤ J := (mem_segreChartComponents.1 hJ).1.2
  have hmem : (MvPolynomial.X (σ.symm i) - 1 : MvPolynomial (Fin m) ℂ) ∈ segreChartIdeal P σ i := by
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    simp [hzi]
  have h := hx _ (hle hmem)
  simp only [map_sub, MvPolynomial.eval_X, map_one] at h
  exact sub_eq_zero.1 h

end Chart

section Lift

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ) :
    (Σ k, ι k) → ℂ :=
  fun p => x (σ.symm (Function.update i p.1 p.2))

theorem contDiff_chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) {n : WithTop ℕ∞} :
    ContDiff ℝ n (chartLift σ i) :=
  contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (σ.symm (Function.update i p.1 p.2))


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartLift_blockNonzero {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) : ∀ k, ∃ j, chartLift σ i x ⟨k, j⟩ ≠ 0 :=
  fun k => ⟨i k, by simp [chartLift, hx]⟩


omit [∀ k, Fintype (ι k)] in
theorem chartLift_segre_apply {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) (k : K) (j : ι k) :
    chartLift σ i (fun a => segre z (σ a)) ⟨k, j⟩ = z ⟨k, j⟩ * (z ⟨k, i k⟩)⁻¹ := by
  have hne : z ⟨k, i k⟩ ≠ 0 := fun h0 => by
    have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hz] at this
    exact one_ne_zero this
  have hupd : (fun k' => z ⟨k', Function.update i k j k'⟩) =
      Function.update (fun k' => z ⟨k', i k'⟩) k (z ⟨k, j⟩) := by
    funext k'
    by_cases h : k' = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hprod : segre z (Function.update i k j) = z ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ := by
    simp only [segre]
    rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hall : z ⟨k, i k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ = 1 := by
    rw [Finset.mul_prod_erase _ (fun k' => z ⟨k', i k'⟩) (Finset.mem_univ k)]
    exact hz
  simp only [chartLift, Equiv.apply_symm_apply]
  rw [hprod]
  field_simp
  linear_combination z ⟨k, j⟩ * hall

theorem segre_chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) :
    segre (chartLift σ i (fun a => segre z (σ a))) = segre z := by
  funext i'
  show ∏ k, chartLift σ i (fun a => segre z (σ a)) ⟨k, i' k⟩ = ∏ k, z ⟨k, i' k⟩
  simp only [chartLift_segre_apply σ i z hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have : ∏ k, z ⟨k, i k⟩ = 1 := hz
  rw [this, inv_one, mul_one]

end Lift

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreCoordGoodProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre PBlk)

def SegreCoordGoodProj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (i : (k : K) → ι k),
    IsArithVar P (e + 1) → (∃ z ∈ mcPts P, segre z i ≠ 0) →
      ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ ∧ ∀ w, Ψ w 0 = w i

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.IsMultiHomogPlaneCoordinate
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def normSq (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) ^ 2

def regLog (A : HermLine ι) (s : MRing ι) (ε : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (normSq A s z + ε) / 2

omit [∀ k, Fintype (ι k)] in
theorem normSq_nonneg (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : 0 ≤ normSq A s z :=
  sq_nonneg _

theorem normSq_smul {A : HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    normSq A s (fun p => c p.1 * z p) = normSq A s z := by
  unfold normSq
  rw [eval_smul_of_isMultiHomog hs c z, A.smul c z hc, norm_mul, norm_prod]
  have hC : (∏ k, ‖c k‖ ^ A.a k) = ∏ k, ‖c k ^ a k‖ := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, norm_pow, zpow_natCast]
  rw [hC, mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ =>
    norm_ne_zero_iff.mpr (pow_ne_zero _ (hc k)))]

def regLine (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : HermLine ι :=
  HermLine.ofWeight (fun z => -regLog A s ε z) fun c z hc => by
    simp only [regLog, normSq_smul ha hs c z hc]

theorem regLine_a (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : (regLine A s ε ha hs).a = 0 := rfl

theorem log_regLine (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : (fun z => Real.log ((regLine A s ε ha hs).h z)) = regLog A s ε := by
  funext z
  simp [regLine, HermLine.ofWeight, Real.log_exp]

theorem contDiff_evalC (s : MRing ι) :
    ContDiff ℝ ∞ (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) s)) := by
  induction s using MvPolynomial.induction_on with
  | C a => simpa only [map_C, eval_C] using contDiff_const
  | add p q hp hq => simpa only [map_add (f := _), eval_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, map_X, eval_mul, eval_X] using hp.mul (contDiff_apply ℝ (fun _ => ℂ) i)

theorem contDiffOn_regLog {A : HermLine ι} (hA : IsSmoothHerm A) (s : MRing ι) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (regLog A s ε) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hN : ContDiffOn ℝ ∞ (normSq A s) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have h1 := (((contDiff_norm_sq ℝ).comp (contDiff_evalC s)).contDiffOn (s := {z : (Σ k, ι k) → ℂ |
      ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})).div (hA.pow 2) fun z hz => pow_ne_zero _ (A.pos z hz).ne'
    exact h1.congr fun z _ => by simp only [normSq, div_pow]; rfl
  exact ((hN.add contDiffOn_const).log fun z _ =>
    (add_pos_of_nonneg_of_pos (normSq_nonneg A s z) hε).ne').div_const 2

theorem isSmoothHerm_regLine {A : HermLine ι} (hA : IsSmoothHerm A) {s : MRing ι} {ε : ℝ} (hε : 0 < ε)
    {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    IsSmoothHerm (regLine A s ε ha hs) :=
  Real.contDiff_exp.comp_contDiffOn (contDiffOn_regLog hA s hε).neg.neg

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithIntersectionSystem

theorem multilin_of_isFamily {I : AllFam} (hI : I.IsFamily) : IsMultilinFam I := by
  intro K _ ι _ P n L j A B hP hL hA hB
  cases n with
  | zero => exact j.elim0
  | succ m =>
    obtain ⟨hsym, hadd, -⟩ := hI K ι
    have e : ∀ X : HermLine ι, IsSmoothHerm X →
        I K ι P (m + 1) (Function.update L j X) =
          I K ι P (m + 1)
            (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
      intro X hX
      rw [← GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.update_comp_swap]
      exact (hsym P (m + 1) _ _ hP
        (GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.smooth_update hL j hX)).symm
    rw [e _ (isSmoothHerm_tensor hA hB), e A hA, e B hB]
    exact hadd P m _ A B hP (fun i => hL _) hA hB

theorem of_found (hE : GroundTheory.Heights₂.Heights.Inter.ThmIExists.Statement) (hPF : PFCoordStatement)
    (hCM : ContractMixedStatement) : ArithIntersectionSystemStatement := by
  obtain ⟨I, hI⟩ := (hE : ExistsStatement)
  exact ⟨I, hI, multilin_of_isFamily hI, hPF I hI, hCM I hI⟩

end ArithIntersectionSystem

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegrePartition
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (segre PBlk)

def SegrePartition.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)],
    (∀ k, Nonempty (ι k)) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ((k : K) → ι k) → ((Σ k, ι k) → ℂ) → ℝ,
        (∀ i, IsDegZeroSmooth (ρ i)) ∧ (∀ z, ∑ i, ρ i z = 1) ∧
          ∀ i z, ‖segre z i‖ < δ * ‖segre z‖ → ρ i z = 0

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsBilinear
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot PBlk oneLine
  isSmoothHerm_oneLine)

def PtsBilinear.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (T : Type) [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ)
    (v : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ t, IsDegZeroSmooth (u t)) →
    IsDegZeroSmooth v →
    ptsIntegral P (Fin.cons v (pot L)) (fun z => ∑ t, u t z) =
        ∑ t, ptsIntegral P (Fin.cons v (pot L)) (u t) ∧
      ptsIntegral P (Fin.cons (fun z => ∑ t, u t z) (pot L)) v =
        ∑ t, ptsIntegral P (Fin.cons (u t) (pot L)) v

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre PBlk oneLine
  isSmoothHerm_oneLine)

def SegreChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (u v : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth u → IsDegZeroSmooth v →
    0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → u z = 0) →
      ∃ (m : ℕ) (Js : Finset (Ideal (MvPolynomial (Fin m) ℂ))) (U V : (Fin m → ℂ) → ℝ)
        (Φ : Fin n → (Fin m → ℂ) → ℝ),
        (∀ J ∈ Js, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (n + 1 : ℕ) ∧
          SmoothNear (ComplexSets.zeroSet J) U ∧ SmoothNear (ComplexSets.zeroSet J) V ∧
          ∀ j, SmoothNear (ComplexSets.zeroSet J) (Φ j)) ∧
        HasCompactSupport U ∧
        ptsIntegral P (Fin.cons v (pot L)) u = ∑ J ∈ Js, varInt J (n + 1) U (Matrix.vecCons V Φ) ∧
        ptsIntegral P (Fin.cons u (pot L)) v = ∑ J ∈ Js, varInt J (n + 1) V (Matrix.vecCons U Φ)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PInvertibleIndexMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt

noncomputable section

namespace InvertibleIndexMultiplicative

variable {Ω : Type} [Field Ω]

theorem index_ne_zero [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {I : Ideal B} (hI : I ≠ ⊥) :
    I.toAddSubgroup.index ≠ 0 := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨c, hc, q, hq⟩ := OrderIdealIndexExtensionAlt.exists_int_eq_mul ha
  refine OrderIdealIndexExtensionAlt.index_ne_zero_of_zsmul_mem _ hc fun x => ?_
  have e : c • x = a * (q * x) := by rw [zsmul_eq_mul, hq, mul_assoc]
  rw [Submodule.mem_toAddSubgroup, e]
  exact I.mul_mem_right _ haI

theorem relIndex_mulBy_ne_zero [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {β : B} (hβ : β ≠ 0) :
    (B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup ≠ 0 := by
  rw [map_mul_eq, relIndex_map_subtype]
  exact index_ne_zero (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hβ)

theorem relIndex_mulBy_mul {B : Subring Ω} {x y : Ω} (hx : x ≠ 0) (hxB : x ∈ B) (hyB : y ∈ B) :
    (B.toAddSubgroup.map (mulBy (x * y))).relIndex B.toAddSubgroup =
      (B.toAddSubgroup.map (mulBy x)).relIndex B.toAddSubgroup *
        (B.toAddSubgroup.map (mulBy y)).relIndex B.toAddSubgroup := by
  have e : B.toAddSubgroup.map (mulBy (x * y)) = (B.toAddSubgroup.map (mulBy y)).map (mulBy x) := by
    rw [AddSubgroup.map_map]
    congr 1
    ext z
    simp [mul_assoc]
  have h1 : B.toAddSubgroup.map (mulBy y) ≤ B.toAddSubgroup := by
    rintro _ ⟨z, hz, rfl⟩; exact B.mul_mem hyB hz
  have h2 : B.toAddSubgroup.map (mulBy x) ≤ B.toAddSubgroup := by
    rintro _ ⟨z, hz, rfl⟩; exact B.mul_mem hxB hz
  rw [e, ← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono h1) h2,
    AddSubgroup.relIndex_map_map_of_injective (f := mulBy x) _ _ (mulBy_injective hx), mul_comm]

theorem ne_bot_of_rep {B : Subring Ω} {X : AddSubgroup Ω} {β δ : B} {I : Ideal B} (hβ : β ≠ 0)
    (hX0 : X ≠ ⊥) (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) : I ≠ ⊥ := by
  intro hI
  obtain ⟨⟨x, hxX⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hX0
  obtain ⟨y, hy, hxy⟩ := (hX x).1 hxX
  rw [hI, Ideal.mem_bot] at hy
  subst hy
  have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  simp [hβL, hx] at hxy

theorem genIndex_rep [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {X : AddSubgroup Ω} {β δ : B}
    {I : Ideal B} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hI : I ≠ ⊥)
    (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) :
    genIndex X B.toAddSubgroup = ((B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup : ℝ) /
      (((B.toAddSubgroup.map (mulBy (δ : Ω))).relIndex B.toAddSubgroup : ℝ) * (I.toAddSubgroup.index : ℝ)) := by
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  have hδL : (δ : Ω) ≠ 0 := fun h => hδ (Subtype.ext h)
  have g := genIndex_eq (X := B.toAddSubgroup) (J := I.toAddSubgroup.map B.subtype.toAddMonoidHom)
    (M := X) hβL hδL
    (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem δ.2 hy)
    (by rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨β * y, I.mul_mem_left β hy, rfl⟩)
    (by
      intro x
      rw [hX x]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨y, ⟨y, hy, rfl⟩, h⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
        exact ⟨y, hy, h⟩)
    (by rw [relIndex_map_subtype]; exact index_ne_zero hI)
    (relIndex_mulBy_ne_zero hδ)
  rwa [relIndex_map_subtype] at g

end InvertibleIndexMultiplicative


open InvertibleIndexMultiplicative in
theorem InvertibleIndexMul.proof (h1 : LocalGenFamily.Statement) (h2 : LocallyPrincipalCoprimeField.Statement)
    (h3 : InvertibleProductRep.Statement) (h4 : InvertibleIndexCharP.Statement) :
    InvertibleIndexMul.Statement := by
  intro Ω _ B M N P η _ g h hB hM hN hP hg0 hh0 hgc hhc hloc
  have hlocM : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B M m (g i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.1
  have hlocN : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B N m (h i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.2.1
  by_cases hc : ringChar Ω ≠ 0
  · rw [h4 Ω B M η g hc hB hM hg0 hlocM, h4 Ω B N η h hc hB hN hh0 hlocN,
      h4 Ω B P η (fun i => g i * h i) hc hB hP (fun i => mul_ne_zero (hg0 i) (hh0 i))
        (fun m hm => (hloc m hm).imp fun _ hi => hi.2.2)]
    norm_num
  push Not at hc
  have : CharP Ω 0 := ringChar.eq_iff.mp hc
  have : CharZero Ω := CharP.charP_to_charZero Ω
  have := hB
  obtain ⟨hM0, ιM, _, aM, haM, hdM, hlM⟩ := h1 Ω B M η g hB hM hg0 hgc hlocM
  obtain ⟨β, δ, I, hβ, hδ, -, hMI⟩ := h2 Ω B M ιM aM hB hM haM hdM hlM hM0 1 one_ne_zero
  have hI0 := ne_bot_of_rep hβ hM0 hMI
  obtain ⟨t, htI, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨hN0, ιN, _, aN, haN, hdN, hlN⟩ := h1 Ω B N η h hB hN hh0 hhc hlocN
  obtain ⟨β', δ', J, hβ', hδ', hJt, hNJ⟩ := h2 Ω B N ιN aN hB hN haN hdN hlN hN0 t ht0
  have hJ0 := ne_bot_of_rep hβ' hN0 hNJ
  have hIJ : I ⊔ J = ⊤ := by
    rw [eq_top_iff, ← hJt, sup_comm I J]
    exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr htI) _
  have hPr := h3 Ω B M N P η g h β δ β' δ' I J hβ hδ hβ' hδ' hMI hNJ hP hloc
  have hIJ0 : I * J ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot]
    tauto
  have hidx : (I * J).toAddSubgroup.index = I.toAddSubgroup.index * J.toAddSubgroup.index :=
    cardQuot_mul_of_coprime (Ideal.isCoprime_iff_sup_eq.mpr hIJ)
  have hβL : (β : Ω) ≠ 0 := fun e => hβ (Subtype.ext e)
  have hδL : (δ : Ω) ≠ 0 := fun e => hδ (Subtype.ext e)
  rw [genIndex_rep hβ hδ hI0 hMI, genIndex_rep hβ' hδ' hJ0 hNJ,
    genIndex_rep (mul_ne_zero hβ hβ') (mul_ne_zero hδ hδ') hIJ0 hPr, hidx, Subring.coe_mul, Subring.coe_mul,
    relIndex_mulBy_mul hβL β.2 β'.2, relIndex_mulBy_mul hδL δ.2 δ'.2]
  have p1 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ)
  have p2 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ)
  have p3 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ')
  have p4 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ')
  have p5 := Nat.pos_of_ne_zero (index_ne_zero hI0)
  have p6 := Nat.pos_of_ne_zero (index_ne_zero hJ0)
  refine ⟨by positivity, by positivity, ?_⟩
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeComplexBaseChange
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace ConeComplexBaseChange

variable {σ : Type} [Fintype σ]


omit [Fintype σ] in
theorem map_int_complex_eq :
    (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℂ) =
      (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp

theorem comap_of_minimal (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
  have hP' : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hm
    rw [hP] at this
    exact this
  obtain ⟨hpr, hco, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have : (P.map (MvPolynomial.map (Int.castRingHom ℚ))).IsPrime := hpr
  rw [map_int_complex_eq, ← Ideal.map_map] at hQ
  have h := ReciprocityTheory.AnForm.R.BaseChangeC.comap_of_mem_minimalPrimes_map _ Q hQ
  rw [map_int_complex_eq, ← Ideal.comap_comap, h]
  exact hco

theorem dim_cancel_one {d : WithBot ℕ∞} {N : ℕ} (h : d + 1 = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    d = (N : WithBot ℕ∞) := by
  refine ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel (h := 1) (N := N + 1) ?_ ?_
  · rw [add_comm]; exact_mod_cast h
  · push_cast; rw [add_comm]

end ConeComplexBaseChange


end GroundTheory.Heights₂.Heights.Targets
end
end
