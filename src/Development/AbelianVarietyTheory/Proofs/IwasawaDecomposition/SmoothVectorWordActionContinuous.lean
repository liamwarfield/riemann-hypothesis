module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyBallSubset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec.WordCont

theorem continuous_apply_family {Y L E : Type} [TopologicalSpace Y] [AddCommGroup L] [Module ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Y → L →ₗ[ℝ] E) (hW : ∀ x, Continuous fun y => W y x)
    {f : Y → L} (hf : Continuous f) : Continuous fun y => W y (f y) := by
  let b := Module.finBasis ℝ L
  have e : (fun y => W y (f y)) = fun y => ∑ i, b.coord i (f y) • W y (b i) := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr (f y), map_sum]
    simp only [map_smul, Module.Basis.coord_apply]
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp hf).smul (hW _)

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lieSub (G : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := GlobalTheory.UnitaryLieAlgebra.unitaryLie G

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem continuous_word [CompleteSpace H] (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G)
    (hσ : IsURepOn (UJset ε) σ) {Y : Type} [TopologicalSpace Y] (l : List (Y → Matrix (Fin n) (Fin n) ℂ))
    (hc : ∀ f ∈ l, Continuous f) (hm : ∀ f ∈ l, ∀ y, f y ∈ lieG G) :
    ∀ w ∈ smSub G (trRep σ P), Continuous fun y => word (trRep σ P) (l.map fun f => f y) w := by
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  induction l using List.reverseRecOn with
  | nil => intro w _; exact continuous_const
  | append_singleton l f ih =>
    intro w hw
    have hc' : ∀ f ∈ l, Continuous f := fun g hg => hc g (by simp [hg])
    have hm' : ∀ f ∈ l, ∀ y, f y ∈ lieG G := fun g hg => hm g (by simp [hg])
    have hl : ∀ y, ∀ X ∈ l.map (fun f => f y), X ∈ lieG G := fun y X hX => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hX
      exact hm' g hg y
    obtain ⟨hadd, hsm⟩ := GlobalTheory.T.derived_action_smooth_vector_real_linear n ε H σ P G hP h hσ w hw
    let W : Y → lieSub G →ₗ[ℝ] H := fun y =>
      { toFun := fun X => word (trRep σ P) (l.map fun f => f y) (dRep (trRep σ P) X w)
        map_add' := fun X Z => by
          rw [Submodule.coe_add, hadd _ X.2 _ Z.2,
            word_add hG hπ (hl y) (dRep_mem hG hπ hw X.2) (dRep_mem hG hπ hw Z.2)]
        map_smul' := fun a X => by
          rw [Submodule.coe_smul, hsm a _ X.2, word_smul hG hπ (hl y) _ (dRep_mem hG hπ hw X.2)]
          simp }
    have hf : Continuous fun y => (⟨f y, hm f (by simp) y⟩ : lieSub G) :=
      (hc f (by simp)).subtype_mk _
    have := continuous_apply_family W (fun X => ih hc' hm' _ (dRep_mem hG hπ hw X.2)) hf
    simp only [List.map_append, word_append, List.map_cons, List.map_nil, word_cons, word_nil]
    exact this

theorem word_rep {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    {w : H} (hw : w ∈ smSub G π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieG G) :
    word π l (π g w) = π g (word π (l.map fun X => g⁻¹ * X * g) w) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieG G := fun Y hY => hl Y (by simp [hY])
    have hm : ∀ Y ∈ l.map (fun X => g⁻¹ * X * g), Y ∈ lieG G := fun Y hY => by
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
      exact conj_mem_lieG hG hg (hl' Z hZ)
    rw [word_cons, ih hl', dRep_rep hG hπ (word_mem hG hπ hm hw) hg (hl X (by simp))]
    rfl

theorem continuous_sigma (hσ : IsURepOn (UJset ε) σ) {u : Formalism.REAL.UJ ε → H} (hu : Continuous u) :
    Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) (u g) := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have h1 : Tendsto (fun g => σ (umat g) (u g) - σ (umat g) (u g₀)) (𝓝 g₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : (fun g : Formalism.REAL.UJ ε => ‖σ (umat g) (u g) - σ (umat g) (u g₀)‖) = fun g => ‖u g - u g₀‖ := by
      funext g
      rw [← map_sub, hσ.2.1 _ g.2]
    rw [e]
    exact tendsto_iff_norm_sub_tendsto_zero.1 hu.continuousAt
  have h2 := h1.add (continuous_orbit hσ (u g₀)).continuousAt
  simpa [ContinuousAt] using h2

theorem continuous_word_translate : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), Continuous fun g : Formalism.REAL.UJ ε => word (trRep σ P) l (σ (umat g) w) := by
  intro n ε H _ _ _ σ P G hP h hσ l hl w hw
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hmem : ∀ g : Formalism.REAL.UJ ε, P⁻¹ * umat g * P ∈ Formalism.QuantumDeterminants.UH G := fun g => conj_mem_UH hP h g.2
  have hinv : ∀ g : Formalism.REAL.UJ ε, (P⁻¹ * umat g * P)⁻¹ = P⁻¹ * umat g⁻¹ * P := fun g => by
    apply Matrix.inv_eq_right_inv
    have e : umat g * umat g⁻¹ = 1 := Units.mul_inv g.1
    calc P⁻¹ * umat g * P * (P⁻¹ * umat g⁻¹ * P) = P⁻¹ * (umat g * (P * P⁻¹) * umat g⁻¹) * P := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv _ hd, Matrix.mul_one, e, Matrix.mul_one, nonsing_inv_mul _ hd]
  have c1 : Continuous fun g : Formalism.REAL.UJ ε => P⁻¹ * umat g * P :=
    (continuous_const.matrix_mul continuous_umat).matrix_mul continuous_const
  have c2 : Continuous fun g : Formalism.REAL.UJ ε => (P⁻¹ * umat g * P)⁻¹ := by
    simp only [hinv]
    exact c1.comp continuous_inv
  have hc := continuous_word hP h hσ
    (l.map fun X (g : Formalism.REAL.UJ ε) => (P⁻¹ * umat g * P)⁻¹ * X * (P⁻¹ * umat g * P))
    (fun f hf => by
      obtain ⟨X, _, rfl⟩ := List.mem_map.1 hf
      exact (c2.matrix_mul continuous_const).matrix_mul c1)
    (fun f hf g => by
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hf
      exact conj_mem_lieG hG (hmem g) (hl X hX)) w hw
  convert continuous_sigma hσ hc using 2 with g
  have := word_rep hG hπ hw (hmem g) hl
  rw [trRep_conj hP] at this
  rw [this, List.map_map]
  rfl

end GlobalTheory.SmVec.WordCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_word_action_continuous : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), Continuous fun g : Formalism.REAL.UJ ε => word (trRep σ P) l (σ (umat g) w) := by
  first | exact @GlobalTheory.SmVec.WordCont.continuous_word_translate | exact GlobalTheory.SmVec.WordCont.continuous_word_translate | (intros; apply GlobalTheory.SmVec.WordCont.continuous_word_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInnerApprox
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem Std.exists_inner_approx {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) :
    ∃ (m : ℕ) (S : Fin m → List (Mx n)), (∀ i, ∀ X ∈ S i, X ∈ lieSet ε) ∧ ∀ δ : ℝ, 0 < δ → ∃ u : H,
      ∀ z, Sm ε σ z → ‖ℓ z - ⟪u, z⟫_ℂ‖ ≤ δ * ∑ i, ‖Dw σ (S i) z‖ := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  refine ⟨m, S, hS, fun δ hδ => ?_⟩
  have hx : ∀ i, ∃ x ∈ smooth (Jm ε) σ, dist ((InnerProductSpace.toDual ℂ H).symm (Λ i)) x < δ := fun i =>
    Metric.mem_closure_iff.1 (h.dense_smooth _) δ hδ
  choose x hxs hxd using hx
  choose u hu using fun i => exists_adjoint (isUnit_Jm ε) h.1 (S i) (hS i) (x i) (hxs i)
  refine ⟨∑ i, u i, fun z hz => ?_⟩
  rw [hΛ z hz, sum_inner, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← hu i z hz, ← InnerProductSpace.toDual_symm_apply, ← inner_sub_left]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [← dist_eq_norm]
  exact (hxd i).le

theorem avgBd_sobCont : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (T : H → H) (Z : Set (Mx n)) (C : ℝ), IsCompact Z →
    Z ⊆ UJset ε → 0 ≤ C → AvgBd σ T Z C → ∀ (ι : Type) [Fintype ι] (ℓ : ι → (H →ₗ[ℂ] ℂ)) (w : ι → H),
    (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) → (∀ j, Sm ε σ (w j)) → (∀ j, Sm ε σ (T (w j))) → ∀ M : ℝ, 0 ≤ M →
    (∀ y ∈ Z, ‖∑ j, ℓ j (σ y (w j))‖ ≤ M) → ‖∑ j, ℓ j (T (w j))‖ ≤ C * M := by
  intro n ε H _ _ _ σ h T Z C hZ hZU hC hA ι _ ℓ w hℓ hw hTw M hM hb
  choose m S hS hap using fun j => h.exists_inner_approx (hℓ j)
  have hc : ContinuousOn (fun y => ∑ j, ∑ i, ‖Dw σ (S j i) (σ y (w j))‖) Z :=
    continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun i _ =>
      ((h.continuousOn_Dw (hS j i) (hw j)).mono hZU).norm
  obtain ⟨K₀, hK₀⟩ := hZ.exists_bound_of_continuousOn hc
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ y ∈ Z, ∑ j, ∑ i, ‖Dw σ (S j i) (σ y (w j))‖ ≤ K := fun y hy =>
    ((le_abs_self _).trans (hK₀ y hy)).trans (le_max_left _ _)
  set K' := ∑ j, ∑ i, ‖Dw σ (S j i) (T (w j))‖ with hK'
  have key : ∀ δ : ℝ, 0 < δ → ‖∑ j, ℓ j (T (w j))‖ ≤ C * M + δ * (C * K + K') := by
    intro δ hδ
    choose u hu using fun j => hap j δ hδ
    have hd : ∀ z : ι → H, (∀ j, Sm ε σ (z j)) →
        ‖∑ j, ℓ j (z j) - ∑ j, ⟪u j, z j⟫_ℂ‖ ≤ δ * ∑ j, ∑ i, ‖Dw σ (S j i) (z j)‖ := fun z hz => by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hu j _ (hz j))
    have h1 := hA ι u w (M + δ * K) (by positivity) fun y hy => by
      have e1 := hd (fun j => σ y (w j)) fun j => (hw j).translate h.1 (hZU hy)
      have e2 := norm_le_norm_add_norm_sub (∑ j, ℓ j (σ y (w j))) (∑ j, ⟪u j, σ y (w j)⟫_ℂ)
      have e3 := mul_le_mul_of_nonneg_left (hK y hy) hδ.le
      have e4 := hb y hy
      linarith
    have h2 := hd (fun j => T (w j)) hTw
    have h3 := norm_le_norm_add_norm_sub' (∑ j, ℓ j (T (w j))) (∑ j, ⟪u j, T (w j)⟫_ℂ)
    nlinarith
  have ht : Tendsto (fun δ : ℝ => C * M + δ * (C * K + K')) (𝓝[>] 0) (𝓝 (C * M + 0 * (C * K + K'))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall key)

end GlobalTheory.TypeSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCf
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section

namespace GlobalTheory.TypeSumCtrl

def allWords {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) : List (List α) :=
  Nat.rec [[]] (fun _ T => [] :: T.flatMap fun l => (List.ofFn E).map fun X => X :: l) m

theorem allWords_zero {α : Type} {k : ℕ} (E : Fin k → α) : allWords E 0 = [[]] := rfl

theorem allWords_succ {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) :
    allWords E (m + 1) = [] :: (allWords E m).flatMap fun l => (List.ofFn E).map fun X => X :: l := rfl

theorem mem_allWords {α : Type} {k : ℕ} (E : Fin k → α) :
    ∀ (m : ℕ) (l : List α), l ∈ allWords E m ↔ l.length ≤ m ∧ ∀ X ∈ l, ∃ i, E i = X
  | 0, l => by
    cases l <;> simp [allWords_zero]
  | m + 1, [] => by simp [allWords_succ]
  | m + 1, X :: l => by
    simp only [allWords_succ, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_ofFn, List.length_cons,
      reduceCtorEq, false_or, List.cons.injEq, forall_eq_or_imp, Nat.add_le_add_iff_right]
    constructor
    · rintro ⟨l', h1, Y, h2, rfl, rfl⟩
      exact ⟨((mem_allWords E m _).1 h1).1, h2, ((mem_allWords E m _).1 h1).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨l, (mem_allWords E m _).2 ⟨h1, h3⟩, X, h2, rfl, rfl⟩

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {k : ℕ}

def cf (E : Fin k → Mx n) (X : Mx n) : ℝ := ∑ i, |((X * (E i)ᴴ).trace).re|

theorem cf_nonneg (E : Fin k → Mx n) (X : Mx n) : 0 ≤ cf E X := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_cf (E : Fin k → Mx n) : Continuous (cf E) := by
  unfold cf
  refine continuous_finsetSum _ fun i _ => ?_
  exact (Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)).abs

omit [CompleteSpace H] in
theorem Dw_sum (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) (c : Fin k → ℂ)
    {x : Fin k → H} (hx : ∀ i, Sm ε σ (x i)) : Dw σ l (∑ i, c i • x i) = ∑ i, c i • Dw σ l (x i) := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have := congrArg Subtype.val (map_sum L (fun i => c i • (⟨x i, hx i⟩ : smooth (Jm ε) σ)) Finset.univ)
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, hL] at this
  exact this

theorem key (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    ∀ p : List (Mx n), (∀ X ∈ p, ∃ i, E i = X) → p.length + l.length ≤ m →
      ‖Dw σ (p ++ l) w‖ ≤ (l.map (cf E)).prod * sobNorm σ (allWords E m) w := by
  induction l with
  | nil =>
    intro p hp hm
    simpa using norm_Dw_le_sobNorm σ ((mem_allWords E m p).2 ⟨by simpa using hm, hp⟩) w
  | cons X l ih =>
    intro p hp hm
    have hX := hl X List.mem_cons_self
    have hl' := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hp' : ∀ Y ∈ p, Y ∈ lieSet ε := fun Y hY => by
      obtain ⟨i, rfl⟩ := hp Y hY
      exact hE i
    have hs := hw.word h.1 hl'
    have e1 : Dw σ (p ++ X :: l) w =
        ∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • Dw σ ((p ++ [E i]) ++ l) w := by
      rw [Dw_append]
      show Dw σ p (dRep σ X (Dw σ l w)) = _
      conv_lhs => rw [hx X hX]
      rw [h.dRep_sum hE hs, Dw_sum h.1 hp' _ (fun i => dRep_mem (isUnit_Jm ε) h.1 hs (hE i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Dw_append, Dw_append]
      rfl
    rw [e1, List.map_cons, List.prod_cons, mul_assoc, cf, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left (ih hl' _ ?_ ?_) (abs_nonneg _)
    · intro Y hY
      rcases List.mem_append.1 hY with hY | hY
      · exact hp Y hY
      · exact ⟨i, (List.mem_singleton.1 hY).symm⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at hm ⊢
      omega

theorem sob_le (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (S : List (List (Mx n))) (hS : Words (lieSet ε) S) (hm : ∀ l ∈ S, l.length ≤ m) :
    sobNorm σ S w ≤ (S.map fun l => (l.map (cf E)).prod).sum * sobNorm σ (allWords E m) w := by
  rw [← List.sum_map_mul_right]
  conv_lhs => unfold sobNorm
  refine List.sum_le_sum fun l hl => ?_
  simpa using key h hE hx m hw l (hS l hl) [] (by simp) (by simpa using hm l hl)

theorem exists_ctrl : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ S₀ : List (List (Mx n)), Words (lieSet ε) S₀ → ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ [] ∈ S ∧ Ctrl (lieSet ε) (UJset ε) σ S ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ w, Sm ε σ w → sobNorm σ S₀ w ≤ A * sobNorm σ S w := by
  intro n ε H _ _ _ σ h S₀ hS₀
  obtain ⟨E, hE, -, hx⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  have hE' : ∀ i, E i ∈ lieSet ε := fun i => (hE i).1
  have hx' : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i := fun X hX => by
    simpa only [Complex.coe_smul] using hx X hX
  set m := (S₀.map List.length).sum with hm
  have hW : Words (lieSet ε) (allWords E m) := fun l hl X hX => by
    obtain ⟨i, rfl⟩ := ((mem_allWords E m l).1 hl).2 X hX
    exact hE' i
  refine ⟨allWords E m, hW, (mem_allWords E m _).2 (by simp), ?_,
    (S₀.map fun l => (l.map (cf E)).prod).sum, ?_, fun w hw => sob_le h hE' hx' m hw S₀ hS₀ fun l hl => ?_⟩
  · refine ⟨fun g => ((allWords E m).map fun l => (l.map fun X => cf E (Jm ε * gᴴ * Jm ε * X * g)).prod).sum, ?_,
      fun g hg w hw => ?_⟩
    · refine continuous_list_sum _ fun l _ => continuous_list_prod _ fun X _ => ?_
      exact (continuous_cf E).comp (f := fun g : Mx n => Jm ε * gᴴ * Jm ε * X * g)
        (((((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
          continuous_const).matrix_mul continuous_const)).matrix_mul continuous_id)
    · rw [sobNorm_translate h.1 hg hw hW]
      have := sob_le h hE' hx' m hw ((allWords E m).map fun l => l.map fun X => g⁻¹ * X * g) ?_ ?_
      · simpa only [List.map_map, Function.comp_def, inv_eq_UJ hg] using this
      · intro l hl X hX
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact conj_mem_lie (isUnit_Jm ε) hg (hW l' hl' Y hY)
      · intro l hl
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        simpa using ((mem_allWords E m l').1 hl').1
  · refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    refine List.prod_nonneg fun y hy => ?_
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hy
    exact cf_nonneg E X
  · exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨l, hl, rfl⟩)

end GlobalTheory.TypeSumCtrl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevInequalityAtOneIndefiniteUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevInequalityAtOneIndefiniteUnitary
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.SobolevHaar

theorem cube_step {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ)
    (c : Fin (N + 1) → ℝ → G) (s : ℝ) (hs : 0 < s)
    (hc : ∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b)
    (f f' : G → ℂ) (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt (fun t => f (x * c (Fin.last N) t)) (f' x) 0) :
    ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖f (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod‖ ^ 2 ≤
      2 / s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖f (List.ofFn fun i => c i (t i)).prod‖ ^ 2) +
      2 * s * ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖f' (List.ofFn fun i => c i (t i)).prod‖ ^ 2 := by
  set l := Fin.last N with hl
  have hΘ := continuous_prod_ofFn_curves (N + 1) c (fun i => (hc i).1)
  have hΘ' := continuous_prod_ofFn_curves N (fun i => c i.castSucc) (fun i => (hc _).1)
  have hsn : ∀ (t : Fin N → ℝ) (r : ℝ),
      (List.ofFn fun i => c i (Fin.snoc (α := fun _ => ℝ) t r i)).prod
        = (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r := by
    intro t r
    rw [List.ofFn_succ']
    simp [hl]
  have fub : ∀ w : G → ℂ, Continuous w →
      IntegrableOn (fun t : Fin N → ℝ => ∫ r in (0 : ℝ)..s,
        ‖w ((List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r)‖ ^ 2)
        (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) ∧
      ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖w (List.ofFn fun i => c i (t i)).prod‖ ^ 2 =
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∫ r in (0 : ℝ)..s,
        ‖w ((List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r)‖ ^ 2 := by
    intro w hw
    have h := integral_cube_succ_last N s
      (fun t => ‖w (List.ofFn fun i => c i (t i)).prod‖ ^ 2) ((hw.comp hΘ).norm.pow 2)
    simp only [hsn] at h
    simp only [intervalIntegral.integral_of_le hs.le, ← integral_Icc_eq_integral_Ioc]
    exact h
  obtain ⟨i1, b1⟩ := fub f hf
  obtain ⟨i2, b2⟩ := fub f' hf'
  have pt : ∀ x : G, ‖f x‖ ^ 2 ≤ 2 / s * (∫ r in (0 : ℝ)..s, ‖f (x * c l r)‖ ^ 2)
      + 2 * s * ∫ r in (0 : ℝ)..s, ‖f' (x * c l r)‖ ^ 2 := by
    intro x
    have h := sobolev_endpoint_one_variable ℂ (fun r => f (x * c l r))
      (fun r => f' (x * c l r)) s hs ?_ ?_
    · simpa only [(hc l).2.1, mul_one] using h
    · intro r _
      have h1 : HasDerivAt (fun t => f (x * c l r * c l t)) (f' (x * c l r)) (r - r) := by
        rw [sub_self]; exact hd _
      have h2 := h1.comp_sub_const r r
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [mul_assoc, ← (hc l).2.2, add_sub_cancel]
    · exact (hf'.comp (continuous_const.mul (hc l).1)).continuousOn
  have i0 : IntegrableOn (fun t : Fin N → ℝ =>
      ‖f (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod‖ ^ 2)
      (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) :=
    ((hf.comp hΘ').norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have key := integral_mono i0 ((i1.const_mul (2 / s)).add (i2.const_mul (2 * s)))
    (fun t => pt _)
  simp only [Pi.add_apply] at key
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul] at key
  rw [b1, b2]
  exact key

theorem cube_sum {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Set V) (u : V)
    (hu : u ∈ A) (s : ℝ) (hs : 0 < s) : ∀ (N : ℕ) (c : Fin N → ℝ → G) (D : Fin N → V → V),
    (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) →
    (∀ i, ∀ v ∈ A, D i v ∈ A) →
    ∃ (S : List V) (C : ℝ), (∀ v ∈ S, v ∈ A) ∧ 0 ≤ C ∧ ∀ Fr : V → G → ℂ, (∀ v ∈ A, Continuous (Fr v)) →
      (∀ v ∈ A, ∀ i x, HasDerivAt (fun t => Fr v (x * c i t)) (Fr (D i v) x) 0) →
      ‖Fr u 1‖ ^ 2 ≤ C * (S.map fun v => ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖Fr v (List.ofFn fun i => c i (t i)).prod‖ ^ 2).sum := by
  intro N
  induction N with
  | zero =>
    intro c D _ _
    refine ⟨[u], 1, by simpa using hu, zero_le_one, fun Fr _ _ => ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [volume_pi, Measure.restrict_pi_pi]
    simp [Measure.real]
  | succ N ih =>
    intro c D hc hD
    obtain ⟨S, C, hS, hC, h⟩ := ih (fun i => c i.castSucc) (fun i => D i.castSucc) (fun i => hc _)
      (fun i => hD _)
    refine ⟨S ++ S.map (D (Fin.last N)), C * (2 / s + 2 * s), ?_, by positivity, fun Fr h1 h2 => ?_⟩
    · intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hS v hv
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
        exact hD _ w (hS w hw)
    refine (h Fr h1 fun v hv i => h2 v hv _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [List.map_append, List.sum_append, List.map_map, ← List.sum_map_add, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun v hv => ?_
    refine (cube_step N c s hs hc (Fr v) (Fr (D (Fin.last N) v)) (h1 v (hS v hv))
      (h1 _ (hD _ v (hS v hv))) (h2 v (hS v hv) _)).trans ?_
    simp only [Function.comp_apply]
    have p : ∀ w, 0 ≤ ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖Fr w (List.ofFn fun i => c i (t i)).prod‖ ^ 2 := fun w => integral_nonneg fun t => by positivity
    have a1 := mul_nonneg (show 0 ≤ 2 * s by positivity) (p v)
    have a2 := mul_nonneg (show 0 ≤ 2 / s by positivity) (p (D (Fin.last N) v))
    nlinarith

theorem exists_small (n : ℕ) : ∃ s : ℝ, 0 < s ∧ n * (Real.exp (3 * n ^ 2 * s) - 1) ≤ 1 / 2 := by
  have h : ContinuousAt (fun s : ℝ => n * (Real.exp (3 * n ^ 2 * s) - 1)) 0 := by fun_prop
  have h2 : ∀ᶠ s : ℝ in 𝓝 0, n * (Real.exp (3 * n ^ 2 * s) - 1) < 1 / 2 :=
    h.eventually_lt continuousAt_const (by simp)
  obtain ⟨s, h3, h4⟩ := ((h2.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))).and self_mem_nhdsWithin).exists
  exact ⟨s, h4, h3.le⟩

theorem sobolev_at_one : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ F : List (Mx n) → Mx n → ℂ, (∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)) → IsDerFam ε F → (∀ l ∈ S, Integrable (fun g : UJ ε => ‖F l (umat g)‖ ^ 2) (muG ε)) → ‖F [] 1‖ ^ 2 ≤ C * (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum := by
  intro n ε
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  obtain ⟨κ, hκ, hg, -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge n ε
  obtain ⟨s, hs, hsn⟩ := exists_small n
  let c : Fin (n ^ 2) → ℝ → UJ ε := fun i t =>
    GlobalTheory.GaugeConst.expJ ε (t • (⟨E i, (hE1 i).1⟩ : GlobalTheory.GaugeConst.lieJ ε))
  have hc : ∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b := fun i =>
    ⟨(GlobalTheory.GaugeConst.continuous_expJ ε).comp (continuous_id.smul continuous_const),
      GlobalTheory.GaugeConst.uMat_injective ε (by
        change NormedSpace.exp ((0 : ℝ) • E i) = 1
        simp),
      fun a b => GlobalTheory.GaugeConst.uMat_injective ε (exp_add_smul (E i) a b)⟩
  obtain ⟨S, C, hS, hC, h⟩ := cube_sum {l : List (Mx n) | ∀ Y ∈ l, Y ∈ lieSet ε} [] (by simp) s hs (n ^ 2) c
    (fun i l => E i :: l) hc (fun i l hl Y hY => by
      rcases List.mem_cons.1 hY with rfl | hY
      exacts [(hE1 i).1, hl Y hY])
  set K := Real.exp (2 * n ^ 3 * (Real.exp (2 * n ^ 2 * s) - 1)) * κ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨S, C * K, hS, by positivity, fun F hF hD hI => ?_⟩
  have hcont : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → Continuous fun g : UJ ε => F l (umat g) :=
    fun l hl => (hF l hl).comp_continuous (GlobalTheory.GaugeConst.continuous_uMat ε) fun g => g.2
  refine (h (fun l g => F l (umat g)) hcont fun l hl i x => hD l hl (E i) (hE1 i).1 _ x.2).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [← List.sum_map_mul_left]
  refine List.sum_le_sum fun l hl => ?_
  have hl' := hcont l (hS l hl)
  have hΘ := continuous_prod_ofFn_curves (n ^ 2) c (fun i => (hc i).1)
  have hch := GlobalTheory.ProductChart.lintegral_chart_le n ε κ s E (fun t => (List.ofFn fun i => c i (t i)).prod) hg
    (fun i => (hE1 i).1) hE2 hs hsn (fun t => by
      have := map_list_prod ((Units.coeHom (Mx n)).comp (UJ ε).subtype) (List.ofFn fun i => c i (t i))
      refine this.trans ?_
      rw [List.map_ofFn]
      simp only [Complex.coe_smul]
      rfl)
    (fun g => ENNReal.ofReal (‖F l (umat g)‖ ^ 2)) (hl'.norm.pow 2).measurable.ennreal_ofReal
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t : Fin (n ^ 2) → ℝ => ‖F l (umat (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
    (Filter.Eventually.of_forall fun t => by positivity)
    ((hl'.comp hΘ).norm.pow 2).aestronglyMeasurable]
  have hp : 0 ≤ ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε) := integral_nonneg fun g => by positivity
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0 hp) (hch.trans ?_)
  rw [ENNReal.ofReal_mul hK0, ofReal_integral_eq_lintegral_ofReal (hI l hl)
    (Filter.Eventually.of_forall fun g => by positivity)]
  exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _

end GlobalTheory.SobolevHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevInequalityAtOneIndefiniteUnitaryStatement
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_inequality_at_one_indefiniteUnitary : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ F : List (Mx n) → Mx n → ℂ, (∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)) → IsDerFam ε F → (∀ l ∈ S, Integrable (fun g : UJ ε => ‖F l (umat g)‖ ^ 2) (muG ε)) → ‖F [] 1‖ ^ 2 ≤ C * (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum := by
  first | exact @GlobalTheory.SobolevHaar.sobolev_at_one | exact GlobalTheory.SobolevHaar.sobolev_at_one | (intros; apply GlobalTheory.SobolevHaar.sobolev_at_one <;> assumption)
end
end
