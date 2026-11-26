module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundlePullbackVanish

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSectionSplit
section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSectionForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]
  {F : Type*} [Field F] [Algebra F Ω] {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
  {Φ : Type*} [Field Φ] [Algebra Ω Φ]

abbrev projMap (F : Type*) [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    MRing (bundleIdx ι M) F →+* MvPolynomial (Option K) Φ :=
  eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω))) (fun p => C (projCoord y w φ t p) * X p.1)

theorem mem_projIdeal_iff {y : (Σ k, ι k) → Ω} {w : Module.Basis (Fin N) Ω E}
    {φ : Fin M → Module.Dual Ω E} {t : Fin N → Φ} {h : MRing (bundleIdx ι M) F} :
    h ∈ projIdeal F y w φ t ↔ projMap F y w φ t h = 0 :=
  RingHom.mem_ker

def tMon (α : K → ℕ) : MvPolynomial (Option K) Φ := ∏ k, X (some k) ^ α k

theorem tMon_add (α β : K → ℕ) : (tMon (α + β) : MvPolynomial (Option K) Φ) = tMon α * tMon β := by
  simp only [tMon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

def liftN (α : K → ℕ) : Option K → ℕ := fun o => Option.elim o 0 α

theorem liftN_add (α β : K → ℕ) : liftN (α + β) = liftN α + liftN β := by
  funext o; cases o <;> simp [liftN]

def chartMon (F : Type*) [Field F] (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) : MRing (bundleIdx ι M) F :=
  ∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ α k

theorem projMap_X_some (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (k : K) (i : ι k) :
    projMap F y w φ t (X ⟨some k, i⟩) = C (algebraMap Ω Φ (y ⟨k, i⟩)) * X (some k) := by
  simp [projMap, projCoord]

theorem projMap_X_none (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (l : Fin M) :
    projMap F y w φ t (X ⟨none, l⟩) =
      C (∑ i, t i * algebraMap Ω Φ (φ l (w i))) * X none := by
  simp [projMap, projCoord]

theorem sum_truncCoord_one (t : Fin N → Φ) (h0 : 0 < N) (z : Fin N → Φ) :
    ∑ i, truncCoord t 1 i * z i = t ⟨0, h0⟩ * z ⟨0, h0⟩ := by
  rw [Finset.sum_eq_single ⟨0, h0⟩]
  · simp [truncCoord]
  · intro j _ hj
    have : ¬ (j : ℕ) < 1 := by
      intro h; apply hj; ext; simp; omega
    simp [truncCoord, this]
  · simp

theorem projMap_C (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (r : F) :
    projMap F y w φ t (C r) = C (algebraMap Ω Φ (algebraMap F Ω r)) := by
  simp [projMap]

theorem projMap_chartMon (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (α : K → ℕ) :
    projMap F y w φ t (chartMon F M c α) =
      C (algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k)) * tMon α := by
  simp only [chartMon, map_prod, map_pow, projMap_X_some, mul_pow, Finset.prod_mul_distrib, tMon]

theorem isMultiHomog_chartMon (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMon F M c α) (liftN α) := by
  unfold IsMultiHomog chartMon
  have h := IsWeightedHomogeneous.prod (w := blockWeight (bundleIdx ι M)) Finset.univ
    (fun k => (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ α k)
    (fun k => α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (α k))
  convert h using 1
  funext o
  cases o with
  | none => simp [liftN, blockWeight, Finset.sum_apply]
  | some k => simp [liftN, blockWeight, Finset.sum_apply, Pi.single_apply]

theorem isMultiHomog_X_none (l : Fin M) :
    IsMultiHomog (X ⟨none, l⟩ : MRing (bundleIdx ι M) F) (Pi.single none 1) := by
  unfold IsMultiHomog
  exact isWeightedHomogeneous_X F _ _


variable (F M) in
def IsChartForm (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (a : Ω) (n : ℕ)
    (A : MRing (bundleIdx ι M) F) : Prop :=
  IsMultiHomog A (liftN fun _ => n) ∧
    projMap F y w φ t A = C (algebraMap Ω Φ (a * segreVec y c ^ n)) * tMon (fun _ => n)

theorem IsChartForm.pad {y : (Σ k, ι k) → Ω} {w : Module.Basis (Fin N) Ω E}
    {φ : Fin M → Module.Dual Ω E} {t : Fin N → Φ} {c : ∀ k, ι k} {a : Ω} {n : ℕ}
    {A : MRing (bundleIdx ι M) F} (h : IsChartForm (F := F) (M := M) y w φ t c a n A) (m : ℕ) :
    IsChartForm (F := F) (M := M) y w φ t c a (n + m) (A * chartMon F M c (fun _ => m)) := by
  refine ⟨?_, ?_⟩
  · have := h.1.mul (isMultiHomog_chartMon (F := F) (M := M) c (fun _ => m))
    rwa [← liftN_add] at this
  · rw [map_mul, h.2, projMap_chartMon]
    have e : (fun _ : K => n + m) = (fun _ => n) + (fun _ => m) := rfl
    rw [e, tMon_add]
    simp only [segreVec, pow_add, Finset.prod_pow, map_mul]
    ring

theorem exists_chartForm (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {a : Ω} (ha : a ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (A : MRing (bundleIdx ι M) F), IsChartForm (F := F) (M := M) y w φ t c a n A := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, chartMon F M j (fun _ => 1), ?_, ?_⟩
    · exact isMultiHomog_chartMon j _
    · rw [projMap_chartMon, div_mul_eq_mul_div, pow_one, mul_div_assoc, div_self hc, mul_one]
      simp [segreVec]
  | algebraMap r =>
    refine ⟨0, C r, ?_, ?_⟩
    · have e : liftN (fun _ : K => 0) = 0 := by funext o; cases o <;> rfl
      unfold IsMultiHomog
      rw [e]
      exact isWeightedHomogeneous_C _ _
    · rw [projMap_C]
      simp [tMon]
  | add x z _ _ hx hz =>
    obtain ⟨n₁, A₁, h₁⟩ := hx
    obtain ⟨n₂, A₂, h₂⟩ := hz
    have h₁' := h₁.pad n₂
    have h₂' := h₂.pad n₁
    rw [Nat.add_comm n₂ n₁] at h₂'
    refine ⟨n₁ + n₂, _, h₁'.1.add h₂'.1, ?_⟩
    rw [map_add (f := _), h₁'.2, h₂'.2, add_mul, map_add (f := _), C_add, add_mul]
  | mul x z _ _ hx hz =>
    obtain ⟨n₁, A₁, h₁⟩ := hx
    obtain ⟨n₂, A₂, h₂⟩ := hz
    refine ⟨n₁ + n₂, A₁ * A₂, ?_, ?_⟩
    · have := h₁.1.mul h₂.1
      rwa [← liftN_add] at this
    · rw [map_mul, h₁.2, h₂.2]
      have e : (fun _ : K => n₁ + n₂) = (fun _ => n₁) + (fun _ => n₂) := rfl
      rw [e, tMon_add, pow_add]
      simp only [map_mul]
      ring

theorem exists_chartForm_family (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {J : Type*} [Fintype J] (a : J → Ω) (ha : ∀ j, a j ∈ chartRing F (segreVec y) c) :
    ∃ n : ℕ, ∀ m, n ≤ m → ∀ j, ∃ A : MRing (bundleIdx ι M) F,
      IsChartForm (F := F) (M := M) y w φ t c (a j) m A := by
  choose n A hA using fun j => exists_chartForm (M := M) y w φ t c hc (ha j)
  refine ⟨∑ j, n j, fun m hm j => ?_⟩
  have hle : n j ≤ m := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hm
  have := (hA j).pad (m - n j)
  rw [Nat.add_sub_cancel' hle] at this
  exact ⟨_, this⟩

def chartZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℤ) : Ω := ∏ k, y ⟨k, c k⟩ ^ e k

theorem chartZ_add {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e e' : K → ℤ) :
    chartZ y c (e + e') = chartZ y c e * chartZ y c e' := by
  simp only [chartZ, Pi.add_apply, zpow_add₀ (hc _), Finset.prod_mul_distrib]

theorem chartZ_natCast (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (α : K → ℕ) :
    chartZ y c (fun k => (α k : ℤ)) = ∏ k, y ⟨k, c k⟩ ^ α k := by
  simp [chartZ]

theorem segreVec_pow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (n : ℕ) :
    segreVec y c ^ n = chartZ y c (fun _ => (n : ℤ)) := by
  simp [chartZ, segreVec, Finset.prod_pow]

theorem chartZ_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : K → ℤ) :
    chartZ y c e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)

theorem live_of_segreVec_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) :
    ∀ k, y ⟨k, c k⟩ ≠ 0 :=
  fun k => (Finset.prod_ne_zero_iff.mp hc) k (Finset.mem_univ k)

theorem segreVec_ne_zero_of_live {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    segreVec y c ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => hc k

theorem tMon_ne_zero (α : K → ℕ) : (tMon α : MvPolynomial (Option K) Φ) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (X_ne_zero _)

end FlagLineSectionProof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω] {F : Type*} [Field F]
  [Algebra F Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

theorem exists_adapted (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = chartZ y c (b i) := by
  have h : chartZ y c (b i) ∈ degLat F y (b i) c := ⟨1, one_mem _, by simp [chartZ]⟩
  rw [← hB.graded c hc i] at h
  obtain ⟨v, hv, h1, h2⟩ := h
  exact ⟨v, hv, h1, h2⟩

theorem exists_dual_first (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      ψ (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩) = 1 := by
  have hlive := live_of_segreVec_ne_zero hc
  choose e he hup hdiag using exists_adapted y B w b hB c hc
  have hm : ∀ i, chartZ y c (b i) ≠ 0 := fun i => chartZ_ne_zero hlive _
  have hspan : ∀ n : ℕ, ∀ i : Fin N, (i : ℕ) = n → w i ∈ Submodule.span Ω (Set.range e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have hsum := w.sum_repr (e i)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      have hrest : ∑ j ∈ Finset.univ.erase i, w.repr (e i) j • w j ∈
          Submodule.span Ω (Set.range e) := by
        refine Submodule.sum_mem _ fun j hj => ?_
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hlt | hgt
        · exact Submodule.smul_mem _ _ (ih j (by rw [← hi]; exact hlt) j rfl)
        · rw [hup i j hgt, zero_smul]
          exact Submodule.zero_mem _
      have hei : e i ∈ Submodule.span Ω (Set.range e) := Submodule.subset_span ⟨i, rfl⟩
      have h1 : w.repr (e i) i • w i ∈ Submodule.span Ω (Set.range e) := by
        rw [eq_sub_of_add_eq hsum]
        exact Submodule.sub_mem _ hei hrest
      rw [hdiag] at h1
      have h2 := Submodule.smul_mem _ (chartZ y c (b i))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ (hm i), one_smul] at h2
  have htop : ⊤ ≤ Submodule.span Ω (Set.range e) := by
    rw [← w.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hspan i i rfl
  have hcard : Fintype.card (Fin N) = Module.finrank Ω E := by
    rw [Module.finrank_eq_card_basis w]
  set eb := basisOfTopLeSpanOfCardEqFinrank e htop hcard with heb_def
  have heb : ∀ i, eb i = e i := fun i => by
    rw [heb_def, coe_basisOfTopLeSpanOfCardEqFinrank]
  set ψ : Module.Dual Ω E := eb.coord ⟨0, h0⟩ with hψ_def
  have hψe : ∀ i, ψ (e i) ∈ chartRing F (segreVec y) c := by
    intro i
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hint : ∀ n : ℕ, n ≤ N → ∀ v ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr v j = 0) →
      ψ v ∈ chartRing F (segreVec y) c := by
    intro n
    induction n with
    | zero =>
      intro _ v _ hv
      have : v = 0 := w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])
      simp [this]
    | succ n ih =>
      intro hn v hvB hv
      set i : Fin N := ⟨n, hn⟩ with hi_def
      have hmem : w.repr v i ∈ degLat F y (b i) c := by
        rw [← hB.graded c hc i]
        refine ⟨v, hvB, fun j hj => hv j ?_, rfl⟩
        rw [Fin.lt_def] at hj
        simp only [hi_def] at hj
        omega
      obtain ⟨α, hα, hαv⟩ := hmem
      have hv' : v - α • e i ∈ B.lat c := (B.lat c).sub_mem hvB (B.stable c α hα _ (he i))
      have hrec := ih (by omega) _ hv' (fun j hj => by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
        rcases Nat.lt_or_ge n (j : ℕ) with hlt | hge
        · rw [hv j (by omega), hup i j (by rw [Fin.lt_def]; exact hlt), mul_zero, sub_zero]
        · have hji : j = i := Fin.ext (by simp only [hi_def]; omega)
          rw [hji, hdiag, hαv]
          simp [chartZ])
      have hsplit : ψ v = ψ (v - α • e i) + α * ψ (e i) := by
        simp [map_sub, smul_eq_mul]
      rw [hsplit]
      exact add_mem hrec (mul_mem hα (hψe i))
  refine ⟨ψ, fun v hv => hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)), ?_⟩
  have he0 : e ⟨0, h0⟩ = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩ := by
    conv_lhs => rw [← w.sum_repr (e ⟨0, h0⟩)]
    rw [Finset.sum_eq_single ⟨0, h0⟩]
    · rw [hdiag]
    · intro j _ hj
      rw [hup _ j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]
    · simp
  have h1 : ψ (e ⟨0, h0⟩) = 1 := by
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  rw [he0, map_smul, smul_eq_mul] at h1
  rw [mul_comm]
  exact h1

theorem chart_data (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) {M : ℕ}
    (a : K → ℤ) (φ : Fin M → Module.Dual Ω E) (hφ : IsTwistedDualGens y B a φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    (∀ l, φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) ∈ chartRing F (segreVec y) c) ∧
      ∃ v : Fin M → Ω, (∀ l, v l ∈ chartRing F (segreVec y) c) ∧
        ∑ l, v l * (φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a)) = 1 := by
  have hlive := live_of_segreVec_ne_zero hc
  have hsplit : chartZ y c (b ⟨0, h0⟩ - a) = chartZ y c (b ⟨0, h0⟩) * chartZ y c (-a) := by
    rw [sub_eq_add_neg, chartZ_add hlive]
  have hinv : chartZ y c a * chartZ y c (-a) = 1 := by
    rw [← chartZ_add hlive, add_neg_cancel]
    simp [chartZ]
  refine ⟨fun l => ?_, ?_⟩
  · obtain ⟨v0, hv0, hup, hdiag⟩ := exists_adapted y B w b hB c hc ⟨0, h0⟩
    have hv0eq : v0 = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩ := by
      conv_lhs => rw [← w.sum_repr v0]
      rw [Finset.sum_eq_single ⟨0, h0⟩]
      · rw [hdiag]
      · intro j _ hj
        rw [hup j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]
      · simp
    obtain ⟨α, hα, hαe⟩ := hφ.sections c hc l v0 hv0
    rw [hv0eq, map_smul, smul_eq_mul] at hαe
    have hαe' : chartZ y c (b ⟨0, h0⟩) * φ l (w ⟨0, h0⟩) = α * chartZ y c a := hαe
    have : φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) = α := by
      rw [hsplit]
      linear_combination chartZ y c (-a) * hαe' + α * hinv
    rw [this]
    exact hα
  · obtain ⟨ψ, hψ, hψ1⟩ := exists_dual_first y B w b hB c hc h0
    obtain ⟨u, hu, hψeq⟩ := hφ.generate c hc ψ hψ
    refine ⟨u, hu, ?_⟩
    have h := LinearMap.congr_fun hψeq (w ⟨0, h0⟩)
    rw [LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    rw [← hψ1, h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsplit]
    simp only [chartZ, Pi.neg_apply]
    ring

end FlagLineSectionProof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F] {M : ℕ}

theorem chartMon_not_mem {W : Ideal (MRing (bundleIdx ι M) F)} [hW : W.IsPrime] {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ∉ W) (α : K → ℕ) :
    chartMon F M c α ∉ W := by
  unfold chartMon
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, _, hk⟩
  exact hc k (hW.mem_of_pow_mem _ hk)

end FlagLineSectionProof


open FlagLineSectionProof in
theorem FlagLineSection.proof : FlagLineSection.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hy _ N E _ _ B w b hB M a φ hφ Φ _ _ t ht h0
  have hXn : ∀ l : Fin M, projMap F y w φ (truncCoord t 1) (X ⟨none, l⟩) =
      C (t ⟨0, h0⟩ * algebraMap Ω Φ (φ l (w ⟨0, h0⟩))) * X none := by
    intro l
    rw [projMap_X_none, sum_truncCoord_one t h0]
  have ht0 : t ⟨0, h0⟩ ≠ 0 := fun h => ht.transcendental ⟨0, h0⟩ (h ▸ isAlgebraic_zero)

  have hyne : ∀ k (i : ι k), (X ⟨k, i⟩ : MRing ι F) ∉ pointIdeal F y → y ⟨k, i⟩ ≠ 0 := by
    intro k i hX h
    apply hX
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h]
  choose c0 hc0 using hy.relevant
  have live0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k => hyne k _ (hc0 k)
  have hs0 := segreVec_ne_zero_of_live live0
  obtain ⟨hξ0, v0, -, hsum0⟩ := chart_data y B w b hB a φ hφ c0 hs0 h0
  obtain ⟨l0, hl0⟩ : ∃ l0, φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at hsum0
  have hu0 : φ l0 (w ⟨0, h0⟩) ≠ 0 := left_ne_zero_of_mul hl0
  obtain ⟨n0, A0, hA0⟩ := exists_chartForm (M := M) y w φ (truncCoord t 1) c0 hs0 (hξ0 l0)
  obtain ⟨p, q, hpq⟩ : ∃ p q : K → ℕ, ∀ k, (p k : ℤ) - q k = -(b ⟨0, h0⟩ k - a k) - n0 :=
    ⟨fun k => (-(b ⟨0, h0⟩ k - a k) - n0).toNat, fun k => (-(-(b ⟨0, h0⟩ k - a k) - n0)).toNat,
      fun k => Int.toNat_sub_toNat_neg _⟩
  have hfval : projMap F y w φ (truncCoord t 1) (X ⟨none, l0⟩ * chartMon F M c0 q) =
      C (t ⟨0, h0⟩ * algebraMap Ω Φ (φ l0 (w ⟨0, h0⟩))) * X none *
        (C (algebraMap Ω Φ (∏ k, y ⟨k, c0 k⟩ ^ q k)) * tMon q) := by
    rw [map_mul, hXn, projMap_chartMon]
  have hgval : projMap F y w φ (truncCoord t 1) (A0 * chartMon F M c0 p) =
      C (algebraMap Ω Φ (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0)) *
        tMon (fun _ => n0) * (C (algebraMap Ω Φ (∏ k, y ⟨k, c0 k⟩ ^ p k)) * tMon p) := by
    rw [map_mul, hA0.2, projMap_chartMon]
  have hprod0 : ∀ r : K → ℕ, ∏ k, y ⟨k, c0 k⟩ ^ r k ≠ 0 :=
    fun r => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (live0 k)
  refine ⟨Pi.single none 1 + liftN q, liftN (fun _ => n0) + liftN p,
    X ⟨none, l0⟩ * chartMon F M c0 q, A0 * chartMon F M c0 p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isMultiHomog_X_none l0).mul (isMultiHomog_chartMon c0 q)
  · exact hA0.1.mul (isMultiHomog_chartMon c0 p)
  · rw [mem_projIdeal_iff, hfval]
    refine mul_ne_zero (mul_ne_zero ?_ (X_ne_zero _)) (mul_ne_zero ?_ (tMon_ne_zero q))
    · rw [Ne, C_eq_zero]
      exact mul_ne_zero ht0 ((map_ne_zero _).mpr hu0)
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (hprod0 q)
  · rw [mem_projIdeal_iff, hgval]
    refine mul_ne_zero (mul_ne_zero ?_ (tMon_ne_zero _)) (mul_ne_zero ?_ (tMon_ne_zero p))
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (mul_ne_zero hl0 (pow_ne_zero _ hs0))
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (hprod0 p)
  · funext o
    cases o with
    | none => simp [liftN, zetaDeg, liftDeg]
    | some k =>
      have := hpq k
      simp [liftN, zetaDeg, liftDeg]
      linarith
  · funext W
    show divCycle _ _ W - divCycle _ _ W = 0
    by_cases hW : W.IsPrime ∧ projIdeal F y w φ (truncCoord t 1) ≤ W ∧ IsRelevant W
    · obtain ⟨hWp, hPW, hWrel⟩ := hW
      choose cc hcc using fun k => hWrel (some k)
      let c : ∀ k, ι k := cc
      have hcW : ∀ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ∉ W := hcc
      obtain ⟨l1, hl1⟩ : ∃ l1 : Fin M, (X ⟨none, l1⟩ : MRing (bundleIdx ι M) F) ∉ W := hWrel none
      have live : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
        intro k h
        apply hcW k
        apply hPW
        rw [mem_projIdeal_iff, projMap_X_some, h, map_zero, C_0, zero_mul]
      have hs := segreVec_ne_zero_of_live live
      obtain ⟨hξ, vc, hvc, hsumc⟩ := chart_data y B w b hB a φ hφ c hs h0
      obtain ⟨nξ, hnξ⟩ := exists_chartForm_family (M := M) y w φ (truncCoord t 1) c hs _ hξ
      obtain ⟨nv, hnv⟩ := exists_chartForm_family (M := M) y w φ (truncCoord t 1) c hs _ hvc
      set m := nξ + nv with hm
      choose Ξ hΞ using hnξ m (by omega)
      choose V hV using hnv m (by omega)
      have htm : (tMon (fun _ : K => m + m) : MvPolynomial (Option K) Φ) =
          tMon (fun _ => m) * tMon (fun _ => m) := tMon_add (fun _ => m) (fun _ => m)
      have hR0 : ∑ l, V l * Ξ l - chartMon F M c (fun _ => m + m) ∈ projIdeal F y w φ (truncCoord t 1) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [mem_projIdeal_iff, map_sub, map_sum, projMap_chartMon, htm, sub_eq_zero]
        have e1 : ∀ l, projMap F y w φ (truncCoord t 1) (V l * Ξ l) =
            C (algebraMap Ω Φ (vc l * (φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a)))) *
              (C (algebraMap Ω Φ (segreVec y c ^ (m + m))) * (tMon (fun _ => m) * tMon (fun _ => m))) := by
          intro l
          rw [map_mul, (hV l).2, (hΞ l).2]
          simp only [map_mul, map_pow, pow_add]
          ring
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_congr rfl (fun l _ => e1 l), ← Finset.sum_mul, ← map_sum, ← map_sum, hsumc,
          map_one, map_one, one_mul]
        simp [segreVec, Finset.prod_pow]
      have hS : chartMon F M c (fun _ => m + m) ∉ W := chartMon_not_mem hcW _
      obtain ⟨l2, hl2⟩ : ∃ l2, Ξ l2 ∉ W := by
        by_contra hcon
        push Not at hcon
        have hsumW : ∑ l, V l * Ξ l ∈ W := Ideal.sum_mem _ fun l _ => W.mul_mem_left _ (hcon l)
        apply hS
        have := W.sub_mem hsumW (hPW hR0)
        rwa [sub_sub_cancel] at this
      have hR1 : X ⟨none, l1⟩ * Ξ l2 - X ⟨none, l2⟩ * Ξ l1 ∈ projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_mul, map_mul, hXn, hXn, (hΞ l2).2, (hΞ l1).2, sub_eq_zero]
        simp only [map_mul]
        ring
      have h12 : X ⟨none, l1⟩ * Ξ l2 ∉ W := fun h => (hWp.mem_or_mem h).elim hl1 hl2
      have h21 : X ⟨none, l2⟩ * Ξ l1 ∉ W := fun h => h12 (by
        have := W.add_mem (hPW hR1) h
        rwa [sub_add_cancel] at this)
      have hx2 : (X ⟨none, l2⟩ : MRing (bundleIdx ι M) F) ∉ W := fun h => h21 (W.mul_mem_right _ h)
      obtain ⟨α, β, hαβ⟩ : ∃ α β : K → ℕ, ∀ k, (β k : ℤ) - α k = m + (b ⟨0, h0⟩ k - a k) :=
        ⟨fun k => (-(m + (b ⟨0, h0⟩ k - a k))).toNat, fun k => (m + (b ⟨0, h0⟩ k - a k)).toNat,
          fun k => Int.toNat_sub_toNat_neg _⟩
      have hne1 : Ξ l2 * chartMon F M c α ∉ W :=
        fun h => (hWp.mem_or_mem h).elim hl2 (chartMon_not_mem hcW α)
      have hne2 : X ⟨none, l2⟩ * chartMon F M c β ∉ W :=
        fun h => (hWp.mem_or_mem h).elim hx2 (chartMon_not_mem hcW β)
      have hT : (tMon (fun _ => m) * tMon α * tMon q : MvPolynomial (Option K) Φ) =
          tMon β * tMon (fun _ => n0) * tMon p := by
        rw [← tMon_add, ← tMon_add, ← tMon_add, ← tMon_add]
        congr 1
        funext k
        have h1 := hαβ k
        have h2 := hpq k
        simp only [Pi.add_apply]
        omega
      have hc1 : chartZ y c (b ⟨0, h0⟩ - a) * segreVec y c ^ m * ∏ k, y ⟨k, c k⟩ ^ α k =
          ∏ k, y ⟨k, c k⟩ ^ β k := by
        rw [segreVec_pow, ← chartZ_natCast, ← chartZ_natCast, ← chartZ_add live, ← chartZ_add live]
        congr 1
        funext k
        have h1 := hαβ k
        simp only [Pi.add_apply, Pi.sub_apply]
        omega
      have hc0 : chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0 * ∏ k, y ⟨k, c0 k⟩ ^ p k =
          ∏ k, y ⟨k, c0 k⟩ ^ q k := by
        rw [segreVec_pow, ← chartZ_natCast, ← chartZ_natCast, ← chartZ_add live0, ← chartZ_add live0]
        congr 1
        funext k
        have h2 := hpq k
        simp only [Pi.add_apply, Pi.sub_apply]
        omega
      have hΩ : φ l2 (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) * segreVec y c ^ m *
            (∏ k, y ⟨k, c k⟩ ^ α k) * φ l0 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c0 k⟩ ^ q k) =
          φ l2 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c k⟩ ^ β k) *
            (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0) *
            (∏ k, y ⟨k, c0 k⟩ ^ p k) := by
        rw [← hc1, ← hc0]
        ring
      have hcross : (Ξ l2 * chartMon F M c α) * (X ⟨none, l0⟩ * chartMon F M c0 q) -
          (X ⟨none, l2⟩ * chartMon F M c β) * (A0 * chartMon F M c0 p) ∈
            projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_mul (projMap F y w φ (truncCoord t 1)) (Ξ l2 * _),
          map_mul (projMap F y w φ (truncCoord t 1)) (X ⟨none, l2⟩ * _), hfval, hgval,
          map_mul (projMap F y w φ (truncCoord t 1)) (Ξ l2),
          map_mul (projMap F y w φ (truncCoord t 1)) (X ⟨none, l2⟩), (hΞ l2).2, hXn, projMap_chartMon, projMap_chartMon, sub_eq_zero]
        calc _ = C (t ⟨0, h0⟩) * C (algebraMap Ω Φ (φ l2 (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) *
                segreVec y c ^ m * (∏ k, y ⟨k, c k⟩ ^ α k) * φ l0 (w ⟨0, h0⟩) *
                (∏ k, y ⟨k, c0 k⟩ ^ q k))) * X none * (tMon (fun _ => m) * tMon α * tMon q) := by
              simp only [map_mul]
              ring
          _ = C (t ⟨0, h0⟩) * C (algebraMap Ω Φ (φ l2 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c k⟩ ^ β k) *
                (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0) *
                (∏ k, y ⟨k, c0 k⟩ ^ p k))) * X none * (tMon β * tMon (fun _ => n0) * tMon p) := by
              rw [hΩ, hT]
          _ = _ := by
              simp only [map_mul]
              ring
      rw [divCycle_eq_of_mul_sub_mem hne1 hne2 hcross, sub_self]
    · have hz : ∀ h, divCycle (projIdeal F y w φ (truncCoord t 1)) h W = 0 := by
        intro h
        by_contra hne
        exact hW (le_and_isRelevant_of_divCycle_ne_zero hne)
      rw [hz, hz, sub_self]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
