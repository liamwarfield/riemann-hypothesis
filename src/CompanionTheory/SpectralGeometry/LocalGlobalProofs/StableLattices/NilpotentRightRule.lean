module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.SmInfUnitary

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRule
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRule
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RightRule

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec

variable {n : ℕ}

def RightOK (ε : Fin n → Bool) (X : GMod n) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) : Prop :=
  ∀ (u : X.V) (Y : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Y → ∀ g, Formalism.REAL.inUJ ε g →
    HasDerivAt (fun t : ℝ => c u (g * NormedSpace.exp ((t : ℂ) • Y))) (c (∑ a, ∑ b, Y a b • X.E a b u) g) 0

set_option backward.isDefEq.respectTransparency false in
theorem exp_entry (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y) i j) (Y i j) 0 := by
  have e1 : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y) i j) =
      fun t : ℝ => Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp (t • Y)) := by
    funext t
    have : (t : ℂ) • Y = t • Y := by ext a b; simp [Complex.real_smul]
    rw [this]; rfl
  have e2 : Y i j = Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp ((0 : ℝ) • Y) * Y) := by
    simp [NormedSpace.exp_zero]
  rw [e1, e2]
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0)

theorem mul_exp_entry (g Y : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • Y)) j i) ((g * Y) j i) 0 := by
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => g j l * NormedSpace.exp ((t : ℂ) • Y) l i)
    fun l _ => (exp_entry Y l i).const_mul (g j l)

theorem mul_exp_zero (g Y : Matrix (Fin n) (Fin n) ℂ) : g * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = g := by
  simp [NormedSpace.exp_zero]

theorem tens_action (X : GMod n) (Y : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → X.V) (i : Fin n) :
    (∑ a, ∑ b, Y a b • (tens X).E a b u) i = (∑ a, ∑ b, Y a b • X.E a b (u i)) + ∑ b, Y i b • u b := by
  show (∑ a, ∑ b, (Y a b • tensE X a b u : Fin n → X.V)) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, tensE_apply, smul_add, sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
  simp

theorem tens_ok {ε : Fin n → Bool} {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (h : RightOK ε X c) (j : Fin n) : RightOK ε (tens X) (tensCoef X c j) := by
  intro u Y hY g hg
  have h1 : ∀ i, HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • Y)) j i *
      c (u i) (g * NormedSpace.exp ((t : ℂ) • Y)))
      ((g * Y) j i * c (u i) g + g j i * c (∑ a, ∑ b, Y a b • X.E a b (u i)) g) 0 := by
    intro i
    refine ((mul_exp_entry g Y j i).fun_mul (h (u i) Y hY g hg)).congr_deriv ?_
    simp only [mul_exp_zero]
  have h2 := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun i (t : ℝ) => (g * NormedSpace.exp ((t : ℂ) • Y)) j i * c (u i) (g * NormedSpace.exp ((t : ℂ) • Y)))
    fun i _ => h1 i
  refine h2.congr_deriv ?_
  have e : ∀ i, c ((∑ a, ∑ b, Y a b • (tens X).E a b u) i) g =
      c (∑ a, ∑ b, Y a b • X.E a b (u i)) g + ∑ b, Y i b * c (u b) g := by
    intro i
    refine (congrArg (fun v => c v g) (tens_action X Y u i)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), Pi.add_apply, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  show _ = ∑ i, g j i * c ((∑ a, ∑ b, Y a b • (tens X).E a b u) i) g
  refine Eq.trans ?_ (sum_congr rfl fun i _ => congrArg (g j i * ·) (e i).symm)
  simp only [mul_add, sum_add_distrib, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem step_ok {ε : Fin n → Bool} {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (h : RightOK ε X c) (z : ℂ) (j : Fin n) : RightOK ε (step X z) (stepCoef X z c j) := by
  intro u Y hY g hg
  let S : (step X z).V →ₗ[ℂ] (tens X).V := (stepSub X z).subtype
  have hS : ∀ a b w, S ((step X z).E a b w) = (tens X).E a b (S w) := fun _ _ _ => rfl
  have e : S (∑ a, ∑ b, Y a b • (step X z).E a b u) = ∑ a, ∑ b, Y a b • (tens X).E a b (S u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hS]
  have h1 := tens_ok h j (S u) Y hY g hg
  refine h1.congr_deriv ?_
  show tensCoef X c j _ g = tensCoef X c j (S _) g
  rw [e]

theorem path_ok {ε : Fin n → Bool} : ∀ (ss : List (Fin n)) (X : GMod n)
    (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (χ : Fin n → ℂ) (js : List (Fin n)),
    RightOK ε X c → RightOK ε (path X χ ss) (pathCoef X c χ ss js)
  | [], _, _, _, _, h => h
  | s :: ss, X, c, χ, js, h => path_ok ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail
      (step_ok h _ _)

theorem base_ok {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (ξ : H) :
    RightOK ε ⟨D, E, hK.gl⟩ (baseCoef σ D ξ) := by
  intro u Y hY g hg
  let L : H →L[ℝ] ℂ := ((innerSL ℂ ξ).comp (σ g)).restrictScalars ℝ
  have h1 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hK.real Y hY u)
  have e : (fun t : ℝ => baseCoef σ D ξ u (g * NormedSpace.exp ((t : ℂ) • Y))) =
      L ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H) := by
    funext t
    show ⟪ξ, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (u : H)⟫_ℂ = ⟪ξ, σ g (σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H))⟫_ℂ
    rw [hσ.1.2 g hg _ (Formalism.REAL.exp_indefinite_unitary_holds n ε Y hY t)]
    rfl
  rw [e]
  refine h1.congr_deriv ?_
  show ⟪ξ, σ g (∑ a, ∑ b, Y a b • (E a b u : H))⟫_ℂ = ⟪ξ, σ g ((∑ a, ∑ b, Y a b • E a b u : D) : H)⟫_ℂ
  simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem rightRule : CompanionTheory.RgExh.Dec.N.RightRule := by
  intro n ε H _ _ _ σ D E hK χ ss hσ i u X hX g hg
  exact path_ok ss ⟨D, E, hK.gl⟩ (baseCoef σ D (i.1 : H)) χ i.2 (base_ok hK hσ _) u X hX g hg

end GlobalTheory.CompanionTheory.RightRule
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRuleStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.NilpotentRightRule : CompanionTheory.RgExh.Dec.N.RightRule := by
  first | exact @GlobalTheory.CompanionTheory.RightRule.rightRule | exact GlobalTheory.CompanionTheory.RightRule.rightRule | (intros; apply GlobalTheory.CompanionTheory.RightRule.rightRule <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRule
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRule
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.PathCoef

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec

variable {n : ℕ}

def LeftAt (ε : Fin n → Bool) (X : GMod n) {ι : Type}
    (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (i : ι) : Prop :=
  ∃ l : Fin n → Fin n → ι →₀ ℂ, ∀ (a b : Fin n) (u : X.V) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
    c i (X.E a b u) g = ∑ p, ∑ q, (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) p q *
      (l p q).sum fun i' r => r * c i' u g

theorem sum_mapDomain_mul {ι κ : Type} (f : κ → ι) (l : κ →₀ ℂ) (w : ι → ℂ) :
    ((l.mapDomain f).sum fun i r => r * w i) = l.sum fun q r => r * w (f q) :=
  Finsupp.sum_mapDomain_index (by simp) (by intros; ring)

theorem sum_weighted {ι κ : Type} [Fintype κ] (l : ι →₀ ℂ) (w : κ → ℂ) (f : κ → ι → ℂ) :
    ∑ k, w k * (l.sum fun x r => r * f k x) = l.sum fun x r => r * ∑ k, w k * f k x := by
  simp only [Finsupp.sum, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun k _ => by ring

theorem LeftAt.reindex {ε : Fin n → Bool} {X : GMod n} {ι κ : Type}
    {c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} {c' : κ → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (f : κ → ι) (hf : ∀ q, c (f q) = c' q) {i : ι} {k : κ} (hk : c i = c' k) (h : LeftAt ε X c' k) :
    LeftAt ε X c i := by
  obtain ⟨l, hl⟩ := h
  refine ⟨fun p q => (l p q).mapDomain f, fun a b u g hg => ?_⟩
  rw [hk, hl a b u g hg]
  simp only [sum_mapDomain_mul, hf]

theorem left_tens {ε : Fin n → Bool} (X : GMod n) {ι : Type}
    (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (h : ∀ i, LeftAt ε X c i) (q : ι × Fin n) :
    LeftAt ε (tens X) (fun q : ι × Fin n => tensCoef X (c q.1) q.2) q := by
  obtain ⟨p, j⟩ := q
  obtain ⟨l, hl⟩ := h p
  refine ⟨fun s t => (l s t).mapDomain (fun i' => (i', j)) +
    (if s = j then Finsupp.single (p, t) 1 else 0), fun a b (u : Fin n → X.V) g hg => ?_⟩
  have hgi : g⁻¹ * g = 1 := ReciprocityTheory.ChartRestriction.DS.Lap.Base.inv_mul_self_of_mem_indefiniteUnitary (ε := ε) hg
  have hMg : (g * Matrix.single a b (1 : ℂ) * g⁻¹) * g = g * Matrix.single a b (1 : ℂ) := by
    rw [Matrix.mul_assoc _ g⁻¹ g, hgi, Matrix.mul_one]
  generalize hM : (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) = M at hMg
  have hT : ∀ (i : ι) (m : Fin n), tensCoef X (c i) m u g = ∑ k, g m k * c i (u k) g := fun _ _ => rfl
  have e1 : ∀ s t, (((l s t).mapDomain (fun i' => (i', j)) +
      (if s = j then Finsupp.single (p, t) 1 else 0) : (ι × Fin n) →₀ ℂ).sum
        fun i' r => r * tensCoef X (c i'.1) i'.2 u g) =
      ((l s t).sum fun i' r => r * ∑ k, g j k * c i' (u k) g) +
        if s = j then ∑ k, g t k * c p (u k) g else 0 := by
    intro s t
    rw [Finsupp.sum_add_index' (by simp) (by intros; ring), sum_mapDomain_mul]
    simp only [hT]
    congr 1
    split_ifs
    · rw [Finsupp.sum_single_index (by simp), one_mul]
    · simp
  have eL : tensCoef X (c p) j ((tens X).E a b u) g =
      ∑ k, g j k * c p (X.E a b (u k)) g + g j a * c p (u b) g := by
    show ∑ k, g j k * c p (tensE X a b u k) g = _
    simp only [tensE_apply, map_add (f := _), Pi.add_apply, mul_add, sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have eA : ∑ k, g j k * c p (X.E a b (u k)) g =
      ∑ s, ∑ t, M s t * ((l s t).sum fun i' r => r * ∑ k, g j k * c i' (u k) g) := by
    simp only [hl a b _ g hg, hM, ← sum_weighted]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun t _ => sum_congr rfl fun k _ => by ring
  have eB : g j a * c p (u b) g = ∑ s, ∑ t, M s t * (if s = j then ∑ k, g t k * c p (u k) g else 0) := by
    rw [Finset.sum_eq_single j (fun s _ hs => by simp [hs]) (by simp)]
    simp only [if_true]
    have : ∑ t, M j t * ∑ k, g t k * c p (u k) g = ∑ k, (M * g) j k * c p (u k) g := by
      simp only [mul_sum, Matrix.mul_apply, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun t _ => by ring
    rw [this, hMg]
    rw [Finset.sum_eq_single b]
    · simp [Matrix.mul_apply, Matrix.single_apply]
    · intro k _ hk
      simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hk]
    · simp
  show tensCoef X (c p) j ((tens X).E a b u) g = ∑ s, ∑ t, M s t *
      (((l s t).mapDomain (fun i' => (i', j)) + (if s = j then Finsupp.single (p, t) 1 else 0) : (ι × Fin n) →₀ ℂ).sum
        fun i' r => r * tensCoef X (c i'.1) i'.2 u g)
  simp only [e1, mul_add, sum_add_distrib]
  rw [eL, eA, eB]

theorem left_step {ε : Fin n → Bool} (X : GMod n) (z : ℂ) {ι : Type}
    (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (h : ∀ i, LeftAt ε X c i) (q : ι × Fin n) :
    LeftAt ε (step X z) (fun q : ι × Fin n => stepCoef X z (c q.1) q.2) q := by
  obtain ⟨l, hl⟩ := left_tens X c h q
  exact ⟨l, fun a b u g hg => hl a b u.1 g hg⟩

theorem left_path {ε : Fin n → Bool} (ss : List (Fin n)) : ∀ (X : GMod n) (χ : Fin n → ℂ) {ι : Type}
    (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)), (∀ i, LeftAt ε X c i) →
    ∀ i : ι × List (Fin n), LeftAt ε (path X χ ss) (fun p : ι × List (Fin n) => pathCoef X (c p.1) χ ss p.2) i := by
  induction ss with
  | nil =>
    intro X χ ι c hc i
    exact LeftAt.reindex (X := X) (c := fun p : ι × List (Fin n) => c p.1) (c' := c)
      (fun k => (k, [])) (fun _ => rfl) (k := i.1) rfl (hc i.1)
  | cons s ss ih =>
    intro X χ ι c hc i
    have h2 := ih (step X (χ s)) (χ + Pi.single s 1) (fun q : ι × Fin n => stepCoef X (χ s) (c q.1) q.2)
      (left_step X (χ s) c hc) ((i.1, i.2.headD s), i.2.tail)
    show LeftAt ε (path (step X (χ s)) (χ + Pi.single s 1) ss) (fun p : ι × List (Fin n) =>
      pathCoef (step X (χ s)) (stepCoef X (χ s) (c p.1) (p.2.headD s)) (χ + Pi.single s 1) ss p.2.tail) i
    exact LeftAt.reindex (fun q : (ι × Fin n) × List (Fin n) => (q.1.1, q.1.2 :: q.2)) (fun _ => rfl) rfl h2

section Base

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Base

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem inner_deriv_skew (hσ : IsURepOn (UJset ε) σ) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) {ξ ξ' u u' : H}
    (hξ : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • -Y)) ξ) ξ' 0)
    (hu : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) u) u' 0) : ⟪ξ, u'⟫_ℂ = ⟪ξ', u⟫_ℂ := by
  have h1 := HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) ξ) hu
  have h2 := HasDerivAt.inner ℂ hξ (hasDerivAt_const (0 : ℝ) u)
  simp only [inner_zero_left, add_zero] at h1
  simp only [inner_zero_right, zero_add] at h2
  have e : (fun t : ℝ => ⟪ξ, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ) =
      fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • -Y)) ξ, u⟫_ℂ := by
    funext t
    have hm := exp_smul_mem_UJset hY t
    have hm' := exp_smul_mem_UJset (SmDerA.inG_neg hY) t
    have hone : NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • -Y) = 1 := by
      have hcomm : Commute ((t : ℂ) • Y) ((t : ℂ) • -Y) := by
        rw [smul_neg]; exact (Commute.refl _).neg_right
      rw [← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, add_neg_cancel, NormedSpace.exp_zero]
    have hw : σ (NormedSpace.exp ((t : ℂ) • Y)) (σ (NormedSpace.exp ((t : ℂ) • -Y)) ξ) = ξ := by
      rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hm _ hm', hone, hσ.1.1]
      rfl
    calc ⟪ξ, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ
        = ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) (σ (NormedSpace.exp ((t : ℂ) • -Y)) ξ),
            σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ := by rw [hw]
      _ = _ := isometry_inner_eq (hσ.2.1 _ hm) _ _
  rw [e] at h1
  exact h1.unique h2

theorem deriv_transport (hσ : IsURepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hX : inG ε X) {u u' : H} (hd : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) u) u' 0) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g u)) (σ g u') 0 := by
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have hm := exp_smul_mem_UJset (inG_conj_unitary hg hX) t
  have hmX := exp_smul_mem_UJset hX t
  have hc : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) = g * NormedSpace.exp ((t : ℂ) • X) * g⁻¹ := by
    rw [← Matrix.exp_conj g _ (isUnit_of_mem_indefiniteUnitary hg), Matrix.mul_smul, Matrix.smul_mul]
  show σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g u) = σ g (σ (NormedSpace.exp ((t : ℂ) • X)) u)
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hm g hg, hc, Matrix.mul_assoc _ g⁻¹ g,
    inv_mul_self_of_mem_indefiniteUnitary hg, Matrix.mul_one, hσ.1.2 g hg _ hmX]
  rfl

theorem conj_entry {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) (p q : Fin n) :
    (starRingEnd ℂ) (Y p q) = -((if ε p = ε q then 1 else -1) * Y q p) := by
  have h := congrFun (congrFun hY q) p
  have hs : star (Y p q) = (starRingEnd ℂ) (Y p q) := rfl
  simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, hs] at h
  cases hp : ε p <;> cases hq : ε q <;> simp [hp, hq] at h ⊢ <;>
    first | linear_combination h | linear_combination -h

theorem real_rule (hσ : IsURepOn (UJset ε) σ) (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (ξ u : D)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) :
    ⟪(ξ : H), σ g (∑ a, ∑ b, X a b • ((E a b u : D) : H))⟫_ℂ =
      ∑ p, ∑ q, (g * X * g⁻¹) p q * ((if ε p = ε q then 1 else -1) * ⟪((E q p ξ : D) : H), σ g u⟫_ℂ) := by
  have hY := inG_conj_unitary hg hX
  have h1 := hK.real (-(g * X * g⁻¹)) (SmDerA.inG_neg hY) ξ
  have h2 := deriv_transport hσ hg hX (hK.real X hX u)
  rw [inner_deriv_skew hσ hY h1 h2]
  simp only [sum_inner, inner_smul_left, Matrix.neg_apply, map_neg, conj_entry hY]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  have : (if ε q = ε p then (1 : ℂ) else -1) = if ε p = ε q then 1 else -1 := by simp only [eq_comm]
  rw [this]
  ring

theorem unit_rule (hσ : IsURepOn (UJset ε) σ) (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (ξ u : D)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (a b : Fin n) :
    ⟪(ξ : H), σ g ((E a b u : D) : H)⟫_ℂ =
      ∑ p, ∑ q, (g * Matrix.single a b (1 : ℂ) * g⁻¹) p q *
        ((if ε p = ε q then 1 else -1) * ⟪((E q p ξ : D) : H), σ g u⟫_ℂ) := by
  obtain ⟨X₁, X₂, h₁, h₂, hdec⟩ : ∃ X₁ X₂ : Matrix (Fin n) (Fin n) ℂ, inG ε X₁ ∧ inG ε X₂ ∧
      Matrix.single a b (1 : ℂ) = X₁ + Complex.I • X₂ :=
    ⟨_, _, SmDerA.inG_cpart1 ε _, SmDerA.inG_cpart2 ε _, SmDerA.cpart_decomp ε _⟩
  have hz : ∀ c d, X₁ c d + Complex.I * X₂ c d = Matrix.single a b (1 : ℂ) c d := by
    intro c d
    rw [hdec]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hv : ((E a b u : D) : H) = (∑ c, ∑ d, X₁ c d • ((E c d u : D) : H)) +
      Complex.I • ∑ c, ∑ d, X₂ c d • ((E c d u : D) : H) := by
    calc ((E a b u : D) : H) = ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • ((E c d u : D) : H) := by
          simp [Matrix.single_apply, ite_smul, ite_and]
      _ = ∑ c, ∑ d, (X₁ c d + Complex.I * X₂ c d) • ((E c d u : D) : H) := by simp only [hz]
      _ = _ := by simp only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
  have hM : g * Matrix.single a b (1 : ℂ) * g⁻¹ = g * X₁ * g⁻¹ + Complex.I • (g * X₂ * g⁻¹) := by
    rw [hdec, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hv, map_add (f := _), map_smul, inner_add_right, inner_smul_right, real_rule hσ hK ξ u hg h₁,
    real_rule hσ hK ξ u hg h₂, hM]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring

theorem left_base (hσ : IsURepOn (UJset ε) σ) (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (ξ : D) :
    LeftAt ε ⟨D, E, hK.gl⟩ (fun ξ : D => baseCoef σ D (ξ : H)) ξ := by
  refine ⟨fun p q => Finsupp.single (E q p ξ) (if ε p = ε q then 1 else -1), fun a b u g hg => ?_⟩
  have h := unit_rule hσ hK ξ u hg a b
  simp only [Finsupp.sum_single_index, zero_mul]
  exact h

end Base

theorem leftRule : CompanionTheory.RgExh.Dec.N.LeftRule := by
  intro n ε H _ _ _ σ D E hK χ ss hσ i
  exact left_path ss ⟨D, E, hK.gl⟩ χ (fun ξ : D => baseCoef σ D (ξ : H)) (fun ξ => left_base hσ hK ξ) i

end GlobalTheory.CompanionTheory.PathCoef
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRuleStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.NilpotentLeftRule : CompanionTheory.RgExh.Dec.N.LeftRule := by
  first | exact @GlobalTheory.CompanionTheory.PathCoef.leftRule | exact GlobalTheory.CompanionTheory.PathCoef.leftRule | (intros; apply GlobalTheory.CompanionTheory.PathCoef.leftRule <;> assumption)
end
end
