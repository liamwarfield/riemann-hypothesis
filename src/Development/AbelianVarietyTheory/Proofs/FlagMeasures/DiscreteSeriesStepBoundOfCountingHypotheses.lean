module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOfMemLowKSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtOrbitTens
open Formalism.MainNotions.S NumberField GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.TensDer

theorem hasDerivAt_orbit_tens : ∀ (B : RowsAut) (E : gInf B) (u u' : ∀ v, B.H v), (∀ v, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v)) (u' v) 0) → (∀ v, B.σ v 1 = 1) → open Classical in HasDerivAt (orbit B E (B.tens u)) (∑ v, B.tens (Function.update u v (u' v))) 0 := by
  intro B E u u' hd h1
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  have hfun : orbit B E (B.tens u) =
      fun t => (m.restrictScalars ℝ) (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) := by
    funext t
    have := B.tens_spec.2.1
    rw [ContinuousMultilinearMap.coe_restrictScalars, hm]
    unfold orbit
    rw [this]
    congr 1
  have h0 : (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0) = u := by
    funext v
    simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]
  have hpi : HasDerivAt (fun t v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) u' 0 :=
    hasDerivAt_pi.2 hd
  have hF := (m.restrictScalars ℝ).hasFDerivAt (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0)
  have := hF.comp_hasDerivAt (0 : ℝ) hpi
  rw [hfun]
  rw [h0, ContinuousMultilinearMap.linearDeriv_apply] at this
  simp only [ContinuousMultilinearMap.coe_restrictScalars, Function.comp_def, hm] at this ⊢
  exact this

end GlobalTheory.TensDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepSpacePropsOfDiff
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepSpaceProps
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.StepLoc

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem kset_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  have h1 : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hg.1
    simpa [Matrix.star_eq_conjTranspose] using this
  unfold inUJ
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem inG_conj {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) :
    inG ε (g * X * gᴴ) := by
  have h2 : gᴴ * Jm ε = Jm ε * gᴴ := by
    have := congrArg Matrix.conjTranspose hg.2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at this
    exact this.symm
  unfold inG at *
  calc (g * X * gᴴ)ᴴ * Jm ε + Jm ε * (g * X * gᴴ)
      = g * Xᴴ * (gᴴ * Jm ε) + (Jm ε * g) * X * gᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = g * (Xᴴ * Jm ε + Jm ε * X) * gᴴ := by
        rw [h2, ← hg.2]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX]; simp

theorem exp_conj_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    NormedSpace.exp (t • (g * X * gᴴ)) * g = g * NormedSpace.exp (t • X) := by
  have h1 : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hg
    simpa [Matrix.star_eq_conjTranspose] using this
  have hi : g⁻¹ = gᴴ := Matrix.inv_eq_left_inv h1
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse h1)
  have : t • (g * X * gᴴ) = g * (t • X) * g⁻¹ := by
    rw [hi]; simp
  rw [this, Matrix.exp_conj _ _ hu, hi, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem orbit_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) (w : H) :
    orbit σ (g * X * gᴴ) (σ g w) = fun t => σ g (orbit σ X w t) := by
  funext t
  have a1 := hσ.2 _ (exp_indefinite_unitary_holds n ε _ (inG_conj hg hX) t) g (kset_inUJ hg)
  have a2 := hσ.2 g (kset_inUJ hg) _ (exp_indefinite_unitary_holds n ε _ hX t)
  rw [exp_conj_mul hg.1, a2] at a1
  exact (congrArg (fun T : H →L[ℂ] H => T w) a1).symm

theorem dAct_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) {w : H}
    (hw : DifferentiableAt ℝ (orbit σ X w) 0) :
    dAct σ (g * X * gᴴ) (σ g w) = σ g (dAct σ X w) := by
  unfold dAct
  rw [orbit_conj hσ hg hX]
  exact (((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw.hasDerivAt).deriv

theorem dAct_add_smul {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {X : Matrix (Fin n) (Fin n) ℂ}
    {w w' : H} (hw : DifferentiableAt ℝ (orbit σ X w) 0) (hw' : DifferentiableAt ℝ (orbit σ X w') 0)
    (c : ℂ) : dAct σ X (w + c • w') = dAct σ X w + c • dAct σ X w' := by
  have : orbit σ X (w + c • w') = fun t => orbit σ X w t + c • orbit σ X w' t := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  exact (hw.hasDerivAt.fun_add (hw'.hasDerivAt.fun_const_smul c)).deriv

theorem dAct_zero (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) :
    dAct σ X 0 = 0 := by
  have : orbit σ X 0 = fun _ => 0 := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  simp

theorem lowKSub_stable (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv
  have : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) := by
    refine sSup_le fun S hS => ?_
    intro x hx
    exact (le_sSup hS : S ≤ lowKSub ε lam σ) (hS.2.1 g hg x hx)
  exact this hv

theorem dWord_mem {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {P : ℕ} {l : List (Matrix (Fin n) (Fin n) ℂ)} {u : H} (hl : l.length ≤ P) (hX : ∀ X ∈ l, inG ε X)
    (hu : u ∈ lowKSub ε lam σ) : dWord σ l u ∈ stepSpace ε lam σ P :=
  Submodule.subset_span ⟨l, u, hl, hX, hu, rfl⟩

theorem dWord_conj {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) (hd : ∀ P, ∀ w ∈ stepSpace ε lam σ P, IsDiffVec ε σ w)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) {u : H} (hu : u ∈ lowKSub ε lam σ)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hX : ∀ X ∈ l, inG ε X) :
    σ g (dWord σ l u) = dWord σ (l.map fun X => g * X * gᴴ) (σ g u) := by
  induction l with
  | nil => rfl
  | cons Y l ih =>
    have hl : ∀ X ∈ l, inG ε X := fun X h => hX X (List.mem_cons_of_mem _ h)
    have hY : inG ε Y := hX Y List.mem_cons_self
    change σ g (dAct σ Y (dWord σ l u)) =
      dAct σ (g * Y * gᴴ) (dWord σ (l.map fun X => g * X * gᴴ) (σ g u))
    rw [← ih hl, dAct_conj hσ hg hY (hd _ _ (dWord_mem le_rfl hl hu) Y hY)]

end GlobalTheory.StepLoc
end
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.StepLoc

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

theorem stepSpace_props_of_diff : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → (∀ P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec ε σ w) → ∀ P : ℕ, IsKStableOn ε σ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ (∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X w) (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w) 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ (P + 1)) ∧ ∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ w' ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ c : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (w + c • w') = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w + c • GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w' := by
  intro n ε H _ _ _ σ lam hU hd P
  have hσ : IsCRepOn (UJset ε) σ := hU.1
  refine ⟨?_, fun X hX w hw => ⟨(hd P w hw X hX).hasDerivAt, ?_⟩,
    fun X hX w hw w' hw' c => dAct_add_smul (hd P w hw X hX) (hd P w' hw' X hX) c⟩
  · intro g hg v hv
    have : stepSpace ε lam σ P ≤ (stepSpace ε lam σ P).comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, u, hl, hX, hu, rfl⟩
      change σ g (dWord σ l u) ∈ stepSpace ε lam σ P
      rw [dWord_conj hσ hd hg hu l hX]
      refine dWord_mem (by simpa using hl) ?_ (lowKSub_stable ε lam σ g hg u hu)
      intro Y hY
      obtain ⟨X, hXl, rfl⟩ := List.mem_map.mp hY
      exact inG_conj hg (hX X hXl)
    exact this hv
  · induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, u, hl, hl', hu, rfl⟩ := hv
      refine dWord_mem (l := X :: l) (by simpa using hl) ?_ hu
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | h
      · exact hX
      · exact hl' Y h
    | zero => rw [dAct_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have := dAct_add_smul (hd P x hx X hX) (hd P y hy X hX) 1
      rw [one_smul, one_smul] at this
      rw [this]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      have := dAct_add_smul (hd P 0 (Submodule.zero_mem _) X hX) (hd P x hx X hX) c
      rw [zero_add, dAct_zero, zero_add] at this
      rw [this]
      exact Submodule.smul_mem _ c ihx

end GlobalTheory.StepLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentiableAtOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VPSubOfLocalBound
open Formalism.MainNotions.S NumberField GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.StepTens

theorem dAct_tens_of_diff (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w)
    (P : ℕ) (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)) (u : ∀ v, B.H v)
    (hu : ∀ v, u v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    ∃ u' : ∀ v, B.H v, (∀ v, u' v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) (P + 1)) ∧
      dAct B (atPlace B v X) (B.tens u) = B.tens u' := by
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  have hloc := (GlobalTheory.StepLoc.stepSpace_props_of_diff B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (hU v)
    (hd v) P).2.1 X.1 X.2 (u v) (hu v)
  have h1 : ∀ v, B.σ v 1 = 1 := fun v => (hU v).1.1
  set y := GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X.1 (u v) with hy
  have hder : ∀ v', HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (atPlace B v X v').1 (u v'))
      ((Pi.single v y : ∀ v, B.H v) v') 0 := by
    intro v'
    by_cases h : v' = v
    · subst h
      simpa [atPlace] using hloc.1
    · have h0 : atPlace B v X v' = 0 := by
        simp [atPlace, h]
      rw [h0, Pi.single_eq_of_ne h]
      have : GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (0 : gLie (B.I.ε v')).1 (u v') = fun _ => u v' := by
        funext t
        simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]
      rw [this]
      exact hasDerivAt_const _ _
  have hT := (GlobalTheory.TensDer.hasDerivAt_orbit_tens B (atPlace B v X) u _ hder h1).deriv
  refine ⟨Function.update u v y, ?_, ?_⟩
  · intro v'
    by_cases h : v' = v
    · subst h
      simpa using hloc.2
    · rw [Function.update_of_ne h]
      exact GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ (Nat.le_succ P) (hu v')
  · unfold dAct
    rw [hT, Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]
    · intro v' _ h
      rw [Pi.single_eq_of_ne h, ← hm]
      exact m.map_coord_zero v' (by simp)
    · simp

theorem wordAct_tens_of_diff (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w)
    (u : ∀ v, B.H v) (hu : ∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v))
    (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) :
    ∃ u' : ∀ v, B.H v, (∀ v, u' v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) l.length) ∧
      wordAct B l (B.tens u) = B.tens u' := by
  induction l with
  | nil =>
    refine ⟨u, fun v => ?_, rfl⟩
    rw [List.length_nil, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_zero]
    exact hu v
  | cons X l ih =>
    obtain ⟨u', h1, h2⟩ := ih
    obtain ⟨u'', h3, h4⟩ := dAct_tens_of_diff B hU hd l.length X.1 X.2 u' h1
    refine ⟨u'', h3, ?_⟩
    rw [← h4, ← h2]
    rfl

theorem stepSpan_le_of_differentiable (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w) (P : ℕ) :
    ∀ w ∈ VP B P, ∃ (k : ℕ) (u : Fin k → ∀ v, B.H v),
      (∀ l v, u l v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) ∧ w = ∑ l, B.tens (u l) := by
  classical
  intro w hw
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, u, hl, hu, rfl⟩ := hx
    obtain ⟨u', h1, h2⟩ := wordAct_tens_of_diff B hU hd u hu l
    exact ⟨1, fun _ => u', fun _ v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ hl (h1 v), by simp [h2]⟩
  | zero => exact ⟨0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, u, hu, rfl⟩ := hx
    obtain ⟨k', u', hu', rfl⟩ := hy
    refine ⟨k + k', Fin.append u u', ?_, ?_⟩
    · intro l
      refine Fin.addCases (fun i => ?_) (fun i => ?_) l
      · simpa using hu i
      · simpa using hu' i
    · simp [Fin.sum_univ_add]
  | smul c x _ hx =>
    obtain ⟨k, u, hu, rfl⟩ := hx
    obtain ⟨v₀⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    refine ⟨k, fun l => Function.update (u l) v₀ (c • u l v₀), ?_, ?_⟩
    · intro l v
      by_cases h : v = v₀
      · subst h
        simpa using Submodule.smul_mem _ c (hu l v)
      · simpa [Function.update_of_ne h] using hu l v
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← hm, ← hm, m.map_update_smul, Function.update_eq_self]

end GlobalTheory.StepTens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormSqTensUpdate
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace GlobalTheory

theorem exists_gram_factor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {k : ℕ}
    (x : Fin k → E) : ∃ C : Fin k → Fin k → ℂ, ∀ l l',
      ⟪x l, x l'⟫_ℂ = ∑ r, (starRingEnd ℂ) (C r l) * C r l' := by
  have h := (Matrix.posSemidef_gram ℂ x).nonneg
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h
  refine ⟨fun r l => C r l, fun l l' => ?_⟩
  have := congrFun (congrFun hC l) l'
  simpa [Matrix.gram_apply, Matrix.mul_apply, Matrix.star_apply] using this

theorem exists_normSq_tens_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (tens : (∀ v, H v) → Hs)
    (ht : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (v₀ : ι) {k : ℕ}
    (u : Fin k → ∀ v, H v) :
    ∃ C : ({v // v ≠ v₀} → Fin k) → Fin k → ℂ, ∀ a : Fin k → H v₀,
      ‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 = ∑ r, ‖∑ l, C r l • a l‖ ^ 2 := by
  choose D hD using fun v : {v // v ≠ v₀} => exists_gram_factor (fun l => u l v.1)
  refine ⟨fun r l => ∏ v, D v (r v) l, fun a => ?_⟩
  have key : ∀ l l', ⟪tens (Function.update (u l) v₀ (a l)),
      tens (Function.update (u l') v₀ (a l'))⟫_ℂ =
      ∑ r : {v // v ≠ v₀} → Fin k,
        ⟪(∏ v, D v (r v) l) • a l, (∏ v, D v (r v) l') • a l'⟫_ℂ := by
    intro l l'
    rw [ht, Fintype.prod_eq_mul_prod_subtype_ne _ v₀]
    simp only [Function.update_self]
    have h1 : ∏ v : {v // v ≠ v₀}, ⟪Function.update (u l) v₀ (a l) v.1,
        Function.update (u l') v₀ (a l') v.1⟫_ℂ =
        ∏ v : {v // v ≠ v₀}, ∑ r, (starRingEnd ℂ) (D v r l) * D v r l' := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Function.update_of_ne v.2, Function.update_of_ne v.2, hD]
    rw [h1, Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [inner_smul_left, inner_smul_right, Finset.prod_mul_distrib, map_prod]
    ring
  have hc : ((‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 : ℝ) : ℂ) =
      ((∑ r : {v // v ≠ v₀} → Fin k, ‖∑ l, (∏ v, D v (r v) l) • a l‖ ^ 2 : ℝ) : ℂ) := by
    have hn : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E),
        ((‖z‖ ^ 2 : ℝ) : ℂ) = ⟪z, z⟫_ℂ := by
      intro E _ _ z
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [Complex.ofReal_sum, hn]
    simp only [hn, sum_inner, inner_sum, key]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
  exact_mod_cast hc

theorem sum_normSq_tens_update_le :
    ∀ (B : RowsAut) (v₀ : InfinitePlace B.I.F) (S : ∀ v, Submodule ℂ (B.H v)) (m : ℕ) (L : Fin m → (S v₀ →ₗ[ℂ] B.H v₀)) (β : ℝ), (∀ y : S v₀, ∑ i, ‖L i y‖ ^ 2 ≤ β * ‖y‖ ^ 2) → ∀ (k : ℕ) (u : Fin k → ∀ v, S v), open Classical in ∑ i, ‖∑ l, B.tens (Function.update (fun v => (u l v : B.H v)) v₀ (L i (u l v₀)))‖ ^ 2 ≤ β * ‖∑ l, B.tens (fun v => (u l v : B.H v))‖ ^ 2 := by
  classical
  intro B v₀ S m L β hL k u
  obtain ⟨C, hC⟩ := exists_normSq_tens_update B.tens B.tens_spec.1 v₀
    (fun l v => (u l v : B.H v))
  have h0 := hC (fun l => (u l v₀ : B.H v₀))
  have hu : ∀ l, Function.update (fun v => (u l v : B.H v)) v₀ (u l v₀ : B.H v₀) =
      fun v => (u l v : B.H v) := fun l => Function.update_eq_self v₀ _
  simp only [hu] at h0
  rw [h0, Finset.mul_sum]
  have h1 : ∀ i, _ := fun i => hC (fun l => L i (u l v₀))
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun r _ => ?_
  have := hL (∑ l, C r l • u l v₀)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul] at this
  refine this.trans_eq ?_
  rw [← Submodule.norm_coe]
  simp

end GlobalTheory
end

open Formalism.MainNotions.S NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace (stepSpace IsDiffVec IsONFamily stepConst)

noncomputable section

namespace GlobalTheory.StepGlob

theorem stepConst_eq (n : ℕ) (b : ℝ) (P : ℕ) : stepConst n b P = beP n b P := by
  unfold stepConst beP
  have h : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' (Nat.cast_nonneg n) (by norm_num), Real.rpow_one]
  rw [h, Real.sqrt_eq_rpow]

theorem beP_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ beP n b P := by
  unfold beP
  positivity

theorem finrank_of_isONBasis {n m : ℕ} {ε : Fin n → Bool} {E : Fin m → gLie ε} (h : IsONBasis E) :
    Module.finrank ℝ (gLie ε) = m := by
  have hli : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (fun X : gLie ε =>
      (((X : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc,
      Matrix.trace_smul, Complex.re_sum, Complex.smul_re, h.1] at h1
    simpa using h1
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli h.2.ge), Fintype.card_fin]

theorem card_of_isONBasis {n m : ℕ} {ε : Fin n → Bool} {E : Fin m → gLie ε} (h : IsONBasis E) :
    m = n ^ 2 := by
  obtain ⟨F, h1, h2, h3⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  have hF : IsONBasis (fun i => (⟨F i, (h1 i).1⟩ : gLie ε)) := by
    refine ⟨h2, ?_⟩
    rw [eq_top_iff]
    rintro ⟨X, hX⟩ -
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => ((X * (F i)ᴴ).trace).re, Subtype.ext ?_⟩
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    conv_rhs => rw [h3 X hX]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.coe_smul]
  rw [← finrank_of_isONBasis h, finrank_of_isONBasis hF]

variable (B : RowsAut)

theorem orbit_sum {k : ℕ} (E : gInf B) (y : Fin k → B.Hs) :
    orbit B E (∑ l, y l) = fun t => ∑ l, orbit B E (y l) t := by
  funext t
  simp [orbit]

theorem dAct_add_smul {E : gInf B} {w w' : B.Hs} (hw : DifferentiableAt ℝ (orbit B E w) 0)
    (hw' : DifferentiableAt ℝ (orbit B E w') 0) (c : ℂ) :
    dAct B E (w + c • w') = dAct B E w + c • dAct B E w' := by
  have : orbit B E (w + c • w') = fun t => orbit B E w t + c • orbit B E w' t := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  exact (hw.hasDerivAt.fun_add (hw'.hasDerivAt.fun_const_smul c)).deriv

theorem dAct_zero (E : gInf B) : dAct B E 0 = 0 := by
  have : orbit B E 0 = fun _ => 0 := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  simp

section Diff

variable {B} (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
  (hd : ∀ v P, ∀ w ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, IsDiffVec (B.I.ε v) (B.σ v) w)

include hU hd


open Classical in
theorem hasDerivAt_orbit_sum {P k : ℕ} (E : gInf B) (u : Fin k → ∀ v, B.H v)
    (hu : ∀ l v, u l v ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    HasDerivAt (orbit B E (∑ l, B.tens (u l)))
      (∑ l, ∑ v, B.tens (Function.update (u l) v
        (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) (E v).1 (u l v)))) 0 := by
  rw [orbit_sum]
  refine HasDerivAt.fun_sum fun l _ => ?_
  exact GlobalTheory.TensDer.hasDerivAt_orbit_tens B E (u l) _
    (fun v => (hd v P _ (hu l v) _ (E v).2).hasDerivAt) (fun v => (hU v).1.1)


open Classical in
theorem dAct_atPlace_sum {P k : ℕ} (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v))
    (u : Fin k → ∀ v, B.H v) (hu : ∀ l v, u l v ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    dAct B (atPlace B v X) (∑ l, B.tens (u l)) =
      ∑ l, B.tens (Function.update (u l) v (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X.1 (u l v))) := by
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  unfold dAct
  rw [(hasDerivAt_orbit_sum hU hd (atPlace B v X) u hu).deriv]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single v]
  · simp [atPlace]
  · intro v' _ h
    have h0 : atPlace B v X v' = 0 := by simp [atPlace, h]
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (0 : gLie (B.I.ε v')).1 (u l v') = fun _ => u l v' := by
      funext t
      simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, (hU v').1.1]
    rw [h0, ← hm]
    refine m.map_coord_zero v' ?_
    rw [Function.update_self, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct, h1]
    simp
  · simp

open Classical in
theorem dAct_atPlace_tens {P : ℕ} (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v))
    (u : ∀ v, B.H v) (hu : ∀ v, u v ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    dAct B (atPlace B v X) (B.tens u) =
      B.tens (Function.update u v (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X.1 (u v))) := by
  simpa using dAct_atPlace_sum hU hd (k := 1) v X (fun _ => u) (fun _ => hu)

theorem differentiableAt_orbit {P : ℕ} (E : gInf B) {w : B.Hs} (hw : w ∈ VP B P) :
    DifferentiableAt ℝ (orbit B E w) 0 := by
  obtain ⟨k, u, hu, rfl⟩ := GlobalTheory.StepTens.stepSpan_le_of_differentiable B hU hd P w hw
  exact (hasDerivAt_orbit_sum hU hd E u hu).differentiableAt

theorem dAct_eq_sum {P : ℕ} (E : gInf B) {w : B.Hs} (hw : w ∈ VP B P) :
    dAct B E w = ∑ v, dAct B (atPlace B v (E v)) w := by
  obtain ⟨k, u, hu, rfl⟩ := GlobalTheory.StepTens.stepSpan_le_of_differentiable B hU hd P w hw
  simp only [dAct_atPlace_sum hU hd _ _ u hu]
  rw [Finset.sum_comm]
  exact (hasDerivAt_orbit_sum hU hd E u hu).deriv

theorem dAct_mem {P : ℕ} (E : gInf B) {w : B.Hs} (hw : w ∈ VP B P) : dAct B E w ∈ VP B (P + 1) := by
  rw [dAct_eq_sum hU hd E hw]
  refine Submodule.sum_mem _ fun v _ => ?_
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, u, hl, hu, rfl⟩ := hx
    exact Submodule.subset_span ⟨⟨v, E v⟩ :: l, u, by simpa using hl, hu, rfl⟩
  | zero => rw [dAct_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    have := dAct_add_smul B (differentiableAt_orbit hU hd (atPlace B v (E v)) hx)
      (differentiableAt_orbit hU hd (atPlace B v (E v)) hy) 1
    rw [one_smul, one_smul] at this
    rw [this]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ihx =>
    have := dAct_add_smul B
      (differentiableAt_orbit hU hd (atPlace B v (E v)) (Submodule.zero_mem (VP B P)))
      (differentiableAt_orbit hU hd (atPlace B v (E v)) hx) c
    rw [zero_add, dAct_zero, zero_add] at this
    rw [this]
    exact Submodule.smul_mem _ c ihx

theorem wordAct_conj (k : B.I.Ginf) (hk : ∀ v, uMat (k v) ∈ Formalism.REAL.Kset (B.I.ε v)) (u : ∀ v, B.H v)
    (hu : ∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v))
    (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) :
    ∃ l' : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v)), l'.length = l.length ∧
      B.σs k (wordAct B l (B.tens u)) = wordAct B l' (B.σs k (B.tens u)) := by
  classical
  induction l with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons X l ih =>
    obtain ⟨v, X⟩ := X
    obtain ⟨l', h1, h2⟩ := ih
    obtain ⟨y, h3, h4⟩ := GlobalTheory.StepTens.wordAct_tens_of_diff B hU hd u hu l
    refine ⟨⟨v, ⟨uMat (k v) * X.1 * (uMat (k v))ᴴ, GlobalTheory.StepLoc.inG_conj (hk v) X.2⟩⟩ :: l',
      by simp [h1], ?_⟩
    change B.σs k (dAct B (atPlace B v X) (wordAct B l (B.tens u))) =
      dAct B (atPlace B v _) (wordAct B l' (B.σs k (B.tens u)))
    have h5 : ∀ v, B.σ v (uMat (k v)) (y v) ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) l.length :=
      fun v => (GlobalTheory.StepLoc.stepSpace_props_of_diff B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (hU v)
        (hd v) l.length).1 _ (hk v) _ (h3 v)
    have hs : ∀ x, B.σs k (B.tens x) = B.tens fun v => B.σ v (uMat (k v)) (x v) :=
      fun x => B.tens_spec.2.1 k x
    rw [← h2, h4, dAct_atPlace_tens hU hd v X y h3, hs, hs, dAct_atPlace_tens hU hd v _ _ h5]
    congr 1
    funext v'
    by_cases h : v' = v
    · subst h
      simp only [Function.update_self]
      exact (GlobalTheory.StepLoc.dAct_conj (hU v').1 (hk v') X.2 (hd v' _ _ (h3 v') _ X.2)).symm
    · simp only [Function.update_of_ne h]

theorem stepSpan_stable {P : ℕ} (k : B.I.Ginf) (hk : ∀ v, uMat (k v) ∈ Formalism.REAL.Kset (B.I.ε v))
    {w : B.Hs} (hw : w ∈ VP B P) : B.σs k w ∈ VP B P := by
  have : VP B P ≤ (VP B P).comap (B.σs k : B.Hs →ₗ[ℂ] B.Hs) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, u, hl, hu, rfl⟩
    obtain ⟨l', h1, h2⟩ := wordAct_conj hU hd k hk u hu l
    change B.σs k (wordAct B l (B.tens u)) ∈ VP B P
    have hs : B.σs k (B.tens u) = B.tens fun v => B.σ v (uMat (k v)) (u v) := B.tens_spec.2.1 k u
    rw [h2, hs]
    exact Submodule.subset_span ⟨l', _, h1.trans_le hl,
      fun v => GlobalTheory.StepLoc.lowKSub_stable _ _ _ _ (hk v) _ (hu v), rfl⟩
  exact this hw

theorem finiteDimensional_VP {P : ℕ}
    (hf : ∀ v, FiniteDimensional ℂ (stepSpace (B.I.ε v) (B.lam v) (B.σ v) P)) :
    FiniteDimensional ℂ (VP B P) := by
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  let L := PiTensorProduct.lift (m.toMultilinearMap.compLinearMap
    fun v => (stepSpace (B.I.ε v) (B.lam v) (B.σ v) P).subtype)
  have hle : VP B P ≤ LinearMap.range L := by
    intro w hw
    obtain ⟨k, u, hu, rfl⟩ := GlobalTheory.StepTens.stepSpan_le_of_differentiable B hU hd P w hw
    refine Submodule.sum_mem _ fun l _ => ⟨PiTensorProduct.tprod ℂ fun v => ⟨u l v, hu l v⟩, ?_⟩
    simp [L, hm]
  exact Submodule.finiteDimensional_of_le hle

theorem sum_normSq_dAct_le {P m : ℕ} (v : InfinitePlace B.I.F) (E : Fin m → gLie (B.I.ε v)) (β : ℝ)
    (hβ : ∀ y ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) (E i).1 y‖ ^ 2 ≤ β * ‖y‖ ^ 2)
    {w : B.Hs} (hw : w ∈ VP B P) : ∑ i, ‖dAct B (atPlace B v (E i)) w‖ ^ 2 ≤ β * ‖w‖ ^ 2 := by
  obtain ⟨k, u, hu, rfl⟩ := GlobalTheory.StepTens.stepSpan_le_of_differentiable B hU hd P w hw
  simp only [dAct_atPlace_sum hU hd _ _ u hu]
  let L : Fin m → (stepSpace (B.I.ε v) (B.lam v) (B.σ v) P →ₗ[ℂ] B.H v) := fun i =>
    { toFun := fun y => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) (E i).1 y
      map_add' := fun x y => by
        simpa using GlobalTheory.StepLoc.dAct_add_smul (hd v P _ x.2 _ (E i).2) (hd v P _ y.2 _ (E i).2) 1
      map_smul' := fun c x => by
        simpa [GlobalTheory.StepLoc.dAct_zero] using GlobalTheory.StepLoc.dAct_add_smul
          (hd v P _ (Submodule.zero_mem _) _ (E i).2) (hd v P _ x.2 _ (E i).2) c }
  exact GlobalTheory.sum_normSq_tens_update_le B v (fun v => stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) m L β
    (fun y => hβ y y.2) k (fun l v => ⟨u l v, hu l v⟩)

end Diff

theorem card_places_le : Fintype.card (InfinitePlace B.I.F) ≤ B.I.f := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank B.I.F
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces B.I.F
  unfold AutInst.f
  omega

theorem stepBoundAt_of_local : ∀ (B : RowsAut) (b : ℝ), (∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) ∧ (∀ P : ℕ, FiniteDimensional ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) ∧ (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w) ∧ (∀ F : Fin (B.I.n ^ 2) → Matrix (Fin B.I.n) (Fin B.I.n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsONFamily (B.I.ε v) F → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) (F i) w‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst B.I.n b P ^ 2 * ‖w‖ ^ 2) ∧ ∀ X, Formalism.REAL.inG (B.I.ε v) X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X w‖ ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst B.I.n b P * ‖w‖)) → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  intro B b h P
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (h v).1
  have hd : ∀ v P, ∀ w ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, IsDiffVec (B.I.ε v) (B.σ v) w :=
    fun v Q => ((h v).2 Q).2.1
  have hb := beP_nonneg B.I.n b P
  have hone : ∀ (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)), ∀ w ∈ VP B P,
      ‖dAct B (atPlace B v X) w‖ ≤ Real.sqrt (Formalism.REAL.hs X.1) * beP B.I.n b P * ‖w‖ := by
    intro v X w hw
    have h1 := sum_normSq_dAct_le hU hd v (fun _ : Fin 1 => X)
      ((Real.sqrt (Formalism.REAL.hs X.1) * beP B.I.n b P) ^ 2) (fun y hy => by
        have h2 := ((h v).2 P).2.2.2 X.1 X.2 y hy
        rw [stepConst_eq] at h2
        rw [Fin.sum_univ_one, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) h2 2) hw
    rw [Fin.sum_univ_one, ← mul_pow] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
  refine ⟨finiteDimensional_VP hU hd fun v => ((h v).2 P).1, fun k hk w hw => stepSpan_stable hU hd k hk hw,
    fun E w hw => differentiableAt_orbit hU hd E hw, ?_, hone, ?_, fun E w hw => dAct_mem hU hd E hw⟩
  · intro v m E hE w hw
    obtain rfl := card_of_isONBasis hE
    refine sum_normSq_dAct_le hU hd v E _ (fun y hy => ?_) hw
    rw [← stepConst_eq]
    exact ((h v).2 P).2.2.1 (fun i => (E i).1) ⟨fun i => (E i).2, hE.1⟩ y hy
  · intro E w hw
    have hs0 : ∀ v, 0 ≤ Formalism.REAL.hs (E v).1 := fun v => by
      unfold Formalism.REAL.hs
      positivity
    have hcs : ∑ v, Real.sqrt (Formalism.REAL.hs (E v).1) ≤
        Real.sqrt B.I.f * Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) := by
      have h1 := Real.sum_sqrt_mul_sqrt_le Finset.univ (f := fun _ : InfinitePlace B.I.F => (1 : ℝ))
        (g := fun v => Formalism.REAL.hs (E v).1) (fun _ => zero_le_one) hs0
      simp only [Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one] at h1
      refine h1.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
      exact_mod_cast card_places_le B
    rw [dAct_eq_sum hU hd E hw]
    calc _ ≤ ∑ v, ‖dAct B (atPlace B v (E v)) w‖ := norm_sum_le _ _
      _ ≤ ∑ v, Real.sqrt (Formalism.REAL.hs (E v).1) * beP B.I.n b P * ‖w‖ :=
        Finset.sum_le_sum fun v _ => hone v (E v) w hw
      _ = (∑ v, Real.sqrt (Formalism.REAL.hs (E v).1)) * beP B.I.n b P * ‖w‖ := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ _ := by gcongr

end GlobalTheory.StepGlob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesStepBoundOfCountingHypotheses
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem stepBoundAt_of_countHyp : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ)
    (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  intro B Cg n₀ d p q b hn₀ hC
  obtain ⟨-, -, -, -, -, -, hrk, -, -, -, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    countHyp_numerics B Cg n₀ d p q b hn₀ hC
  have hK := countHyp_isKTypeOf_lowKSub B Cg n₀ d p q b hn₀ hC
  obtain ⟨hD, -, -, -, -, -, -, -, hlam, -⟩ := hC
  refine GlobalTheory.StepGlob.stepBoundAt_of_local B b (fun v => ?_)
  obtain ⟨hpar, hds, -, -⟩ := hD v
  have hU : IsURepOn (UJset (B.I.ε v)) (B.σ v) := hds.2.2.1
  have h120v : 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hrk v]; exact h120
  have heig := GlobalTheory.T.lowestKType_infinitesimalChar_large_gap B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hpar hds h (hgap v) h120v
  exact ⟨hU, GlobalTheory.StepBoundOneRep.stepBound_of_eigen B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) b hU
    (hK v) heig (hlam v)⟩

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesStepBoundOfCountingHypothesesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_stepBound_of_countingHypotheses : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  first | exact @GlobalTheory.Dec.stepBoundAt_of_countHyp | exact GlobalTheory.Dec.stepBoundAt_of_countHyp | (intros; apply GlobalTheory.Dec.stepBoundAt_of_countHyp <;> assumption)
end
