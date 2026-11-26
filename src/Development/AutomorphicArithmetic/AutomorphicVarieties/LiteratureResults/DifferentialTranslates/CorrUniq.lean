module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem mat_cancel {E : Type} [Field E] {a : ℕ} (Ξ : AlgRep E a) (g : GL (Fin a) (Cinf E))
    {v v' : Fin Ξ.d → ℂ} (h : Ξ.mat g *ᵥ v = Ξ.mat g *ᵥ v') : v = v' := by
  have h2 := congrArg (fun z => Ξ.mat g⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] using h2

private theorem sand_surj {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GL (Fin a) (Cinf E)) (v : HV E a) :
    (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ v))) = v := by
  rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul,
    ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem corrUniq : CorrUniq := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α α' w h h' => ?_, fun α w w' h h' => ?_⟩
  · refine AlternatingMap.ext fun X => (evFacts E a Ξ.d).1 (funext fun g => ?_)
    rw [← infGL_mul_finGL g]
    exact mat_cancel Ξ _ ((h _ _ X).symm.trans (h' _ _ X))
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ cone E a
    · obtain ⟨g, rfl⟩ := hp
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
      refine ContinuousAlternatingMap.ext fun v => ?_
      have e := (h g x fun i => hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i))).trans
        (h' g x fun i => hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i))).symm
      simp only [sand_surj] at e
      exact e
    · rw [(w.2 s).2 p hp, (w'.2 s).2 p hp]

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrSmooth
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem sub_smooth {f : X → HV E a} {x : X} (h : ContDiffAt ℝ ∞ (fun y => (f y).1) x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨r, hr⟩ := (HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1 :=
    funext fun y => (LinearMap.congr_fun hr (f y)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h

private theorem inv_smooth {τ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ContDiffAt ℝ ∞ (fun y => toL (τ y).val) x) (i j : Fin a) :
    ContDiffAt ℝ ∞ (fun y => (τ y)⁻¹.val i j) x := by
  have hd : ContDiffAt ℝ ∞ (fun y => (τ y).val.det) x := (contDiff_det (E := E) (a := a)).contDiffAt.comp x h
  have hu : IsUnit (τ x).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (τ x).isUnit
  have hi : ContDiffAt ℝ ∞ (fun y => Ring.inverse (τ y).val.det) x := by
    have := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
    rw [hu.unit_spec] at this
    exact this.comp x hd
  have ha : ContDiffAt ℝ ∞ (fun y => (τ y).val.adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    refine (contDiff_det (E := E) (a := a)).contDiffAt.comp x
      (f := fun y => toL ((τ y).val.updateRow j (Pi.single i 1))) ?_
    refine contDiffAt_pi.2 fun k => ?_
    by_cases hk : k = j
    · subst hk
      have : (fun y => toL ((τ y).val.updateRow k (Pi.single i 1)) k) = fun _ => Pi.single i 1 :=
        funext fun y => Matrix.updateRow_self
      rw [this]; exact contDiffAt_const
    · have : (fun y => toL ((τ y).val.updateRow j (Pi.single i 1)) k) = fun y => toL (τ y).val k :=
        funext fun y => Matrix.updateRow_ne hk
      rw [this]; exact contDiffAt_pi.1 h k
  have e : (fun y => (τ y)⁻¹.val i j) = fun y => Ring.inverse (τ y).val.det * (τ y).val.adjugate i j := by
    funext y
    rw [Matrix.coe_units_inv, Matrix.inv_def]; rfl
  rw [e]
  exact hi.mul ha

private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (v : HV E a) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) v) x := by
  refine sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)
  have e : (fun y => (sand (σ y) v).1 i j) =
      fun y => ∑ l, (∑ k, (σ y).val i k * v.1 k l) * star ((σ y).val j l) := by
    funext y
    change ((σ y).val * Matrix.of v.1 * star (σ y).val) i j = _
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul contDiffAt_const).mul ?_
  exact (starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)

theorem corrSmooth : CorrSmooth := by
  intro E _ _ _ a U Ξ q α w hc s p₀ hp₀
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
  refine ContDiffAt.contDiffWithinAt ?_
  set f : HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ) := fun p =>
    (w (x : GL (Fin a) (Af E) ⧸ U) p).compContinuousLinearMap ((2 : ℝ) • sand (τ p)) with hf
  have hfs : ContDiffAt ℝ ∞ f p₀ := by
    refine altSmooth _ _ _ q f p₀ fun Y => ?_
    have h1 : ContDiffAt ℝ ∞ (fun p => Ξ.mat (τ p) *ᵥ
        ev (α fun i => hv.symm (Y i)) (infGL E a (τ p) * finGL E a x)) p₀ := by
      refine contDiffAt_pi.2 fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      refine ContDiffAt.sum fun j _ => ContDiffAt.mul ?_ ?_
      · have := (((matSmooth E a Ξ i j).1).contDiffAt
          (isOpen_invSet.mem_nhds (val_mem_invSet (τ p₀)))).comp p₀ hτ
        simpa only [Function.comp_def, extGL_val] using this
      · have := (contDiffAt_chart ((evFacts E a Ξ.d).2.1 (α fun i => hv.symm (Y i)) j) (finGL E a x)
          (val_mem_invSet (τ p₀))).comp p₀ hτ
        simpa only [Function.comp_def, chart_val, infGL_comm] using this
    refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
    have := hc (τ p) x fun i => hv.symm (Y i)
    simp only [hp, LinearEquiv.apply_symm_apply] at this
    exact this
  refine altSmooth _ _ _ q _ p₀ fun v => ?_
  have h2 := applySmooth _ _ _ q f (fun i p => (2 : ℝ)⁻¹ • sand (τ p)⁻¹ (v i)) p₀ hfs
    fun i => (sand_smooth (σ := fun p => (τ p)⁻¹) (inv_smooth hτ) (v i)).const_smul _
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  change w _ p v = w _ p _
  congr 1
  funext i
  have : sand (τ p) (sand (τ p)⁻¹ (v i)) = v i := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  simp [this, smul_smul]

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrFwd
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem cont_multi {V F ι : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (ι → V) →ₘₗ[ℝ] F) : Continuous f := by
  classical
  let b := Module.finBasis ℝ V
  have h : (f : (ι → V) → F) = fun v => ∑ r : ι → Fin (Module.finrank ℝ V),
      (∏ i, b.coord (r i) (v i)) • f fun i => b (r i) := by
    funext v
    have e : v = fun i => ∑ j, b.coord j (v i) • b j := funext fun i => (b.sum_repr (v i)).symm
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [f.map_sum]
    exact Finset.sum_congr rfl fun r _ => f.map_smul_univ _ _
  rw [h]
  exact continuous_finsetSum _ fun r _ => (continuous_finsetProd _ fun i _ =>
    (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)).smul continuous_const

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def back (g : GL (Fin a) (Cinf E)) : HV E a →ₗ[ℝ] Herm E a :=
  (hv.symm : HV E a ≃ₗ[ℝ] Herm E a).toLinearMap ∘ₗ ((2⁻¹ : ℝ) • (sand g⁻¹).toLinearMap)

private theorem back_apply (g : GL (Fin a) (Cinf E)) (v : HV E a) :
    back g v = hv.symm ((2⁻¹ : ℝ) • sand g⁻¹ v) := rfl

private theorem sand_sand (g h : GL (Fin a) (Cinf E)) (v : HV E a) : sand g (sand h v) = sand (g * h) v := by
  rw [map_mul]; rfl

private theorem back_sand (g : GL (Fin a) (Cinf E)) (X : Herm E a) : back g ((2 : ℝ) • sand g (hv X)) = X := by
  rw [back_apply, map_smul (sand g⁻¹), smul_smul, sand_sand, inv_mul_cancel, map_one, inv_mul_cancel₀ two_ne_zero, one_smul]
  exact hv.symm_apply_apply X

private theorem adHerm_back (g : GL (Fin a) (Cinf E)) (k : Kinf E a) (v : HV E a) :
    adHerm k (back (g * Unitary.toUnits k) v) = back g v := by
  have h : ∀ y : HV E a, adHerm k (hv.symm y) = hv.symm (sand (Unitary.toUnits k) y) := fun _ => rfl
  rw [back_apply, back_apply, h, map_smul, sand_sand, _root_.mul_inv_rev, mul_inv_cancel_left]

private theorem exists_unitary {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← sand_sand, ← e, sand_sand, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

variable [_root_.NumberField.IsTotallyComplex E] (Ξ : AlgRep E a) {q : ℕ}
  (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)))

private def alt (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : HV E a [⋀^Fin q]→ₗ[ℝ] (Fin Ξ.d → ℂ) :=
  ((Matrix.toLin' (Ξ.mat g) ∘ₗ (LinearMap.proj (infGL E a g * finGL E a x) : (GA E a → Fin Ξ.d → ℂ) →ₗ[ℂ] (Fin Ξ.d → ℂ)) ∘ₗ
    ev).restrictScalars ℝ).compAlternatingMap (α.compLinearMap (back g))

private theorem alt_apply (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (v : Fin q → HV E a) :
    alt Ξ α g x v = Ξ.mat g *ᵥ ev (α fun i => back g (v i)) (infGL E a g * finGL E a x) := rfl

private def altL (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ) :=
  { alt Ξ α g x with cont := cont_multi (alt Ξ α g x).toMultilinearMap }

private theorem altL_apply (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (v : Fin q → HV E a) :
    altL Ξ α g x v = alt Ξ α g x v := rfl

private theorem alt_cpt (hα : IsCochain (smK Ξ) α) (g : GL (Fin a) (Cinf E)) (k : Kinf E a) (x : GL (Fin a) (Af E))
    (v : Fin q → HV E a) : alt Ξ α (g * Unitary.toUnits k) x v = alt Ξ α g x v := by
  have h := hα k fun i => back (g * Unitary.toUnits k) (v i)
  simp only [adHerm_back] at h
  rw [alt_apply, alt_apply, h, evK, Matrix.mulVec_mulVec, ← map_mul Ξ.mat, map_mul (infGL E a), mul_assoc, mul_assoc,
    infGL_comm]

private theorem alt_fin {U : Subgroup (GL (Fin a) (Af E))} (hU : ∀ X, RightInv U (α X)) (g : GL (Fin a) (Cinf E))
    (x : GL (Fin a) (Af E)) {u : GL (Fin a) (Af E)} (hu : u ∈ U) (v : Fin q → HV E a) :
    alt Ξ α g (x * u) v = alt Ξ α g x v := by
  rw [alt_apply, alt_apply, map_mul (finGL E a), ← mul_assoc, hU _ u hu]

end UpperTheory.V.Lit.Dr

open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.corrFwd :
    CorrFwd := by
  classical
  intro E _ _ _ a U Ξ q α hα hU
  refine ⟨fun s p => if h : p ∈ cone E a then altL Ξ α h.choose s.out else 0, fun g x X => ?_,
    fun s p hp => dite_eq_right hp⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := exists_unitary hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dite_eq_left hp, altL_apply, hk, hu, alt_cpt Ξ α hα, alt_fin Ξ α hU _ _ u.2, alt_apply]
  simp only [back_sand]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrCochain
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped TensorProduct

private theorem mat_cancel {E : Type} [Field E] [NumberField E] {a : ℕ} (Ξ : AlgRep E a) (g : GL (Fin a) (Cinf E))
    {v v' : Fin Ξ.d → ℂ} (h : Ξ.mat g *ᵥ v = Ξ.mat g *ᵥ v') : v = v' := by
  have h2 := congrArg (fun z => Ξ.mat g⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] using h2

private theorem sand_unit_one {E : Type} [Field E] [NumberField E] {a : ℕ} (k : Kinf E a) :
    sand (Unitary.toUnits k) (hOne E a) = hOne E a := Subtype.ext (by
  change k.1 * (1 : Matrix (Fin a) (Fin a) (Cinf E)) * star k.1 = (1 : Matrix (Fin a) (Fin a) (Cinf E))
  rw [mul_one]
  exact k.2.2)

private theorem sand_unit_hv {E : Type} [Field E] [NumberField E] {a : ℕ} (k : Kinf E a) (X : Herm E a) :
    sand (Unitary.toUnits k) (hv X) = hv (adHerm k X) := rfl

theorem UpperTheory.V.Lit.Dr.corrCochain :
    CorrCochain := by
  intro E _ _ _ a U Ξ q α w h
  refine ⟨fun k X => ?_, fun X u hu g => ?_⟩
  · refine (evFacts E a Ξ.d).1 (funext fun g => ?_)
    rw [evK, ← infGL_mul_finGL g]
    generalize GeneralLinearGroup.map (pInf E) g = y
    generalize GeneralLinearGroup.map (pFin E) g = x
    refine mat_cancel Ξ y ?_
    have h1 := h (y * Unitary.toUnits k) x X
    rw [← h y x, Matrix.mulVec_mulVec, ← map_mul, mul_assoc, ← infGL_comm, ← mul_assoc, ← map_mul, ← h1]
    simp only [map_mul, ContinuousLinearMap.mul_apply, sand_unit_one, sand_unit_hv]
  · rw [← infGL_mul_finGL g]
    generalize GeneralLinearGroup.map (pInf E) g = y
    generalize GeneralLinearGroup.map (pFin E) g = x
    refine mat_cancel Ξ y ?_
    rw [mul_assoc, ← map_mul, ← h y x, ← h y (x * u), QuotientGroup.mk_mul_of_mem x hu]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBasic
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.corrBasic :
    CorrBasic := by
  intro E _ _ _ a U Ξ q α w hc
  have two : ∀ (s : GL (Fin a) (Af E) ⧸ U) (p : HV E a) (v : Fin q → HV E a),
      w s p (fun i => (2 : ℝ) • v i) = (∏ _i : Fin q, (2 : ℝ)) • w s p v := fun s p v =>
    (w s p).toContinuousMultilinearMap.map_smul_univ (fun _ => (2 : ℝ)) v
  have hs : ∀ (g : GL (Fin a) (Cinf E)) (p : HV E a), sand g (sand g⁻¹ p) = p := fun g p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hs' : ∀ (g : GL (Fin a) (Cinf E)) (p : HV E a), sand g⁻¹ (sand g p) = p := fun g p => by
    simpa using hs g⁻¹ p
  constructor
  · intro h s p hp v i hi
    obtain ⟨g, rfl⟩ := hp
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have h0 : α (fun j => hv.symm (sand g⁻¹ (v j))) = 0 := by
      refine h _ i ?_
      rw [hi, hs']
      rfl
    have h1 := hc g x (fun j => hv.symm (sand g⁻¹ (v j)))
    simp only [LinearEquiv.apply_symm_apply, hs] at h1
    rw [h0, map_zero, two, Pi.zero_apply, Matrix.mulVec_zero] at h1
    exact (smul_eq_zero.1 h1).resolve_left (Finset.prod_ne_zero_iff.2 fun _ _ => two_ne_zero)
  · intro h X i hi
    apply (evFacts E a Ξ.d).1
    rw [map_zero]
    funext y
    set g := GeneralLinearGroup.map (pInf E) y
    set x := GeneralLinearGroup.map (pFin E) y
    have hy : infGL E a g * finGL E a x = y := infGL_mul_finGL y
    have h1 := hc g x X
    have hX : hv (X i) = hOne E a := congrArg hv (Subtype.ext hi)
    rw [two, h _ _ ⟨g, rfl⟩ (fun j => sand g (hv (X j))) i (by rw [hX]), smul_zero, hy] at h1
    have h2 := congrArg (fun v => Ξ.mat g⁻¹ *ᵥ v) h1
    simp only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
    exact h2.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBwd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BwdSmooth
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def sandL (Z : HV E a) (x : Lie E a) : HV E a :=
  ⟨toL (Matrix.of x * Matrix.of Z.1 * star (Matrix.of x)), IsSelfAdjoint.conjugate Z.2 (Matrix.of x)⟩

private theorem contDiff_sandL (Z : HV E a) : ContDiff ℝ ∞ (sandL Z) := by
  obtain ⟨π, hπ⟩ := (HV E a).subtype.exists_leftInverse_of_injective (HV E a).ker_subtype
  have h1 : ContDiff ℝ ∞ fun x : Lie E a => (sandL Z x).1 := by
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    have e : (fun x : Lie E a => (sandL Z x).1 i j) =
        fun x : Lie E a => ∑ k, (∑ l, x i l * Z.1 l k) * star (x j k) := by
      funext x
      simp only [sandL, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply]
    rw [e]
    have hs : ContDiff ℝ ∞ fun z : Cinf E => star z := (starL' ℝ (A := Cinf E)).contDiff
    refine ContDiff.sum fun k _ => ContDiff.mul (ContDiff.sum fun l _ => ContDiff.mul ?_ contDiff_const) (hs.comp ?_)
    all_goals fun_prop
  have e : sandL Z = fun x => LinearMap.toContinuousLinearMap π (sandL Z x).1 :=
    funext fun x => (LinearMap.congr_fun hπ _).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap π).contDiff.comp h1

end UpperTheory.V.Lit.Dr

open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.bwdSmooth :
    BwdSmooth := by
  intro E _ _ _ a ho U Ξ q w X j g x hx
  let y := GeneralLinearGroup.map (pInf E) g
  let s : GL (Fin a) (Af E) ⧸ U := QuotientGroup.mk (GeneralLinearGroup.map (pFin E) g)
  let L : Lie E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap
    (LinearMap.mulLeft ℝ y.val : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))
  have hL : ∀ u : GL (Fin a) (Cinf E), L (toL u.val) = toL (y * u).val := fun _ => rfl
  have hS : ∀ (Z : HV E a) (u : GL (Fin a) (Cinf E)), sandL Z (toL u.val) = sand u Z := fun _ _ => rfl
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  have hSL : ∀ Z : HV E a, ContDiffAt ℝ ∞ (fun z => sandL Z (L z)) (toL u.val) := fun Z =>
    ((contDiff_sandL Z).comp L.contDiff).contDiffAt
  have hw : ContDiffAt ℝ ∞ (fun z => w.1 s (sandL (hOne E a) (L z))) (toL u.val) := by
    refine ContDiffAt.comp (g := w.1 s) _ (Geo.contDiffAt_Om w s ?_) (hSL _)
    rw [hL, hS]
    exact sand_mem_cone _ hOne_mem_cone
  have hv' := applySmooth _ _ _ q _ (fun i z => (2 : ℝ) • sandL (hv (X i)) (L z)) _ hw fun i => (hSL _).const_smul _
  have hm : ∀ k, ContDiffAt ℝ ∞ (fun z => extGL (fun t => Ξ.mat t⁻¹ j k) (L z)) (toL u.val) := fun k => by
    refine ContDiffAt.comp (g := extGL fun t => Ξ.mat t⁻¹ j k) _ ?_ L.contDiff.contDiffAt
    rw [hL]
    exact (matSmooth E a Ξ j k).2.contDiffAt (isOpen_invSet.mem_nhds (val_mem_invSet _))
  have hall := ContDiffAt.sum (s := Finset.univ) fun k _ => (hm k).mul (contDiffAt_pi.1 hv' k)
  refine (hall.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet u)] with z hz
  obtain ⟨v, hv⟩ := hz
  obtain rfl : z = toL v.val := hv.symm
  rw [chart_val]
  simp only [map_mul, pInf_infGL, pFin_infGL, mul_one, hL, hS, extGL_val]
  rfl
end
end

open UpperTheory.V.Lit.Dr
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

private theorem lift_alt {ι V M N : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (e : M →ₗ[ℝ] N) (he : Function.Injective e) (F : V [⋀^ι]→ₗ[ℝ] N)
    (h : ∀ X, ∃ m, e m = F X) : ∃ α : V [⋀^ι]→ₗ[ℝ] M, ∀ X, e (α X) = F X := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap.compAlternatingMap
    (F.codRestrict (LinearMap.range e) h), fun X => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply (F.codRestrict (LinearMap.range e) h X))

private def piMultilinearForm {ι V N J : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup N] [Module ℝ N]
    (F : J → V [⋀^ι]→ₗ[ℝ] N) : V [⋀^ι]→ₗ[ℝ] (J → N) where
  toMultilinearMap := MultilinearMap.pi fun j => (F j).toMultilinearMap
  map_eq_zero_of_eq' v _ _ h hne := funext fun j => (F j).map_eq_zero_of_eq v h hne

theorem UpperTheory.V.Lit.Dr.corrBwd :
    CorrBwd := by
  intro E _ _ _ a ho U Ξ q w
  obtain ⟨hinj, -, hsurj⟩ := evFacts E a Ξ.d
  obtain ⟨α, hα⟩ := lift_alt ((ev (E := E) (a := a) (d := Ξ.d)).restrictScalars ℝ) hinj
    (piMultilinearForm fun g : GA E a => (mulVecL (Ξ.mat (GeneralLinearGroup.map (pInf E) g)⁻¹)).toLinearMap.compAlternatingMap
      ((w.1 (GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E) ⧸ U)
        (sand (GeneralLinearGroup.map (pInf E) g) (hOne E a))).toAlternatingMap.compLinearMap
        ((2 : ℝ) • ((sand (GeneralLinearGroup.map (pInf E) g)).toLinearMap ∘ₗ (hv (E := E) (a := a)).toLinearMap))))
    (fun X => hsurj _ (bwdSmooth E a ho U Ξ q w X))
  refine ⟨α, fun g x X => ?_⟩
  have h1 : GeneralLinearGroup.map (pInf E) (infGL E a g * finGL E a x) = g := by
    rw [map_mul, pInf_infGL, pInf_finGL, mul_one]
  have h2 : GeneralLinearGroup.map (pFin E) (infGL E a g * finGL E a x) = x := by
    rw [map_mul, pFin_infGL, pFin_finGL, one_mul]
  have h3 : ev (α X) (infGL E a g * finGL E a x) =
      Ξ.mat (GeneralLinearGroup.map (pInf E) (infGL E a g * finGL E a x))⁻¹ *ᵥ
      w.1 (GeneralLinearGroup.map (pFin E) (infGL E a g * finGL E a x) : GL (Fin a) (Af E) ⧸ U)
        (sand (GeneralLinearGroup.map (pInf E) (infGL E a g * finGL E a x)) (hOne E a))
        fun i => (2 : ℝ) • sand (GeneralLinearGroup.map (pInf E) (infGL E a g * finGL E a x)) (hv (X i)) :=
    congrFun (hα X) _
  rw [h3, h1, h2, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
end
