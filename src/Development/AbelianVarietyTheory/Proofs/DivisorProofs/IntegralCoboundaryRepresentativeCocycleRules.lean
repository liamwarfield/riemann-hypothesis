module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHausdorffOfProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryMultiplicationDefectMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormalGroupLawHomFormalGroupLawNatMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormalGroupLawHomFormalGroupLawNatMultiple
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.NMulHom

theorem isHom_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) :=
  GlobalTheory.NMulEndo.isHom_nmul

end GlobalTheory.NMulHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormalGroupLawHomFormalGroupLawNatMultipleStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFormalGroupLawHom_formalGroupLawNatMultiple : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) := by
  first | exact @GlobalTheory.NMulHom.isHom_nmul | exact GlobalTheory.NMulHom.isHom_nmul | (intros; apply GlobalTheory.NMulHom.isHom_nmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawPointsCommMonoidSubstHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawPointsCommMonoidSubstHom
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.Katz.LawMonoid

variable {R : Type} [CommRing R] {d : ℕ}

theorem constantCoeff_bivariateSeriesSubstPair {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : constantCoeff (at2 c u v) = constantCoeff c :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.1 c

theorem powerSeriesEvalTwoGroups_swapVariableGroups {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : at2 (swap c) u v = at2 c v u :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.2.1 c

theorem cc_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  show constantCoeff (at2 (μ i) u v) = 0
  rw [constantCoeff_bivariateSeriesSubstPair hu hv, hμ]

theorem subst_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (a : τ → MvPowerSeries τ' R) (ha : ∀ t, constantCoeff (a t) = 0) (i : Fin d) :
    subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i :=
  GlobalTheory.Katz.SubstCalc.subst_powerSeriesEvalTwoGroups hu hv ha (μ i)

theorem constantCoeff_mvPowerSeries_X_eq_zero {τ : Type} (s : τ) : constantCoeff (X s : MvPowerSeries τ R) = 0 := constantCoeff_X s

theorem mon : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  intro R _ d μ hμ τ _ u v w hu hv hw
  refine ⟨cc_op hμ.const hu hv, ?_, ?_, ?_, fun τ' a ha i => subst_op hu hv a ha i⟩
  ·
    let a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w)
    have ha : ∀ t, constantCoeff (a t) = 0 := by
      intro t; rcases t with t | t | t
      · exact hu t
      · exact hv t
      · exact hw t
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have h1 : (fun j => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = u := by
      funext j; simp only [x1]; rw [subst_X hs]; rfl
    have h2 : (fun j => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = v := by
      funext j; simp only [x2]; rw [subst_X hs]; rfl
    have h3 : (fun j => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = w := by
      funext j; simp only [x3]; rw [subst_X hs]; rfl
    have hx1 : ∀ j, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx2 : ∀ j, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx3 : ∀ j, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    funext i
    have e := congrArg (fun F => subst a (F i)) hμ.assoc
    try simp only at e
    rw [subst_op (cc_op hμ.const hx1 hx2) hx3 a ha, subst_op hx1 (cc_op hμ.const hx2 hx3) a ha] at e
    have e1 : (fun j => subst a (op μ x1 x2 j)) = op μ u v := by
      funext j; rw [subst_op hx1 hx2 a ha, h1, h2]
    have e2 : (fun j => subst a (op μ x2 x3 j)) = op μ v w := by
      funext j; rw [subst_op hx2 hx3 a ha, h2, h3]
    rw [e1, e2, h1, h3] at e
    exact e
  · funext i
    show at2 (μ i) u v = at2 (μ i) v u
    rw [← powerSeriesEvalTwoGroups_swapVariableGroups hu hv, hμ.comm i]
  ·
    have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
    have hX : ∀ j, constantCoeff ((X j : MvPowerSeries (Fin d) R)) = 0 := fun j => constantCoeff_X j
    have h0 : ∀ j : Fin d, constantCoeff ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j) = 0 := fun _ => map_zero _
    funext i
    have e := congrArg (fun F => subst u (F i)) hμ.unit
    try simp only at e
    rw [subst_op hX h0 u hu, subst_X hs] at e
    have e1 : (fun j => subst u ((X j : MvPowerSeries (Fin d) R))) = u := by
      funext j; rw [subst_X hs]
    have e0 : (fun j : Fin d => subst u ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j)) = fun _ => 0 := by
      funext j; show subst u (0 : MvPowerSeries (Fin d) R) = 0
      rw [← coe_substAlgHom hs]; exact map_zero _
    rw [e1, e0] at e
    exact e

end GlobalTheory.Katz.LawMonoid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawPointsCommMonoidSubstHomStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  first | exact @GlobalTheory.Katz.LawMonoid.mon | exact GlobalTheory.Katz.LawMonoid.mon | (intros; apply GlobalTheory.Katz.LawMonoid.mon <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLaws
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NMul

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_zero' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :
    nmul μ 0 = fun _ => 0 := rfl

theorem nmul_succ' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem nmul_const (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul_zero']
  | succ n ih =>
    rw [nmul_succ']
    exact (GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ n) (fun i => X i) (fun _ => 0) ih
      (fun i => constantCoeff_X i) (fun _ => map_zero _)).1

theorem nmul_add (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, nmul_zero']
    exact ((GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (fun _ => 0) (fun _ => 0)
      (nmul_const μ hμ m) (fun _ => map_zero _) (fun _ => map_zero _)).2.2.2.1).symm
  | succ n ih =>
    rw [← Nat.add_assoc, nmul_succ', ih, nmul_succ']
    exact (GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (nmul μ n) (fun i => X i)
      (nmul_const μ hμ m) (nmul_const μ hμ n) (fun i => constantCoeff_X i)).2.1

theorem nmul_one (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) :
    nmul μ 1 = fun i => X i := by
  rw [nmul_succ', nmul_zero']
  have h := GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (fun i => X i) (fun _ => 0) (fun _ => 0)
    (fun i => constantCoeff_X i) (fun _ => map_zero _) (fun _ => map_zero _)
  rw [← h.2.2.1, h.2.2.2.1]

theorem nmul_mul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    ∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i) := by
  have ha : HasSubst (nmul μ n) := hasSubst_of_constantCoeff_zero (nmul_const μ hμ n)
  induction m with
  | zero =>
    intro i
    rw [Nat.zero_mul, nmul_zero']
    exact (map_zero (substAlgHom (R := R) ha)).symm.trans (by rw [coe_substAlgHom])
  | succ m ih =>
    intro i
    rw [Nat.succ_mul, nmul_add μ hμ, nmul_succ']
    rw [(GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (fun i => X i) (fun _ => 0)
      (nmul_const μ hμ m) (fun i => constantCoeff_X i) (fun _ => map_zero _)).2.2.2.2
      (Fin d) (nmul μ n) (nmul_const μ hμ n) i]
    have e1 : (fun j => subst (nmul μ n) (nmul μ m j)) = nmul μ (m * n) := funext fun j => (ih j).symm
    have e2 : (fun j => subst (nmul μ n) ((X j : MvPowerSeries (Fin d) R))) = nmul μ n :=
      funext fun j => subst_X ha j
    rw [e1, e2]

theorem nmul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧
      nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧
      (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i :=
  fun _ _ _ μ hμ m n => ⟨nmul_const μ hμ n, nmul_add μ hμ m n, nmul_mul μ hμ m n, nmul_one μ hμ⟩

end GlobalTheory.NMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLawsStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧ nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧ (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i := by
  first | exact @GlobalTheory.NMul.nmul_laws | exact GlobalTheory.NMul.nmul_laws | (intros; apply GlobalTheory.NMul.nmul_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1SubstEqPull2OfIsHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1SubstEqPull2OfIsHom
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.CobPull

theorem cob1_subst_eq_pull2_of_isHom_formal : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), ∀ (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (φ : Fin d → MvPowerSeries (Fin d) R), (∀ i, constantCoeff (μ i) = 0) → (∀ i, constantCoeff (ν i) = 0) → IsHom μ ν φ → ∀ f : MvPowerSeries (Fin d) R, cob1 μ (subst φ f) = pull2 φ (cob1 ν f) := by
  intro R _ d μ ν φ hμ hν hφ f
  have hp : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.const
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hu : ∀ j, constantCoeff (inL (φ j)) = 0 := fun j => by
    unfold inL
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  have hv : ∀ j, constantCoeff (inR (φ j)) = 0 := fun j => by
    unfold inR
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  obtain ⟨hL, hR, hAS, -, -, hsub, -, -⟩ :=
    SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (fun j => inL (φ j))
      (fun j => inR (φ j)) hu hv
  unfold pull2 cob1
  rw [(hAS _ _).2, (hAS _ _).2, hL, hR, hsub d ν hν f]
  have e1 : subst μ (subst φ f) = subst (fun j => at2 (ν j) (fun j => inL (φ j)) (fun j => inR (φ j))) f := by
    rw [subst_comp_subst_apply hp (hasSubst_of_constantCoeff_zero hμ)]
    congr 1
    funext j
    exact hφ.hom j
  have e2 : inL (subst φ f) = subst (fun j => inL (φ j)) f := by
    unfold inL
    rw [subst_comp_subst_apply hp hX]
  have e3 : inR (subst φ f) = subst (fun j => inR (φ j)) f := by
    unfold inR
    rw [subst_comp_subst_apply hp hY]
  rw [e1, e2, e3]

end GlobalTheory.Katz.CobPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1SubstEqPull2OfIsHomStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_subst_eq_pullback_of_is_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), ∀ (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (φ : Fin d → MvPowerSeries (Fin d) R), (∀ i, constantCoeff (μ i) = 0) → (∀ i, constantCoeff (ν i) = 0) → IsHom μ ν φ → ∀ f : MvPowerSeries (Fin d) R, cob1 μ (subst φ f) = pull2 φ (cob1 ν f) := by
  first | exact @GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal | exact GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal | (intros; apply GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryMultiplicationDefectMul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem cob1_defect_and_defect_mul_of_isLaw : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (f : MvPowerSeries (Fin d) E) (m n : ℕ),
    cob1 (up E μ) (defect μ n f) = (n : E) • cob1 (up E μ) f - pull2 (up E (nmul μ n)) (cob1 (up E μ) f) ∧
    defect μ (m * n) f = (m : E) • defect μ n f + subst (up E (nmul μ n)) (defect μ m f) := by
  intro O E _ _ _ d μ hμ f m n
  obtain ⟨hL, hmap⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d μ hμ E (algebraMap O E)
  have hup : ∀ k, up E (nmul μ k) = nmul (up E μ) k := fun k =>
    funext fun i => (hmap k i).2
  have hc : ∀ i, constantCoeff (up E μ i) = 0 := hL.const
  have hk : ∀ k, HasSubst (up E (nmul μ k)) := fun k =>
    hasSubst_of_constantCoeff_zero fun i => by
      rw [hup k]; exact ((GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws E d (up E μ) hL 0 k).1 i)
  have hsub : ∀ a b : MvPowerSeries (Fin d) E, cob1 (up E μ) (a - b) = cob1 (up E μ) a - cob1 (up E μ) b :=
    fun a b => by rw [eq_sub_iff_add_eq, ← formalCoboundary_add hc, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · unfold defect
    rw [hsub, formalCoboundary_smul hc, hup n]
    rw [GlobalTheory.T.coboundary_subst_eq_pullback_of_is_hom E d (up E μ) (up E μ) (nmul (up E μ) n) hc hc (GlobalTheory.T.isFormalGroupLawHom_formalGroupLawNatMultiple E d (up E μ) hL n) f]
  · have hcomp : subst (up E (nmul μ n)) (subst (up E (nmul μ m)) f) = subst (up E (nmul μ (m * n))) f := by
      rw [subst_comp_subst_apply (hk m) (hk n)]
      congr 1
      funext i
      rw [hup, hup, hup, (GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws E d (up E μ) hL m n).2.2.1 i]
    unfold defect
    rw [subst_sub (hk n), subst_smul (hk n), hcomp, smul_sub, Nat.cast_mul, mul_smul]
    abel

end GlobalTheory.QLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryMultiplicationDefectMulStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (f : MvPowerSeries (Fin d) E) (m n : ℕ), cob1 (up E μ) (defect μ n f) = (n : E) • cob1 (up E μ) f - pull2 (up E (nmul μ n)) (cob1 (up E μ) f) ∧ defect μ (m * n) f = (m : E) • defect μ n f + subst (up E (nmul μ n)) (defect μ m f) := by
  first | exact @GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw | exact GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw | (intros; apply GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRules
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem map_inj_of_inj {σ O E : Type} [CommRing O] [CommRing E] (ι : O →+* E)
    (hι : Function.Injective ι) : Function.Injective (map ι : MvPowerSeries σ O → MvPowerSeries σ E) := by
  intro a b h
  ext α
  apply hι
  rw [← coeff_map, ← coeff_map, h]

theorem integral_cob_defect_rules : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → Function.Injective (algebraMap O E) → ∀ (f : MvPowerSeries (Fin d) E) (κ : MvPowerSeries (Fin d ⊕ Fin d) O), map (algebraMap O E) κ = cob1 (up E μ) f → IsCoc μ κ ∧ (constantCoeff f = 0 → constantCoeff κ = 0) ∧ ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect μ n f → cob1 μ s = (n : O) • κ - pull2 (nmul μ n) κ ∧ ∀ (m : ℕ) (t u : MvPowerSeries (Fin d) O), map (algebraMap O E) t = defect μ m f → map (algebraMap O E) u = defect μ (m * n) f → u = (m : O) • s + subst (nmul μ n) t := by
  intro O E _ _ _ d μ hμ hι f κ hκ
  set ι := algebraMap O E with hιdef
  have inj2 := map_inj_of_inj (σ := Fin d ⊕ Fin d) ι hι
  have inj3 := map_inj_of_inj (σ := Fin d ⊕ (Fin d ⊕ Fin d)) ι hι
  have inj1 := map_inj_of_inj (σ := Fin d) ι hι
  obtain ⟨hlawE, hnm⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d μ hμ E ι
  obtain ⟨hcob1, hcob2, hswap, -, hpull⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d μ hμ.const E ι
  have hupμ : up E μ = fun i => map ι (μ i) := rfl
  have hconstE : ∀ i, constantCoeff (up E μ i) = 0 := hlawE.const
  have hcocE := (GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt E d (up E μ) hconstE f).2.2.2.2.2 hlawE
  have hsmul : ∀ {σ : Type} (k : ℕ) (g : MvPowerSeries σ O), map ι ((k : O) • g) = (k : E) • map ι g := by
    intro σ k g
    ext α
    simp [coeff_map, map_natCast]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply inj3
    rw [hcob2, ← hupμ, hκ, hcocE.1, map_zero]
  · apply inj2
    rw [hswap, hκ, hcocE.2]
  · intro hf
    apply hι
    have h1 : ι (constantCoeff κ) = constantCoeff (map ι κ) := by
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    rw [h1, hκ, map_zero]
    unfold cob1 inL inR
    rw [map_sub, map_sub, GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero hconstE,
      GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _),
      GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _), hf]
    simp
  · intro n s hs
    have hnc : ∀ i, constantCoeff (nmul μ n i) = 0 := fun i => (hnm n i).1
    have hupn : up E (nmul μ n) = fun i => map ι (nmul μ n i) := rfl
    obtain ⟨hpl, hsb⟩ := hpull (nmul μ n) hnc
    obtain ⟨hd1, -⟩ := GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul O E d μ hμ f 0 n
    refine ⟨?_, ?_⟩
    · apply inj2
      rw [hcob1, ← hupμ, hs, hd1, map_sub, hsmul, hpl, hκ, ← hupn]
    · intro m t u ht hu
      obtain ⟨-, hd2⟩ := GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul O E d μ hμ f m n
      apply inj1
      rw [hu, hd2, map_add (f := _), hsmul, hsb, ← hupn, hs, ht]

end GlobalTheory.QLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRulesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_coboundary_representative_cocycle_rules : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → Function.Injective (algebraMap O E) → ∀ (f : MvPowerSeries (Fin d) E) (κ : MvPowerSeries (Fin d ⊕ Fin d) O), map (algebraMap O E) κ = cob1 (up E μ) f → IsCoc μ κ ∧ (constantCoeff f = 0 → constantCoeff κ = 0) ∧ ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect μ n f → cob1 μ s = (n : O) • κ - pull2 (nmul μ n) κ ∧ ∀ (m : ℕ) (t u : MvPowerSeries (Fin d) O), map (algebraMap O E) t = defect μ m f → map (algebraMap O E) u = defect μ (m * n) f → u = (m : O) • s + subst (nmul μ n) t := by
  first | exact @GlobalTheory.QLog.integral_cob_defect_rules | exact GlobalTheory.QLog.integral_cob_defect_rules | (intros; apply GlobalTheory.QLog.integral_cob_defect_rules <;> assumption)
end
