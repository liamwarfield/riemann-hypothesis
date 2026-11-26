module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B2x4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section form
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

lemma herm_sum (u v : Fin m → ℂ) : ∑ j, herm H (bvec j) v * u j = herm H u v := by
  simp only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma herm_add_left (u u' w : Fin m → ℂ) : herm H (u + u') w = herm H u w + herm H u' w := by
  simp only [herm, mulVec_add, dotProduct_add]

lemma herm_sub_left (u u' w : Fin m → ℂ) : herm H (u - u') w = herm H u w - herm H u' w := by
  simp only [herm, mulVec_sub, dotProduct_sub]

lemma herm_smul_left (c : ℂ) (u w : Fin m → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma herm_add_right (u w w' : Fin m → ℂ) : herm H u (w + w') = herm H u w + herm H u w' := by
  simp only [herm, star_add, add_dotProduct]

lemma herm_sub_right (u w w' : Fin m → ℂ) : herm H u (w - w') = herm H u w - herm H u w' := by
  simp only [herm, star_sub, sub_dotProduct]

lemma herm_smul_right (c : ℂ) (u w : Fin m → ℂ) : herm H u (c • w) = star c * herm H u w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

lemma herm_symm (hH : Hᴴ = H) (u w : Fin m → ℂ) : star (herm H u w) = herm H w u := by
  unfold herm
  rw [← Matrix.star_dotProduct_star, star_star, star_mulVec, hH, ← dotProduct_mulVec]

lemma herm_bvec (i j : Fin m) : herm H (bvec j) (bvec i) = H i j := by
  simp [herm, bvec, dotProduct, mulVec, Pi.single_apply]

lemma herm_mulVec (g : Matrix (Fin m) (Fin m) ℂ) (u w : Fin m → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ w) = herm (gᴴ * H * g) u w := by
  unfold herm
  rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star w) gᴴ]

lemma mem_UH_of_herm (g : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ u w, herm H (g *ᵥ u) (g *ᵥ w) = herm H u w) : g ∈ UH H := by
  show gᴴ * H * g = H
  ext i j
  rw [← herm_bvec (gᴴ * H * g), ← herm_mulVec, h, herm_bvec]

lemma heis_isom (hH : Hᴴ = H) (e v : Fin m → ℂ) (b : ℂ) (hee : herm H e e = 0) (hve : herm H v e = 0)
    (hb : b + star b + herm H v v = 0) (u w : Fin m → ℂ) :
    herm H (u - herm H u v • e + herm H u e • (v + b • e)) (w - herm H w v • e + herm H w e • (v + b • e)) =
      herm H u w := by
  have hev : herm H e v = 0 := by rw [← herm_symm H hH v e, hve, star_zero]
  simp only [herm_add_left, herm_sub_left, herm_smul_left, herm_add_right, herm_sub_right, herm_smul_right,
    herm_symm H hH, hee, hve, hev]
  linear_combination (herm H u e * herm H e w) * hb

end form

def lastI (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

lemma Hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1

lemma Hpk_zero_row (k r' : ℕ) (j : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') (eI k (1 + r') (a0 r')) j = if j.val = 2 * (1 + r') + k then 1 else 0 := by
  have hv : (eI k (1 + r') (a0 r')).val = 0 := rfl
  unfold Hpk
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hermitian_first_basis_right (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (e0 k r') = u (lastI k r') := by
  rw [← herm_sum]
  rw [Finset.sum_eq_single (lastI k r')]
  · rw [e0, herm_bvec, Hpk_zero_row, if_pos (show (lastI k r').val = 2 * (1 + r') + k from rfl), one_mul]
  · intro j _ hj
    have : j.val ≠ 2 * (1 + r') + k := fun h => hj (Fin.ext h)
    rw [e0, herm_bvec, Hpk_zero_row, if_neg this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma hermitian_form_base_vector_left (k r' : ℕ) (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (e0 k r') w = star (w (lastI k r')) := by
  rw [← herm_symm _ (Hpk_herm k (1 + r')), hermitian_first_basis_right]

lemma goodRowsProjector_apply_eq_sum (k r' : ℕ) (i : Fin (2 * (1 + r') + k + 1)) : e0 k r' i = if i.val = 0 then 1 else 0 := by
  simp only [e0, bvec, eI, a0, Pi.single_apply, Fin.ext_iff]

lemma liftVec_last (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (lastI k r') = 0 := by
  unfold liftVec lastI
  rw [dite_eq_right (by simp only []; omega)]

lemma sum_lift (k r' : ℕ) (F : Fin (2 * (1 + r') + k + 1) → ℂ)
    (h : ∀ p, ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) → F p = 0) :
    ∑ p, F p = ∑ j, F (levPos k 1 r' j) := by
  symm
  apply Finset.sum_of_injOn (levPos k 1 r')
  · intro a _ b _ hab
    have := congrArg Fin.val hab
    simp only [levPos] at this
    exact Fin.ext (by omega)
  · intro a _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro p _ hp
    apply h
    intro hc
    apply hp
    refine ⟨⟨p.val - 1, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    apply Fin.ext
    simp only [levPos]
    omega
  · intro _ _; rfl

lemma liftVec_levPos (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' y (levPos k 1 r' j) = y j := by
  have := j.isLt
  unfold liftVec levPos
  rw [dite_eq_left (by simp only []; omega)]
  congr 1

lemma liftVec_out (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)) : liftVec k 1 r' y p = 0 := by
  unfold liftVec
  rw [dite_eq_right hp]

lemma Hpk_levPos (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (levPos k 1 r' i) (levPos k 1 r' j) = Hpk k r' i j := by
  have e1 : (levPos k 1 r' i = levPos k 1 r' j) ↔ i.val = j.val := by
    simp only [levPos, Fin.ext_iff]; omega
  have e2 : (i = j) ↔ i.val = j.val := Fin.ext_iff
  have hi : (levPos k 1 r' i).val = i.val + 1 := rfl
  have hj : (levPos k 1 r' j).val = j.val + 1 := rfl
  unfold Hpk
  simp only [e1, e2]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_lift (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' y) (liftVec k 1 r' y') = herm (Hpk k r') y y' := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  rw [sum_lift]
  · apply Finset.sum_congr rfl; intro i _
    rw [liftVec_levPos, sum_lift]
    · congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [liftVec_levPos, Hpk_levPos]
    · intro p hp; rw [liftVec_out k r' y p hp, mul_zero]
  · intro p hp; rw [liftVec_out k r' y' p hp, star_zero, zero_mul]

lemma hb_rel (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' y s + star (hb k r' y s) + herm (Hpk k r') y y = 0 := by
  have h := herm_symm _ (Hpk_herm k r') y y
  have him : (herm (Hpk k r') y y).im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  apply Complex.ext
  · simp [hb]
  · simp [hb, him]

theorem heisAct : HeisAct := by
  intro k r' v u b
  ext i
  simp only [heisG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have h1 : ∀ (w φ : Fin (2 * (1 + r') + k + 1) → ℂ), (Matrix.vecMulVec w φ *ᵥ u) i = (∑ j, φ j * u j) * w i := by
    intro w φ
    simp only [mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h1, h1, herm_sum, herm_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

lemma heisG_apply (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) (i j : Fin (2 * (1 + r') + k + 1)) :
    heisG k r' v b i j = (if i = j then 1 else 0) - e0 k r' i * herm (Hpk k (1 + r')) (bvec j) v +
      (v i + b * e0 k r' i) * (if j.val = 2 * (1 + r') + k then 1 else 0) := by
  simp only [heisG, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, hermitian_first_basis_right,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, lastI, Fin.ext_iff]
  congr 2
  simp only [eq_comm]

theorem heisMem : HeisMem := by
  intro k r' x
  obtain ⟨y, s⟩ := x
  refine ⟨?_, ?_, ?_⟩
  · apply mem_UH_of_herm
    intro u w
    simp only [heis0]
    rw [heisAct, heisAct]
    apply heis_isom _ (Hpk_herm k (1 + r'))
    · rw [hermitian_first_basis_right, goodRowsProjector_apply_eq_sum]; simp [lastI]
    · rw [hermitian_first_basis_right, liftVec_last]
    · rw [herm_lift]; exact hb_rel k r' y s
  · intro a i hai
    have ha := a.isLt
    simp only [heis0]
    have hv : (eI k (1 + r') a).val = a.val := rfl
    have hz : (if (eI k (1 + r') a).val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    rw [heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum]
    by_cases hi : i.val = 0
    · have : bvec (eI k (1 + r') a) = e0 k r' := by
        unfold e0; congr 1; apply Fin.ext; simp only [eI, a0]; omega
      rw [this, hermitian_form_base_vector_left, liftVec_last]; simp
    · rw [if_neg hi]; simp
  · intro i j h1 h2 h3
    simp only [heis0]
    have hz : (if j.val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    have hz2 : (if i.val = 0 then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    rw [heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum, hz2]; simp

end Formalism.FourierDecayAlt.P.B2x4

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem conjugation_invariance_of_parts : Formalism.FourierDecayAlt.B2.AssembleConjInv := by
  intro hCC hN hW hK hU
  have raw : ConjInvRaw := by
    intro k r z μN hz hT hμ h hh
    exact hCC k r (Nset k r) (UWset k r z) μN (hN k r) (hW k r z) (hK k r z hz hT)
      (fun a ha u hu => (hU k r z hz a ha u hu).1) hμ h hh
  refine ⟨raw, ?_⟩
  intro k r Wp Wq _ _ _ _ D h₀ hh
  rcases hh with hh | hh
  · exact raw k r D.z D.μN D.z_mem D.T_pos D.haarN h₀ hh
  · exact raw k r D.z' D.μN D.z'_mem D.T'_pos D.haarN h₀ hh

theorem B2x4.conjInv_of (hN : ClosedN) (hW : ClosedW) (hK : CompactW) : ConjInvRaw ∧ ConjInvAll :=
  conjugation_invariance_of_parts compact_subgroup_conjugation hN hW hK uWNormal

theorem b2_conjInvRaw_proof : Formalism.FourierDecayAlt.B2.ConjInvRaw :=
  (B2x4.conjInv_of unipotent_radical_closed weyl_subgroup_closed weyl_subgroup_compact).1

theorem conjugation_invariance_every_setting : Formalism.FourierDecayAlt.B2.ConjInvAll :=
  (B2x4.conjInv_of unipotent_radical_closed weyl_subgroup_closed weyl_subgroup_compact).2

theorem heisenberg_action_formula : Formalism.FourierDecayAlt.B2.HeisAct := B2x4.heisAct

theorem heisenberg_mem_unipotent : Formalism.FourierDecayAlt.B2.HeisMem := B2x4.heisMem

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open PI.UpqRep

namespace TranslationBesselVanishing

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : hᴴ * Hpk k r * h = Hpk k r) (hg : gᴴ * Hpk k r * g = Hpk k r) :
    (h * g)ᴴ * Hpk k r * (h * g) = Hpk k r := by
  calc (h * g)ᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hh, hg]

theorem sigma_mul {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : hᴴ * Hpk k r * h = Hpk k r) (hg : gᴴ * Hpk k r * g = Hpk k r) :
    σ (h * g) = (σ h).comp (σ g) := by
  obtain ⟨P, hP, hDS⟩ := hds
  have hmul := hDS.2.2.1.1.2
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hsP : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hPu
  have hPs : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp hPu
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hsP
  have hJ : Jm ε = P * Hpk k r * star P := by
    rw [← hP.1.2, ← Matrix.star_eq_conjTranspose]
    calc Jm ε = (P * star P) * Jm ε * (P * star P) := by rw [hPs, Matrix.one_mul, Matrix.mul_one]
      _ = P * (star P * Jm ε * P) * star P := by simp only [Matrix.mul_assoc]
  have memJ : ∀ x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      xᴴ * Hpk k r * x = Hpk k r → P * x * P⁻¹ ∈ UJset ε := by
    intro x hx
    have hx' : star x * Hpk k r * x = Hpk k r := by rw [Matrix.star_eq_conjTranspose]; exact hx
    show (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε
    rw [hinv, hJ, ← Matrix.star_eq_conjTranspose]
    calc star (P * x * star P) * (P * Hpk k r * star P) * (P * x * star P)
        = P * (star x * (star P * P) * Hpk k r * (star P * P) * x) * star P := by
          simp only [star_mul, star_star, Matrix.mul_assoc]
      _ = P * (star x * Hpk k r * x) * star P := by simp only [hsP, Matrix.mul_one]
      _ = P * Hpk k r * star P := by rw [hx']
  have key : ∀ x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P⁻¹ * (P * x * P⁻¹) * P = x := by
    intro x
    rw [hinv]
    calc star P * (P * x * star P) * P = (star P * P) * x * (star P * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hsP, Matrix.one_mul, Matrix.mul_one]
  have hprod : (P * h * P⁻¹) * (P * g * P⁻¹) = P * (h * g) * P⁻¹ := by
    rw [hinv]
    calc P * h * star P * (P * g * star P) = P * h * (star P * P) * g * star P := by
          simp only [Matrix.mul_assoc]
      _ = P * (h * g) * star P := by rw [hsP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h1 := hmul (P * h * P⁻¹) (memJ h hh) (P * g * P⁻¹) (memJ g hg)
  dsimp only at h1
  rw [hprod, key, key, key] at h1
  exact h1

theorem smooth_add {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {x y : H}
    (hx : x ∈ smoothVecs (k := k) (r := r) σ) (hy : y ∈ smoothVecs (k := k) (r := r) σ) :
    x + y ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g (x + y))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g x) from hx) g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hGe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g y) from hy) g₀ hg₀
  refine ⟨U ∩ V, fun g => F g + G g, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
  simp only [map_add (f := _), hFe g hg.1 hgl, hGe g hg.2 hgl]

theorem smooth_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (c : ℂ) {x : H}
    (hx : x ∈ smoothVecs (k := k) (r := r) σ) : c • x ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g (c • x))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g x) from hx) g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgl => ?_⟩
  simp only [map_smul, hFe g hg hgl]

theorem smooth_zero {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} :
    (0 : H) ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g 0)
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => by simp⟩

def mulRightCLM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ]
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => h * g
      map_add' := fun a b => Matrix.add_mul a b g
      map_smul' := fun c a => by simp [Matrix.smul_mul] }

theorem smooth_translate {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    σ g v ∈ smoothVecs (k := k) (r := r) σ := by
  intro h0 hh0
  obtain ⟨U, F, hU, hmem, hF, hEq⟩ := hv (h0 * g) (uh_mul hh0 hg)
  refine ⟨(mulRightCLM g) ⁻¹' U, fun h => F (h * g), hU.preimage (mulRightCLM g).continuous, hmem,
    hF.comp (mulRightCLM g).contDiff.contDiffOn (fun h hh => hh), ?_⟩
  intro h hhU hh
  have e := (hEq (h * g) hhU (uh_mul hh hg)).symm
  show σ h (σ g v) = F (h * g)
  rw [e]
  show σ h (σ g v) = σ (h * g) v
  rw [sigma_mul hds hh hg]
  rfl

end TranslationBesselVanishing


open TranslationBesselVanishing in
theorem bessel_ne_zero_of_cyclic_orbit : Formalism.FourierDecayAlt.ThreeDimData.DDNzOfCyc := by
  intro hCyc hKF k r ε lam H _ _ _ σ w0 Wp _ _ z c π hlam hds hlow Bm hB hzero x hx
  obtain ⟨hadd, -, -, C, Ws, hWs, hbd⟩ := hB
  have hw0 : w0 ∈ smoothVecs (k := k) (r := r) σ :=
    PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth hKF k r ε lam H σ w0 hlam hds hlow
  by_contra hne
  have hpos : 0 < ‖Bm x‖ := norm_pos_iff.mpr hne
  have h2 : 0 < 2 * (|C| + 1) := by positivity
  set δ : ℝ := ‖Bm x‖ / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := div_pos hpos h2
  obtain ⟨N, cc, g, hg, hsum⟩ := hCyc k r ε lam H σ w0 hlam hds hlow x hx Ws hWs δ hδ
  set y : H := ∑ i, cc i • σ (g i) w0 with hy
  have hysm : y ∈ smoothVecs (k := k) (r := r) σ :=
    Finset.sum_induction _ (· ∈ smoothVecs (k := k) (r := r) σ) (fun a b ha hb => smooth_add ha hb)
      smooth_zero (fun i _ => smooth_smul _ (smooth_translate hds hw0 (hg i)))
  have hyDD : y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0 :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g i, hg i, rfl⟩))
  have hxy : x - y ∈ smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ y]
    exact smooth_add hx (smooth_smul _ hysm)
  have hsplit : Bm x = Bm (x - y) + Bm y := by
    rw [← hadd _ hxy _ hysm, sub_add_cancel]
  have hBy : Bm y = 0 := hzero y hyDD
  have hb := hbd (x - y) hxy
  have hS0 : 0 ≤ (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp ha
    exact norm_nonneg _
  have hlt : ‖Bm x‖ < ‖Bm x‖ :=
    calc ‖Bm x‖ = ‖Bm (x - y)‖ := by rw [hsplit, hBy, add_zero]
      _ ≤ C * (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum := hb
      _ ≤ |C| * (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hsum.le (abs_nonneg C)
      _ < ‖Bm x‖ := by
          rw [hδdef, ← mul_div_assoc, div_lt_iff₀ h2]
          nlinarith [abs_nonneg C, hpos]
  exact lt_irrefl _ hlt

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem gf_cont (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous fun g : B.Mat k r => Gf k r z z' g := by
  obtain ⟨q, _, hq⟩ := P.gram_function_polynomial k r z z'
  have h1 : Continuous fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ) := by
    have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) =
        fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
    rw [e]
    refine (MvPolynomial.continuous_eval q).comp ?_
    refine continuous_pi fun i => ?_
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · simp only [Sum.elim_inl]; exact continuous_id.matrix_elem a b
    · simp only [Sum.elim_inr]; exact continuous_star.comp (continuous_id.matrix_elem a b)
  have := Complex.continuous_re.comp h1
  refine this.congr fun g => ?_
  simp

end ops

end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

namespace Formalism.FourierDecayAlt.P

open DifferentialOperatorClasses

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellOpenDomain

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem qdom_open (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (QDom k r z z') := by
  have h1 : IsOpen {q : (Fin r → ℂ) × ℂ | ∀ a, q.1 a ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
  have h2 : IsOpen {q : (Fin r → ℂ) × ℂ | Tz k r z * Tz k r z' < Complex.normSq q.2} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  exact h1.inter h2

theorem c_apply (n : ℕ) (a : Fin r) (s : Set ((Fin r → ℂ) × ℂ)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => q.1 a) s :=
  ((contDiff_apply ℝ (fun _ => ℂ) a).comp contDiff_fst).contDiffOn

theorem c_inv (z z' : Fin (2 * r + k + 1) → ℂ) (n : ℕ) (a : Fin r) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => (star (q.1 a))⁻¹) (QDom k r z z') := by
  have h0 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => q.1 a) :=
    (contDiff_apply ℝ (fun _ => ℂ) a).comp contDiff_fst
  have hc : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => star (q.1 a)) :=
    Complex.conjCLE.contDiff.comp h0
  exact hc.contDiffOn.inv (fun q hq => star_ne_zero.2 ((show (∀ a, q.1 a ≠ 0) ∧ _ from hq).1 a))

theorem mu_entry (D : RealPlaceData k r Wp Wq) (n : ℕ) (a b : Fin (k + 1)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => D.μsec q.2 a b) (QDom k r D.z D.z') := by
  have hle : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  exact ((D.sec.1 a b).of_le hle).comp (s := QDom k r D.z D.z') contDiff_snd.contDiffOn fun q hq => hq.2

theorem gq_contDiffOn (D : RealPlaceData k r Wp Wq) (n : ℕ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q => gq D q) (QDom k r D.z D.z') := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => bigCell k r q.1 (D.μsec q.2) i j) _
  unfold bigCell
  split_ifs <;> first
    | exact contDiffOn_const
    | exact c_apply n _ _
    | exact c_inv D.z D.z' n _
    | exact mu_entry D n _ _

end Formalism.FourierDecayAlt.P.BigCellOpenDomain

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bessel_smooth_of_parts : Formalism.FourierDecayAlt.JF.JqSmoothOfParts := by
  intro hW hGD k r Wp Wq _ _ _ _ _ _ D A m F hT hF
  have hg := BigCellOpenDomain.gq_contDiffOn D m
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hG := hGD k r Wp Wq D q hq
  obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 (gq D q) ⟨WordKeyIdentity.glev0 hG.1, hG.2⟩
  refine ⟨QDom k r D.z D.z' ∩ (fun q => gq D q) ⁻¹' U,
    hg.continuousOn.isOpen_inter_preimage (BigCellOpenDomain.qdom_open D.z D.z') hU, ⟨hq, hgU⟩, ?_⟩
  have hcomp : ContDiffOn ℝ (m : WithTop ℕ∞) (F' ∘ fun q => gq D q)
      (QDom k r D.z D.z' ∩ (QDom k r D.z D.z' ∩ (fun q => gq D q) ⁻¹' U)) :=
    hc.comp (hg.mono Set.inter_subset_left) fun x hx => hx.2.2
  refine hcomp.congr fun x hx => ?_
  exact he _ hx.2.2 (WordKeyIdentity.glev0 (hGD k r Wp Wq D x hx.1).1)

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x6

open C2x5

variable {k r : ℕ}

lemma herm_ff {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) = C2.Adiag k r z a b := by
  rw [ggBlockA k r z hz a b, hzz_real]
  simp only [C2.Adiag, ggLastU, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
  · subst ha hb; simp
  · simp [ha, hb, Ne.symm hb, show a ≠ b from fun h => hb (h ▸ ha)]
  · simp [ha, hb, show a ≠ b from fun h => ha (h ▸ hb)]
  · by_cases hab : a = b
    · subst hab; simp [ha]
    · simp [ha, hab]

lemma E_cast {n : ℕ} (x : Fin n → ℂ) : star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

lemma E_unit {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) (v : Fin n → ℂ) :
    ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  apply Complex.ofReal_injective
  rw [← E_cast (H *ᵥ v), ← E_cast v, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec]

lemma euclid_cs {n : ℕ} (a b : Fin n → ℂ) :
    Complex.normSq (star b ⬝ᵥ a) ≤ (∑ i, Complex.normSq (a i)) * (∑ i, Complex.normSq (b i)) := by
  have h1 : ‖star b ⬝ᵥ a‖ ≤ ∑ i, ‖b i‖ * ‖a i‖ := by
    rw [dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Pi.star_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖b i‖) (fun i => ‖a i‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖star b ⬝ᵥ a‖ ^ 2 ≤ (∑ i, ‖b i‖ * ‖a i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖a i‖ ^ 2) := h2
    _ = (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := mul_comm _ _

lemma Hpk_mul_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * M) i j = GBasic.sgn k r i * M (GBasic.sig k r i) j := by
  rw [Matrix.mul_apply]
  simp [GBasic.Hpk_eq]

lemma mul_Hpk_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (M * Hpk k r) i j = M i (GBasic.sig k r j) * GBasic.sgn k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (GBasic.sig k r j)]
  · rw [GBasic.Hpk_eq, if_pos (GBasic.sig_sig k r j).symm, GBasic.sgn_sig]
  · intro l _ hl
    rw [GBasic.Hpk_eq, if_neg, mul_zero]
    intro h
    exact hl (by rw [h, GBasic.sig_sig])
  · simp

lemma normSq_sgn (i : Fin (2 * r + k + 1)) : Complex.normSq (GBasic.sgn k r i) = 1 := by
  unfold GBasic.sgn
  split_ifs <;> simp

end C2x6

open C2x5 C2x6

theorem gram_block_form : C2.GramBlocks := by
  intro k r z z' hz hz' g hg
  have hH := GBasic.Hpk_herm k r

  have hpres : ∀ v w, herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
    intro v w
    simp only [herm]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, show gᴴ * Hpk k r * g = Hpk k r from hg]
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₁]
    exact herm_ff hz.1 a b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [ggHerm_swap _ hH]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₂]
    rw [hpres]
    exact herm_ff hz'.1 a b

theorem majorant_estimate : C2.Majorant := by
  intro k r
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  refine ⟨?_, hsq, fun v => ⟨?_, ?_⟩⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hH, hsq, Matrix.one_mul]
  · simp only [herm]
    rw [E_cast, E_unit _ hH hsq]
  · have hcs := euclid_cs (Hpk k r *ᵥ v) v
    rw [E_unit _ hH hsq] at hcs
    set S := ∑ i, Complex.normSq (v i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have h1 : ‖herm (Hpk k r) v v‖ ^ 2 ≤ S ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, sq]
      exact hcs
    have h2 : ‖herm (Hpk k r) v v‖ ≤ S := (pow_le_pow_iff_left₀ (norm_nonneg _) hS two_ne_zero).mp h1
    exact (Complex.re_le_norm _).trans h2

theorem norm_of_inverse : C2.NormInv := by
  intro k r g hg
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg

  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hsq]
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hleft
  have hright : g * g⁻¹ = 1 := by
    rw [hinv]
    first
    | exact Matrix.mul_eq_one_comm.mp hleft
    | exact mul_eq_one_comm.mp hleft
  have hsum : ∑ i, ∑ j, Complex.normSq (g⁻¹ i j) = ∑ i, ∑ j, Complex.normSq (g i j) := by
    have he : ∀ i j, Complex.normSq (g⁻¹ i j) =
        Complex.normSq (g (GBasic.sig k r j) (GBasic.sig k r i)) := by
      intro i j
      rw [hinv, mul_Hpk_apply, Hpk_mul_apply, Matrix.conjTranspose_apply, Complex.normSq_mul,
        Complex.normSq_mul, normSq_sgn, normSq_sgn, Complex.star_def, Complex.normSq_conj]
      ring
    simp only [he]
    let σ : Equiv.Perm (Fin (2 * r + k + 1)) :=
      Function.Involutive.toPerm _ (GBasic.sig_sig k r)
    rw [Finset.sum_comm]
    refine Fintype.sum_equiv σ _ _ fun j => ?_
    exact Fintype.sum_equiv σ _ _ fun i => rfl
  refine ⟨by simp only [B.gN, hsum], ?_⟩

  set i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have hcs := euclid_cs (fun l => g⁻¹ l i0) (fun l => star (g i0 l))
  have h1 : star (fun l => star (g i0 l)) ⬝ᵥ (fun l => g⁻¹ l i0) = 1 := by
    have := congrFun (congrFun hright i0) i0
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simpa [dotProduct] using this
  rw [h1, Complex.normSq_one] at hcs
  have hgN : ∀ h : B.Mat k r, B.gN h ^ 2 = ∑ i, ∑ j, Complex.normSq (h i j) := fun h =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hA : ∑ l, Complex.normSq (g⁻¹ l i0) ≤ B.gN g⁻¹ ^ 2 := by
    rw [hgN, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun j => ∑ l, Complex.normSq (g⁻¹ l j))
      (fun j _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hB : ∑ l, Complex.normSq (star (g i0 l)) ≤ B.gN g ^ 2 := by
    rw [hgN]
    simp only [Complex.star_def, Complex.normSq_conj]
    exact Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (g i l))
      (fun i _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hN0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have hEq : B.gN g⁻¹ = B.gN g := by simp only [B.gN, hsum]
  rw [hEq] at hA
  have h4 : 1 ≤ B.gN g ^ 2 * B.gN g ^ 2 :=
    hcs.trans (mul_le_mul hA hB (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _)
      (sq_nonneg _))
  by_contra hlt
  push_neg at hlt
  have : B.gN g ^ 2 * B.gN g ^ 2 < 1 := by
    have h5 : B.gN g ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (B.gN g)]
  linarith

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem smooth_zero (σ : Mx k r → (H →L[ℂ] H)) : (0 : H) ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH]
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => map_zero (σ g)⟩

theorem smooth_add {σ : Mx k r → (H →L[ℂ] H)} {v w : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ)
    (hw : w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) : v + w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv hw ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hGe⟩ := hw g₀ hg₀
  refine ⟨U ∩ V, fun g => F g + G g, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  simp only [map_add (f := _), hFe g hg.1 hgH, hGe g hg.2 hgH]

theorem smooth_smul {σ : Mx k r → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) :
    a • v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, fun g hg hgH => ?_⟩
  simp only [map_smul, hFe g hg hgH]

theorem DD_smooth (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hw : PI.UpqRep.IsLowUnitH k r ε lam σ w0) :
    ∀ x ∈ DDsp σ w0, x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hrep := hDS.2.2.1.1.2
  have hconj := Formalism.QuantumDeterminants.unitary_conjugation_holds _ ε (PI.UpqRep.Hpk k r) P hdet hPJ
  have hback : ∀ g, P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      hPP, Matrix.one_mul, Matrix.mul_one]
  have hmul : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      σ (a * b) = (σ a).comp (σ b) := by
    intro a b ha hb
    have ha' := (hconj a).mp ha
    have hb' := (hconj b).mp hb
    have h := hrep _ ha' _ hb'
    simp only [hback] at h
    rw [← h]
    congr 1
    rw [show P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPP, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
  have hinUH : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      PI.UpqRep.inUH (PI.UpqRep.Hpk k r) (a * b) := by
    intro a b ha hb
    unfold PI.UpqRep.inUH at *
    rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * PI.UpqRep.Hpk k r * (a * b) =
      bᴴ * (aᴴ * PI.UpqRep.Hpk k r * a) * b by simp only [Matrix.mul_assoc], ha, hb]
  have hw0 : PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g => σ g w0) :=
    low_smooth_of_k_finite hK k r ε lam H σ w0 hl ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ hw
  have htr : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro g hg
    have hgH : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g := hg
    have hcd : ContDiff ℝ ∞ (fun x : Mx k r => x * g) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)).contDiff
    show PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g' => σ g' (σ g w0))
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFeq⟩ := hw0 (g₀ * g) (hinUH _ _ hg₀ hgH)
    refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g), hU.preimage hcd.continuous, hgU,
      hF.comp hcd.contDiffOn (fun x hx => hx), ?_⟩
    intro x hx hxH
    have hx' := hFeq (x * g) hx (hinUH _ _ hxH hgH)
    simp only at hx'
    show σ x (σ g w0) = F (x * g)
    rw [← hx', hmul x g hxH hgH]
    rfl
  intro x hx
  unfold DDsp at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    exact htr g hg
  | zero => exact smooth_zero σ
  | add y z _ _ hy hz => exact smooth_add hy hz
  | smul a y _ hy => exact smooth_smul a hy

end Smooth

end Formalism.FourierDecayAlt.P.DDSmoothness
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CasimirEigenvalueCoefficients
open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Qb1

variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]

theorem ckOn_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (h : CkOn m (GV k r) f) : CkOn m (GV k r) f' := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  exact ⟨U, F, a, b, c, fun g hg hgG => (he g hgG).symm.trans (d g hg hgG)⟩

variable {σ : Mx k r → (Vs →L[ℂ] Vs)}

theorem lie1 (Z : Mx k r) : inLie k r (hpart1 (Hpk k r) Z) := Qx2.hpart1_lie Z

theorem lie2 (Z : Mx k r) : inLie k r (hpart2 (Hpk k r) Z) := Qx2.hpart2_lie Z

end Qb1

end Formalism.FourierDecayAlt.P
end
end
