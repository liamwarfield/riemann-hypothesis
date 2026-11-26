module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpNormPiLe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AestronglyMeasurableGermIntegrand
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstDerivativeAtNormalSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceInductionLevel

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiContOf
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem psi_cont_of {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous (fun g : B.Mat k r => psi k r z c g) := by
  have hl : Continuous fun g : B.Mat k r => ell k r z g := Formalism.FourierDecayAlt.P.B7.continuous_ell (k := k) (r := r) z
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hl))))

theorem krI_aesm {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (y₀ : B.Mat k (p + ρ))
    (hy₀ : y₀ ∈ B.GV k (p + ρ)) (hD : U.DjU k p ρ y₀ ≠ 0) :
    AEStronglyMeasurable (LeftFubiniLemmas.KrI B0 H y₀) (B0.μW'.prod B0.μN) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite B0.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite B0.haarN
  set S := {ξ : Mt k (p + ρ) × Mt k (p + ρ) | Formalism.FourierDecayAlt.P.PBG.InR B0 ξ} with hS
  have hcG := Formalism.FourierDecayAlt.P.unitary_group_closed k (p + ρ)
  have hcW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k (p + ρ) B0.z'
  have hmem : ∀ ξ ∈ S, y₀ * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    intro ξ hξ
    refine ⟨hcG.mul_mem _ (hcG.mul_mem _ hy₀ _ hξ.2.1) _ hξ.1.1, ?_⟩
    show U.DjU k p ρ (y₀ * Matrix.of ξ.2 * Matrix.of ξ.1) ≠ 0
    rw [LeftFubiniLemmas.djU_mul_UW B0.z' _ _ hξ.1, LeftFubiniLemmas.djU_mul_N _ _ hξ.2]
    exact hD
  have hof1 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.1 : B.Mat k (p + ρ))) :=
    continuous_fst
  have hof2 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.2 : B.Mat k (p + ρ))) :=
    continuous_snd
  have hc1 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => y₀ * Matrix.of ξ.2 * Matrix.of ξ.1) :=
    (continuous_const.matrix_mul hof2).matrix_mul hof1
  have hH : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => H (y₀ * Matrix.of ξ.2 * Matrix.of ξ.1)) S :=
    hHc.comp hc1.continuousOn hmem
  have hinv : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.1 : B.Mat k (p + ρ))⁻¹) S :=
    Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof1.continuousOn (fun ξ hξ => hξ.1.1)
  have hπ : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => B0.π' (Matrix.of ξ.1 : B.Mat k (p + ρ))⁻¹) S :=
    B0.π'_cont.comp hinv (fun ξ hξ => hcW.inv_mem _ hξ.1)
  have hψ : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => star (psi k (p + ρ) B0.z' cStd (Matrix.of ξ.2))) :=
    continuous_star.comp ((psi_cont_of B0.z' cStd).comp hof2)
  have hK : ContinuousOn (LeftFubiniLemmas.KrI B0 H y₀) S := hψ.continuousOn.smul (hH.clm_comp hπ)
  have hm := hK.aestronglyMeasurable (μ := B0.μW'.prod B0.μN) (Formalism.FourierDecayAlt.P.PBG.isClosed_InR B0).measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := S) (Formalism.FourierDecayAlt.P.PBG.ae_inR B0)] at hm

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section pt

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rn_zero : U.Rn k p ρ 0 = 1 := by
  have h1 : U.skewOf (0 : (G.UT p → ℂ) × (Fin p → ℝ)) = 0 := by
    unfold U.skewOf; ext a b; simp [G.strictUpper]
  unfold U.Rn
  rw [← Formalism.FourierDecayAlt.P.Ux3.block3_one]
  simp only [Prod.fst_zero, Prod.snd_zero, h1]
  congr 1 <;> ext <;> simp

theorem upper_zero : G.upper (0 : G.UT p → ℂ) = 1 := by
  unfold G.upper G.strictUpper; ext a b; simp

theorem rcAct_one_zero : rcAct (1 : B.Mat k ρ) (0 : U.RC k p ρ) = 0 := by
  unfold rcAct; ext <;> simp

theorem sxL_mem (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) :
    sxL Bj σ x ∈ Sset k (p + ρ) (liftVec k p ρ Bj.z) := by
  by_cases hx : GoodL Bj σ x
  · rw [sxL, if_pos hx]
    exact left_factor_mem k p ρ Bj.z (-x.2.1) (lhOf σ x.2.2.2) (Matrix.of x.1.1) (Matrix.of x.1.2) Bj.z_mem
      (lh_lower σ _) hx.1 hx.2
  · rw [sxL, if_neg hx]
    refine ⟨1, (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k (p + ρ) _).one_mem, 1,
      (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)).one_mem, by simp⟩

theorem goodL_pt (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (g : B.Mat k ρ) (hg : g ∈ B.GV k ρ) (x : XL k p ρ σ) (hx : GoodL Bj σ x) :
    sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g ∈ B.GV k (p + ρ) ∧
      U.DjU k p ρ (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g) ≠ 0 := by
  set ξ0 : U.Xi k p 0 ρ σ := ((x.2.1, 0), (x.2.2.1, (x.2.2.2, 0))) with hξ0
  have uh : IsUnit (Matrix.of x.1.1 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z).unit _ hx.1
  have uν : IsUnit (Matrix.of x.1.2 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).unit _ hx.2
  have hH1 : (1 : B.Mat k ρ)ᴴ * Hpk k ρ * 1 = Hpk k ρ := by simp
  have e := gamma_xi_split k p ρ σ d ξ0 (fun a => a.elim0) (Matrix.of x.1.1) (Matrix.of x.1.2) 1 1 g uh uν hH1
  simp only [hξ0, Formalism.FourierDecayAlt.P.PBM.embG_one, upper_zero, Formalism.FourierDecayAlt.P.PBM.muP_one, rcAct_one_zero, rn_zero,
    Matrix.mul_one] at e
  have hx' : sxL Bj σ x = U.Rn k p ρ (-x.2.1) * U.muP k p ρ (lhOf σ x.2.2.2)ᴴ⁻¹ *
      U.embG k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹) := if_pos hx
  have cG := Formalism.FourierDecayAlt.P.unitary_group_closed k ρ
  have hγ : (Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹ * g ∈ B.GV k ρ :=
    cG.mul_mem _ (cG.mul_mem _ (cG.inv_mem _ hx.1.1) _ (cG.inv_mem _ hx.2.1)) _ hg
  rw [hx', ← e]
  have hZ : G.detM (fun a : Fin 0 => a.elim0 : G.Mat 0) ≠ 0 := by rw [detM_zero]; exact one_ne_zero
  refine ⟨Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ0 _ hZ hγ, ?_⟩
  intro h0
  have h1 := Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice σ d ξ0 (fun a : Fin 0 => a.elim0)
    ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹ * g)
  rw [detM_zero, mul_one] at h1
  exact Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd (h1.symm.trans h0)

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem core_lf (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) (muL Bj σ) ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ x, ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) ∂(muL Bj σ) :=
  core_main gamma_xi_split psi_right_equivariant psi_right_action_comm psi_measure_preserving right_measure_preserving hp σ d hd Bj B0 hz' hπ' hW'
    hW0' hNj hN0 g hg H hHc R hR (fl_aesm Bj σ d hd H hHc g hg.1)
    (aestronglyMeasurable_germ_integrand gamma_xi_split Bj B0 hz' hπ' σ d hd H hHc g hg.1)
    (fun x hx => Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.krI_aesm B0 H hHc _ (goodL_pt Bj σ d hd g hg.1 x hx).1
      (goodL_pt Bj σ d hd g hg.1 x hx).2)
    (fun γ hγ => slice_int_cont σ d hd H hHc _ _ γ hγ)

end pt

theorem left_fubini_reduced_form : CoreLF := by
  intro k p m n e hp σ d hd Wp Wq _ _ _ _ _ _ Bj B0 hz hz' hπ' hW' hW0' hNj hN0
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz hz'
  refine ⟨XL k p m σ, inferInstance, muL Bj σ, ellL Bj σ, sxL Bj σ, fun x => hz ▸ sxL_mem Bj σ x, ?_⟩
  intro g hg H hHc hRb
  obtain ⟨R, hR⟩ := hRb
  have hπ'' : ∀ y : B.Mat k m, Bj.π' y = B0.π' (U.embG k p m y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hset : {x | x ∈ B.GV k (p + m) ∧ Dmin k (p + m) B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} =
      {x | x ∈ B.GV k (p + m) ∧ U.DjU k p m x ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Formalism.FourierDecayAlt.P.hat_z_minimum_degree k p m B0.z B0.z' x]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + m) ∧ U.DjU k p m x ≠ 0} := hset ▸ hHc
  have h := core_lf hp σ d hd Bj B0 hz'.symm hπ'' hW' hW0' hNj hN0 g hg H hHc' R hR
  have hF : D.castF (rfl : p + m = p + m) H = H := funext fun y => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hV : ∀ v : Fin (2 * (p + m) + k + 1) → ℂ, D.castV (rfl : p + m = p + m).symm v = v :=
    fun v => Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl v
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, hF, hV, ← hz, ← hz']
  exact h

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas

namespace Formalism.FourierDecayAlt.P

theorem left_fubini_normalized_tower : LeftFubiniLemmas.LeftFubini := LeftFubiniReduction.leftFubini_of_core LeftFubiniLemmas.left_fubini_reduced_form

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.VLetZeroNear
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section supp

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem qminorOp_zero {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (Q.EH k r) a b u (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
  have htop : ∀ (v : ℂ) (p q : Fin (2 * r + k + 1)),
      QuantumDeterminants.Top (Q.EH k r) v p q (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
    intro v p q
    funext x
    simp only [QuantumDeterminants.Top, smul_zero, ite_self, zero_add]
    exact eabH_zero p q x
  have hfold : ∀ L : List ((Q.Mx k r → E) → Q.Mx k r → E), (∀ T ∈ L, T (fun _ => 0) = fun _ => 0) →
      L.foldr (fun T h => T h) (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons T L ih =>
      intro hT
      simp only [List.foldr_cons]
      rw [ih (fun T' h' => hT T' (by simp [h']))]
      exact hT T (by simp)
  funext x
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro σ _
  rw [hfold _ (fun T hT => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact htop _ _ _)]
  simp

theorem AAop_zero' (m : ℕ) (hm : m ≤ r) (u : ℂ) (g : Q.Mx k r) :
    C3.AAop k r m hm u (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
  unfold C3.AAop
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem AAvop_zero' (m : ℕ) (hm : m ≤ r) (ell : ℂ) (g : Q.Mx k r) :
    C3.AAvop k r m hm ell (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
  unfold C3.AAvop
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem vLet_zero_near (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2)
    (f : B.Mat k r → E) {V : Set (Q.Mx k r)} (hV : IsOpen V) (hf : ∀ x ∈ V, x ∈ B.GV k r → f x = 0)
    (g : B.Mat k r) (hg : g ∈ V) (hgG : g ∈ B.GV k r) : D.vLet k r z z' j hj l e f g = 0 := by
  have hgl : g ∈ Q.Glev k r 0 ∩ V := ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG, hg⟩
  have hloc : ∀ x ∈ Q.Glev k r 0 ∩ V, f x = (fun _ : Q.Mx k r => (0 : E)) x := fun x hx => hf x hx.2 hx.1.1
  unfold D.vLet
  split_ifs
  · rfl
  · rw [AAop_loc hV _ _ _ f _ hloc g hgl, AAop_zero', smul_zero]
  · rw [AAvop_loc hV _ _ _ f _ hloc g hgl, AAvop_zero', smul_zero]

theorem uwG_supp (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (R : ℝ)
    (hR : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) (j : ℕ) (hj : j ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV k r,
      D.uwG k r z z' F j hj w e g ≠ 0 → B.gN g ≤ R
  | [], _, g, hg, hne => hR g hg hne
  | l :: w, e, g, hg, hne => by
    by_contra hgt
    push Not at hgt
    apply hne
    show D.vLet k r z z' j hj l (e 0) (D.uwG k r z z' F j hj w fun a => e a.succ) g = 0
    refine vLet_zero_near z z' j hj l (e 0) _ (V := {x | R < B.gN x})
      (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous) (fun x hx hxG => ?_) g hgt hg
    by_contra h0
    exact absurd (uwG_supp z z' F R hR j hj w _ x hxG h0) (not_le.2 hx)

theorem contOn_of_loc {f : B.Mat k r → E} {S : Set (B.Mat k r)}
    (h : ∀ x ∈ S, x ∈ B.GV k r → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) f x) : ContinuousOn f {x | x ∈ B.GV k r ∧ x ∈ S} := by
  intro x hx
  obtain ⟨U, f', hU, hxU, hf', he⟩ := h x hx.2 hx.1
  have hc : ContinuousWithinAt f' {x | x ∈ B.GV k r ∧ x ∈ S} x :=
    ((hf'.continuousOn).continuousAt (hU.mem_nhds hxU)).continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (he x hxU hx.1)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hxU), self_mem_nhdsWithin] with y hyU hyS
  exact he y hyU hyS.1

end supp

end Formalism.FourierDecayAlt.P.PBG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocSetCApp
namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate

noncomputable section

def PStdC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2)

theorem pStdC_of (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) : PStdC :=
  Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT

theorem decay_scale (lam x : ℝ) (hlam : 0 < lam) (hx : 0 ≤ x) :
    ((1 + lam * x) ^ 3)⁻¹ ≤ (max 1 lam⁻¹) ^ 3 * ((1 + x) ^ 3)⁻¹ := by
  have hM : 1 ≤ max 1 lam⁻¹ := le_max_left _ _
  have hle : 1 + x ≤ max 1 lam⁻¹ * (1 + lam * x) := by
    rcases le_or_gt 1 lam with h1 | h1
    · have e1 : x ≤ lam * x := le_mul_of_one_le_left hx h1
      have e2 : 1 + lam * x ≤ max 1 lam⁻¹ * (1 + lam * x) := le_mul_of_one_le_left (by positivity) hM
      linarith
    · have hi : lam⁻¹ ≤ max 1 lam⁻¹ := le_max_right _ _
      have e : lam⁻¹ * (1 + lam * x) = lam⁻¹ + x := by field_simp
      have h2 : 1 ≤ lam⁻¹ := by rw [le_inv_comm₀ one_pos hlam]; simpa using h1.le
      nlinarith [mul_le_mul_of_nonneg_right hi (by positivity : (0 : ℝ) ≤ 1 + lam * x)]
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 + lam * x := by positivity
  have hc : (1 + x) ^ 3 ≤ (max 1 lam⁻¹) ^ 3 * (1 + lam * x) ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h1.le hle 3
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ((1 + lam * x) ^ 3)⁻¹ * (1 + x) ^ 3 ≤ ((1 + lam * x) ^ 3)⁻¹ * ((max 1 lam⁻¹) ^ 3 * (1 + lam * x) ^ 3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (max 1 lam⁻¹) ^ 3 := by field_simp

section frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def Kg (S : C.HidaSetting E Wp Wq) (j : ℕ) (h h' : C.LPt) : ℝ :=
  √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * rhoS S j

theorem gramLoc_setC_app {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) (c : ℂ) (hc : c ≠ 0) :
    (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) =
      ((Kg S j h h' : ℝ) : ℂ) * ((KB.levW (D.parOf S v) (j + 1) ((lamS S j : ℂ) * c) : ℝ) : ℂ) *
        (p v).RR (F v ε) (j + 1) w (stdS S h ++ [(1, (lamS S j : ℂ) * c)])
          (stdS S h' ++ [(1, (lamS S j : ℂ) * c)]) := by
  have hgpos := g_pos_of_built hB
  have hTT := (pdG_of_built hB v).2
  have hrd := rd_pos' E
  have hfr : ∀ b s, 0 < S.fr b s := fun b s => Real.rpow_pos_of_pos hrd _
  set lam := lamS S j with hlam
  have hlam_pos : 0 < lam := lamS_pos S hgpos j
  set xw : ℂ → ℝ := fun c => C.nAux S.G.k S.G.r (Complex.normSq c - S.T * S.T') S.fr (j + 1) [(1, c)] with hxw
  have hn_nonneg : ∀ H, D.ptSize H = j → 0 ≤ nnS S H := fun H hH =>
    lpt_value_nonneg_of_pos_of_size_le _ _ _ _ hfr H 1 le_rfl (by omega)
  have hsq : √(nnS S (h ++ [(1, c)])) * √(nnS S (h' ++ [(1, c)])) =
      √(nnS S h) * √(nnS S h') * (√(xw c) * √(xw c)) := by
    rw [nnS_app S j hj h c hsz, nnS_app S j hj h' c hsz', Real.sqrt_mul (hn_nonneg h hsz),
      Real.sqrt_mul (hn_nonneg h' hsz')]
    ring
  set RRs : ℕ → C.LPt → C.LPt → ℂ := fun i P Q => (p v).RR (F v ε) i w P Q with hRRs
  set Mj : ℤ := C.Mlev S.G.k S.G.r (j + 1) with hMj
  have hW : ∀ (H H' : C.LPt), D.ptSize H = j →
      ((√(xw c) * √(xw c) : ℝ) : ℂ) * RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) =
        ((rhoS S j * KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) : ℝ) : ℂ) *
          RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) := by
    intro H H' hH
    by_cases hjt : j = S.G.r
    · have hnu : S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
        unfold S6.nuBlock; rw [hjt]; push_cast; ring
      have hlam1 : lam = 1 := by rw [hlam, lamS, hnu, zpow_zero]
      have hfr1 : S.fr (j + 1) 1 = 1 := by
        unfold C.HidaSetting.fr
        have : ((S6.nuBlock (S.G.r : ℤ) (Nat.cast (j + 1)) (Nat.cast 1) : ℤ) : ℝ) = 0 := by
          unfold S6.nuBlock; rw [hjt]; push_cast; ring
        rw [this]; simp
      have hρ1 : rhoS S j = 1 := by rw [rhoS, ← hlam, hlam1, hfr1]; simp
      have hx : xw c = (Complex.normSq c - S.T * S.T') ^ (S.G.k - 1) := by
        simp only [hxw, C.nAux]
        rw [if_pos (by constructor <;> first | trivial | omega), mul_one]
      have hlev : KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) = B2.zWeight S.G.k S.T S.T' c := by
        rw [hlam1, Complex.ofReal_one, one_mul]
        unfold KB.levW
        rw [if_pos (by simp [hjt])]
      rw [hρ1, hlev, one_mul, hx]
      by_cases hc2 : S.T * S.T' ≤ Complex.normSq c
      · rw [Real.mul_self_sqrt (pow_nonneg (by linarith) _)]
        unfold B2.zWeight
        rw [if_pos hc2]
      · have h0 : RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) = 0 := by
          have := rrTop_zero (D.parOf S v) (p v).l0 (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP
            (M.sgn (D.parOf S v) (p v).l0) (F v ε) w H (H' ++ [(1, (lam : ℂ) * c)])
            ((lam : ℂ) * c) (by rw [hH, hjt]) (by
              rw [hlam1, Complex.ofReal_one, one_mul]
              rw [hTT]; linarith)
          simp only [hRRs]
          rw [show j + 1 = (D.parOf S v).r + 1 by rw [hjt]]
          exact this
        rw [h0, mul_zero, mul_zero]
    · have hx : xw c = (S.fr (j + 1) 1 * ‖c‖) ^ (2 * (Mj - 2)) := by
        simp only [hxw, C.nAux]
        rw [if_neg (by omega), mul_one, hMj]
        congr 1
        simp only [Nat.add_sub_cancel, Nat.cast_one]
        ring
      have hxpos : 0 < xw c := by rw [hx]; exact zpow_pos (mul_pos (hfr _ _) (norm_pos_iff.2 hc)) _
      rw [Real.mul_self_sqrt hxpos.le]
      congr 2
      rw [hx, rhoS, ← hlam, ← hMj]
      unfold KB.levW
      rw [if_neg (by show ¬ (j + 1 = S.G.r + 1); omega)]
      have hnorm : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnorm, ← mul_zpow]
      congr 1
      field_simp
  rw [gramLoc_setC hB, stdS_app S j h c hsz, stdS_app S j h' c hsz']
  have hWc := hW (stdS S h) (stdS S h') (by rw [stdS_size]; exact hsz)
  have hb1 : bS S (h ++ [(1, c)]) = bS S h := bSt_append_one _ _ _
  have hb2 : bS S (h' ++ [(1, c)]) = bS S h' := bSt_append_one _ _ _
  rw [hb1, hb2, hsq]
  simp only [hRRs] at hWc
  unfold Kg
  push_cast at hWc ⊢
  linear_combination ((√(nnS S h) : ℂ) * (√(nnS S h') : ℂ) *
    (1 / ((bS S h : ℂ) * (bS S h' : ℂ) * (ΓS S (j + 1) : ℂ)))) * hWc

theorem int_gramLoc_setC (hPS : PStdC) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (hF : KB.CptCoef (p v).T.base (F v ε)) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter)
    (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt) (hh : D.IsLocPt h j)
    (hh' : D.IsLocPt h' j) :
    ∫ c : ℂ, (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c =
      ((Kg S j h h' * |(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2)) := by
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
  have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
  obtain ⟨φ, -, -, hφ, hφint⟩ := hPS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj w
    (stdS S h) (stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) hF (by rw [hl0]; exact hw)
  have hlam_pos := lamS_pos S hgpos j
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun c' => P5.fsv (sW S j l) c' * φ c' := ⟨_, rfl⟩
  have hae : (fun c : ℂ => (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) *
      KB.psiL S l c) =ᵐ[volume] fun c => ((Kg S j h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    filter_upwards [ae_ne_zero_complex] with c hc
    have hlc : (lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
    simp only [hgdef, Complex.real_smul]
    rw [gramLoc_setC_app hB F v ε j hj w h h' hh.2 hh'.2 c hc, hφ _ hlc, psiL_eq_fsv S hgpos j l c]
    ring
  rw [integral_congr_ae hae, integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex,
    Complex.real_smul, hgdef]
  simp only
  rw [hφint (sW S j l)]
  push_cast
  ring

end frame

end

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

def DecayUnif : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ) (lo hi : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    (∀ Y, lo ≤ Y → Y ≤ hi → I.OnCut P.u P.u' p.l0 Y) → 10 * ((N : ℝ) + 3 * (2 * P.r + 1) + 1) ≤ hi - lo →
    ∀ (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → w.length ≤ N →
    ∀ (h h' : C.LPt) (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j),
    ∃ C : ℝ, ∀ n : ℕ,
      (∀ c : ℂ, c ≠ 0 → ‖(KB.levW P (j + 1) c : ℂ) * p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) (j + 1) w
        (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
      ∀ s : ℂ, ‖p.form j hj w (KB.waveG (p.T.bs j) s w
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj w h hh.2))
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ C * ((1 + ‖s‖) ^ 3)⁻¹

section wave

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def waveL (Bs : B.RealPlaceData k ρ Wp Wq) (s : ℂ) (w : List C.Letter) :
    (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) where
  toFun := KB.waveG Bs s w
  map_add' x y := by simpa using Formalism.FourierDecayAlt.P.PBG.waveG_add_smul Bs s w x y 1
  map_smul' c x := by
    simpa [Formalism.FourierDecayAlt.P.PBG.waveG_zero] using Formalism.FourierDecayAlt.P.PBG.waveG_add_smul Bs s w 0 x c

def mDiff (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter) :
    (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :=
  (waveL Bs σ w - 1) ^ 3

end wave

def WaveDiffForm : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → w.length ≤ N →
    ∀ (h : C.LPt) (hh : D.IsLocPt h j), ∀ ys : List ℝ, ys.length ≤ 3 → KB.CutWord P p.l0 (KB.plusW ys w) →
      ∃ C : ℝ, ∀ (n : ℕ) (σ : ℂ), ‖σ‖ ≤ 2 →
      ‖p.form j hj (KB.plusW ys w) (KB.onOld (mDiff (p.T.bs j) σ w) ys
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj (KB.plusW ys w) h hh.2))
        (KB.onOld (mDiff (p.T.bs j) σ w) ys
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj (KB.plusW ys w) h hh.2))‖ ≤ C * ‖σ‖ ^ 6

theorem cutWord_sub (P : M.Par) (l0 : ℕ) (w : List C.Letter) (ys zs : List ℝ) (hz : ∀ z ∈ zs, z ∈ ys)
    (hpw : zs.Pairwise (fun y y' => 2 < |y - y'|)) (h1 : KB.CutWord P l0 (KB.plusW ys w))
    (h2 : KB.CutWord P l0 (KB.minusW ys w)) :
    KB.CutWord P l0 (KB.plusW zs w) ∧ KB.CutWord P l0 (KB.minusW zs w) := by
  have hsub := hz
  have hplus : ∀ ys : List ℝ, KB.plusW ys w = ys.map (fun y => ((true, y) : C.Letter)) ++ w := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih => simp [KB.plusW, ih]
  have hminus : ∀ ys : List ℝ, KB.minusW ys w = ys.map (fun y => ((false, y + 1) : C.Letter)) ++ w := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih => simp [KB.minusW, ih]
  have hiff : ∀ L : List C.Letter, KB.CutWord P l0 L ↔
      (∀ l ∈ L, I.OnCut P.u P.u' l0 l.2) ∧ L.Pairwise (fun l l' => 2 < |l.2 - l'.2|) := by
    intro L
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun l hl => ?_, ?_⟩
      · obtain ⟨a, rfl⟩ := List.get_of_mem hl
        exact h1 a
      · rw [List.pairwise_iff_get]
        intro i j hij
        exact h2 i j (ne_of_lt hij)
    · rintro ⟨h1, h2⟩
      refine ⟨fun a => h1 _ (List.get_mem L a), fun a b hab => ?_⟩
      rw [List.pairwise_iff_get] at h2
      rcases lt_or_gt_of_ne hab with h | h
      · exact h2 a b h
      · rw [abs_sub_comm]
        exact h2 b a h
  rw [hiff, hplus, List.pairwise_append] at h1
  rw [hiff, hminus, List.pairwise_append] at h2
  obtain ⟨h1on, -, h1w, h1x⟩ := h1
  obtain ⟨h2on, -, h2w, h2x⟩ := h2
  rw [hiff, hiff, hplus, hminus, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨fun l hl => ?_, ?_, h1w, fun a ha b hb => ?_⟩, ⟨fun l hl => ?_, ?_, h2w, fun a ha b hb => ?_⟩⟩
  · rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hl
      exact h1on _ (List.mem_append_left _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩))
    · exact h1on _ (List.mem_append_right _ hl)
  · exact List.pairwise_map.2 hpw
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    exact h1x _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩) b hb
  · rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hl
      exact h2on _ (List.mem_append_left _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩))
    · exact h2on _ (List.mem_append_right _ hl)
  · refine List.pairwise_map.2 (hpw.imp fun {a b} hab => ?_)
    simpa [add_sub_add_right_eq_sub] using hab
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    exact h2x _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩) b hb

theorem grid_exists (P : M.Par) (l0 : ℕ) (lo hi : ℝ) (hcut : ∀ Y, lo ≤ Y → Y ≤ hi → I.OnCut P.u P.u' l0 Y)
    (w : List C.Letter) (hw : KB.CutWord P l0 w) (j : ℕ)
    (hroom : 10 * ((w.length : ℝ) + 3 * (2 * j + 1) + 1) ≤ hi - lo) :
    ∃ grid : Fin 3 → Fin (2 * j + 1) → ℝ, (∀ a, Function.Injective (grid a)) ∧
      ∀ n : Fin 3 → Fin (2 * j + 1), KB.CutWord P l0 (KB.plusW (List.ofFn fun a => grid a (n a)) w) ∧
        KB.CutWord P l0 (KB.minusW (List.ofFn fun a => grid a (n a)) w) ∧
        (List.ofFn fun a => grid a (n a)).Pairwise (fun y y' => 2 < |y - y'|) := by
  obtain ⟨ys, hl, -, hp, h1, h2⟩ := Formalism.FourierDecayAlt.P.room_off_grid P l0 lo hi hcut w (3 * (2 * j + 1)) ∅ hw
    (by simpa using hroom)
  have hget : ∀ i i' : Fin ys.length, i ≠ i' → 4 < |ys.get i - ys.get i'| := by
    intro i i' hne
    rw [List.pairwise_iff_get] at hp
    rcases lt_or_gt_of_ne hne with h | h
    · exact hp i i' h
    · have := hp i' i h
      rwa [abs_sub_comm] at this
  let idx : Fin 3 → Fin (2 * j + 1) → Fin ys.length := fun a i => ⟨a.val * (2 * j + 1) + i.val, by
    rw [hl]; have := a.isLt; have := i.isLt; nlinarith⟩
  have hidx : ∀ a b i i', idx a i = idx b i' → a = b ∧ i = i' := by
    intro a b i i' he
    have e : a.val * (2 * j + 1) + i.val = b.val * (2 * j + 1) + i'.val := congrArg Fin.val he
    have hi := i.isLt
    have hi' := i'.isLt
    have hab : a.val = b.val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have : (a.val + 1) * (2 * j + 1) ≤ b.val * (2 * j + 1) := Nat.mul_le_mul_right _ h
        nlinarith
      · have : (b.val + 1) * (2 * j + 1) ≤ a.val * (2 * j + 1) := Nat.mul_le_mul_right _ h
        nlinarith
    refine ⟨Fin.ext hab, Fin.ext ?_⟩
    rw [hab] at e
    omega
  refine ⟨fun a i => ys.get (idx a i), fun a i i' he => ?_, fun n => ?_⟩
  · by_contra hne
    have := hget (idx a i) (idx a i') (fun h => hne (hidx a a i i' h).2)
    simp only at he
    rw [he, sub_self, abs_zero] at this
    linarith
  · have hpw : (List.ofFn fun a => ys.get (idx a (n a))).Pairwise (fun y y' => 2 < |y - y'|) := by
      rw [List.pairwise_ofFn]
      intro a b hab
      have := hget (idx a (n a)) (idx b (n b)) (fun h => (ne_of_lt hab) (hidx a b _ _ h).1)
      linarith
    have hz : ∀ z ∈ (List.ofFn fun a => ys.get (idx a (n a))), z ∈ ys := by
      intro z hz
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hz
      exact List.get_mem _ _
    obtain ⟨c1, c2⟩ := cutWord_sub P l0 w ys _ hz hpw h1 h2
    exact ⟨c1, c2, hpw⟩

theorem onOld_cpt {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {w : List C.Letter} (Bs : B.RealPlaceData k ρ Wp Wq)
    (M : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) → Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hM : ∀ x, (∀ e, KB.CptCoef Bs (x e)) → ∀ e, KB.CptCoef Bs (M x e)) :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
      (∀ e, KB.CptCoef Bs (x e)) → ∀ e, KB.CptCoef Bs (KB.onOld M ys x e)
  | [], x, h => hM x h
  | _ :: ys, x, h => fun e => onOld_cpt Bs M hM ys
      (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun _ => h _) _

theorem wave_bound3 (hP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef p.T.base F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j)
    (grid : Fin 3 → Fin (2 * j + 1) → ℝ) (hinj : ∀ a, Function.Injective (grid a))
    (hgr : ∀ n : Fin 3 → Fin (2 * j + 1), KB.CutWord P p.l0 (KB.plusW (List.ofFn fun a => grid a (n a)) w) ∧
        KB.CutWord P p.l0 (KB.minusW (List.ofFn fun a => grid a (n a)) w) ∧
        (List.ofFn fun a => grid a (n a)).Pairwise (fun y y' => 2 < |y - y'|))
    (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))
    (hMo : ∀ ε x, (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → ∀ e, JC.NiceCoef (p.T.bs j) ε (Mo x e))
    (hMoC : ∀ x, (∀ e, KB.CptCoef (p.T.bs j) (x e)) → ∀ e, KB.CptCoef (p.T.bs j) (Mo x e)) (s : ℂ) :
    ‖s‖ ^ 3 * ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo (KB.slv p.T F j hj w h hh.2)))
      (KB.slv p.T F j hj w h' hh'.2)‖ ≤
    ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
      Real.sqrt ((p.form j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w)
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))).re *
        (p.form j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w)
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)).re /
        ((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod) := by
  have hdeg := Formalism.FourierDecayAlt.P.degree_of_plane_wave Wp Wq P p F j hj w h h' hh hh' 3 grid s Mo hMo hF hinj
  rw [← norm_pow, ← norm_mul, hdeg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  obtain ⟨hc1, hc2, hpw⟩ := hgr n
  set ys := List.ofFn fun a => grid a (n a) with hys
  obtain ⟨hq, hss⟩ := Formalism.FourierDecayAlt.P.size_standard_compact hP Wp Wq P p j hj w ys hc1 hc2 hpw
  set X := KB.slv p.T F j hj (KB.plusW ys w) h hh.2 with hX
  set Y := KB.slv p.T F j hj (KB.minusW ys w) h' hh'.2 with hY
  have hXc : ∀ e, KB.CptCoef (p.T.bs j) (X e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj (KB.plusW ys w) h hh hF e
  have hYc : ∀ e, KB.CptCoef (p.T.bs j) (Y e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj (KB.minusW ys w) h' hh' hF e
  have hOc : ∀ e, KB.CptCoef (p.T.bs j) (KB.onOld Mo ys X e) := onOld_cpt (p.T.bs j) Mo hMoC ys X hXc
  obtain ⟨hWc, hiso⟩ := Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support hP Wp Wq P p j hj (KB.plusW ys w) hc1 s
    (KB.onOld Mo ys X) (KB.onOld Mo ys X) hOc hOc
  have key := hss (KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld Mo ys X)) Y hWc hYc
  rw [hiso] at key
  have hqpos : 0 < (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod := by
    refine List.prod_pos fun a ha => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    exact hq y hy
  have habs := Real.abs_le_sqrt ((le_div_iff₀ hqpos).2 key)
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

end Formalism.FourierDecayAlt.P.PBO
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadPictureEmptyWord
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section read

variable {k : ℕ}

theorem pic_read {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n ρ : ℕ} (hn : 1 + ρ = n)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    (Φ : Fn k n E) (J : Mx k n → E)
    (hΦ : ∀ x ∈ DomR k n z z', Φ x.1 x.2 = resG k n (Fin.last n) J x.1 x.2)
    {t : ℂ} (ht : t ≠ 0) (y : (Fin ρ → ℂ) × Mx k ρ) (hy : y ∈ DomR k ρ zs zs') :
    Φ (fun l => PBH.consC t y.1 (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ y.2)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) y.1 y.2 := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hΦ _ ((PBH.domR_iota ht zs zs' y.1 y.2).2 hy)]
  exact resG_consC ht J y.1 y.2

end read

def HeadPicNil : Prop :=
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (L : R.LevelData (Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (Φ : Wd.Ix (Fin ([] : List C.Letter).length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    KB.CptCoef p.T.base F →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Φ e) (KB.slv p.T F j (by omega) [] h hh.2 e)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin ([] : List C.Letter).length)),
    ∀ y ∈ Q.DomR P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z',
      (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ e :
          Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp))
        (fun l => PBH.consC t y.1 (Fin.cast (by change P.r - j = 1 + (P.r - (j + 1)); omega) l))
          (D.castM (by change 1 + (P.r - (j + 1)) = P.r - j; omega) (ιLev P.k 1 (P.r - (j + 1)) y.2)) =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
          Q.resG P.k (P.r - (j + 1)) (Fin.last _)
            (B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj [] (h ++ [(1, t)]) ht.2 e)) y.1 y.2

theorem headPic_nil (hS : KB.SliceStep) : HeadPicNil := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h hh L Φ hF hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega

  have hact : P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ = Φ :=
    Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ Φ
  rw [hact]
  have hread := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
    (Subtype.val (Φ e)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) [] h hh.2 e))
    (hΦ e) ht0 y hy
  refine hread.trans ?_
  congr 1
  unfold resG
  congr 1
  have hc : ∀ a, y.1 a ≠ 0 := hy.1
  have hγ := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV (i := Fin.last _) hc hy.2.1
  have hΩ := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2
  have he : e = fun a => a.elim0 := funext fun a => a.elim0
  subst he
  exact (hS Wp Wq P p F j hj h t hh ht hF _ hγ hΩ).symm

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem head_picture_empty_word : PBP.HeadPicNil := PBP.headPic_nil slice_induction_level

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftCovarianceChartHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem left_covariance_chart_holds : CovL := by
  intro k r d O U κ Φ hC x hx ξ Ξ₀ _hΞ₀ hcov X hX
  have hg : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
  obtain ⟨hgi, hig, hHg, hgH⟩ := gv_facts hg
  have hY : B.inLie k r ((κ x)⁻¹ * X * κ x) := by
    unfold B.inLie at hX ⊢

    have e1 : ((κ x)⁻¹ * X * κ x)ᴴ * Hpk k r = (κ x)ᴴ * (Xᴴ * Hpk k r) * κ x := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [← hHg]
    have e2 : Hpk k r * ((κ x)⁻¹ * X * κ x) = (κ x)ᴴ * (Hpk k r * X) * κ x := by
      simp only [← Matrix.mul_assoc]
      rw [← hgH]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX, Matrix.mul_zero, Matrix.zero_mul]
  have hV : VL κ Φ X x = VR κ Φ ((κ x)⁻¹ * X * κ x) x := by
    show fderiv ℝ Φ (κ x) (X * κ x) = fderiv ℝ Φ (κ x) (κ x * ((κ x)⁻¹ * X * κ x))
    rw [show κ x * ((κ x)⁻¹ * X * κ x) = X * κ x by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hig, Matrix.one_mul]]
  have ht : Matrix.trace (Ξ₀ * ((κ x)⁻¹ * X * κ x)) = Matrix.trace (κ x * Ξ₀ * (κ x)⁻¹ * X) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hV, hcov _ hY, ht]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
