module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.SameChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem fills_Pj_m_add_one {p : ℕ} {G : GAtP p} (Fl : Fills G) (j : ℕ) :
    (Fl.Pj j).m + 1 = Formalism.MainNotions.FormalGroupSystem.NN G.P.m Fl.t j := by
  cases j with
  | zero => simp [Fills.Pj, Formalism.MainNotions.FormalGroupSystem.NN]
  | succ j => simp only [Fills.Pj, Places.withWt, Formalism.MainNotions.FormalGroupSystem.NN]; ring

theorem sysS_ranks : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (sysS H X std).mm = D.R.m ∧ (sysS H X std).t = D.R.t ∧ (∀ j, ((sysS H X std).Pj j).m + 1 = D.R.N j) ∧ ∀ j, RankTie (sysS H X std) D j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  have hk : (D.gat u w hg).P.m + 1 = D.R.N 0 := (lev0At J.Gd u w hg).A.rk
  have ht : (Gl.Fl u w hg).t = D.R.t := X.fl_t
  have hN : ∀ j, D.R.N j = Formalism.MainNotions.FormalGroupSystem.NN (D.gat u w hg).P.m (Gl.Fl u w hg).t j := by
    intro j
    simp only [Formalism.MainNotions.FormalGroupSystem.NN, ht]
    simp only [Formalism.BasicNotions.Ranks.N] at hk ⊢
    omega
  refine ⟨X.fl_m, X.fl_t, fun j => ?_, fun j => ⟨hN j, hN (j + 1)⟩⟩
  exact (fills_Pj_m_add_one (Gl.Fl u w hg) j).trans (hN j).symm

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanksStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siteSystem_ranks_eq_datum_ranks : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (sysS H X std).mm = D.R.m ∧ (sysS H X std).t = D.R.t ∧ (∀ j, ((sysS H X std).Pj j).m + 1 = D.R.N j) ∧ ∀ j, RankTie (sysS H X std) D j) := by
  first | exact @GlobalTheory.TwV.DelB.sysS_ranks | exact GlobalTheory.TwV.DelB.sysS_ranks | (intros; apply GlobalTheory.TwV.DelB.sysS_ranks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalContragredientMonomial
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.WeakTheRep

theorem eq_of_mono0_charPol {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (x y : WD h)
    (hx : x.mono0) (hy : y.mono0) (hc : ∀ g, x.charPol g = y.charPol g) : x = y := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hx hy
  obtain ⟨e, he⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n m a b
    (fun σ => by rw [← WD.charPol_mk, ← WD.charPol_mk]; exact hc σ)
  exact WD.sound ⟨e, he, fun v => by rw [hx, hy]; simp⟩

theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') {K : Subgroup G}
    (h : GlobalTheory.PRep.fixed ρ K ≠ ⊥) : GlobalTheory.PRep.fixed ρ' K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e v, ?_, fun h0 => hv0 ?_⟩
  · refine GlobalTheory.ContraRefl.mem_fix.2 fun g hg => ?_
    have h1 := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
    simp only [LinearMap.comp_apply] at h1
    rw [GlobalTheory.ContraRefl.mem_fix.1 hv g hg] at h1
    exact h1.symm
  · exact e.toLinearEquiv.injective (h0.trans (map_zero e.toLinearEquiv).symm)

end GlobalTheory.WeakTheRep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatrices
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

open Matrix

section Gen

variable {E : Type} [Field E] {N : ℕ}

theorem toLE_eq_mulVec (γ : GL (Fin N) E) (x : Fin N → E) : toLE γ x = γ.1 *ᵥ x := rfl

theorem toStdCo_stdG_eq (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) :
    ((toStdCo σ G co).trans (stdG σ G γ)).toLinearMap =
      ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap ∘ₗ Matrix.toLin' (co.1 * γ.1 * (co⁻¹).1) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (toLE co).surjective x
  have h1 : (co⁻¹ : GL (Fin N) E).1 * co.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (toLE (1 : GL (Fin N) E)) = LinearEquiv.refl E _ := by
    ext z : 1
    simp [toLE_eq_mulVec]
  have h3 : Matrix.toLin' (co.1 * γ.1 * (co⁻¹).1) (toLE co y) = toLE co (toLE γ y) := by
    rw [Matrix.toLin'_apply, toLE_eq_mulVec, toLE_eq_mulVec, toLE_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc _ (co⁻¹).1, h1, Matrix.mul_one]
  rw [LinearMap.comp_apply, h3]
  simp [toStdCo, stdG, h2]

theorem det_toStdCo_stdG (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) :
    (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G γ)).toLinearMap).det =
      γ.1.det * (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap).det := by
  rw [toStdCo_stdG_eq, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.det_mul, Matrix.det_mul,
    Matrix.det_mul]
  have h : (co.1).det * ((co⁻¹ : GL (Fin N) E).1).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  calc _ = γ.1.det * ((co.1).det * ((co⁻¹ : GL (Fin N) E).1).det) *
        (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap).det := by ring
    _ = _ := by rw [h, mul_one]

theorem det_cT (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E) : (cT σ M).det = σ M.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem det_norm_of_UJ (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E)
    (hco : cT σ co.1 * co.1 = G) (hγ : γ ∈ UJ σ G) : σ γ.1.det * γ.1.det = 1 := by
  have hγ' : cT σ γ.1 * G * γ.1 = G := hγ
  have hG : G.det ≠ 0 := by
    rw [← hco, Matrix.det_mul, det_cT]
    have hc : (co.1).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp co.isUnit |>.ne_zero
    exact mul_ne_zero ((map_ne_zero σ).mpr hc) hc
  have h := congrArg Matrix.det hγ'
  rw [Matrix.det_mul, Matrix.det_mul, det_cT] at h
  have h' : (σ γ.1.det * γ.1.det - 1) * G.det = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hG

end Gen

end GlobalTheory.TwV.DelB

namespace GlobalTheory.TwV.DelB

theorem gMat_det : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ k (hk : k ≤ D.R.m), (gMat J k hk 1).det * D.host.conj (gMat J k hk 1).det = 1 ∧
      ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk),
        (gMat J k hk γ).det = γ.1.det * (gMat J k hk 1).det ∧ γ.1.det * D.host.conj γ.1.det = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S k hk
  have hs : ∀ y : D.host.E, (sigD D : D.host.E →+* D.host.E) y = D.host.conj y := fun y =>
    Formalism.BasicNotions.bridge_star_holds D.R D.host y
  have hco := J.pins.crd_orth k hk
  refine ⟨?_, fun γ hγ => ⟨?_, ?_⟩⟩
  · have h := GlobalTheory.TwV.cT_mul_self_toStdCo_stdG (sigD D : D.host.E →+* D.host.E) (gramN D k hk) (J.A.crd k hk) 1 hco
      (Subgroup.one_mem _)
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, det_cT, Matrix.det_one, hs] at h2
    rw [mul_comm]
    exact h2
  · exact det_toStdCo_stdG _ _ _ _
  · have h := det_norm_of_UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk) (J.A.crd k hk) γ hco hγ
    rw [hs, mul_comm] at h
    exact h

end GlobalTheory.TwV.DelB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatricesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ k (hk : k ≤ D.R.m), (gMat J k hk 1).det * D.host.conj (gMat J k hk 1).det = 1 ∧ ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk), (gMat J k hk γ).det = γ.1.det * (gMat J k hk 1).det ∧ γ.1.det * D.host.conj γ.1.det = 1) := by
  first | exact @GlobalTheory.TwV.DelB.gMat_det | exact GlobalTheory.TwV.DelB.gMat_det | (intros; apply GlobalTheory.TwV.DelB.gMat_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecompositionUnitaryMulStarEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecompositionUnitaryMulStarEqOne
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem Dec.eM_mul_star : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ (d : Dec J std) j La, d.eM j La * star (d.eM j La) = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j La
  unfold Dec.eM
  split_ifs with h
  · have hu := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary J.A J.dtU J.a J.pins J.tie j h.1 (d.gam j h.1 La) (d.mem j h.1 La)
    have hc : (Fin.cast h.2 : Fin (((sysS H X std).Pj j).m + 1) → Fin (D.R.N j)) = ⇑(finCongr h.2) := rfl
    rw [hc, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose]
    have hu' : gMat J j h.1 (d.gam j h.1 La) * star (gMat J j h.1 (d.gam j h.1 La)) = 1 := hu
    rw [hu', Matrix.submatrix_one_equiv]
  · simp

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecompositionUnitaryMulStarEqOneStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_unitary_mul_star_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j La, d.eM j La * star (d.eM j La) = 1) := by
  first | exact @GlobalTheory.TwV.DelB.Dec.eM_mul_star | exact GlobalTheory.TwV.DelB.Dec.eM_mul_star | (intros; apply GlobalTheory.TwV.DelB.Dec.eM_mul_star <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponents
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponents
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem wG_succ_eq_shift (R : Ranks) (z : ℤ) (j : ℕ) :
    Formalism.BasicNotions.wG R (z : ℚ) (j + 1) = ((z - ((j * (R.t + 1) / 2 : ℕ) : ℤ) - ((R.N (j + 1) / 2 : ℕ) : ℤ) : ℤ) : ℚ) := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  have h1 : j * (R.t + 1) / 2 = j * (b + 1) := by
    rw [hb, show j * (2 * b + 1 + 1) = 2 * (j * (b + 1)) by ring]; omega
  have h2 : R.N (j + 1) / 2 = a + (j + 1) * (b + 1) := by
    show (R.k + (j + 1) * (R.t + 1)) / 2 = _
    rw [hb, ha, show a + a + (j + 1) * (2 * b + 1 + 1) = 2 * (a + (j + 1) * (b + 1)) by ring]; omega
  rw [h1, h2]
  unfold Formalism.BasicNotions.wG
  rw [ha, hb]
  push_cast
  ring


set_option maxHeartbeats 4000000 in
theorem fillAt_of_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ j (hj : j < D.R.m), (sysS H X std).Lv.comp (j + 1) → FillAt (hT := hT) (H := H) (X := X) std j hj) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c
  have hj' : j + 1 ≤ D.R.m := hj
  have c' : Lv.comp (j + 1) := c
  have hW := (H.core j hj' ((I.at' j hj').st.eC.symm c').1).wt
  rw [J.pos j hj'] at hW
  have ht : (Gl.Fl u w hg).t = D.R.t := X.fl_t
  have hk := hT.gat_k u w hg
  have rk := rk_of hT w hg (Gl.Fl u w hg) ht j
  intro e he v s
  show (Gl.Fl u w hg).w v (j + 1) s = e (hT.gat_pos u w hg ⟨v, s⟩) - ((j * ((Gl.Fl u w hg).t + 1) / 2 : ℕ) : ℤ) -
      (((((Gl.Fl u w hg).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)
  have hlt : (D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) < ((Gl.Fl u w hg).Pj (j + 1)).m + 1 := by
    show _ < (D.gat u w hg).P.m + (j + 1) * ((Gl.Fl u w hg).t + 1) + 1
    nlinarith
  have h := hW v s ⟨_, hlt⟩
  have h0 := (congrArg (fun z : ℤ => (z : ℚ)) h).trans (((I.at' j hj').M).lam_eq (j + 1) hj' (hT.gat_pos u w hg ⟨v, s⟩) _)
  have hi : ¬ (D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) < D.R.k := by omega
  have hq : ((D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) - D.R.k) / (D.R.t + 1) = j := by
    rw [← hk, ← ht, Nat.add_sub_cancel_left]; exact Nat.mul_div_cancel _ (Nat.succ_pos _)
  simp only [finCongr_apply, Fin.coe_cast] at h0
  rw [dite_eq_right hi] at h0
  simp only [hq] at h0
  have hL : ((Gl.Fl u w hg).Pj (j + 1)).lam0 v s ⟨_, hlt⟩ = -((Gl.Fl u w hg).w v (j + 1) s) := by
    show liftWt (Gl.Fl u w hg).t (D.gat u w hg).P.m ((D.gat u w hg).P.lam0 v s) (fun a => (Gl.Fl u w hg).w v a s) (j + 1) ⟨_, hlt⟩ = _
    unfold liftWt
    rw [dite_eq_right (Nat.not_lt.mpr (Nat.le_add_right _ _))]
    congr 2
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.mul_div_cancel _ (Nat.succ_pos _)]
  rw [hL, Int.cast_neg, neg_inj, D.hcW_e, ← he] at h0
  rw [rk, ht]
  apply Int.cast_injective (α := ℚ)
  rw [h0]
  exact wG_succ_eq_shift D.R _ j

end GlobalTheory.TwV.Xc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponentsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.systemWeights_eq_shifted_character_exponents : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), (sysS H X std).Lv.comp (j + 1) → FillAt (hT := hT) (H := H) (X := X) std j hj) := by
  first | exact @GlobalTheory.TwV.Xc.fillAt_of_comp | exact GlobalTheory.TwV.Xc.fillAt_of_comp | (intros; apply GlobalTheory.TwV.Xc.fillAt_of_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSite
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSite
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.EigenGenerator in
theorem GlobalTheory.TwV.DelB.dgen_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ τ, ‖ι ((t.O u μ).dgen τ)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S ι hι τ
  have h5 := hg.2.1
  have hc := hg.2.2.1
  have hk := (primeClass_eq_inert_iff D.host.toHostRaw).1 hc
  have h2 : D.what₂.places.resChar w ∉ D.host.small := hk.1
  have hq : D.what₂.places.resChar w ≠ D.host.q := hk.2.1
  obtain ⟨M, hMnf, hM, hs⟩ := J.dgen
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have h1 : ι (s : ℂ) = lamM M S.lam s := hι ⟨(s : ℂ), mem_Qbar M s⟩
  rw [t.O_dgen u μ, ← hsc, h1, lamM_apply]
  exact norm_generator_eq_one D _ S.lam h2 hq M hM τ s hsp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSiteStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_derivation_generators_eq_one_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ τ, ‖ι ((t.O u μ).dgen τ)‖ = 1) := by
  first | exact @GlobalTheory.TwV.DelB.dgen_unit | exact GlobalTheory.TwV.DelB.dgen_unit | (intros; apply GlobalTheory.TwV.DelB.dgen_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameMatricesEqOfSameComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameMatricesEqOfSameComponent
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem frM_fd_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), (J.fd std).frM j (c, La) = (J.fd std).frM j (c, Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j c La Lb
  funext v
  cases j with
  | zero =>
    simp only [Joint.fd, fdAtL, fdAt, fdOfCharts, cpAt, chAt]
    rfl
  | succ i => exact Formalism.MainNotions.G.KAat.frM_comp i c La Lb v

end GlobalTheory.TwV.Xc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameMatricesEqOfSameComponentStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), (J.fd std).frM j (c, La) = (J.fd std).frM j (c, Lb)) := by
  first | exact @GlobalTheory.TwV.Xc.frM_fd_comp | exact GlobalTheory.TwV.Xc.frM_fd_comp | (intros; apply GlobalTheory.TwV.Xc.frM_fd_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumPairEqAdelicDatumTwoPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumPairEqAdelicDatumTwoPoints
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem xiM_eq_adelic : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' z = S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe hr hr' z)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj hr hr' La La' z
  have h : j + 1 ≤ D.R.m ∧ ((sysS H X std).Pj j).m + 1 = D.R.N j ∧ ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := ⟨hj, hr, hr'⟩
  have hz : Formalism.L2.Col.inFr ((J.fd std).trG j La).symm ((J.fd std).trG (j + 1) La').symm
      (Formalism.L2.Col.inFr ((J.fd std).trG j La) ((J.fd std).trG (j + 1) La') z) = z := by
    unfold Formalism.L2.Col.inFr
    ext x
    simp
  show Formalism.L2.PairingIndexBounds.F.movD _ _ _ z = _
  unfold Formalism.L2.PairingIndexBounds.F.movD Joint.xi0
  rw [dite_eq_left h, hz]

end GlobalTheory.TwV.Xc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumPairEqAdelicDatumTwoPointsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' z = S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe hr hr' z)) := by
  first | exact @GlobalTheory.TwV.Xc.xiM_eq_adelic | exact GlobalTheory.TwV.Xc.xiM_eq_adelic | (intros; apply GlobalTheory.TwV.Xc.xiM_eq_adelic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponent
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem chart_eq_of_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), ((sysS H X std).Pj j).IsLatTup La → ((sysS H X std).Pj j).IsLatTup Lb → J.chart std j hj (c, La) = J.chart std j hj (c, Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c La Lb hLa hLb
  unfold Joint.chart
  rcases j with _ | j
  · haveI := J.ch0
    exact Subsingleton.elim _ _
  · simp only
    rw [Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c La, Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c Lb]
    have ea := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c La hLa
    have eb := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c Lb hLb
    have key : ∀ (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (h : (I.at' j hj).C = C) (St' : GlobalTheory.TwU.StepCharts C (j + 1) hj)
        (_ : St' = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st)) (x y : (I.at' j hj).C.cls (j + 1)),
        (I.at' j hj).st.chOf x = (I.at' j hj).st.chOf y →
        St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) x) = St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) y) := by
      intro C h St' hst x y e
      subst h
      subst hst
      exact e
    exact key _ (X.onCh j hj) _ (J.st j hj) _ _ (ea.trans eb.symm)

end GlobalTheory.TwV.Xc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponentStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTuple_chart_eq_of_same_component : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), ((sysS H X std).Pj j).IsLatTup La → ((sysS H X std).Pj j).IsLatTup Lb → J.chart std j hj (c, La) = J.chart std j hj (c, Lb)) := by
  first | exact @GlobalTheory.TwV.Xc.chart_eq_of_comp | exact GlobalTheory.TwV.Xc.chart_eq_of_comp | (intros; apply GlobalTheory.TwV.Xc.chart_eq_of_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCodimOneStalkDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClauseAtOfRepIso
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published GlobalTheory.ContraPair

namespace GlobalTheory.GalCut

theorem clauseAt_of_repIso : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → UpperTheory.V.Af.RepIso r r' → ∀ c w, ClauseAt c π ι r w → ClauseAt c π ι r' w := by
  intro E Ω _ _ _ _ _ _ l _ ι a π r r' _ hiso c w hc
  obtain ⟨p, hp⟩ := hiso
  have hcw : ∀ {A : ValuationSubring Ω} (h : IsPlaceOver A w) (g : Weil h), p * r g = r' g * p :=
    fun h g => by rw [hp]; group
  have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := E) A)), r'.comp (Dec (F := E) A).subtype g =
      p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
  cases c with
  | ss =>
    intro hl A h rc hrc σ hσ g
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h rc hrc σ hσ g
  | pure =>
    intro hl A h wt hwt
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h wt hwt
  | dR =>
    intro P AI hT A hA O _ _ _ Bw hj
    obtain ⟨h1, h2⟩ := hc P AI hT A hA O Bw hj
    obtain ⟨k1, -, -, k4⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact ⟨k1 h1, fun τ LL' τ' hτ J hJ => k4 τ J (h2 τ LL' τ' hτ J hJ)⟩
  | crys =>
    intro P AI hT A hA O _ _ _ Bw hj σ hσ hS
    obtain ⟨-, k2, -, -⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact k2 (hc P AI hT A hA O Bw hj σ hσ hS)
  | iwa =>
    intro P AI hT A h O _ _ _ Bw hj σ hσ hI
    obtain ⟨h3, h4⟩ := hc P AI hT A h O Bw hj σ hσ hI
    exact ⟨GlobalTheory.AboveL.RepConj.isSstAt_conj P Bw p (hcd A) h3, fun rc hrc =>
      (GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)).trans (h4 rc hrc)⟩

end GlobalTheory.GalCut
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut

namespace GlobalTheory.RoadW

theorem sphAt_of_repIso {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : CuspSub E a) {r r' : G E Ω →* GL (Fin a) (Qbar l)}
    (hr : Continuous r) (hiso : UpperTheory.V.Af.RepIso r r') (c : GlobalTheory.RoadU.Sph) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hc : GlobalTheory.RoadU.SphAt c π ι r w B) : GlobalTheory.RoadU.SphAt c π ι r' w B := by
  cases c with
  | unr =>
    obtain ⟨p, hp⟩ := hiso
    intro hl A hA
    obtain ⟨h1, h2⟩ := hc hl A hA
    refine ⟨fun s hs => by rw [hp, h1 s hs]; group, fun σ hσ => ?_⟩
    rw [← h2 σ hσ, hp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  | dR => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .dR w hc
  | crys => exact clauseAt_of_repIso E Ω l ι a π r r' hr hiso .crys w hc
  | phi =>
    obtain ⟨p, hp⟩ := hiso
    have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := E) A)), r'.comp (Dec (F := E) A).subtype g =
        p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
    intro P AI hT A h O _ _ _ Bw hj g
    have e := GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)
    exact (congrArg (fun x => WD.charPol x g) e).trans (hc P AI hT A h O Bw hj g)

theorem core_of_rowStarCore : GlobalTheory.RoadW.RowStarCore → GlobalTheory.RoadU.Core := by
  intro h
  refine ⟨fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hs => ?_, fun c E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w _ B hB => ?_⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r, hr, -⟩ := h E Ω l ι a ha π hs
    exact ⟨r, hr⟩
  · obtain rfl : χ = quadChar E ^ a := hs.2.2.2
    obtain ⟨r₀, hr₀, hc⟩ := h E Ω l ι a ha π hs
    refine sphAt_of_repIso ι π hr₀.1 (weak_repIso E Ω l ι a π r₀ r hr₀ hr) c w B ?_
    obtain ⟨h1, h2, h3, h4⟩ := hc w B hB
    cases c
    exacts [h1, h2, h3, h4]

end GlobalTheory.RoadW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersCharOnNormOneIdelesMulUnramifiedClassValueStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharOnNormOneIdelesMulUnramifiedClassValue
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.ChiHom

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} {t : KerEntTied ex}

theorem chiI_det (J : Joint t H X) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  unfold chiI
  rw [dite_eq_left h]
  have e : h.choose = y := Subtype.ext (GlobalTheory.TwV.MuLawPf.generalLinearGroupOne_eq_of_det_eq h.choose_spec)
  rw [e]


set_option maxHeartbeats 2000000 in
theorem carries_std_of_int (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) (hy : Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E) :
    Formalism.L2.Herm.Carries y.1 (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) := by
  have hu := (Submonoid.mem_units_iff _ _).1 hy
  intro v
  show v ∈ latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E 1) ↔
    _ ∈ latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E 1)
  rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std]
  have e1 : Units.val ((y.1)⁻¹) 0 0 = Units.val ((Matrix.GeneralLinearGroup.det y.1)⁻¹) := by
    rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  have e2 : ∀ i : Fin 1, (Matrix.mulVec (Units.val ((y.1)⁻¹)) v) i = Units.val ((Matrix.GeneralLinearGroup.det y.1)⁻¹) * v 0 := by
    intro i
    fin_cases i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
    rw [← e1]; rfl
  simp only [e2]
  constructor
  · intro h i
    exact mul_mem hu.2 (h 0)
  · intro h i
    fin_cases i
    have := mul_mem hu.1 (h 0)
    rwa [← mul_assoc, Units.mul_inv, one_mul] at this


set_option maxHeartbeats 2000000 in
theorem dtU_mem_UO (J : Joint t H X) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hy : Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E) : J.dtU y ∈ D.UO := by
  have h := J.rel 1 ⟨_, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D 1⟩ ⟨_, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D 1⟩ y.1 y.2
    (carries_std_of_int y hy) y rfl
  exact (QuotientGroup.eq_one_iff _).1 (h.symm.trans (D.relDet_self _ _))

end GlobalTheory.TwV.Xc.ChiHom

namespace GlobalTheory.TwV.Xc


open GlobalTheory.TwV.Xc.ChiHom in
set_option maxHeartbeats 4000000 in
theorem chiI_hom : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), chiI J (x * y) = chiI J x * chiI J y) ∧ (∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E → chiI J x = 1) ∧ (∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ)) ∧ ∀ x ∈ U1 (sigD D), ∃ 𝔞, TaylorLogMetric.N1 D 𝔞 ∧ chiI J x = t.χ 𝔞) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _
  refine ⟨?_, ?_, fun y => chiI_det J y, ?_⟩
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    obtain ⟨y', rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hy
    have e : Matrix.GeneralLinearGroup.det x'.1 * Matrix.GeneralLinearGroup.det y'.1 =
        Matrix.GeneralLinearGroup.det (x' * y').1 := by
      rw [Subgroup.coe_mul, map_mul]
    rw [e, chiI_det, chiI_det, chiI_det, map_mul, map_mul, Units.val_mul]
  · intro x hx hint
    obtain ⟨y, rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    rw [chiI_det, D.chiD_UO _ (dtU_mem_UO J y hint), Units.val_one]
  · intro x hx
    obtain ⟨y, rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    refine ⟨t.idl (QuotientGroup.mk (J.dtU y)), (t.idl_ok.2.1 _).2 ⟨_, rfl⟩, ?_⟩
    rw [chiI_det, t.χ_rec, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
    rfl

end GlobalTheory.TwV.Xc

end
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), chiI J (x * y) = chiI J x * chiI J y) ∧ (∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E → chiI J x = 1) ∧ (∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ)) ∧ ∀ x ∈ U1 (sigD D), ∃ 𝔞, TaylorLogMetric.N1 D 𝔞 ∧ chiI J x = t.χ 𝔞) := by
  first | exact @GlobalTheory.TwV.Xc.chiI_hom | exact GlobalTheory.TwV.Xc.chiI_hom | (intros; apply GlobalTheory.TwV.Xc.chiI_hom <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReaderLevelBadPrimesCoprimeResidueCharStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelBadPrimesCoprimeResidueChar
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.SBad

theorem not_both_mem {R : Type*} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) {a b : ℕ} (h : Nat.Coprime a b)
    (ha : (a : R) ∈ I) (hb : (b : R) ∈ I) : False := by
  obtain ⟨s, r, hsr⟩ := h.cast (R := R)
  exact hI ((Ideal.eq_top_iff_one _).2 (hsr ▸ I.add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)))

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ Formalism.L2.Col.divs a) : a ∈ P.asIdeal := by
  unfold Formalism.L2.Col.divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

theorem coprime_absNorm_of_notMem {E : Type} [Field E] [NumberField E] (p : ℕ) [Fact p.Prime]
    (P : HeightOneSpectrum (𝓞 E)) (h : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime (Ideal.absNorm P.asIdeal) p := by
  refine GlobalTheory.NormUnitInert.Arith.coprime_absNorm p P.ne_bot ?_
  refine P.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left fun he => h ?_)
  rw [he]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

theorem notMem_Sall (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) (hp : p.Prime)
    (hTp : Nat.Coprime (D.mem u).A.T p) (hgp : ∀ i, p ≠ D.host.g i) (hQ : p ∉ Dx.Qp μ)
    (P : HeightOneSpectrum (𝓞 t.X.E)) (hP : P ∈ Formalism.L2.Col.Sall t.sel (t.tup μ) (t.word u)) :
    ((p : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
  intro hpP
  simp only [Formalism.L2.Col.Sall, Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG, Formalism.L2.Col.Primes.vGs, Finset.mem_union] at hP
  have hG : ∀ i, P ∈ t.Pr.vG i → False := fun i hPi => by
    have hc := mem_of_mem_divs hPi
    have hgm : ((D.host.g i : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.g_rec i, ← t.pr_ok.piG_norm]
      exact Ideal.mul_mem_left _ _ hc
    have hgi : (D.host.g i).Prime := t.g_rec i ▸ t.pr_ok.g_prime i
    exact not_both_mem P.isPrime.ne_top ((Nat.coprime_primes hgi hp).2 (hgp i).symm) hgm hpP
  rcases hP with hP | (hP | hP) | hP
  · have hpi := mem_of_mem_divs hP
    have hTm : (((D.mem u).A.T : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.T_rec u, ← t.pr_ok.piT_norm]
      exact Ideal.mul_mem_right _ _ hpi
    exact not_both_mem P.isPrime.ne_top hTp hTm hpP
  · exact hG 0 hP
  · exact hG 1 hP
  · exact hQ ((t.Q_rec μ p).2 ⟨hp, P, hP, hpP⟩)


set_option maxHeartbeats 1000000 in
theorem bad_prime_to_p : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => Nat.Coprime (t.rd u μ).lev (D.what₂.places.resChar w) ∧ (∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ (∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ), (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, GlobalTheory.TwU.UnderSB t μ v → (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X hF std t J S _ _
  classical
  have hp : (D.what₂.places.resChar w).Prime := hF.out
  obtain ⟨-, -, hTp, hgp⟩ := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  have hSS := (t.rd_chain u μ).1
  have hlev := (t.rd_chain u μ).2.1
  have key := fun P hP => notMem_Sall t u μ _ hp hTp hgp J.away P hP
  have keyE : ∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hQ hm
    obtain ⟨P, hP, rfl⟩ := Finset.mem_map.1 hQ
    refine key P (hSS ▸ hP) ((GlobalTheory.TwU.mem_seamP t.seam P _).1 ?_)
    rw [map_natCast]
    exact hm
  have keyF : ∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ),
      (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.F) ∉ v.asIdeal := by
    rintro v ⟨Q, hQ, hv⟩ hm
    rw [hv, Ideal.mem_comap, map_natCast] at hm
    exact keyE Q hQ hm
  refine ⟨?_, keyE, keyF, ?_⟩
  · rw [hlev]
    have hq : ∀ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Nat.Coprime (Formalism.L2.Col.qOf P.1) (D.what₂.places.resChar w) :=
      fun P => coprime_absNorm_of_notMem _ P.1 (key P.1 (Finset.mem_union_right _ P.2))
    have hprod : Nat.Coprime (∏ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1) (D.what₂.places.resChar w) :=
      Nat.Coprime.prod_left fun P _ => hq P
    have hT' : Nat.Coprime (t.Pr.T (t.word u)) (D.what₂.places.resChar w) := by rw [t.T_rec u]; exact hTp
    simp only [Formalism.L2.Ker.levC, Formalism.L2.Col.cAof, Formalism.L2.Col.cBof]
    exact Nat.Coprime.mul_left (Nat.Coprime.pow_left _ hprod) (Nat.Coprime.mul_left hT' (Nat.Coprime.pow_left _ hprod))
  · rintro v ⟨P, hP, hv⟩ hm
    rw [hv, Ideal.mem_comap, map_natCast] at hm
    refine key P (Finset.mem_union_right _ hP) ((GlobalTheory.TwU.mem_seamP t.seam P _).1 ?_)
    rw [map_natCast]
    exact hm

end GlobalTheory.TwV.Xc.SBad

end
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_badPrimes_coprime_residueChar : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => Nat.Coprime (t.rd u μ).lev (D.what₂.places.resChar w) ∧ (∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ (∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ), (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, GlobalTheory.TwU.UnderSB t μ v → (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) := by
  first | exact @GlobalTheory.TwV.Xc.SBad.bad_prime_to_p | exact GlobalTheory.TwV.Xc.SBad.bad_prime_to_p | (intros; apply GlobalTheory.TwV.Xc.SBad.bad_prime_to_p <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsAgreeAwayOfLatticeTuplesAgreeAway
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameOffOfIsPt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc

theorem sameOff_of_isPt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) :
    LocGood σ J A → ∀ (i : G.comp) (g g' : (∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)), A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∀ v, (∀ v', v' ≠ v → g v' = g' v') → SameOff (A.pl v).1 x.1 x'.1 := by
  intro H i g g' x x' hx hx' v hg w hw
  by_cases hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
  · obtain ⟨v', rfl⟩ := LocGood.exists_pl A w hp
    have hv : v' ≠ v := fun h => hw (h ▸ rfl)
    have h1 := hx.2 v'
    have h2 := hx'.2 v'
    rw [hg v' hv] at h1
    have hmem : bc (prV (E := E) (A.pl v').1) ((x.1)⁻¹ * x'.1) ∈ UPts σ J ((A.pl v').1.adicCompletion F) :=
      Formalism.UG.P.afsplit_bc_mem σ J (A.pl v').1 _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) x'.2)
    have h3 := LocGood.eq_one_of_ph H v' _ hmem (by rw [map_mul, map_mul, map_inv, map_inv, h1, h2]; exact inv_mul_cancel _)
    rw [map_mul, map_inv] at h3
    exact (inv_mul_eq_one.1 h3)
  · rw [hx.1 w hp, hx'.1 w hp]

end GlobalTheory.TwV.Xc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsAgreeAwayOfLatticeTuplesAgreeAway
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem bc_reGL_comm {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {m n : ℕ} (e : Fin m ≃ Fin n) (x : GL (Fin m) A) :
    Formalism.UG.bc φ (Formalism.L2.PairingIndexBounds.F.reGL e x) = Formalism.L2.PairingIndexBounds.F.reGL e (Formalism.UG.bc φ x) := by
  apply Units.ext
  ext a b
  rfl

theorem sameOff_reGL_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) {m n : ℕ} (e : Fin m ≃ Fin n) (x y : GL (Fin m) (AfE F E))
    (h : SameOff w x y) : SameOff w (Formalism.L2.PairingIndexBounds.F.reGL e x) (Formalism.L2.PairingIndexBounds.F.reGL e y) := fun w' hw => by
  rw [bc_reGL_comm, bc_reGL_comm, h w' hw]

theorem sameOff_eps_of_bases {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}
    {σ : E →ₐ[F] E} {Jm : Matrix (Fin n) (Fin n) E} {A : LocAt F E n G} (hG : LocGood σ Jm A) (i : G.comp)
    (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (v : Fin G.P.nV) (hgg : ∀ v', v' ≠ v → g v' = g' v') :
    SameOff (A.pl v).1 (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
      (Classical.epsilon fun x => A.IsPt i g' x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F)) := by
  have ha := Classical.epsilon_spec (p := fun x => A.IsPt i g x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hG.isPt_sec i g, Subgroup.mul_mem _ (hG.yG_mem i) (hG.sec _).2⟩
  have hb := Classical.epsilon_spec (p := fun x => A.IsPt i g' x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hG.isPt_sec i g', Subgroup.mul_mem _ (hG.yG_mem i) (hG.sec _).2⟩
  exact GlobalTheory.TwV.Xc.sameOff_of_isPt F E σ n p G A Jm hG i g g' ⟨_, ha.2⟩ ⟨_, hb.2⟩ ha.1 hb.1 v hgg


set_option maxHeartbeats 4000000 in
theorem sameOff_len_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameOff ((A0 J).pl v).1 (J.pt std j hj La).1 (J.pt std j hj Lb).1 ∧ ∀ v', v' ≠ v → len (sysS H X std) v' j La.2 = len (sysS H X std) v' j Lb.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v j hj La Lb hab
  obtain ⟨hLa, hLb, h1, h2⟩ := hab
  have hent : ∀ v', v' ≠ v → La.2 ((sysS H X std).vJ j v') = Lb.2 ((sysS H X std).vJ j v') := by
    intro v' hv'
    have hne : (sysS H X std).vJ j v' ≠ (sysS H X std).vJ j v := by
      intro h
      apply hv'
      have := congrArg ((sysS H X std).vB j) h
      rwa [Formalism.L2.G.Pend.vB_vJ, Formalism.L2.G.Pend.vB_vJ] at this
    have := congrFun h2 ((sysS H X std).vJ j v')
    exact (Function.update_of_ne hne _ _).symm.trans (this.trans (Function.update_of_ne hne _ _))
  refine ⟨?_, fun v' hv' => by unfold len; rw [hent v' hv']⟩
  have hlat : ∀ v', v' ≠ v → (sysS H X std).latAt v' j La.2 = (sysS H X std).latAt v' j Lb.2 := by
    intro v' hv'
    have := hent v' hv'
    cases j <;> exact this
  obtain ⟨hr, hpa⟩ := (hD j hj La hLa).1
  obtain ⟨hr', hpb⟩ := (hD j hj Lb hLb).1
  rw [hpa, hpb]
  apply sameOff_reGL_of
  obtain ⟨c, a⟩ := La
  obtain ⟨c', b⟩ := Lb
  dsimp only at h1
  subst h1
  cases j with
  | zero =>
    simp only [Joint.cp, cpAt, chAt]
    apply sameOff_reGL_of
    apply sameOff_eps_of_bases J.one.good
    intro v' hv'
    have hl := hlat v' hv'
    dsimp only at hl
    unfold basesAt
    rw [hl]
  | succ i =>
    simp only [Joint.cp, cpAt]
    simp only [chAt, dif_pos hj]
    apply sameOff_reGL_of
    rw [show (A0 J).pl v = ((I.at' i hj).st.loc ((I.at' i hj).st.eC.symm c).1).pl v from (J.pl i hj _ v).symm]
    apply sameOff_eps_of_bases (H.core i hj _).good
    intro v' hv'
    have hl := hlat v' hv'
    dsimp only at hl
    unfold basesAt
    rw [hl]

end GlobalTheory.TwV.Xc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsAgreeAwayOfLatticeTuplesAgreeAwayStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameOff ((A0 J).pl v).1 (J.pt std j hj La).1 (J.pt std j hj Lb).1 ∧ ∀ v', v' ≠ v → len (sysS H X std) v' j La.2 = len (sysS H X std) v' j Lb.2) := by
  first | exact @GlobalTheory.TwV.Xc.sameOff_len_of_sameAway | exact GlobalTheory.TwV.Xc.sameOff_len_of_sameAway | (intros; apply GlobalTheory.TwV.Xc.sameOff_len_of_sameAway <;> assumption)
end
end
