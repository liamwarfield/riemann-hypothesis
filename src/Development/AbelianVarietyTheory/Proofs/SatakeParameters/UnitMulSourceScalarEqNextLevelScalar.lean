module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SourceScalarLatticeTupleConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SourceScalarLatticeTupleConstant
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem source_scalar_const : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j < D.R.m), Nonempty (Lv.comp (j + 1)) → ∀ La : (sysS H X std).Lt j, dPow (mM d j hj.le La).1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d j hj.le La * d.uS S j La = kS J j hj.le La.1) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S d j hj hne La
  have hW := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hj hne
  have hfr := (GlobalTheory.T.changedFrame_rational_unitary S d j hj.le (rkS _ _ hW.rk) La).2.2
  obtain ⟨e, he, hmu⟩ := GlobalTheory.T.stepCharacter_det_rationalIsometry S j hj
  have hgd := (GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S j hj.le).2 _ (d.mem j hj.le La)
  obtain ⟨q, hq⟩ := Formalism.L2.Ker.even_rankN D.R (j + 1)
  have hs : ∀ τ, (D.chTw u μ).sSharp j τ = e τ - ((D.R.N (j + 1) / 2 : ℕ) : ℤ) := by
    intro τ
    have h1 := (D.chTw u μ).sSharp_eq j hj τ
    rw [D.hcW_e u τ, ← he τ] at h1
    have h2 : D.R.N (j + 1) / 2 = q := by omega
    rw [h2]
    have h3 : ((D.R.N (j + 1) : ℕ) : ℚ) = (q : ℚ) + q := by exact_mod_cast hq
    unfold sExp' at h1
    rw [h3] at h1
    have h4 : ((D.chTw u μ).sSharp j τ : ℚ) = ((e τ - (q : ℤ) : ℤ) : ℚ) := by push_cast; rw [h1]; ring
    exact_mod_cast h4
  have hχ : d.chi j hj.le La ≠ 0 := by unfold Dec.chi; exact Units.ne_zero _
  have hcD : ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  unfold dPow sPt Dec.uS kS dPow
  rw [dite_eq_left hj.le, hmu j hj.le _ (d.mem j hj.le La), hgd.1]
  simp only []
  set n : ℤ := ((D.R.N (j + 1) / 2 : ℕ) : ℤ) with hn
  set c : ℤ := cTw D j with hc
  rw [show ∀ (A χ C B Mu P : ℂ), A * (χ * C ^ c * B) * (χ⁻¹ * Mu⁻¹ * P * C ^ (-c)) = A * B * Mu⁻¹ * P * (χ * χ⁻¹) * (C ^ c * C ^ (-c)) from
    fun _ _ _ _ _ _ => by ring]
  rw [mul_inv_cancel₀ hχ, ← zpow_add₀ hcD, add_neg_cancel, zpow_zero, mul_one, mul_one]
  rw [← Finset.prod_zpow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm : (embT D τ) (mM d j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hgn : (embT D τ) (d.gam j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hb := congrArg (embT D τ) hfr
  rw [map_mul] at hb
  rw [← hb, hW.sh τ, hs τ]
  show (embT D τ) _ ^ _ * _ * ((embT D τ) _ ^ _)⁻¹ * ((embT D τ) (_ * _)) ^ _ = _
  rw [map_mul]
  generalize (embT D τ) (mM d j hj.le La).1.det = m at hm ⊢
  generalize (embT D τ) (d.gam j hj.le La).1.det = g at hgn ⊢
  generalize (embT D τ) (gMat J j hj.le 1).det = G
  generalize e τ = ee
  simp only [mul_zpow, zpow_neg, zpow_sub₀ hm, zpow_sub₀ hgn, zpow_add₀ hm, zpow_add₀ hgn]
  field_simp
  ring

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SourceScalarLatticeTupleConstantStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sourceScalar_latticeTuple_constant : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j < D.R.m), Nonempty (Lv.comp (j + 1)) → ∀ La : (sysS H X std).Lt j, dPow (mM d j hj.le La).1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d j hj.le La * d.uS S j La = kS J j hj.le La.1) := by
  first | exact @GlobalTheory.TwV.DelA.source_scalar_const | exact GlobalTheory.TwV.DelA.source_scalar_const | (intros; apply GlobalTheory.TwV.DelA.source_scalar_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScalInvFrame
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelA

theorem scal_inv_frame : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n) (M : GL (Fin n) D.host.E), StdU D M → FrIs fd ρ j La h M → Formalism.L2.G.Pend.cA X Kc j (BOf fd j La) = ι (∏ τ, embT D τ (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j τ))) := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd j La n h M hU hF
  have hMu : IsUnit (M : Matrix (Fin n) (Fin n) D.host.E).det := by
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det M).isUnit
  have hdet : ∀ v, (fd.frM j La v).det = ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det := by
    intro v
    rw [hF v, Matrix.det_submatrix_equiv_self, RingHom.map_det]
    rfl
  have hu : ∀ v, IsUnit (fd.frM j La v).det := fun v => by rw [hdet v]; exact hMu.map (ρ v)
  have hfr : ∀ v, ((frGL fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) = fd.frM j La v := by
    intro v; unfold frGL; rw [dite_eq_left (hu v)]; rfl
  have hB : ∀ v s, tw X Kc v s ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det =
      (tw X Kc v s (ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det))⁻¹ := by
    intro v s
    have h1 : ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det * (fd.frM j La v).det = 1 := by
      rw [← hfr v, ← Matrix.det_mul]
      unfold BOf
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 := congrArg (tw X Kc v s) h1
    rw [map_mul, map_one, hdet v] at h2
    exact eq_inv_of_mul_eq_one_left h2
  unfold Formalism.L2.G.Pend.cA
  have hterm : ∀ v s, (tw X Kc v s ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det) ^
      ((if IsOddPos s then -1 else 1) * X.w v (j + 1) s) =
      ι (embT D (pos ⟨v, s⟩) (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j (pos ⟨v, s⟩)))) := by
    intro v s
    rw [hB v s, (GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU v s).2, map_zpow₀]
    simp only [wT]
    rw [Equiv.symm_apply_apply]
    split_ifs <;> simp [zpow_neg, inv_inv]
  simp_rw [hterm]
  rw [map_prod]
  exact (Fintype.prod_sigma (fun x => ι (embT D (pos x) (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j (pos x)))))).symm.trans
    (Fintype.prod_equiv pos _ _ (fun _ => rfl))

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitMulSourceScalarEqNextLevelScalar
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), cKs S ι j hj La.1 La'.1 * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) * ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hpos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hps := GlobalTheory.TwV.DelA.posTie_at S hpos ι hι
  intro d j hj La La'
  have hr := GlobalTheory.TwV.DelB.sysS_ranks S
  have hfr := GlobalTheory.T.changedFrame_rational_unitary S d j (Nat.le_of_succ_le hj) (hr.2.2.1 j) La
  have hsc := GlobalTheory.T.sourceScalar_latticeTuple_constant S d j hj ⟨La'.1⟩ La
  have hun := (GlobalTheory.T.stepDeterminantConstant_unit_independent S hpos ι hι j hj La.1 La'.1).2.1
  have hcA := GlobalTheory.TwV.DelA.scal_inv_frame (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hps.1 d.fd2 j La (hr.2.2.1 j) (mM d j (Nat.le_of_succ_le hj) La) hfr.1 hfr.2.1
  have key : cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La * ι (d.uS S j La) =
      ι (kS J j (Nat.le_of_succ_le hj) La.1 * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) := by
    rw [hcA, sO, dite_eq_left (Nat.le_of_succ_le hj), ← map_mul, ← map_mul, ← hsc]
    congr 1
    unfold dPow
    ring
  rw [mul_assoc (cKs S ι j hj La.1 La'.1), key]
  unfold cKs scT
  rw [dite_eq_left hj, map_mul ι (kT J j hj La'.1), map_inv₀, map_mul ι (d.uT S j La')]
  have hy : ι (kS J j (Nat.le_of_succ_le hj) La.1 * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 := hun
  field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitMulSourceScalarEqNextLevelScalarStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_mul_sourceScalar_eq_nextLevelScalar : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), cKs S ι j hj La.1 La'.1 * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) * ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2) := by
  first | exact @GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT | exact GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT | (intros; apply GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT <;> assumption)
end
