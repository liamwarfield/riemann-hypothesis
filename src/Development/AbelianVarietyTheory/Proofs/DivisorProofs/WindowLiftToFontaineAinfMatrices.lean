module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePadicOfFrobeniusEigenAinf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoWindowsOfMatrixCongrModTau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHausdorffOfProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOver

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSolutionOfApproxModPhiXiMu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSolutionOfApproxModPhiXiMu
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WTop

theorem mulVec_add_mul {R ι : Type} [CommRing R] [Fintype ι] (N : Matrix ι ι R) (a b : ι → R) (s : R) (i : ι) :
    N.mulVec (fun j => a j + s * b j) i = N.mulVec a i + s * N.mulVec b i := by
  simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring


set_option maxHeartbeats 1000000 in
theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (N : Matrix ι ι (Ainf p O)) (v0 : ι → Ainf p O), IsNil (WittVector.fontaineTheta O p) WittVector.frobenius N → (∀ i, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ N.mulVec (fun j => WittVector.frobenius (v0 j)) i - WittVector.frobenius (xi ε) * v0 i) → ∃ w : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ w i - v0 i) ∧ ∀ i, WittVector.frobenius (xi ε) * w i = N.mulVec (fun j => WittVector.frobenius (w j)) i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε ι _ N v0 hN h
  choose c hc using h
  obtain ⟨z, hz⟩ := (GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι N hN).1 c
  refine ⟨fun i => v0 i + Sandwich.mu ε * z i, fun i => ⟨z i, by ring⟩, fun i => ?_⟩
  have hw : (fun j => WittVector.frobenius (v0 j + Sandwich.mu ε * z j)) =
      fun j => WittVector.frobenius (v0 j) +
        (WittVector.frobenius (xi ε) * Sandwich.mu ε) * WittVector.frobenius (z j) := by
    funext j
    rw [map_add (f := _), map_mul, GlobalTheory.WinLift.frob_mu]
  rw [hw, mulVec_add_mul]
  linear_combination (-1 : Ainf p O) * hc i + WittVector.frobenius (xi ε) * Sandwich.mu ε * hz i

end GlobalTheory.WTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSolutionOfApproxModPhiXiMuStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_solution_of_approx_mod_phi_xi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (N : Matrix ι ι (Ainf p O)) (v0 : ι → Ainf p O), IsNil (WittVector.fontaineTheta O p) WittVector.frobenius N → (∀ i, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ N.mulVec (fun j => WittVector.frobenius (v0 j)) i - WittVector.frobenius (xi ε) * v0 i) → ∃ w : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ w i - v0 i) ∧ ∀ i, WittVector.frobenius (xi ε) * w i = N.mulVec (fun j => WittVector.frobenius (w j)) i := by
  first | exact @GlobalTheory.WTop.main | exact GlobalTheory.WTop.main | (intros; apply GlobalTheory.WTop.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeLiftSolvesModFrobXiMu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeLiftSolvesModFrobXiMu
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WinLift

theorem lift_solves_div_frob_xi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V G0 hP hθ i m
  have ent : ∀ (c : Ainf p O) (i : Fin d ⊕ Fin k) (m : Fin h),
      (V * blk d k c 1 * G0.map WittVector.frobenius) i m =
        ∑ l, V i l * (Sum.elim (fun _ => c) (fun _ => (1 : Ainf p O)) l *
          WittVector.frobenius (G0 l m)) := by
    intro c i m
    rw [Matrix.mul_apply]
    simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h1 : ∀ l, ∃ w : Ainf p O,
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l *
        WittVector.frobenius (G0 l m) = WittVector.frobenius (xi ε) * w := by
    rintro (l | l)
    · exact ⟨_, rfl⟩
    · have hmem : G0 (Sum.inr l) m ∈ RingHom.ker (WittVector.fontaineTheta O p) := hθ l m
      rw [AinfXi.ker_theta hv ε (root_prim hε), Ideal.mem_span_singleton'] at hmem
      obtain ⟨w, hw⟩ := hmem
      exact ⟨WittVector.frobenius w, by rw [← hw, map_mul]; simp; ring⟩
  choose w hw using h1
  have hE : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
      WittVector.frobenius (xi ε) * G0 i m =
        WittVector.frobenius (xi ε) * ((∑ l, V i l * w l) - G0 i m) := by
    rw [ent]
    simp_rw [hw]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hdiff : ∀ l : Fin d ⊕ Fin k, Sandwich.mu ε ∣
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
        Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l := by
    rintro (l | l)
    · exact mu_dvd_frob_xi_sub ε
    · simp
  have hmu : Sandwich.mu ε ∣
      (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m := by
    have hPim := hP i m
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hPim
    have key : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m -
        ((V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius) i m - (p : Ainf p O) * G0 i m) =
        (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
          Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
            WittVector.frobenius (G0 l m))) -
        (WittVector.frobenius (xi ε) - p) * G0 i m := by
      rw [ent, ent]
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    have hR : Sandwich.mu ε ∣ (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε))
        (fun _ => (1 : Ainf p O)) l - Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
          WittVector.frobenius (G0 l m))) - (WittVector.frobenius (xi ε) - p) * G0 i m :=
      dvd_sub (Finset.dvd_sum fun l _ => Dvd.dvd.mul_left ((hdiff l).mul_right _) _)
        ((mu_dvd_frob_xi_sub ε).mul_right _)
    rw [← key] at hR
    have := dvd_add hR hPim
    rwa [sub_add_cancel] at this
  rw [hE] at hmu ⊢
  exact mul_dvd_mul_left _ (mu_dvd_of_xi_mul F _ hmu)

end GlobalTheory.WinLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeLiftSolvesModFrobXiMuStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transpose_lift_solves_mod_frobXi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := by
  first | exact @GlobalTheory.WinLift.lift_solves_div_frob_xi_mu | exact GlobalTheory.WinLift.lift_solves_div_frob_xi_mu | (intros; apply GlobalTheory.WinLift.lift_solves_div_frob_xi_mu <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMatrixLiftModTauAinf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMatrixLiftModTauAinf
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.WinLift

theorem isUnit_of_isUnit_theta {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O)
    (z : Ainf p O) (hz : IsUnit (WittVector.fontaineTheta O p z)) : IsUnit z := by
  haveI := GlobalTheory.AinfXi.isLocalRing_ainf (p := p) hv
  haveI := ReciprocityTheory.PGsh.Ainf.O_local O hv
  by_contra hn
  obtain ⟨w, hw⟩ := ReciprocityTheory.PGsh.Ainf.theta_surj p O hv (↑hz.unit⁻¹ : O)
  have hm : z ∈ IsLocalRing.maximalIdeal (Ainf p O) := (IsLocalRing.mem_maximalIdeal _).2 hn
  have hk : z * w - 1 ∈ IsLocalRing.maximalIdeal (Ainf p O) := by
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (WittVector.fontaineTheta O p))
    rw [RingHom.mem_ker, map_sub, map_mul, hw, map_one, IsUnit.mul_val_inv, sub_self]
  have h1 := Ideal.sub_mem _ (Ideal.mul_mem_right w _ hm) hk
  rw [sub_sub_cancel] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal (Ainf p O)).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_unit_lift_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι F.B), IsUnit U → ∃ V : Matrix ι ι (Ainf p O), IsUnit V ∧ ∀ i j, F.τ ∣ U i j - F.a (V i j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F ι _ _ U hU
  choose x y hxy using fun i j => F.gen (U i j)
  refine ⟨Matrix.of x, ?_, fun i j => ⟨F.a (y i j), by rw [hxy i j]; simp⟩⟩
  have hτ := GlobalTheory.WinLift.theta_tau F hv hε
  have e : F.θ.mapMatrix (F.a.mapMatrix (Matrix.of x)) = F.θ.mapMatrix U :=
    Matrix.ext fun i j => by simp [hxy i j, hτ]
  have hdet : WittVector.fontaineTheta O p (Matrix.of x).det = F.θ U.det := by
    rw [← F.θ_a, RingHom.map_det, RingHom.map_det, e, ← RingHom.map_det]
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_isUnit_theta hv
  rw [hdet]
  exact ((Matrix.isUnit_iff_isUnit_det U).1 hU).map F.θ

end GlobalTheory.WinLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMatrixLiftModTauAinfStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_matrix_lift_mod_tau_ainf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι F.B), IsUnit U → ∃ V : Matrix ι ι (Ainf p O), IsUnit V ∧ ∀ i j, F.τ ∣ U i j - F.a (V i j) := by
  first | exact @GlobalTheory.WinLift.exists_unit_lift_mod_tau | exact GlobalTheory.WinLift.exists_unit_lift_mod_tau | (intros; apply GlobalTheory.WinLift.exists_unit_lift_mod_tau <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobXiEigenvectorEqOfFrameImageEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobXiEigenvectorEqOfFrameImageEq
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem eigen_eq_of_frame_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius (xi ε) * x → WittVector.frobenius y = WittVector.frobenius (xi ε) * y → F.a x = F.a y → x = y := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F x y hx hy hxy
  have hsub : WittVector.frobenius (x - y) = WittVector.frobenius (xi ε) * (x - y) := by
    rw [map_sub, hx, hy, mul_sub]
  obtain ⟨c, hc, -⟩ := GlobalTheory.PDivLat.existsUnique_padic_of_eigen p C v O hv ε hε (x - y) hsub
  have h0 : F.a (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [← hc, map_mul, ← F.p_τ] at h0
  have h1 : F.τ * F.a (ofPadic p O c) = 0 := by
    apply tf F
    rw [← h0]; ring
  have h2 : Sandwich.mu ε ∣ ofPadic p O c := (F.τ_mul _).1 h1
  have h3 : WittVector.fontaineTheta O p (ofPadic p O c) = 0 := by
    obtain ⟨w, hw⟩ := h2
    rw [hw, map_mul, theta_mu hv hε, zero_mul]
  have hc0 : c = 0 := by
    by_contra hne
    have hs := PadicInt.unitCoeff_spec hne
    rw [hs, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast] at h3
    have hp : (p : O) ≠ 0 := by
      intro h
      have := congrArg (algebraMap O C) h
      rw [map_natCast, map_zero] at this
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
    have hu : IsUnit (WittVector.fontaineTheta O p (ofPadic p O (PadicInt.unitCoeff hne : ℤ_[p]))) :=
      ((PadicInt.unitCoeff hne).isUnit.map (ofPadic p O)).map _
    rcases mul_eq_zero.1 h3 with h | h
    · exact hu.ne_zero h
    · exact hp (pow_eq_zero_iff'.1 h).1
  rw [← sub_eq_zero, ← hc, hc0, map_zero, zero_mul]

end GlobalTheory.WinLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobXiEigenvectorEqOfFrameImageEqStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobXi_eigenvector_eq_of_frame_image_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius (xi ε) * x → WittVector.frobenius y = WittVector.frobenius (xi ε) * y → F.a x = F.a y → x = y := by
  first | exact @GlobalTheory.WinLift.eigen_eq_of_frame_eq | exact GlobalTheory.WinLift.eigen_eq_of_frame_eq | (intros; apply GlobalTheory.WinLift.eigen_eq_of_frame_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdLiftOfFrameMatrixEquation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdLiftOfFrameMatrixEquation
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem mu_dvd_of_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι κ : Type) [Fintype ι] (R S : Matrix ι ι F.B) (R0 S0 : Matrix ι ι (Ainf p O)) (Y : Matrix ι κ F.B) (F0 : Matrix ι κ (Ainf p O)), (∀ i j, F.τ ∣ R i j - F.a (R0 i j)) → (∀ i j, F.τ ∣ S i j - F.a (S0 i j)) → (∀ i m, F.τ ∣ Y i m - F.a (F0 i m)) → R * Y.map F.σ = S * Y → ∀ i m, Sandwich.mu ε ∣ (R0 * F0.map WittVector.frobenius - S0 * F0) i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F ι κ _ R S R0 S0 Y F0 hR hS hY hRS i m
  apply (F.a_dvd _).1
  set q := Ideal.Quotient.mk (Ideal.span {F.τ})
  have key : ∀ x y : F.B, F.τ ∣ x - y → q x = q y := fun x y h =>
    Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
  have hR' : ∀ i j, q (R i j) = q (F.a (R0 i j)) := fun i j => key _ _ (hR i j)
  have hS' : ∀ i j, q (S i j) = q (F.a (S0 i j)) := fun i j => key _ _ (hS i j)
  have hY' : ∀ i m, q (Y i m) = q (F.a (F0 i m)) := fun i m => key _ _ (hY i m)
  have hYσ : ∀ i m, q (F.σ (Y i m)) = q (F.a (WittVector.frobenius (F0 i m))) := fun i m => by
    apply key
    rw [← F.σ_a, ← map_sub]
    exact tau_dvd_sigma F _ (hY i m)
  have h := congrArg (fun M => q (M i m)) hRS
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul] at h
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change q _ = 0
  rw [Matrix.sub_apply, map_sub, map_sub, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Matrix.map_apply, ← hR', ← hS', ← hYσ, ← hY']
  exact h

end GlobalTheory.WinLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdLiftOfFrameMatrixEquationStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_dvd_lift_of_frame_matrix_equation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι κ : Type) [Fintype ι] (R S : Matrix ι ι F.B) (R0 S0 : Matrix ι ι (Ainf p O)) (Y : Matrix ι κ F.B) (F0 : Matrix ι κ (Ainf p O)), (∀ i j, F.τ ∣ R i j - F.a (R0 i j)) → (∀ i j, F.τ ∣ S i j - F.a (S0 i j)) → (∀ i m, F.τ ∣ Y i m - F.a (F0 i m)) → R * Y.map F.σ = S * Y → ∀ i m, Sandwich.mu ε ∣ (R0 * F0.map WittVector.frobenius - S0 * F0) i m := by
  first | exact @GlobalTheory.WinLift.mu_dvd_of_mod_tau | exact GlobalTheory.WinLift.mu_dvd_of_mod_tau | (intros; apply GlobalTheory.WinLift.mu_dvd_of_mod_tau <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftSolvesModFrobXiMu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftSolvesModFrobXiMu
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

theorem GlobalTheory.WinLift.frob_lift_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (F0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), IsUnit V → (∀ i m, Sandwich.mu ε ∣ (F0.map WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m) → (∀ i m, WittVector.fontaineTheta O p (F0 (Sum.inl i) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε)) * F0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * F0 i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V F0 hV hF hθ i m
  set ξ' : Ainf p O := WittVector.frobenius (xi ε) with hξ'
  set μ : Ainf p O := Sandwich.mu ε with hμ
  set G : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) := V.transpose * F0 with hG
  set E : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) :=
    blk d k 1 ξ' * F0.map WittVector.frobenius - ξ' • G with hEdef
  have hVt : IsUnit V.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det V).1 hV
  have key : V.transpose⁻¹ * blk d k 1 ξ' * F0.map WittVector.frobenius - ξ' • F0 =
      V.transpose⁻¹ * E := by
    rw [hEdef, hG, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc (V.transpose⁻¹),
      Matrix.nonsing_inv_mul _ hVt, Matrix.one_mul]
  have hEe : ∀ j n, E j n = Sum.elim (fun _ => (1 : Ainf p O)) (fun _ => ξ') j *
      WittVector.frobenius (F0 j n) - ξ' * G j n := by
    intro j n
    simp [hEdef, blk, Matrix.diagonal_mul]
  have hyp : ∀ j n, μ ∣ WittVector.frobenius (F0 j n) -
      Sum.elim (fun _ => (p : Ainf p O)) (fun _ => 1) j * G j n := by
    intro j n
    have := hF j n
    rw [Matrix.mul_assoc, ← hG] at this
    simpa [blk, Matrix.diagonal_mul] using this
  have hE : ∀ j n, ξ' * μ ∣ E j n := by
    intro j n
    rw [hEe]
    rcases j with j | j
    · obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton').1
        (show F0 (Sum.inl j) n ∈ Ideal.span {xi ε} by
          rw [← AinfXi.ker_theta hv ε (root_prim hε)]; exact hθ j n)
      have h1 : μ ∣ ξ' * (WittVector.frobenius w - G (Sum.inl j) n) := by
        have := dvd_sub (hyp (Sum.inl j) n) ((mu_dvd_frob_xi_sub ε).mul_right (G (Sum.inl j) n))
        convert this using 1
        simp only [Sum.elim_inl]
        rw [← hw, map_mul, ← hξ']
        ring
      have h2 := mul_dvd_mul_left ξ' (mu_dvd_of_xi_mul F _ h1)
      convert h2 using 1
      simp only [Sum.elim_inl]
      rw [← hw, map_mul, ← hξ']
      ring
    · have := mul_dvd_mul_left ξ' (hyp (Sum.inr j) n)
      convert this using 1
      simp only [Sum.elim_inr]
      ring
  have e := congrFun (congrFun key i) m
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e
  rw [e, Matrix.mul_apply]
  exact Finset.dvd_sum fun j _ => (hE j m).mul_left _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftSolvesModFrobXiMuStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_lift_solves_mod_frobXi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (F0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), IsUnit V → (∀ i m, Sandwich.mu ε ∣ (F0.map WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m) → (∀ i m, WittVector.fontaineTheta O p (F0 (Sum.inl i) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε)) * F0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * F0 i m := by
  first | exact @GlobalTheory.WinLift.frob_lift_dvd | exact GlobalTheory.WinLift.frob_lift_dvd | (intros; apply GlobalTheory.WinLift.frob_lift_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentInvTransposeBlockFrobeniusAinfOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentInvTransposeBlockFrobeniusAinfOfFrame
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift.NilF

theorem map_inv_transpose_blk {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d k : ℕ)
    (M : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) (hM : IsUnit M) (a b : R) (i j : Fin d ⊕ Fin k) :
    f ((M.transpose⁻¹ * blk d k a b) i j) = (((M.map f).transpose)⁻¹ * blk d k (f a) (f b)) i j := by
  have hMt : IsUnit M.transpose := (Matrix.isUnit_iff_isUnit_det _).2
    (by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 hM)
  have hb : (blk d k a b).map f = blk d k (f a) (f b) := by
    rw [blk, blk, Matrix.diagonal_map (map_zero f)]
    congr 1
    funext l
    rcases l with l | l <;> rfl
  have := congr_fun (congr_fun (Matrix.map_mul (f := f) (L := M.transpose⁻¹)
    (M := blk d k a b)) i) j
  rw [Matrix.map_apply] at this
  rw [this, ← map_inv_of_isUnit f _ hMt, Matrix.transpose_map, hb]

theorem isNil_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), IsUnit U → IsUnit V → (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U V hU hV hUV hN
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  have hp : ¬IsUnit (p : O) := Fact.out
  have hθτ := theta_tau F hv hε
  have hUV' : U.map F.θ = V.map (WittVector.fontaineTheta O p) := by
    refine Matrix.ext fun i j => ?_
    obtain ⟨c, hc⟩ := hUV i j
    rw [Matrix.map_apply, Matrix.map_apply, ← F.θ_a, ← sub_eq_zero, ← map_sub, hc, map_mul, hθτ,
      zero_mul]
  refine isNil_of_map F.a (WittVector.fontaineTheta O p) F.θ WittVector.frobenius F.σ F.θ_a F.σ_a _ ?_
  refine isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN
  rw [Matrix.map_apply, F.θ_a, map_inv_transpose_blk F.θ d k U hU, map_inv_transpose_blk _ d k V hV,
    hUV', map_one, map_one, map_natCast, theta_frob_xi hv hε]

end GlobalTheory.WinLift.NilF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentInvTransposeBlockFrobeniusAinfOfFrameStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_invTranspose_blockFrobenius_ainf_of_frameNil : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), IsUnit U → IsUnit V → (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) := by
  first | exact @GlobalTheory.WinLift.NilF.isNil_frob | exact GlobalTheory.WinLift.NilF.isNil_frob | (intros; apply GlobalTheory.WinLift.NilF.isNil_frob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusXiEqPMulUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusXiEqPMulUnit
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.QLog.BFrame

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_xi (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.xi ε) = ∑ i ∈ Finset.range p, (1 + Sandwich.mu ε) ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Sandwich.xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, Sandwich.mu,
    add_sub_cancel]
  congr 2
  exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε

theorem one_add_pow {ε : PreTilt O p} (F : BFrame ε) (i : ℕ) :
    (1 + (p : F.B) * F.τ) ^ i = 1 + (i : F.B) * ((p : F.B) * F.τ) := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((n : F.B) * (p : F.B) ^ 2) * F.τ_sq

theorem a_frobenius_xi {ε : PreTilt O p} (F : BFrame ε) :
    F.a (WittVector.frobenius (Sandwich.xi ε)) = p * (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [frobenius_xi, map_sum]
  have h1 : ∀ i ∈ Finset.range p, F.a ((1 + Sandwich.mu ε) ^ i) = 1 + (i : F.B) * ((p : F.B) * F.τ) :=
    fun i _ => by rw [map_pow, map_add (f := _), map_one, ← F.p_τ, one_add_pow]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  have h2 : (∑ i ∈ Finset.range p, (i : F.B)) = ((p.choose 2 : ℕ) : F.B) := by
    rw [← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]
  rw [h2]
  ring

theorem frobenius_xi_unit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∃ u : F.B, IsUnit u ∧ F.τ ∣ u - 1 ∧ F.a (WittVector.frobenius (xi ε)) = p * u := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F
  refine ⟨1 + ((p.choose 2 : ℕ) : F.B) * F.τ, ?_, ⟨((p.choose 2 : ℕ) : F.B), by ring⟩,
    a_frobenius_xi F⟩
  have h : (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) * (1 - ((p.choose 2 : ℕ) : F.B) * F.τ) = 1 := by
    linear_combination (-(((p.choose 2 : ℕ) : F.B)) ^ 2) * F.τ_sq
  exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩

end GlobalTheory.QLog.BFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusXiEqPMulUnitStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_xi_eq_p_mul_unit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∃ u : F.B, IsUnit u ∧ F.τ ∣ u - 1 ∧ F.a (WittVector.frobenius (xi ε)) = p * u := by
  first | exact @GlobalTheory.QLog.BFrame.frobenius_xi_unit | exact GlobalTheory.QLog.BFrame.frobenius_xi_unit | (intros; apply GlobalTheory.QLog.BFrame.frobenius_xi_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfFrameLiftTwistedFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxStep
namespace GlobalTheory.FixedPointApproximation

noncomputable def approx {B : Type} [CommRing B] (q : B) (σ : B →+* B) (w : B) : ℕ → B
  | 0 => 0
  | n + 1 => -w + q * σ (approx q σ w n)

theorem approx_step {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B) (n : ℕ) :
    q ^ n ∣ approx q σ w (n + 1) - approx q σ w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨σ t, ?_⟩
    have e : approx q σ w (n + 1 + 1) - approx q σ w (n + 1) =
        q * σ (approx q σ w (n + 1) - approx q σ w n) := by
      rw [map_sub]
      show -w + q * σ (approx q σ w (n + 1)) - (-w + q * σ (approx q σ w n)) = _
      ring
    rw [e, ht, map_mul, map_pow, hq]
    ring

theorem approx_dvd {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B)
    (m n : ℕ) (h : m ≤ n) : q ^ m ∣ approx q σ w m - approx q σ w n := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h2 : q ^ m ∣ approx q σ w (n + 1) - approx q σ w n :=
      (pow_dvd_pow q hmn).trans (approx_step q σ hq w n)
    have e : approx q σ w m - approx q σ w (n + 1) =
        (approx q σ w m - approx q σ w n) - (approx q σ w (n + 1) - approx q σ w n) := by ring
    rw [e]
    exact dvd_sub ih h2

theorem smodEq_iff {B : Type} [CommRing B] (q : B) (n : ℕ) (x y : B) :
    x ≡ y [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule B B)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem exists_fixed {B : Type} [inst : CommRing B] (q : B)
    [h : IsAdicComplete (Ideal.span {q}) B] (σ : B →+* B) (hq : σ q = q) (w : B) :
    ∃ c : B, c = -w + q * σ c := by
  obtain ⟨c, hc⟩ := h.toIsPrecomplete.prec (f := approx q σ w) fun {m n} hmn =>
    (smodEq_iff q m _ _).mpr (approx_dvd q σ hq w m n hmn)
  refine ⟨c, ?_⟩
  have hd : ∀ n, q ^ n ∣ c - (-w + q * σ c) := by
    intro n
    have h1 : q ^ n ∣ approx q σ w n - c := (smodEq_iff q n _ _).mp (hc n)
    have h2 : q ^ (n + 1) ∣ approx q σ w (n + 1) - c := (smodEq_iff q (n + 1) _ _).mp (hc (n + 1))
    obtain ⟨t, ht⟩ := h1
    have e : c - (-w + q * σ c) = -(approx q σ w (n + 1) - c) + q * σ (approx q σ w n - c) := by
      rw [map_sub]
      show _ = -((-w + q * σ (approx q σ w n)) - c) + q * (σ (approx q σ w n) - σ c)
      ring
    rw [e, ht, map_mul, map_pow, hq]
    exact dvd_add (dvd_neg.mpr ((pow_dvd_pow q (Nat.le_succ n)).trans h2)) ⟨q * σ t, by ring⟩
  have h0 := h.toIsHausdorff.haus (c - (-w + q * σ c)) fun n =>
    (smodEq_iff q n _ _).mpr (by simpa using hd n)
  exact sub_eq_zero.mp h0

end GlobalTheory.FixedPointApproximation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfFrameLiftTwistedFrobenius
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FLam

theorem exists_fixed {B : Type} [CommRing B] (q : B) [h : IsAdicComplete (Ideal.span {q}) B]
    (σ : B →+* B) (hσ : σ q = q) (w : B) : ∃ c : B, c = -w + q * σ c := by
  first
  | exact @_root_.GlobalTheory.FixedPointApproximation.exists_fixed
  | exact _root_.GlobalTheory.FixedPointApproximation.exists_fixed
  | (apply _root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FixedPointApproximation.exists_fixed ..)

theorem one_add_pow_of_sq {B : Type} [CommRing B] (x : B) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination (n : B) * hx

theorem frobenius_mu (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = (Sandwich.mu ε + 1) ^ p - 1 := by
  unfold Sandwich.mu
  rw [WittVector.frobenius_eq_map_frobenius, map_sub, map_one, WittVector.map_teichmuller,
    frobenius_def, map_pow]
  ring

theorem σ_τ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε) :
    F.σ F.τ = p * F.τ := by
  have tf : ∀ x : F.B, (p : F.B) * x = 0 → x = 0 := by
    intro x hx
    have h1 : (p : F.Q) * algebraMap F.B F.Q x = 0 := by
      rw [← map_natCast (algebraMap F.B F.Q), ← map_mul, hx, map_zero]
    have h2 := (F.frame.unit_p.mul_right_eq_zero).1 h1
    exact F.frame.inj (by rw [h2, map_zero])
  apply sub_eq_zero.1
  apply tf
  have e1 : (p : F.B) * F.σ F.τ = F.a (WittVector.frobenius (Sandwich.mu ε)) := by
    rw [← F.σ_a, ← F.p_τ, map_mul, map_natCast]
  have e2 : F.a (WittVector.frobenius (Sandwich.mu ε)) = p * (p * F.τ) := by
    have hsq : (p * F.τ) * (p * F.τ) = 0 := by
      rw [show (p : F.B) * F.τ * (p * F.τ) = p * p * (F.τ * F.τ) by ring, F.τ_sq, mul_zero]
    rw [frobenius_mu, map_sub, map_pow, map_add (f := _), map_one, ← F.p_τ, add_comm,
      one_add_pow_of_sq _ hsq]
    ring
  rw [mul_sub, e1, e2, sub_self]

end GlobalTheory.FLam


open GlobalTheory.FLam in
theorem GlobalTheory.FLam.exists_lam : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ u : F.B, F.τ ∣ u - 1 → ∃ l : F.B, F.τ ∣ l - 1 ∧ F.σ l = u * l := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F u hu
  obtain ⟨w, hw⟩ := hu
  haveI : IsAdicComplete (Ideal.span {(p : F.B)}) F.B := F.frame.complete
  obtain ⟨c, hc⟩ := exists_fixed (p : F.B) F.σ (map_natCast F.σ p) w
  refine ⟨1 + F.τ * c, ⟨c, by ring⟩, ?_⟩
  have hu' : u = 1 + F.τ * w := by rw [← hw]; ring
  rw [map_add (f := _), map_one, map_mul, σ_τ, hu']
  have hτ := F.τ_sq
  linear_combination (-(w * c)) * hτ - F.τ * hc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfFrameLiftTwistedFrobeniusStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_frame_lift_twisted_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ u : F.B, F.τ ∣ u - 1 → ∃ l : F.B, F.τ ∣ l - 1 ∧ F.σ l = u * l := by
  first | exact @GlobalTheory.FLam.exists_lam | exact GlobalTheory.FLam.exists_lam | (intros; apply GlobalTheory.FLam.exists_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WindowLiftToFontaineAinfMatrices
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift.Top

theorem c_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι F.B), IsUnit U → ∃ V : Matrix ι ι (Ainf p O), IsUnit V ∧ ∀ i j, F.τ ∣ U i j - F.a (V i j) := GlobalTheory.T.exists_unit_matrix_lift_mod_tau_ainf

theorem c_nilF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), IsUnit U → IsUnit V → (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) := GlobalTheory.T.isNilpotent_invTranspose_blockFrobenius_ainf_of_frameNil

theorem c_nilG : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := GlobalTheory.T.isNilpotent_blockFrobeniusXi_ainf_of_frameBlockP

theorem c_solve : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (N : Matrix ι ι (Ainf p O)) (v0 : ι → Ainf p O), IsNil (WittVector.fontaineTheta O p) WittVector.frobenius N → (∀ i, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ N.mulVec (fun j => WittVector.frobenius (v0 j)) i - WittVector.frobenius (xi ε) * v0 i) → ∃ w : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ w i - v0 i) ∧ ∀ i, WittVector.frobenius (xi ε) * w i = N.mulVec (fun j => WittVector.frobenius (w j)) i := GlobalTheory.T.exists_ainf_solution_of_approx_mod_phi_xi_mu

theorem c_modtau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι κ : Type) [Fintype ι] (R S : Matrix ι ι F.B) (R0 S0 : Matrix ι ι (Ainf p O)) (Y : Matrix ι κ F.B) (F0 : Matrix ι κ (Ainf p O)), (∀ i j, F.τ ∣ R i j - F.a (R0 i j)) → (∀ i j, F.τ ∣ S i j - F.a (S0 i j)) → (∀ i m, F.τ ∣ Y i m - F.a (F0 i m)) → R * Y.map F.σ = S * Y → ∀ i m, Sandwich.mu ε ∣ (R0 * F0.map WittVector.frobenius - S0 * F0) i m := GlobalTheory.T.mu_dvd_lift_of_frame_matrix_equation

theorem c_divF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (F0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), IsUnit V → (∀ i m, Sandwich.mu ε ∣ (F0.map WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m) → (∀ i m, WittVector.fontaineTheta O p (F0 (Sum.inl i) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε)) * F0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * F0 i m := GlobalTheory.T.frobenius_lift_solves_mod_frobXi_mu

theorem c_divG : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := GlobalTheory.T.transpose_lift_solves_mod_frobXi_mu

theorem c_eig : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius (xi ε) * x → WittVector.frobenius y = WittVector.frobenius (xi ε) * y → F.a x = F.a y → x = y := GlobalTheory.T.frobXi_eigenvector_eq_of_frame_image_eq

theorem c_cmpF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y Z : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U' → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z → (∀ i m, F.τ ∣ Z i m - Y i m) → Z = X.transpose * Y := GlobalTheory.T.ainfFrame_solution_congr_eq_transpose_mul

theorem c_cmpG : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (u l : F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B) (W : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → F.τ ∣ u - 1 → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → F.σ l = u * l → F.τ ∣ l - 1 → U * blk d k (p : F.B) 1 * Gm.transpose.map F.σ = (p : F.B) • Gm.transpose → U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W → (∀ i m, F.τ ∣ W i m - Gm m i) → X * W = l • Gm.transpose := GlobalTheory.T.ainfFrame_solution_mul_congr_Gm_transpose

theorem frob_phiInv {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (a : Ainf p O) :
    WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem phiInv_frob {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (a : Ainf p O) :
    phiInv p O (WittVector.frobenius a) = a := by
  ext n
  rw [phiInv, WittVector.map_coeff, WittVector.coeff_frobenius_charP]
  exact (_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _

theorem blk_mul_blk {R : Type} [CommRing R] (d k : ℕ) (a b c e : R) :
    blk d k a b * blk d k c e = blk d k (a * c) (b * e) := by
  rw [blk, blk, blk, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> rfl

theorem blk_same {R : Type} [CommRing R] (d k : ℕ) (a : R) :
    blk d k a a = a • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) := by
  ext i j
  simp only [blk, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs with hij
  · subst hij; rcases i with i | i <;> simp
  · simp

theorem blk_transpose {R : Type} [CommRing R] (d k : ℕ) (a b : R) :
    (blk d k a b).transpose = blk d k a b := Matrix.diagonal_transpose _

theorem blk_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d k : ℕ) (a b : R) :
    (blk d k a b).map f = blk d k (f a) (f b) := by
  rw [blk, blk, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  rcases i with i | i <;> rfl

theorem c_nilCong : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U U' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsUnit U' → (∀ i j, F.τ ∣ U i j - U' i j) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U U' hU hU' hUU' h1 h2
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  have hθτ := theta_tau F hv hε
  have hθ : ∀ i j, F.θ (U i j) = F.θ (U' i j) := by
    intro i j
    obtain ⟨c, hc⟩ := hUU' i j
    rw [← sub_eq_zero, ← map_sub, hc, map_mul, hθτ, zero_mul]
  have hp : ¬IsUnit (p : O) := Fact.out
  have hmap : U.map F.θ = U'.map F.θ := Matrix.ext hθ
  have htu : ∀ M : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit M → IsUnit M.transpose :=
    fun M hM => (Matrix.isUnit_iff_isUnit_det _).2
      (by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 hM)
  have e : ∀ M : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit M → ∀ i j,
      F.θ ((M.transpose⁻¹ * blk d k 1 (p : F.B)) i j) =
        (((M.map F.θ).transpose)⁻¹ * blk d k 1 (p : O)) i j := by
    intro M hM i j
    have := congr_fun (congr_fun (Matrix.map_mul (f := F.θ) (L := M.transpose⁻¹)
      (M := blk d k 1 (p : F.B))) i) j
    rw [Matrix.map_apply] at this
    rw [this, ← map_inv_of_isUnit F.θ _ (htu M hM), Matrix.transpose_map, blk_map, map_one,
      map_natCast]
  refine ⟨isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) h1,
    isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) h2⟩
  · rw [e U hU, e U' hU', hmap]
  · simp only [blk, Matrix.mul_diagonal, map_mul, hθ]

theorem window_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U Y Gm hyp
  obtain ⟨hU, hY, hG, hGY, hYθ, hGθ, hN1, hN2⟩ := hyp
  haveI : IsDomain (Ainf p O) := GlobalTheory.AinfXi.isDomain_ainf hv
  have hθτ : F.θ F.τ = 0 := theta_tau F hv hε
  have hξ0 : WittVector.frobenius (xi ε) ≠ 0 := by
    intro h0
    have h1 := theta_frob_xi hv hε
    rw [h0, map_zero] at h1
    have h2 := congrArg (algebraMap O C) h1
    rw [map_zero, map_natCast] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2.symm
  obtain ⟨V, hV, hUV⟩ := c_lift p C v O hv ε hε F _ U hU
  obtain ⟨F0, F1, hF0⟩ : ∃ F0 F1 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O),
      ∀ i m, Y i m = F.a (F0 i m) + F.τ * F.a (F1 i m) := by
    choose F0 F1 hF0 using fun i m => F.gen (Y i m)
    exact ⟨F0, F1, hF0⟩
  obtain ⟨G0, G1, hG0⟩ : ∃ G0 G1 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O),
      ∀ i m, Gm m i = F.a (G0 i m) + F.τ * F.a (G1 i m) := by
    choose G0 G1 hG0 using fun (i : Fin d ⊕ Fin k) (m : Fin h) => F.gen (Gm m i)
    exact ⟨G0, G1, hG0⟩
  have hYF : ∀ i m, F.τ ∣ Y i m - F.a (F0 i m) := fun i m => ⟨F.a (F1 i m), by rw [hF0 i m]; ring⟩
  have hGG : ∀ i m, F.τ ∣ Gm m i - F.a (G0 i m) := fun i m => ⟨F.a (G1 i m), by rw [hG0 i m]; ring⟩
  have hθY : ∀ i m, WittVector.fontaineTheta O p (F0 i m) = F.θ (Y i m) := by
    intro i m; rw [hF0 i m, map_add (f := _), map_mul, hθτ, zero_mul, add_zero, F.θ_a]
  have hθG : ∀ i m, WittVector.fontaineTheta O p (G0 i m) = F.θ (Gm m i) := by
    intro i m; rw [hG0 i m, map_add (f := _), map_mul, hθτ, zero_mul, add_zero, F.θ_a]
  have hdvdμ : ∀ x : Ainf p O, Sandwich.mu ε ∣ x → F.τ ∣ F.a x := by
    rintro x ⟨c, rfl⟩; rw [map_mul, ← F.p_τ]; exact ⟨p * F.a c, by ring⟩
  have hone : ∀ i j, F.τ ∣ (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j -
      F.a ((1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) i j) := by
    intro i j; simp only [Matrix.one_apply]; split_ifs <;> simp
  have hpone : ∀ i j, F.τ ∣ ((p : F.B) • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B)) i j -
      F.a (((p : Ainf p O) • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O))) i j) := by
    intro i j; simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]; split_ifs <;> simp
  have hel : ∀ (x : F.B) (y : Ainf p O), F.a y = x → ∀ i : Fin d ⊕ Fin k,
      F.a (Sum.elim (fun _ => y) (fun _ => (1 : Ainf p O)) i) = Sum.elim (fun _ => x) (fun _ => 1) i := by
    intro x y hxy i; rcases i with i | i <;> simp [hxy]
  have hL : ∀ i j, F.τ ∣ (blk d k (p : F.B) 1 * U.transpose) i j -
      F.a ((blk d k (p : Ainf p O) 1 * V.transpose) i j) := by
    intro i j
    simp only [blk, Matrix.diagonal_mul, Matrix.transpose_apply, map_mul]
    rw [hel (p : F.B) (p : Ainf p O) (map_natCast _ _) i, ← mul_sub]
    exact dvd_mul_of_dvd_right (hUV j i) _
  have hR : ∀ i j, F.τ ∣ (U * blk d k (p : F.B) 1) i j -
      F.a ((V * blk d k (p : Ainf p O) 1) i j) := by
    intro i j
    simp only [blk, Matrix.mul_diagonal, map_mul]
    rw [hel (p : F.B) (p : Ainf p O) (map_natCast _ _) j, ← sub_mul]
    exact dvd_mul_of_dvd_left (hUV i j) _

  have hF0μ : ∀ i m, Sandwich.mu ε ∣ (F0.map
      WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m := by
    have := c_modtau p C v O hv ε hε F _ (Fin h) 1 (blk d k (p : F.B) 1 * U.transpose) 1
      (blk d k (p : Ainf p O) 1 * V.transpose) Y F0 hone hL hYF (by rw [Matrix.one_mul, hY])
    simpa only [Matrix.one_mul] using this
  have hdivF := c_divF p C v O hv ε hε F d k h V F0 hV hF0μ (fun i m => by rw [hθY]; exact hYθ i m)
  have hnilF := c_nilF p C v O hv ε hε F d k U V hU hV hUV hN2
  choose Fw hFw1 hFw2 using fun m : Fin h => c_solve p C v O hv ε hε _
    (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) (fun i => F0 i m) hnilF
    (fun i => hdivF i m)

  set ξ' := WittVector.frobenius (xi ε) with hξ'
  let Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) := Matrix.of fun i m => Fw m i
  have hFaeq : ξ' • Fa = (V.transpose⁻¹ * blk d k 1 ξ') * Fa.map WittVector.frobenius := by
    exact Matrix.ext fun i m => hFw2 m i
  have hdetV : IsUnit V.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det V).1 hV
  have hφFa : Fa.map WittVector.frobenius = blk d k ξ' 1 * V.transpose * Fa := by
    have e1 : V.transpose * (ξ' • Fa) = blk d k 1 ξ' * Fa.map WittVector.frobenius := by
      rw [hFaeq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetV,
        Matrix.one_mul]
    have e2 : ξ' • (blk d k ξ' 1 * V.transpose * Fa) = ξ' • Fa.map WittVector.frobenius := by
      rw [Matrix.mul_assoc, ← Matrix.mul_smul, ← Matrix.mul_smul, e1, ← Matrix.mul_assoc, blk_mul_blk, mul_one,
        one_mul, blk_same, Matrix.smul_mul, Matrix.one_mul]
    refine Matrix.ext fun i m => ?_
    have := congr_fun (congr_fun e2 i) m
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact (mul_left_cancel₀ hξ0 this).symm
  let Ψ := (blk d k ξ' 1 * V.transpose).map (phiInv p O)
  let Ψ' := (V.transpose⁻¹ * blk d k 1 ξ').map (phiInv p O)
  have hfinj : ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius y → x = y :=
    fun x y hxy => by rw [← phiInv_frob x, hxy, phiInv_frob]
  have hFaΨ : Fa = Ψ * Fa.map (phiInv p O) := by
    have : (Ψ * Fa.map (phiInv p O)).map WittVector.frobenius = Fa.map WittVector.frobenius := by
      rw [Matrix.map_mul, hφFa, Matrix.map_map, Matrix.map_map]
      have h1 : (WittVector.frobenius ∘ phiInv p O) = id := funext frob_phiInv
      rw [h1, Matrix.map_id, Matrix.map_id]
    refine Matrix.ext fun i m => ?_
    exact (hfinj _ _ (congr_fun (congr_fun this i) m)).symm
  have hΨΨ' : Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) := by
    have e : blk d k ξ' 1 * V.transpose * (V.transpose⁻¹ * blk d k 1 ξ') =
        ξ' • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc V.transpose, Matrix.mul_nonsing_inv _ hdetV,
        Matrix.one_mul, blk_mul_blk, mul_one, one_mul, blk_same]
    rw [← Matrix.map_mul, e]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [hξ', phiInv_frob]

  have hG0μ : ∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius -
      (p : Ainf p O) • G0) i m := by
    have := c_modtau p C v O hv ε hε F _ (Fin h) (U * blk d k (p : F.B) 1)
      ((p : F.B) • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B)) (V * blk d k (p : Ainf p O) 1)
      ((p : Ainf p O) • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O))) Gm.transpose G0
      hR hpone (fun i m => hGG i m) (by rw [hG, Matrix.smul_mul, Matrix.one_mul])
    simpa only [Matrix.smul_mul, Matrix.one_mul] using this
  have hdivG := c_divG p C v O hv ε hε F d k h V G0 hG0μ (fun j m => by rw [hθG]; exact hGθ m j)
  have hnilG := c_nilG p C v O hv ε hε F d k U V hUV hN1
  choose Gw hGw1 hGw2 using fun m : Fin h => c_solve p C v O hv ε hε _
    (V * blk d k ξ' 1) (fun i => G0 i m) hnilG (fun i => hdivG i m)
  let Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O) := Matrix.of fun m i => Gw m i
  have hGaeq : ξ' • Ga.transpose = V * blk d k ξ' 1 * Ga.transpose.map WittVector.frobenius :=
    Matrix.ext fun i m => hGw2 m i
  have hφP : (Ga * Fa).map WittVector.frobenius = ξ' • (Ga * Fa) := by
    have e : ξ' • Ga = Ga.map WittVector.frobenius * blk d k ξ' 1 * V.transpose := by
      have := congrArg Matrix.transpose hGaeq
      rw [Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_mul,
        Matrix.transpose_mul, blk_transpose, Matrix.transpose_map, Matrix.transpose_transpose,
        ← Matrix.mul_assoc] at this
      exact this
    rw [Matrix.map_mul, hφFa, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← e, Matrix.smul_mul]

  obtain ⟨u, hu, hτu, hau⟩ := GlobalTheory.T.frobenius_xi_eq_p_mul_unit p C v O hv ε hε F
  obtain ⟨l, hτl, hσl⟩ := GlobalTheory.T.exists_ainf_frame_lift_twisted_frobenius p C v O hv ε hε F u hτu
  let U' := V.map F.a * blk d k u 1
  have hU' : IsUnit U' := by
    refine IsUnit.mul ?_ ?_
    · exact hV.map (RingHom.mapMatrix F.a)
    · refine Matrix.isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i => ?_)
      rcases i with i | i
      · exact hu
      · exact isUnit_one
  have hUU' : ∀ i j, F.τ ∣ U i j - U' i j := by
    intro i j
    simp only [U', blk, Matrix.mul_diagonal, Matrix.map_apply]
    rcases j with j | j
    · have : U i (Sum.inl j) - F.a (V i (Sum.inl j)) * u =
          (U i (Sum.inl j) - F.a (V i (Sum.inl j))) - F.a (V i (Sum.inl j)) * (u - 1) := by ring
      simp only [Sum.elim_inl]
      rw [this]
      exact dvd_sub (hUV _ _) (dvd_mul_of_dvd_right hτu _)
    · simp only [Sum.elim_inr, mul_one]
      exact hUV _ _
  obtain ⟨X, hX1, hX2⟩ := GlobalTheory.T.isIso_windows_of_matrix_congr_mod_tau p C v O hv ε hε F d k U U' hU hU' hUU' hN1
  obtain ⟨hn1', hn2'⟩ := c_nilCong p C v O hv ε hε F d k U U' hU hU' hUU' hN2 hN1
  have haξ : F.a ξ' = (p : F.B) * u := hau
  let Z := Fa.map F.a
  have hZσ : Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z := by
    have e1 : Z.map F.σ = (Fa.map WittVector.frobenius).map F.a :=
      Matrix.ext fun i m => F.σ_a _
    rw [e1, hφFa, Matrix.map_mul, Matrix.map_mul, blk_map, haξ, map_one, Matrix.transpose_map]
    show _ = blk d k (p : F.B) 1 * (V.map F.a * blk d k u 1).transpose * Fa.map F.a
    rw [Matrix.transpose_mul, blk_transpose, ← Matrix.mul_assoc (blk d k (p : F.B) 1), blk_mul_blk,
      mul_one]
  have hZY : ∀ i m, F.τ ∣ Z i m - Y i m := by
    intro i m
    have e : Z i m - Y i m = F.a (Fw m i - F0 i m) - (Y i m - F.a (F0 i m)) := by
      simp only [Z, Fa, Matrix.map_apply, Matrix.of_apply, map_sub]; ring
    rw [e]
    exact dvd_sub (hdvdμ _ (hFw1 m i)) (hYF i m)
  have hZ := c_cmpF p C v O hv ε hε F d k h U U' X Y Z hU' hn1' hn2' hX2 hX1 hY hZσ hZY
  let W := Ga.transpose.map F.a
  have hWσ : U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W := by
    have e1 : W.map F.σ = (Ga.transpose.map WittVector.frobenius).map F.a :=
      Matrix.ext fun i m => F.σ_a _
    have hGaeq' : blk d k ξ' ξ' * Ga.transpose = V * blk d k ξ' 1 * Ga.transpose.map WittVector.frobenius := by
      rw [blk_same, Matrix.smul_mul, Matrix.one_mul]; exact hGaeq
    have e2 := congrArg (fun M => M.map F.a) hGaeq'
    simp only [Matrix.map_mul, blk_map, haξ, map_one] at e2
    have e3 : U' * blk d k (p : F.B) 1 = V.map F.a * blk d k ((p : F.B) * u) 1 := by
      show V.map F.a * blk d k u 1 * blk d k (p : F.B) 1 = _
      rw [Matrix.mul_assoc, blk_mul_blk, mul_comm u, mul_one]
    rw [e1, e3, ← e2, blk_same, Matrix.smul_mul, Matrix.one_mul]

  have hWG : ∀ i m, F.τ ∣ W i m - Gm m i := by
    intro i m
    have e : W i m - Gm m i = F.a (Gw m i - G0 i m) - (Gm m i - F.a (G0 i m)) := by
      simp only [W, Ga, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, map_sub]; ring
    rw [e]
    exact dvd_sub (hdvdμ _ (hGw1 m i)) (hGG i m)
  have hXW := c_cmpG p C v O hv ε hε F d k h U U' X u l Gm W hU hN2 hN1 hτu hX2 hX1 hσl hτl hG hWσ hWG
  have hlμ : l * F.a (Sandwich.mu ε) = F.a (Sandwich.mu ε) := by
    obtain ⟨c, hc⟩ := hτl
    rw [← F.p_τ, sub_eq_iff_eq_add.1 hc]
    linear_combination (p * c) * F.τ_sq
  have hprod : (Ga * Fa).map F.a = F.a (Sandwich.mu ε) •
      (1 : Matrix (Fin h) (Fin h) F.B) := by
    have eW : Ga.map F.a = W.transpose := by
      simp only [W, Matrix.transpose_map, Matrix.transpose_transpose]
    rw [Matrix.map_mul, eW, show Fa.map F.a = Z from rfl, hZ, ← Matrix.mul_assoc,
      ← Matrix.transpose_mul, hXW, Matrix.transpose_smul, Matrix.transpose_transpose,
      Matrix.smul_mul, hGY, smul_smul, hlμ]
  have hGaFa : Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
    refine Matrix.ext fun i j => ?_
    refine c_eig p C v O hv ε hε F _ _ ?_ ?_ ?_
    · have := congr_fun (congr_fun hφP i) j
      simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
    · simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp only [mul_one, mul_zero, map_zero, frob_mu]
    · have := congr_fun (congr_fun hprod i) j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this ⊢
      rw [this]
      split_ifs <;> simp
  refine ⟨Fa, Ga, Ψ, Ψ', hGaFa, hFaΨ, hΨΨ', fun i m => ?_, fun m i => ?_⟩
  · obtain ⟨c, hc⟩ := hFw1 m i
    show WittVector.fontaineTheta O p (Fw m i) = _
    rw [sub_eq_iff_eq_add.1 hc, map_add (f := _), map_mul, theta_mu hv hε, zero_mul, zero_add, hθY]
  · obtain ⟨c, hc⟩ := hGw1 m i
    show WittVector.fontaineTheta O p (Gw m i) = _
    rw [sub_eq_iff_eq_add.1 hc, map_add (f := _), map_mul, theta_mu hv hε, zero_mul, zero_add, hθG]

end GlobalTheory.WinLift.Top
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WindowLiftToFontaineAinfMatricesStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.window_lift_to_fontaineAinf_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i) := by
  first | exact @GlobalTheory.WinLift.Top.window_lift | exact GlobalTheory.WinLift.Top.window_lift | (intros; apply GlobalTheory.WinLift.Top.window_lift <;> assumption)
end
