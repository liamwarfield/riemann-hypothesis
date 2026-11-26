module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorSchroedingerImageAtLevelPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorSchroedingerImageAtLevelPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadPlace


set_option maxHeartbeats 2000000 in
theorem vec_read_at : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → ∃ (ea : AE D) (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) (c : ℂ), IsIdemSum ea (R.Pg ∪ R.Q t) ∧ IsSplitIdem D e ∧ e * ea = e ∧ f = e + cA D e ∧ IsStdChar D R.ψ (-1) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ IsLatVac (heisO R.ψ (Vc D i) (Wc D i)) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (R.vacP i) ∧ IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) 1 (R.vacP i) Tm ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) ∧ R.vP i t = Tm (datP R i t ea) ∧ R.ωP i t (1, k) (R.vP i t) = c • Tm (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t P hP e f hPI k hk
  obtain ⟨⟨hψ, hvac⟩, ea, hIS, hth⟩ := hL.thP.vP i t
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hvP : R.vP i t = Tm (datP R i t ea) := hall Tm hTm
  have lV := GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hL.lev.βV i)
  have lW := GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hL.lev.βW i)
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) := GlobalTheory.AdTh.RecPair.selfDual_of_coe lV
  have hSW : IsSelfDualC (Wc D i) (R.ΛW i) := GlobalTheory.AdTh.RecPair.selfDual_of_coe lW
  have hIS' := hIS
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := hIS'
  have hPm : P ∈ R.Pg ∪ R.Q t := Finset.mem_union.2 hP
  obtain ⟨rfl, rfl⟩ := GlobalTheory.Hk3.SplitMatch.idem_unique (hes P hPm) hPI
  have h1 : ∀ PP ∈ R.Pg ∪ R.Q t, IsSplitIdem D (es PP) := fun PP hPP => (hes PP hPP).1
  have h2 : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ QQ ∈ R.Pg ∪ R.Q t, QQ ≠ PP → es PP * es QQ = 0 := by
    intro PP hPP QQ hQQ hne
    refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP) (h1 QQ hQQ)).resolve_left fun h => hne ?_
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [(hes PP hPP).2 x hx, (hes QQ hQQ).2 x hx, h]
  have hee : es P * ea = es P := by
    rw [hsum]; exact GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hPm
  have ho := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hinf : infPart D (cA D ea) = 0 := ho.infPart_eq
  have hSB : IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) :=
    GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hSV)
      (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hSW) hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
      (R.Pg ∪ R.Q t) (fun y => omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => by
        rw [GlobalTheory.PlaceVec.omegaK_congr R.Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          GlobalTheory.PlaceVec.omegaQ_congr (R.Q t) _ (R.xiR t) _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ (R.ΛV i) hSV
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ (R.ΛW i) hSW
  have hSB2 := GlobalTheory.SplitLinear.isSBHalf_actO inferInstance inferInstance 1 k⁻¹ hSB
  have hcc : cA D ea * cA D (cA D ea) = 0 := by rw [GlobalTheory.SplitOnto.cA_cA, mul_comm, hc]
  have ha : cA D ea * cA D ea = cA D ea := ho.idem
  have r1 : cA D ea * cA D (es P) = cA D (es P) := by rw [← map_mul, mul_comm, hee]
  have r2 : ea * cA D (es P) = 0 := by
    have e1 : cA D (es P) = cA D (es P) * cA D ea := by rw [← map_mul, hee]
    rw [e1, ← mul_assoc, mul_comm ea, mul_assoc, hc, mul_zero]
  have r3 : cA D ea * es P = 0 := by
    have := congrArg (cA D) r2
    rwa [map_mul, GlobalTheory.SplitOnto.cA_cA, map_zero] at this
  have r4 : ea * es P = es P := by rw [mul_comm, hee]
  have key : (cA D ea + cA D (cA D ea)) * (es P + cA D (es P)) = es P + cA D (es P) := by
    rw [GlobalTheory.SplitOnto.cA_cA]
    linear_combination r1 + r2 + r3 + r4
  have hsupp : SuppAt (cA D ea) (Wc D i) k := fun a b => by
    rw [← hk a b, ← mul_assoc, key]
  have hLaw := GlobalTheory.SplitLinear.law_orth (hF i t).datum hSV hSW ho hcc hvac.theta hvac.lat one_ne_zero hTm
    (GlobalTheory.SplitLinear.suppAt_one _ _) hsupp (GlobalTheory.VecInv.isDetAt_detAt _ ha _ 1) (GlobalTheory.VecInv.isDetAt_detAt _ ha _ k)
  have hω := hLaw _ hSB
  rw [← hvP] at hω
  simp only [inv_one] at hω
  exact ⟨ea, Tm, _, hIS, (hes P hPm).1, hee, rfl, hψ, hSV, hSW, hvac.theta, hvac.lat, hTm, hSB, hSB2, hvP, hω⟩

end GlobalTheory.BadPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorSchroedingerImageAtLevelPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftVector_schroedingerImage_at_levelPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → ∃ (ea : AE D) (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) (c : ℂ), IsIdemSum ea (R.Pg ∪ R.Q t) ∧ IsSplitIdem D e ∧ e * ea = e ∧ f = e + cA D e ∧ IsStdChar D R.ψ (-1) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ IsLatVac (heisO R.ψ (Vc D i) (Wc D i)) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (R.vacP i) ∧ IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) 1 (R.vacP i) Tm ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) ∧ R.vP i t = Tm (datP R i t ea) ∧ R.ωP i t (1, k) (R.vP i t) = c • Tm (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) := by
  first | exact @GlobalTheory.BadPlace.vec_read_at | exact GlobalTheory.BadPlace.vec_read_at | (intros; apply GlobalTheory.BadPlace.vec_read_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaHalfSpaceDatumTranslateDisjointSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointMulFrameMatrixEqIdempotentSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointMulFrameMatrixEqIdempotentSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LocDisj

theorem map_cA_smul_of_fix (D : D7) {m n : ℕ} (f : AE D) (hf : cA D f = f) (X : Matrix (Fin m) (Fin n) (AE D)) :
    (f • X).map (cA D) = f • X.map (cA D) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hf]

theorem map_toEAf_smul (D : D7) {m n : ℕ} (f : AE D) (Y : Matrix (Fin m) (Fin n) (AE D)) :
    (f • Y).map (toEAf D) = toEAf D f • Y.map (toEAf D) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem frMapAdj_smul_of_fix (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (hf : cA D f = f) (x : WO V W) :
    frMapAdj V W βV βW (f • x) = toEAf D f • frMapAdj V W βV βW x := by
  unfold frMapAdj
  have h3 : (HMul.hMul (HMul.hMul ((V.gram⁻¹).map (incA D)) ((f • (x : Matrix (Fin W.rank) (Fin V.rank) (AE D))).map (cA D)).transpose) (W.gram.map (incA D)) : Matrix (Fin V.rank) (Fin W.rank) (AE D))
      = f • (HMul.hMul (HMul.hMul ((V.gram⁻¹).map (incA D)) ((x : Matrix (Fin W.rank) (Fin V.rank) (AE D)).map (cA D)).transpose) (W.gram.map (incA D)) : Matrix (Fin V.rank) (Fin W.rank) (AE D)) := by
    rw [map_cA_smul_of_fix D f hf, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [h3, map_toEAf_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_smul_eq {n : ℕ} {R : Type} [CommRing R] (c : R) (β : GL (Fin n) R) (M : Matrix (Fin n) (Fin n) R)
    (h0 : ∀ i j, c * (M - 1) i j = 0) :
    c • (β⁻¹.val * M * β.val) = c • (1 : Matrix (Fin n) (Fin n) R) := by
  have hM : c • M = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← sub_eq_zero, ← smul_sub]
    ext i j
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using h0 i j
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.inv_mul]

theorem split_mul {m n : ℕ} {R : Type} [CommRing R] (c : R) (A A' : Matrix (Fin m) (Fin n) R) (K : Matrix (Fin n) (Fin n) R)
    (hx : c • A = c • A') (hK : (1 - c) • K = (1 - c) • (1 : Matrix (Fin n) (Fin n) R)) :
    A' * K = c • (A * K) + (1 - c) • A' := by
  calc A' * K = (c + (1 - c)) • (A' * K) := by rw [add_sub_cancel, one_smul]
    _ = (c • A') * K + A' * ((1 - c) • K) := by rw [add_smul, Matrix.smul_mul, Matrix.mul_smul]
    _ = (c • A) * K + A' * ((1 - c) • (1 : Matrix (Fin n) (Fin n) R)) := by rw [hx, hK]
    _ = c • (A * K) + (1 - c) • A' := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]

theorem suppF_entry (D : D7) (W : HSp D) (f : AE D) (k : GA D W) (hk : SuppF W f k) (i j : Fin W.rank) :
    (1 - toEAf D f) * ((Formalism.L2.Theta.mt W k).map (toEAf D) - 1) i j = 0 := by
  have e : ((Formalism.L2.Theta.mt W k).map (toEAf D) - 1) i j = toEAf D ((Formalism.L2.Theta.mt W k - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, ← map_one (toEAf D), ← map_sub, ← map_mul, sub_mul, one_mul, hk i j, sub_self, map_zero]

end GlobalTheory.LocDisj

namespace GlobalTheory.LocDisj

theorem frMapAdj_mul_frame_eq (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (hf : cA D f = f) (k : GA D W) (hk : SuppF W f k) (x x' : WO V W) (hxx : ∀ a b, f * x a b = f * x' a b) :
  (HMul.hMul (frMapAdj V W βV βW x') (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) = toEAf D f • (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) + (1 - toEAf D f) • frMapAdj V W βV βW x' := by
  have hfx : f • x = f • x' := by
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hxx a b
  have hx : toEAf D f • frMapAdj V W βV βW x = toEAf D f • frMapAdj V W βV βW x' := by
    rw [← frMapAdj_smul_of_fix D V W βV βW f hf, ← frMapAdj_smul_of_fix D V W βV βW f hf, hfx]
  exact split_mul (toEAf D f) _ _ _ hx (conj_smul_eq _ βW _ (suppF_entry D W f k hk))

end GlobalTheory.LocDisj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointMulFrameMatrixEqIdempotentSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMapAdjoint_mul_frameMatrix_eq_idempotent_split : ∀ (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D), cA D f = f → ∀ k : GA D W, SuppF W f k → ∀ x x' : WO V W, (∀ a b, f * x a b = f * x' a b) → (HMul.hMul (frMapAdj V W βV βW x') (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) = toEAf D f • (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) + (1 - toEAf D f) • frMapAdj V W βV βW x' := by
  first | exact @GlobalTheory.LocDisj.frMapAdj_mul_frame_eq | exact GlobalTheory.LocDisj.frMapAdj_mul_frame_eq | (intros; apply GlobalTheory.LocDisj.frMapAdj_mul_frame_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicMemSelfDualFrameStabilizerOfSplitSup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicMemSelfDualFrameStabilizerOfSplitSup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.SplitStabFrame

open GlobalTheory.StdFrames GlobalTheory.IdemSupport GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

variable {D : D7}


set_option maxHeartbeats 400000 in
theorem cpt_sg_mem {Q : Pl D.host.E} {z : Ef D}
    (hz : cpt Q z ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    cpt (cP Q) (sg D z) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) := by
  obtain ⟨e, -, -, h1, h0⟩ := exists_idem (D := D) {Q}
  have hQ1 : cpt Q e = 1 := h1 Q (Set.mem_singleton Q)
  have hez : e * z ∈ OA D := by
    refine (mem_OA_iff _).2 fun R => ?_
    rw [map_mul]
    by_cases hR : R = Q
    · rw [hR, hQ1, one_mul]; exact hz
    · rw [h0 R (Set.notMem_singleton_iff.2 hR), zero_mul]; exact zero_mem _
  have h2 : cpt (cP Q) (sg D (e * z)) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) :=
    (mem_OA_iff (sg D (e * z))).1 (GlobalTheory.LevSplit.sigR_int hez) (cP Q)
  have h3 : cpt (cP Q) (sg D (1 - e)) = 0 :=
    cpt_sg_eq_zero (by rw [cP_cP, map_sub, map_one, hQ1, sub_self])
  have h4 : cpt (cP Q) (sg D e) = 1 := by
    rw [map_sub, map_one, map_sub, map_one, sub_eq_zero] at h3
    exact h3.symm
  rw [map_mul, map_mul, h4, one_mul] at h2
  exact h2

theorem int_mul {Q : Pl D.host.E} {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Ef D)}
    (hA : ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q)
    (hB : ∀ i j, cpt Q (B i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    ∀ i j, cpt Q ((A * B) i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
  intro i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  exact sum_mem fun l _ => by rw [map_mul]; exact mul_mem (hA i l) (hB l j)

theorem int_of_OA {Q : Pl D.host.E} {n : ℕ} {A : Matrix (Fin n) (Fin n) (Ef D)} (h : ∀ i j, A i j ∈ OA D) :
    ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q :=
  fun i j => (mem_OA_iff _).1 (h i j) Q

theorem int_cT {Q : Pl D.host.E} {n : ℕ} {A : Matrix (Fin n) (Fin n) (Ef D)}
    (h : ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    ∀ i j, cpt (cP Q) (Formalism.UG.cT (sg D) A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) :=
  fun i j => cpt_sg_mem (h j i)

theorem inv_eq_of_unitary {n : ℕ} {J U' : Matrix (Fin n) (Fin n) (Ef D)} (hU : U' * J = 1) (Y : GL (Fin n) (Ef D))
    (hY : Formalism.UG.cT (sg D) Y.val * J * Y.val = J) : (Y⁻¹).val = U' * Formalism.UG.cT (sg D) Y.val * J := by
  have h1 : U' * (Formalism.UG.cT (sg D) Y.val * J * Y.val) = 1 := by rw [hY, hU]
  calc (Y⁻¹).val = (U' * (Formalism.UG.cT (sg D) Y.val * J * Y.val)) * (Y⁻¹).val := by rw [h1, Matrix.one_mul]
    _ = U' * Formalism.UG.cT (sg D) Y.val * J * (Y.val * (Y⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Units.mul_inv, Matrix.mul_one]

theorem unitary_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) (Ef D)} (Y : GL (Fin n) (Ef D))
    (hY : Formalism.UG.cT (sg D) Y.val * J * Y.val = J) :
    Formalism.UG.cT (sg D) (Y⁻¹).val * J * (Y⁻¹).val = J := by
  calc Formalism.UG.cT (sg D) (Y⁻¹).val * J * (Y⁻¹).val
        = Formalism.UG.cT (sg D) (Y⁻¹).val * (Formalism.UG.cT (sg D) Y.val * J * Y.val) * (Y⁻¹).val := by rw [hY]
    _ = Formalism.UG.cT (sg D) (Y.val * (Y⁻¹).val) * J * (Y.val * (Y⁻¹).val) := by
        rw [cT_mul']; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, cT_one', Matrix.one_mul, Matrix.mul_one]

theorem inv_int_at {Q : Pl D.host.E} {n : ℕ} (X : GL (Fin n) (Ef D))
    (hint : ∀ i j, cpt Q (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q)
    (hdet : Valued.v (cpt Q X.val.det) = 1) :
    ∀ i j, cpt Q ((X⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
  set A := (cpt Q).mapMatrix X.val with hAdef
  have hBA : (cpt Q).mapMatrix (X⁻¹).val * A = 1 := by rw [hAdef, ← map_mul, Units.inv_mul, map_one]
  have hB : (cpt Q).mapMatrix (X⁻¹).val = A⁻¹ := (Matrix.inv_eq_left_inv hBA).symm
  let A' : Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :=
    fun i j => ⟨A i j, hint i j⟩
  have hA' : (HeightOneSpectrum.adicCompletionIntegers D.host.E Q).subtype.mapMatrix A' = A := rfl
  have hdetA : A.det = cpt Q X.val.det := (RingHom.map_det _ _).symm
  intro i j
  have e : cpt Q ((X⁻¹).val i j) = ((cpt Q).mapMatrix (X⁻¹).val) i j := rfl
  rw [e, hB, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem ?_ ?_
  · rw [hdetA, Ring.inverse_eq_inv', HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hdet, inv_one]
  · rw [← hA', ← RingHom.map_adjugate]
    exact (A'.adjugate i j).2

theorem int_of_split {n : ℕ} (J U' : Matrix (Fin n) (Fin n) (Ef D)) (hJ : ∀ i j, J i j ∈ OA D)
    (hU' : ∀ i j, U' i j ∈ OA D) (hUJ : U' * J = 1) (X : GL (Fin n) (Ef D))
    (hX : Formalism.UG.cT (sg D) X.val * J * X.val = J) (P : Pl D.host.E)
    (hint : ∀ i j, cpt P (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E P)
    (hdet : Valued.v (cpt P X.val.det) = 1)
    (hoff : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix X.val = 1) :
    (∀ i j, X.val i j ∈ OA D) ∧ ∀ i j, (X⁻¹).val i j ∈ OA D := by
  have hXi := unitary_inv X hX
  have intPi := inv_int_at X hint hdet
  have key : ∀ Y : GL (Fin n) (Ef D), Formalism.UG.cT (sg D) Y.val * J * Y.val = J →
      (∀ i j, cpt P (Y.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E P) →
      ∀ i j, cpt (cP P) ((Y⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP P) := by
    intro Y hY hYP
    rw [inv_eq_of_unitary hUJ Y hY]
    exact int_mul (int_mul (int_of_OA hU') (int_cT hYP)) (int_of_OA hJ)
  have hall : ∀ Q : Pl D.host.E,
      (∀ i j, cpt Q (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) ∧
        ∀ i j, cpt Q ((X⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
    intro Q
    by_cases h1 : Q = P
    · rw [h1]; exact ⟨hint, intPi⟩
    by_cases h2 : Q = cP P
    · rw [h2]
      refine ⟨?_, key X hX hint⟩
      have := key X⁻¹ hXi intPi
      rwa [inv_inv] at this
    · have h3 := hoff Q h1 h2
      have h4 : (cpt Q).mapMatrix (X⁻¹).val = 1 :=
        calc (cpt Q).mapMatrix (X⁻¹).val = (cpt Q).mapMatrix (X⁻¹).val * (cpt Q).mapMatrix X.val := by
              rw [h3, Matrix.mul_one]
          _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      have one_int : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E)) i j ∈
          HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
        intro i j
        rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have : cpt Q (X.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := congrFun (congrFun h3 i) j
        rw [this]; exact one_int i j
      · have : cpt Q ((X⁻¹).val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := congrFun (congrFun h4 i) j
        rw [this]; exact one_int i j
  exact ⟨fun i j => (mem_OA_iff _).2 fun Q => (hall Q).1 i j,
    fun i j => (mem_OA_iff _).2 fun Q => (hall Q).2 i j⟩


set_option maxHeartbeats 800000 in
theorem finE_mem_St_of_split : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ (e f : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → f = e + cA D e → GlobalTheory.IdemSupport.cP P ≠ P → ∀ k : GA D W, SuppF W f k → (∀ a b, GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) a b) ∈ P.adicCompletionIntegers D.host.E) → Valued.v (GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D))).det) = 1 → finE W k ∈ St β := by
  intro D W β Λ hSD e f P hP hf _ k hS hint hdet
  obtain ⟨hJ, U', hU', hUJ⟩ := unimod_of_isSD hSD
  have hg : Formalism.UG.cT (sg D) (finE W k).val * ratM W.gram * (finE W k).val = ratM W.gram :=
    GlobalTheory.LevSplit.finE_mem_UA W k
  set g := finE W k with hgdef
  let X : GL (Fin W.rank) (Ef D) := β⁻¹ * g * β
  have hXv : X.val = (β⁻¹).val * g.val * β.val := rfl
  have hX : Formalism.UG.cT (sg D) X.val * gramOf W β * X.val = gramOf W β := by
    have e2 : Formalism.UG.cT (sg D) (β⁻¹).val * Formalism.UG.cT (sg D) β.val = 1 := by
      rw [← cT_mul', Units.mul_inv, cT_one']
    have e3 : β.val * (β⁻¹).val = 1 := Units.mul_inv β
    show Formalism.UG.cT (sg D) X.val * (Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val) * X.val =
      Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val
    rw [hXv, cT_mul', cT_mul']
    calc Formalism.UG.cT (sg D) β.val * (Formalism.UG.cT (sg D) g.val * Formalism.UG.cT (sg D) (β⁻¹).val) *
          (Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val) * ((β⁻¹).val * g.val * β.val)
        = Formalism.UG.cT (sg D) β.val * Formalism.UG.cT (sg D) g.val *
          (Formalism.UG.cT (sg D) (β⁻¹).val * Formalism.UG.cT (sg D) β.val) * ratM W.gram * (β.val * (β⁻¹).val) *
          g.val * β.val := by simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT (sg D) β.val * (Formalism.UG.cT (sg D) g.val * ratM W.gram * g.val) * β.val := by
          rw [e2, e3]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hg]
  have hf0 : ∀ Q, Q ≠ P → Q ≠ cP P → cpt Q (toEAf D f) = 0 := by
    intro Q h1 h2
    have h3 : cP Q ≠ P := fun h => h2 (by rw [← h, cP_cP])
    rw [hf, RingHom.map_add (toEAf D), toEAf_cA, RingHom.map_add (cpt Q), (cpt_of_isIdemAt hP).2 Q h1,
      cpt_sg_eq_zero ((cpt_of_isIdemAt hP).2 _ h3), add_zero]
  have hM : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix g.val = 1 := by
    intro Q h1 h2
    refine Matrix.ext fun i j => ?_
    have h3 := congrArg (fun z => cpt Q (toEAf D z)) (hS i j)
    rw [RingHom.map_mul (toEAf D), RingHom.map_mul (cpt Q), hf0 Q h1 h2, zero_mul, Matrix.sub_apply,
      RingHom.map_sub (toEAf D), RingHom.map_sub (cpt Q)] at h3
    rw [eq_comm, sub_eq_zero] at h3
    change cpt Q (toEAf D (Formalism.L2.Theta.mt W k i j)) = (1 : Matrix (Fin W.rank) (Fin W.rank) _) i j
    rw [h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hoff : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix X.val = 1 := by
    intro Q h1 h2
    rw [hXv, map_mul, map_mul, hM Q h1 h2, Matrix.mul_one, ← map_mul, Units.inv_mul, map_one]
  obtain ⟨h1, h2⟩ := int_of_split (gramOf W β) U' hJ hU' hUJ X hX P hint hdet hoff
  let Mi : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun i j => ⟨_, h1 i j⟩
  let Mi' : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun i j => ⟨_, h2 i j⟩
  have inj : Function.Injective ((Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix (m := Fin W.rank)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p1 : Mi * Mi' = 1 := inj (by rw [map_mul, map_one]; exact Units.mul_inv X)
  have p2 : Mi' * Mi = 1 := inj (by rw [map_mul, map_one]; exact Units.inv_mul X)
  refine ⟨⟨Mi, Mi', p1, p2⟩, ?_⟩
  have hX' : intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ = X := Units.ext rfl
  show β * intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ * β⁻¹ = g
  rw [hX']
  show β * (β⁻¹ * g * β) * β⁻¹ = g
  rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc, mul_inv_cancel, one_mul]

end GlobalTheory.SplitStabFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicMemSelfDualFrameStabilizerOfSplitSupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelic_mem_selfDualFrameStabilizer_of_splitSupport : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ (e f : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → f = e + cA D e → GlobalTheory.IdemSupport.cP P ≠ P → ∀ k : GA D W, SuppF W f k → (∀ a b, GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) a b) ∈ P.adicCompletionIntegers D.host.E) → Valued.v (GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D))).det) = 1 → finE W k ∈ St β := by
  first | exact @GlobalTheory.SplitStabFrame.finE_mem_St_of_split | exact GlobalTheory.SplitStabFrame.finE_mem_St_of_split | (intros; apply GlobalTheory.SplitStabFrame.finE_mem_St_of_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameReductionEqOneOfFrameMatrixCongruentOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameReductionEqOneOfFrameMatrixCongruentOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.RedAt

theorem redFn_finE_eq_one : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (PP : Pl D.host.E), finE W k ∈ St β → (∀ a b, Valued.v (GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b)) < 1) → redFn β PP (finE W k) = 1 := by
  intro D W β k PP hk hv
  obtain ⟨y, hy⟩ := hk
  have hyv : (Formalism.L2.DIV.intGL _ _ _ y).val
      = (HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val :
          Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) := by
    have h2 : Formalism.L2.DIV.intGL _ _ _ y = β⁻¹ * finE W k * β := by
      rw [← hy]; simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, mul_assoc]
    rw [h2]; rfl
  rw [← hy, GlobalTheory.LiftLevel.redFn_eq_one_iff]
  intro i j
  rw [GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]
  have := hv i j
  rw [← hyv] at this
  convert this using 3
  simp [Matrix.sub_apply, Matrix.one_apply, Formalism.L2.DIV.intGL, Formalism.UG.bc]
  split_ifs <;> simp

end GlobalTheory.RedAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameReductionEqOneOfFrameMatrixCongruentOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameReduction_eq_one_of_frameMatrix_congruent_one : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (PP : Pl D.host.E), finE W k ∈ St β → (∀ a b, Valued.v (GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b)) < 1) → redFn β PP (finE W k) = 1 := by
  first | exact @GlobalTheory.RedAt.redFn_finE_eq_one | exact GlobalTheory.RedAt.redFn_finE_eq_one | (intros; apply GlobalTheory.RedAt.redFn_finE_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFrameChangeMemIntegralGLAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFrameChangeMemIntegralGLAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.LocCore

theorem adj_det_integral {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1) :
    (∀ i j, v (A.adjugate i j) ≤ 1) ∧ v A.det ≤ 1 := by
  let A' : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  have hA' : A'.map v.integer.subtype = A := by ext i j; rfl
  constructor
  · intro i j
    have h := RingHom.map_adjugate v.integer.subtype A'
    simp only [RingHom.mapMatrix_apply, hA'] at h
    rw [← h]
    exact (A'.adjugate i j).2
  · have h := RingHom.map_det v.integer.subtype A'
    simp only [RingHom.mapMatrix_apply, hA'] at h
    rw [← h]
    exact (A'.det).2

theorem solve_integral {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} (A B κ : Matrix (Fin n) (Fin n) K) (hAB : A * κ = B)
    (hA : ∀ i j, v (A i j) ≤ 1) (hB : ∀ i j, v (B i j) ≤ 1)
    (hdA : v A.det = 1) (hdB : v B.det = 1) :
    (∀ a b, v (κ a b) ≤ 1) ∧ v κ.det = 1 ∧
      ((∀ i j, v ((A - 1) i j) < 1) → (∀ i j, v ((B - 1) i j) < 1) →
        ∀ a b, v ((κ - 1) a b) < 1) := by
  obtain ⟨hadj, -⟩ := adj_det_integral v A hA
  have key : A.det • κ = A.adjugate * B := by
    rw [← hAB, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have key' : A.det • (κ - 1) = A.adjugate * (B - A) := by
    rw [smul_sub, key, Matrix.mul_sub, Matrix.adjugate_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have h := congrFun (congrFun key a) b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
    have h2 := congrArg v h
    rw [map_mul, hdA, one_mul] at h2
    rw [h2]
    apply v.map_sum_le
    intro k _
    rw [map_mul]
    exact mul_le_one' (hadj a k) (hB k b)
  · have h := congrArg v (congrArg Matrix.det hAB)
    rw [Matrix.det_mul, map_mul, hdA, one_mul, hdB] at h
    exact h
  · intro hA1 hB1 a b
    have h := congrFun (congrFun key' a) b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
    have h2 := congrArg v h
    rw [map_mul, hdA, one_mul] at h2
    rw [h2]
    apply v.map_sum_lt one_ne_zero
    intro k _
    rw [map_mul]
    have hBA : (B - A) k b = (B - 1) k b - (A - 1) k b := by
      simp only [Matrix.sub_apply, sub_sub_sub_cancel_right]
    have hlt : v ((B - A) k b) < 1 := by
      rw [hBA]; exact lt_of_le_of_lt (v.map_sub _ _) (max_lt (hB1 k b) (hA1 k b))
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hadj a k)) hlt

end GlobalTheory.LocCore

namespace GlobalTheory.LocCore

noncomputable def topAt {D : D7} (P : Pl D.host.E) {m n : ℕ} (hmn : n ≤ m)
    (U : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) :
    Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion D.host.E P) :=
  fun i j => GlobalTheory.StdFrames.cpt P (U (Fin.castLE hmn i) j)

theorem topAt_facts {D : D7} (P : Pl D.host.E) {m n : ℕ} (hmn : n ≤ m)
    (U : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (hU : IsIntM U)
    (hdU : IsUnit (topL n (redM P U)).det) :
    (∀ i j, Valued.v (topAt P hmn U i j) ≤ 1) ∧ Valued.v (topAt P hmn U).det = 1 ∧
      (topL n (redM P U) = 1 → ∀ i j, Valued.v ((topAt P hmn U - 1) i j) < 1) := by
  let S := Formalism.L2.Herm.intAf (↥D.host.F) D.host.E
  let A' : Matrix (Fin n) (Fin n) S := fun i j => ⟨U (Fin.castLE hmn i) j, hU _ _⟩
  let φ : S →+* HeightOneSpectrum.adicCompletion D.host.E P :=
    (GlobalTheory.StdFrames.cpt P).comp S.subtype
  have hA : A'.map φ = topAt P hmn U := by ext i j; rfl
  have hred : A'.map (resS (↥D.host.F) P) = topL n (redM P U) := by
    ext i j
    simp only [Matrix.map_apply, topL, redM]
    rw [dite_eq_left ⟨lt_of_lt_of_le i.2 hmn, j.2⟩, dite_eq_left (hU _ _)]
    rfl
  have hint : ∀ i j, Valued.v (topAt P hmn U i j) ≤ 1 := by
    intro i j
    have := (GlobalTheory.StdFrames.mem_OA_iff (U (Fin.castLE hmn i) j)).1 (hU _ _) P
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 this
  have hφ : ∀ s : S, resS (↥D.host.F) P s = 0 ↔ Valued.v (φ s) < 1 :=
    fun s => GlobalTheory.AdIsom.resS_eq_zero_iff_cpt P s
  refine ⟨hint, ?_, ?_⟩
  · apply le_antisymm ((adj_det_integral Valued.v _ hint).2)
    have h1 : resS (↥D.host.F) P A'.det ≠ 0 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hred]; exact hdU.ne_zero
    rw [Ne, hφ, not_lt, RingHom.map_det, RingHom.mapMatrix_apply, hA] at h1
    exact h1
  · intro h1 i j
    have hm : (resS (↥D.host.F) P).mapMatrix (A' - 1) = 0 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hred, h1, sub_self]
    have h2 : resS (↥D.host.F) P ((A' - 1) i j) = 0 := by
      have := congrFun (congrFun hm i) j
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
    have hm' : φ.mapMatrix (A' - 1) = topAt P hmn U - 1 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hA]
    have h3 : (topAt P hmn U - 1) i j = φ ((A' - 1) i j) := by
      have e := congrFun (congrFun hm' i) j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply] at e
      exact e.symm
    rw [h3]
    exact (hφ _).1 h2

end GlobalTheory.LocCore

namespace GlobalTheory.LocCore

theorem kappa_integral_at : ∀ (D : D7) (P : Pl D.host.E) (m n : ℕ) (U Y : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (κ : Matrix (Fin n) (Fin n) (Formalism.IndefR.Datum.EAf D)) (c : Formalism.IndefR.Datum.EAf D), GlobalTheory.StdFrames.cpt P c = 1 → (HMul.hMul U κ : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) = c • Y + (1 - c) • U → IsIntM U → IsIntM Y → IsUnit (topL n (redM P U)).det → IsUnit (topL n (redM P Y)).det → (∀ a b, GlobalTheory.StdFrames.cpt P (κ a b) ∈ P.adicCompletionIntegers D.host.E) ∧ Valued.v (GlobalTheory.StdFrames.cpt P κ.det) = 1 ∧ (topL n (redM P U) = 1 → topL n (redM P Y) = 1 → ∀ a b, Valued.v (GlobalTheory.StdFrames.cpt P ((κ - 1) a b)) < 1) := by
  intro D P m n U Y κ c hc hUk hU hY hdU hdY
  by_cases hmn : n ≤ m
  swap
  · exfalso
    push_neg at hmn
    have h0 : (topL n (redM P U)).det = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero ⟨m, hmn⟩
      intro j
      simp [topL]
    rw [h0] at hdU
    exact not_isUnit_zero hdU
  set cp := GlobalTheory.StdFrames.cpt (D := D) P with hcp
  obtain ⟨hAi, hAd, hA1⟩ := topAt_facts P hmn U hU hdU
  obtain ⟨hBi, hBd, hB1⟩ := topAt_facts P hmn Y hY hdY
  have hAB : topAt P hmn U * κ.map cp = topAt P hmn Y := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg cp (congrFun (congrFun hUk (Fin.castLE hmn i)) j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
      map_mul, map_add, map_sub, map_one, hc, sub_self, zero_mul, add_zero, one_mul] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply]
    exact h
  obtain ⟨k1, k2, k3⟩ := solve_integral Valued.v _ _ _ hAB hAi hBi hAd hBd
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (k1 a b)
  · rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact k2
  · intro h1 h2 a b
    have e : cp.mapMatrix (κ - 1) = κ.map cp - 1 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply]
    have e2 := congrFun (congrFun e a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at e2
    rw [e2]
    exact k3 (hA1 h1) (hB1 h2) a b

end GlobalTheory.LocCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFrameChangeMemIntegralGLAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFrameChange_mem_integralGL_at_place : ∀ (D : D7) (P : Pl D.host.E) (m n : ℕ) (U Y : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (κ : Matrix (Fin n) (Fin n) (Formalism.IndefR.Datum.EAf D)) (c : Formalism.IndefR.Datum.EAf D), GlobalTheory.StdFrames.cpt P c = 1 → (HMul.hMul U κ : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) = c • Y + (1 - c) • U → IsIntM U → IsIntM Y → IsUnit (topL n (redM P U)).det → IsUnit (topL n (redM P Y)).det → (∀ a b, GlobalTheory.StdFrames.cpt P (κ a b) ∈ P.adicCompletionIntegers D.host.E) ∧ Valued.v (GlobalTheory.StdFrames.cpt P κ.det) = 1 ∧ (topL n (redM P U) = 1 → topL n (redM P Y) = 1 → ∀ a b, Valued.v (GlobalTheory.StdFrames.cpt P ((κ - 1) a b)) < 1) := by
  first | exact @GlobalTheory.LocCore.kappa_integral_at | exact GlobalTheory.LocCore.kappa_integral_at | (intros; apply GlobalTheory.LocCore.kappa_integral_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixComponentSubOneEqZeroOffIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixComponentSubOneEqZeroOffIdempotent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.FrameOff

theorem cpt_frame_sub_one_eq_zero_of_suppF : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (k : GA D W) (PP : Pl D.host.E), SuppF W f k → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 → ∀ a b, GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b) = 0 := by
  intro D W β f k PP hS hf a b
  set M := Formalism.L2.Theta.mt W k with hMdef
  have hmap : M.map (toEAf D) - 1 = (M - 1).map (toEAf D) := by
    rw [Matrix.map_sub (toEAf D) (fun x y => (toEAf D).map_sub x y),
      Matrix.map_one _ (toEAf D).map_zero (toEAf D).map_one]
  have hM : ((M - 1).map (toEAf D)).map (GlobalTheory.StdFrames.cpt PP) = 0 := by
    refine Matrix.ext fun i j => ?_
    change GlobalTheory.StdFrames.cpt PP (toEAf D ((M - 1) i j)) = 0
    rw [← hS i j, RingHom.map_mul, RingHom.map_mul, hf, zero_mul]
  have hk : (HMul.hMul (HMul.hMul ((β)⁻¹).val (M.map (toEAf D))) (β).val :
        Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1
      = ((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
  rw [hk]
  change ((((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val).map (GlobalTheory.StdFrames.cpt PP)) a b = 0
  rw [Matrix.map_mul, Matrix.map_mul, hmap, hM, Matrix.mul_zero, Matrix.zero_mul]
  rfl

end GlobalTheory.FrameOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixComponentSubOneEqZeroOffIdempotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_component_sub_one_eq_zero_off_idempotent : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (k : GA D W) (PP : Pl D.host.E), SuppF W f k → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 → ∀ a b, GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b) = 0 := by
  first | exact @GlobalTheory.FrameOff.cpt_frame_sub_one_eq_zero_of_suppF | exact GlobalTheory.FrameOff.cpt_frame_sub_one_eq_zero_of_suppF | (intros; apply GlobalTheory.FrameOff.cpt_frame_sub_one_eq_zero_of_suppF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaHalfSpaceDatumTranslateDisjointSupport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadPlace

theorem datP_ne_zero_unpack {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ea : AE D)
    (y : WO (Vc D i) (Wc D i)) (h : datP R i t ea y ≠ 0) :
    IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y) ∧
    (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) ∧
    (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) := by
  unfold datP at h
  split_ifs at h with hc
  · refine ⟨hc.2, fun PP hPP => ?_, fun PP hPP => ?_⟩
    · have hK := left_ne_zero_of_mul h
      unfold omegaK at hK
      split_ifs at hK with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hK
    · have hQ := right_ne_zero_of_mul h
      unfold omegaQ at hQ
      split_ifs at hQ with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hQ
  · exact absurd rfl h

theorem disj_supp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ea : AE D), IsIdemSum ea (R.Pg ∪ R.Q t) → ∀ (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → ∀ x x' : WO (Vc D i) (Wc D i), (∀ a b, f * x a b = f * x' a b) → datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x) ≠ 0 → datP R i t ea x' ≠ 0 → False := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hFP i t ea hea P hP e f hpe k hk hkn x x' hxx h1 h2
  apply hkn
  have hPS : P ∈ R.Pg ∪ R.Q t := Finset.mem_union.2 hP
  obtain ⟨heP, hfe, hcf, hinf, hcP⟩ := GlobalTheory.T.primeIdempotent_of_idempotentSum_place_split D P e f ea (R.Pg ∪ R.Q t) hpe hea hPS
  obtain ⟨hI1, hK1, hQ1⟩ := datP_ne_zero_unpack R i t ea _ h1
  obtain ⟨hI2, hK2, hQ2⟩ := datP_ne_zero_unpack R i t ea _ h2
  have hY := GlobalTheory.T.frameMapAdjoint_translate_inv_eq_mul_frameMatrix D (Vc D i) (Wc D i) (R.βV i) (R.βW i) k x
  have hid := GlobalTheory.T.frameMapAdjoint_mul_frameMatrix_eq_idempotent_split D (Vc D i) (Wc D i) (R.βV i) (R.βW i) f hcf k hk x x' hxx
  rw [← hY] at hid

  have he1 := GlobalTheory.StdFrames.cpt_of_isIdemAt heP
  have hcPP : GlobalTheory.IdemSupport.cP P ≠ P := hcP P hPS
  have hfP : GlobalTheory.StdFrames.cpt P (toEAf D f) = 1 := by
    rw [hfe, RingHom.map_add (f := _), GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add (f := _), he1.1,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ hcPP), add_zero]
  have hfoff : ∀ PP ∈ R.Pg, PP ≠ P → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 := by
    intro PP hPP hne
    rw [hfe, RingHom.map_add (f := _), GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add (f := _), he1.2 _ hne,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ (hcP PP (Finset.mem_union_left _ hPP))), add_zero]
  have hu : ∀ (y : WO (Vc D i) (Wc D i)), (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) →
      (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) →
      IsUnit (topL (Wc D i).rank (redM P (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det := by
    intro y hK hQ
    rcases hP with hP | hP
    · rw [hK P hP, Matrix.det_one]; exact isUnit_one
    · exact hQ P hP
  obtain ⟨hint, hdet, hone⟩ := GlobalTheory.T.localFrameChange_mem_integralGL_at_place D P _ _ _ _ _ _ hfP hid hI2 hI1 (hu _ hK2 hQ2) (hu _ hK1 hQ1)
  have hSt := GlobalTheory.T.finiteAdelic_mem_selfDualFrameStabilizer_of_splitSupport D (Wc D i) (R.βW i) (R.ΛW i) (hL.lev.βW i) e f P heP hfe hcPP k hk hint hdet
  have hred : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → redFn (R.βW i) PP (finE (Wc D i) k) = 1 := by
    rintro PP (hPP | hPP)
    · change PP ∈ R.Pg at hPP
      refine GlobalTheory.T.frameReduction_eq_one_of_frameMatrix_congruent_one D (Wc D i) (R.βW i) k PP hSt ?_
      by_cases hPe : PP = P
      · subst hPe
        exact hone (hK2 PP hPP) (hK1 PP hPP)
      · intro a b
        rw [GlobalTheory.T.frameMatrix_component_sub_one_eq_zero_off_idempotent D (Wc D i) (R.βW i) f k PP hk (hfoff PP hPP hPe) a b, map_zero]
        exact zero_lt_one
    · exact absurd hPP (Finset.notMem_empty _)
  exact ⟨GlobalTheory.IdemSupport.mem_GfC_of_suppF (Wc D i) hinf hk,
    GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv) _ (GlobalTheory.LevSplit.finE_mem_UA _ k) hSt hred⟩

end GlobalTheory.BadPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaHalfSpaceDatumTranslateDisjointSupportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaHalfSpaceDatum_translate_disjoint_support : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ea : AE D), IsIdemSum ea (R.Pg ∪ R.Q t) → ∀ (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → ∀ x x' : WO (Vc D i) (Wc D i), (∀ a b, f * x a b = f * x' a b) → datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x) ≠ 0 → datP R i t ea x' ≠ 0 → False := by
  first | exact @GlobalTheory.BadPlace.disj_supp | exact GlobalTheory.BadPlace.disj_supp | (intros; apply GlobalTheory.BadPlace.disj_supp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientVanishesOffLevelGroupAtBadPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace

noncomputable section

namespace GlobalTheory.BadPlace


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem actO_one_inv_half {D : D7} {S T : HSp D} {e f : AE D} (hef : e * f = e) {γ : GA D T}
    (hγ : GlobalTheory.RawLift.TrivAt T f γ) {y : WO S T} (hy : IsHalf e y) : actO S T 1 γ⁻¹ y = y := by
  have h1 : f • Formalism.L2.Theta.mt T γ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    ext a b
    have := hγ a b
    rw [Matrix.sub_apply, mul_sub] at this
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    exact sub_eq_zero.1 this
  have h2 : Formalism.L2.Theta.mt T γ * Formalism.L2.Theta.mt T γ⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h3 : f • Formalism.L2.Theta.mt T γ⁻¹ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    calc f • Formalism.L2.Theta.mt T γ⁻¹ = (f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) * Formalism.L2.Theta.mt T γ⁻¹ := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (f • Formalism.L2.Theta.mt T γ) * Formalism.L2.Theta.mt T γ⁻¹ := by rw [h1]
      _ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by rw [Matrix.smul_mul, h2]
  have h4 : e • Formalism.L2.Theta.mt T γ⁻¹ = e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    rw [← hef, ← smul_smul, h3, smul_smul]
  have hy' : e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = y := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hy a b
  have hone : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1 := by
    simp only [inv_one, Formalism.L2.Theta.mt, map_one, Units.val_one]
  unfold actO
  rw [hone, Matrix.mul_one]
  calc HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      = HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by rw [hy']
    _ = HMul.hMul (e • Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = HMul.hMul (e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [h4]
    _ = y := by rw [Matrix.smul_mul, Matrix.one_mul, hy']

theorem pureTensorL_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have e : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  rw [e]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]
  simp [opPow]


set_option maxHeartbeats 2000000 in
theorem coef_bad_vanish : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hC P hP e f hPI γ _ hTr k hk hlev
  obtain ⟨ea, Tm, c, hIS, hSe, hee, hf, hψ, hSV, hSW, hv0, hvl, hTm, hSB2, hSB1, hvP, hωk⟩ :=
    GlobalTheory.T.thetaLiftVector_schroedingerImage_at_levelPrime D G Pl0 T A Ks R F hL hF i t P hP e f hPI k hk
  have hdisj := GlobalTheory.T.thetaHalfSpaceDatum_translate_disjoint_support D G Pl0 T A Ks R F hL hF i t ea hIS P hP e f hPI k hk hlev
  have hW := (hF i t).datum
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [RealDat.ptP, pureTensorO, pureTensorL_one] at this
  have hef : e * f = e := by
    rw [hf, mul_add, hSe.1, hSe.2.1, add_zero]
  have e1 := GlobalTheory.WeilPairing.thetaInner_weilRep D R.ψ _ _ _ _ (R.ωP i t) μ 𝓕 hW hC (1, γ⁻¹)
    (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) (hW.om_pres (1, γ * k) _ hth) hth
  rw [← e1, ← Module.End.mul_apply, ← map_mul]
  have e2 : ((1 : GA D (Vc D i)), γ⁻¹) * (1, γ * k) = (1, k) := by
    ext
    · exact mul_one 1
    · exact (inv_mul_cancel_left γ k)
  rw [e2, hωk, thetaInner_smul_left]
  have hz := GlobalTheory.T.schrodingerImages_orthogonal_disjoint_splitSupport D R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) _ ea e (R.vacP i) Tm μ 𝓕 hψ hSV hSW hIS hSe hee hv0 hvl
    hTm hC _ _ hSB1 hSB2 (fun x x' hxx' h1 h2 => hdisj x x' (by rw [hf]; exact hxx') h1 h2) (R.ωP i t (1, γ⁻¹))
    (fun g hg => hW.om_pres _ _ hg) (fun y hy g hg => by
      rw [hW.om_heis _ _ _ _ hg, actO_one_inv_half hef hTr hy])
  rw [← hvP] at hz
  rw [hz, mul_zero]

end GlobalTheory.BadPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientVanishesOffLevelGroupAtBadPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = 0 := by
  first | exact @GlobalTheory.BadPlace.coef_bad_vanish | exact GlobalTheory.BadPlace.coef_bad_vanish | (intros; apply GlobalTheory.BadPlace.coef_bad_vanish <;> assumption)
end
