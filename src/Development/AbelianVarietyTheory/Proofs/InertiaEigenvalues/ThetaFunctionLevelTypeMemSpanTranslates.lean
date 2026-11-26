module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlacesThetaFunctionFixedVectorShape
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationSplitPlaceOffLevels
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunAtTypePrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalTranslatesSpanPrescribedCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanTranslatesConjugateHalfTwistPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaShapeRelationDropSplitPlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunctionsTwistPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductDatumThetaHasShapeAdjointPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceInvariantFormKillsVanishingSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceInvariantFormKillsVanishingSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef

theorem form_placeModel_eq_zero_of_vanish : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a b : AE D, IsSplitIdem D a → b * b = b → b * cA D b = 0 → infPart D b = 0 → b * a = a → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b (latH S T ΛS ΛT) 1 f₀ Tm → ∀ ℓ, InvForm ψ S T a ℓ → ∀ Ψ : WO S T → ℂ, IsSBHalf b (latH S T ΛS ΛT) Ψ → (∀ t : WO S T, a • t = 0 → Ψ t = 0) → ℓ (Tm Ψ) = 0 := by
  intro D ψ S T hψ ΛS ΛT hS hT a b ha hbb hbc hbinf hba f₀ Tm hf₀ hTm ℓ hℓ Ψ hΨ hΨ0
  have hth : ∀ Ψ', IsSBHalf b (latH S T ΛS ΛT) Ψ' → IsThetaFunO ψ S T (Tm Ψ') := by
    intro Ψ' h'
    have hspan := (GlobalTheory.Chain.StepVac.placeModel_span_ne hψ hS hT hbb hbc hbinf hTm h').1
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
    · rintro _ ⟨u, rfl⟩
      exact GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ u
    · exact Formalism.IndefR.Fock.CCR.theta_zero ψ S T
    · intro x y _ _ hx hy
      exact Formalism.IndefR.Fock.CCR.theta_add hx hy
    · intro c x _ hx
      exact Formalism.IndefR.Fock.CCR.theta_smul hx c
  have hca : cA D b * cA D a = cA D a := by rw [← RingHom.map_mul, hba]
  have hmod : ∀ y, IsHalf (cA D a) y → ℓ (Tm (fun t => ψ (symplO S T t y) * Ψ t)) = ℓ (Tm Ψ) := by
    intro y hy
    have hy' : IsHalf (cA D b) y := fun i j => by rw [← hy i j, ← mul_assoc, hca]
    rw [hTm.modul Ψ hΨ y hy']
    exact hℓ y hy _ (hth Ψ hΨ)
  obtain ⟨k, hk, hinv, hden⟩ := hΨ.2
  have hcomm : ∀ (c : AE D) (x : WO S T), c • (k • x) = k • (c • x) := fun c x =>
    map_nsmul (DistribSMul.toAddMonoidHom (WO S T) c) k x
  have haa : a * a = a := ha.1
  have hainf : infPart D a = 0 := GlobalTheory.SplitScalar.infPart_splitIdem ha
  obtain ⟨Y, hYne, hY1, -, hY3⟩ := GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ ΛS ΛT hS hT a haa hainf k hk
  have hzero : (fun t => ∑ y ∈ Y, ψ (symplO S T t y) * Ψ t) = 0 := by
    funext t
    simp only [Pi.zero_apply]
    by_cases ht : Ψ t = 0
    · simp [ht]
    rw [← Finset.sum_mul]
    have hsym : ∀ y ∈ Y, symplO S T t y = symplO S T (a • t) y := by
      intro y hy
      rw [GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.SplitScalar.isHalf_iff _ _).1 (hY1 y hy).1]
    have hx : IsHalf a (a • t) := (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, haa])
    have hkx : k • (a • t) ∈ latH S T ΛS ΛT := by
      rw [← hcomm a t]
      exact GlobalTheory.SplitScalar.idem_smul_mem haa _ (hden t ht)
    obtain ⟨-, h2⟩ := hY3 (a • t) hx hkx
    by_cases hex : ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ a • t = k • u
    · exfalso
      obtain ⟨u, hu, hau, hxu⟩ := hex
      have hbu : IsHalf b u := fun i j => by rw [← hau i j, ← mul_assoc, hba]
      have e1 : Ψ (t - k • u + k • u) = Ψ (t - k • u) := hinv u hu hbu (t - k • u)
      rw [sub_add_cancel] at e1
      apply ht
      rw [e1]
      apply hΨ0
      rw [smul_sub, hxu, hcomm a u, (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hau, sub_self]
    · rw [Finset.sum_congr rfl fun y hy => by rw [hsym y hy], h2 hex, zero_mul]
  have hsum : ∑ y ∈ Y, ℓ (Tm (fun t => ψ (symplO S T t y) * Ψ t)) =
      ℓ (Tm (fun t => ∑ y ∈ Y, ψ (symplO S T t y) * Ψ t)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum ℓ, ← map_sum Tm]
    congr 2
    funext t
    simp [Finset.sum_apply]
  rw [hzero, map_zero, map_zero, Finset.sum_congr rfl fun y hy => hmod y (hY1 y hy).1, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have hc : (Y.card : ℂ) ≠ 0 := by exact_mod_cast hYne.card_pos.ne'
  exact (mul_eq_zero.1 hsum).resolve_left hc

end GlobalTheory.DownLift.SplitCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceInvariantFormKillsVanishingSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeInvariantForm_kills_vanishing_schwartzBruhat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a b : AE D, IsSplitIdem D a → b * b = b → b * cA D b = 0 → infPart D b = 0 → b * a = a → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b (latH S T ΛS ΛT) 1 f₀ Tm → ∀ ℓ, InvForm ψ S T a ℓ → ∀ Ψ : WO S T → ℂ, IsSBHalf b (latH S T ΛS ΛT) Ψ → (∀ t : WO S T, a • t = 0 → Ψ t = 0) → ℓ (Tm Ψ) = 0 := by
  first | exact @GlobalTheory.DownLift.SplitCoef.form_placeModel_eq_zero_of_vanish | exact GlobalTheory.DownLift.SplitCoef.form_placeModel_eq_zero_of_vanish | (intros; apply GlobalTheory.DownLift.SplitCoef.form_placeModel_eq_zero_of_vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductDatumThetaHasShapeAdjointPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.ProdShape

variable {D : D7}

theorem isSBHalf_sub_smul {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f g : Mx D m n → ℂ}
    (hf : IsSBHalf e Λ f) (hg : IsSBHalf e Λ g) (c : ℂ) : IsSBHalf e Λ (f - c • g) := by
  obtain ⟨f1, k, hk, f2, f3⟩ := hf
  obtain ⟨g1, l, hl, g2, g3⟩ := hg
  have hne : ∀ t, (f - c • g) t ≠ 0 → f t ≠ 0 ∨ g t ≠ 0 := fun t ht => by
    by_contra h
    push_neg at h
    exact ht (by rw [Pi.sub_apply, Pi.smul_apply, h.1, h.2, smul_zero, sub_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (hne t ht).elim (f1 t) (g1 t), k * l, mul_pos hk hl, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have e1 : f (t + (k * l) • u) = f t := by
      rw [mul_smul]; exact f2 _ (nsmul_mem hu l) (hh l u hu') t
    have e2 : g (t + (k * l) • u) = g t := by
      rw [mul_comm, mul_smul]; exact g2 _ (nsmul_mem hu k) (hh k u hu') t
    rw [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact nsmul_mem (f3 t h) l
    · rw [mul_smul]; exact nsmul_mem (g3 t h) k

theorem isHalf_add_iff {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (t : Mx D m n) :
    IsHalf e (t + x) ↔ IsHalf e t := by
  rw [GlobalTheory.SplitScalar.isHalf_iff] at hx
  rw [GlobalTheory.SplitScalar.isHalf_iff, GlobalTheory.SplitScalar.isHalf_iff, smul_add, hx, add_left_inj]

theorem isSBHalf_transl {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f : Mx D m n → ℂ}
    (hf : IsSBHalf e Λ f) {x : Mx D m n} (hx : IsHalf e x) (hx' : ∃ l : ℕ, 0 < l ∧ l • x ∈ Λ) :
    IsSBHalf e Λ fun t => f (t + x) := by
  obtain ⟨f1, k, hk, f2, f3⟩ := hf
  obtain ⟨l, hl, hlx⟩ := hx'
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (isHalf_add_iff hx t).1 (f1 _ ht), k * l, mul_pos hk hl, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · beta_reduce
    rw [add_right_comm, mul_smul]
    exact f2 _ (nsmul_mem hu l) (hh l u hu') _
  · have h1 : (k * l) • (t + x) ∈ Λ := by rw [mul_comm, mul_smul]; exact nsmul_mem (f3 _ ht) l
    have h2 : (k * l) • x ∈ Λ := by rw [mul_smul]; exact nsmul_mem hlx k
    have := sub_mem h1 h2
    rwa [smul_add, add_sub_cancel_right] at this

theorem frMapAdj_conj_smul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (e : AE D) (x : WO S T) :
    frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := by
  have h : (((cA D e • x).map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      toEAf D e • ((x.map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ := Matrix.ext fun i j => by
    change GlobalTheory.AdelicLatMove.cF D (toEAf D (cA D e * x j i)) = toEAf D e * GlobalTheory.AdelicLatMove.cF D (toEAf D (x j i))
    rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.AdelicLatMove.toEAf_cA, GlobalTheory.PlaceVec.cF_cF_toEAf]
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq, h, Matrix.mul_smul, Matrix.smul_mul]

section Red

variable {a b : ℕ} {p : Formalism.IndefR.Datum.EAf D} {M N : Matrix (Fin a) (Fin b) (Formalism.IndefR.Datum.EAf D)}

theorem isIntM_add_iff (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hM : p • M = 0) (hN : p • N = N) :
    IsIntM (M + N) ↔ IsIntM M ∧ IsIntM N := by
  refine ⟨fun h => ?_, fun h i j => add_mem (h.1 i j) (h.2 i j)⟩
  have h1 : p • (M + N) = N := by rw [smul_add, hM, hN, zero_add]
  have h2 : IsIntM N := fun i j => by
    rw [← h1]
    exact mul_mem hp (h i j)
  exact ⟨fun i j => (add_mem_cancel_right (h2 i j)).1 (h i j), h2⟩

theorem redM_add (PP : Pl D.host.E) (hM : IsIntM M) (hN : IsIntM N) : redM PP (M + N) = redM PP M + redM PP N := by
  funext i j
  have h2 : (M + N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := add_mem (hM i j) (hN i j)
  rw [Matrix.add_apply]
  unfold redM
  rw [dite_eq_left h2, dite_eq_left (hM i j), dite_eq_left (hN i j), ← RingHom.map_add (f := _)]
  rfl

theorem redM_smul (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hM : IsIntM M) :
    redM PP (p • M) = resS D.host.F PP ⟨p, hp⟩ • redM PP M := by
  funext i j
  have h2 : (p • M) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem hp (hM i j)
  rw [Matrix.smul_apply, smul_eq_mul]
  unfold redM
  rw [dite_eq_left h2, dite_eq_left (hM i j), ← RingHom.map_mul]
  rfl

theorem redM_add_of_one (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1 : resS D.host.F PP ⟨p, hp⟩ = 1) (hM : p • M = 0) (hN : p • N = N) (iM : IsIntM M) (iN : IsIntM N) :
    redM PP (M + N) = redM PP N := by
  have h := redM_smul PP hp ((isIntM_add_iff hp hM hN).2 ⟨iM, iN⟩)
  rw [h1, one_smul, smul_add, hM, hN, zero_add] at h
  exact h.symm

theorem redM_add_of_zero (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h0 : resS D.host.F PP ⟨p, hp⟩ = 0) (hN : p • N = N) (iM : IsIntM M) (iN : IsIntM N) :
    redM PP (M + N) = redM PP M := by
  have h := redM_smul PP hp iN
  rw [h0, zero_smul, hN] at h
  rw [redM_add PP iM iN, h, add_zero]

end Red

theorem hasShape_adjDat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (P : Finset (Pl D.host.E)) (e e₀ : AE D) (PP : Pl D.host.E), IsIdemSum e P → PP ∈ P → Formalism.L2.NTheta.IsIdemAt e₀ PP → ∀ ω₁ ω₂ : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ, (∀ y y', y PP = y' PP → ω₁ y = ω₁ y') → (∀ y y', (∀ PP' ∈ P, PP' ≠ PP → y PP' = y' PP') → ω₂ y = ω₂ y') → ∀ f₀ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latH S T ΛS ΛT) 1 f₀ (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) f → HasShape ψ S T (cA D e₀) (adjDat S T βS βT e₀ ω₁) f := by
  intro D ψ S T hψ ΛS ΛT hS hT βS βT P e e₀ PP he hPP he₀ ω₁ ω₂ h₁ h₂ f₀ f hf₀ hf ℓ hℓ
  classical
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hfT : f = Tm (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) := hall Tm hTm
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hec : cA D e * cA D (cA D e) = 0 := by rw [← RingHom.map_mul, he.2, RingHom.map_zero]
  have hee₀ : cA D e * cA D e₀ = cA D e₀ := by rw [← RingHom.map_mul, GlobalTheory.DiagLiftFix.idemSum_mul he hPP he₀]
  have hSB : ∀ ω : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ,
      (∀ y y', (∀ PP ∈ P, y PP = y' PP) → ω y = ω y') →
      IsSBHalf (cA D e) (latH S T ΛS ΛT) (adjDat S T βS βT e ω) := fun ω hω =>
    GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS)
      (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
      (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) P ω hω
  have s12 := hSB (fun y => ω₁ y * ω₂ y) fun y y' h => by
    rw [h₁ y y' (h PP hPP), h₂ y y' fun Q hQ _ => h Q hQ]
  have s2 := hSB ω₂ fun y y' h => h₂ y y' fun Q hQ _ => h Q hQ
  refine ⟨ℓ (Tm (adjDat S T βS βT e ω₂)), fun x hx => ?_⟩
  have hxs : cA D e₀ • x = x := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx
  have hx' : IsHalf (cA D e) x := by
    rw [GlobalTheory.SplitScalar.isHalf_iff, ← hxs, smul_smul, hee₀]
  have st := isSBHalf_transl s12 hx' (GlobalTheory.PlaceVec.exists_nsmul_mem_latO
    (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS) (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) x
    (GlobalTheory.PlaceVec.half_infPart hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx')))
  obtain ⟨hp, hp1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e₀ PP he₀
  have hN : toEAf D e₀ • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
    rw [← frMapAdj_conj_smul, hxs]
  have key := GlobalTheory.T.placeInvariantForm_kills_vanishing_schwartzBruhat D ψ S T hψ ΛS ΛT hS hT (cA D e₀) (cA D e) (GlobalTheory.SplitScalar.isSplitIdem_conj he₀.1)
    hee hec hinf hee₀ f₀ Tm hf₀ hTm ℓ hℓ _ (isSBHalf_sub_smul st s2 (adjDat S T βS βT e₀ ω₁ x)) fun t ht => by
      have hz : frMapAdj S T βS βT 0 = 0 :=
        (AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_zero
      have hM : toEAf D e₀ • frMapAdj S T βS βT t = 0 := by
        rw [← frMapAdj_conj_smul, ht, hz]
      have hI := isIntM_add_iff hp hM hN
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      unfold adjDat
      rw [GlobalTheory.PlaceVec.frMapAdj_add]
      by_cases c1 : IsIntM (frMapAdj S T βS βT x)
      · by_cases c2 : IsHalf (cA D e) t ∧ IsIntM (frMapAdj S T βS βT t)
        · rw [if_pos ⟨(isHalf_add_iff hx' t).2 c2.1, hI.2 ⟨c2.2, c1⟩⟩, if_pos ⟨hx, c1⟩, if_pos c2]
          beta_reduce
          rw [h₁ _ (fun Q => redM Q (frMapAdj S T βS βT x)) (redM_add_of_one PP hp hp1 hM hN c2.2 c1),
            h₂ _ (fun Q => redM Q (frMapAdj S T βS βT t)) fun Q _ hQ =>
              redM_add_of_zero Q hp (GlobalTheory.TameProd.resS_idem_eq_zero he₀ hQ.symm hp) hN c2.2 c1]
        · rw [if_neg c2, if_neg fun h => c2 ⟨(isHalf_add_iff hx' t).1 h.1, (hI.1 h.2).1⟩, mul_zero]
      · rw [if_neg fun h => c1 (hI.1 h.2).2, if_neg fun h => c1 h.2, zero_mul]
  rw [map_sub, map_smul, hTm.trans _ s12 x hx', ← hfT, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at key
  rw [key, mul_comm]

end GlobalTheory.DownLift.ProdShape

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductDatumThetaHasShapeAdjointPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productDatumTheta_hasShape_adjoint_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (P : Finset (Pl D.host.E)) (e e₀ : AE D) (PP : Pl D.host.E), IsIdemSum e P → PP ∈ P → Formalism.L2.NTheta.IsIdemAt e₀ PP → ∀ ω₁ ω₂ : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ, (∀ y y', y PP = y' PP → ω₁ y = ω₁ y') → (∀ y y', (∀ PP' ∈ P, PP' ≠ PP → y PP' = y' PP') → ω₂ y = ω₂ y') → ∀ f₀ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latH S T ΛS ΛT) 1 f₀ (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) f → HasShape ψ S T (cA D e₀) (adjDat S T βS βT e₀ ω₁) f := by
  first | exact @GlobalTheory.DownLift.ProdShape.hasShape_adjDat | exact GlobalTheory.DownLift.ProdShape.hasShape_adjDat | (intros; apply GlobalTheory.DownLift.ProdShape.hasShape_adjDat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeisenbergSpanPreservesTypeRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeisenbergSpanPreservesTypeRelations
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.PlaceTranslate

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by simp [Formalism.L2.Theta.mt]

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mul_mt_eq {S T : HSp D} {e : AE D} {g : GA D S} (hg : ∀ i j, e * (mt S g - 1) i j = 0) {u : WO S T}
    (hu : IsHalf e u) : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g) = u := by
  have hM : ∀ k j, e * mt S g k j = e * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by
    intro k j
    have h := hg k j
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero] at h
    exact h
  ext i j
  rw [Matrix.mul_apply]
  conv_rhs => rw [← Matrix.mul_one (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc u i k * mt S g k j = (e * u i k) * mt S g k j := by rw [hu i k]
    _ = u i k * (e * mt S g k j) := by ring
    _ = u i k * (e * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j) := by rw [hM k j]
    _ = (e * u i k) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by ring
    _ = u i k * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by rw [hu i k]

theorem actO_fix {S T : HSp D} {e : AE D} {g : GA D S} (hg : ∀ i j, e * (mt S g - 1) i j = 0) {u : WO S T}
    (hu : IsHalf e u) : actO S T g 1 u = u ∧ actO S T g⁻¹ 1 u = u := by
  have h1 := mul_mt_eq (T := T) hg hu
  have h2 : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) = u := by
    conv_lhs => rw [← h1]
    rw [Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · simp only [actO, mt_one', Matrix.one_mul]; exact h2
  · simp only [actO, mt_one', Matrix.one_mul, inv_inv]; exact h1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem avgW_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (f g : WO (Vc D i) (Wc D i) → ℂ) :
    avgW R i t PP a tr ε κ (f + g) = avgW R i t PP a tr ε κ f + avgW R i t PP a tr ε κ g := by
  simp only [avgW, map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem avgW_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (c : ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) :
    avgW R i t PP a tr ε κ (c • f) = c • avgW R i t PP a tr ε κ f := by
  simp only [avgW, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => smul_comm _ _ _

theorem avgW_zero (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) : avgW R i t PP a tr ε κ 0 = 0 := by
  simp only [avgW, map_zero, smul_zero, Finset.sum_const_zero]

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D) (u : WO S T') : heisO ψ S T' u 0 = 0 := by
  funext w; simp [heisO]

theorem locSpan_pres : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP →
    ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)),
    v ∈ Sb → ∀ (ε : AF D.host.F) (a : AE D), IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε →
    ∀ f : WO (Vc D i) (Wc D i) → ℂ, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f →
    ∀ f' ∈ locSpan R.ψ (Vc D i) (Wc D i) a f,
      TypeIn R i t (dropPl Sb v) f' ∧ CleanIn R i t (dropPl Sb v) f' ∧ LikeOff R i t Sb f' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv ε a hε hae f hT hC hL f' hf'
  set E' := algebraMap (AF D.host.F) (AE D) ε with hE'
  have hW := hω i t
  have hψ := hW.std
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := hT.1
  have hvd : v ∉ dropPl Sb v := by
    classical
    unfold dropPl
    simp
  have hsub : ∀ w, w ∈ dropPl Sb v → w ∈ Sb := by
    classical
    intro w hw
    unfold dropPl at hw
    exact Finset.mem_of_mem_erase hw

  have hsupp : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ →
      SuppIn Sb (Vc D i) κ ∧ ∀ i' j', E' * (mt (Vc D i) κ - 1) i' j' = 0 := by
    intro κ hκ
    exact ⟨⟨hκ.1, fun w hw => hκ.2 w fun h => hw (hsub w h)⟩, hκ.2 v hvd ε hε⟩
  have hcE : cA D E' = E' := by
    rw [← hae, map_add (f := _), GlobalTheory.DualPairCheck.cA_cA, add_comm]

  let P : (WO (Vc D i) (Wc D i) → ℂ) → Prop := fun φ =>
    TypeIn R i t (dropPl Sb v) φ ∧ CleanIn R i t (dropPl Sb v) φ ∧ LikeOff R i t Sb φ
  have hgen : ∀ u : WO (Vc D i) (Wc D i), IsHalf E' u → P (heisO R.ψ (Vc D i) (Wc D i) u f) := by
    intro u hu
    have hthu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hth u
    refine ⟨⟨hthu, fun κ hκ hκs => ?_⟩, ?_, ⟨hthu, ?_⟩⟩
    · obtain ⟨hκS, hκv⟩ := hsupp κ hκs
      rw [hW.om_heis κ 1 u f hth, (actO_fix hκv hu).1, hT.2 κ hκ hκS, GlobalTheory.SplitScalar.heisO_smul]
    · intro PP a' ha' tr e he hex κ hκ hκs
      have hex' : ∃ w ∈ Sb, Over PP.1 w := by
        obtain ⟨w, hw, hO⟩ := hex; exact ⟨w, hsub w hw, hO⟩
      have hκs' : ∀ g, mirC R i PP a' tr e g ≠ 0 → SuppIn Sb (Vc D i) (κ g) := fun g hg => (hsupp _ (hκs g hg)).1
      have key : avgW R i t PP a' tr e κ (heisO R.ψ (Vc D i) (Wc D i) u f) =
          heisO R.ψ (Vc D i) (Wc D i) u (avgW R i t PP a' tr e κ f) := by
        simp only [avgW]
        rw [GlobalTheory.SplitScalar.heisO_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        by_cases hc : mirC R i PP a' tr e g = 0
        · rw [hc, zero_mul, zero_smul, zero_smul, heisO_zero']
        · rw [hW.om_heis (κ g)⁻¹ 1 u f hth, (actO_fix (hsupp _ (hκs g hc)).2 hu).2, GlobalTheory.SplitScalar.heisO_smul]
      rw [key, hC PP a' ha' tr e he hex' κ hκ hκs', heisO_zero']
    · intro c hc h0
      have hcomm : ∀ w ∈ c.support, heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f) =
          heisO R.ψ (Vc D i) (Wc D i) u (heisO R.ψ (Vc D i) (Wc D i) w f) := by
        intro w hw
        have hw0 : E' • w = 0 := by
          ext i' j'; exact (hc w hw).2 v hv ε hε i' j'
        have hs : symplO (Vc D i) (Wc D i) w u = 0 := by
          have hu' : E' • u = u := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hu
          rw [← hu', ← hcE, ← GlobalTheory.SplitScalar.symplO_smul, hw0, GlobalTheory.SplitScalar.symplO_zero_left]
        rw [GlobalTheory.SplitScalar.heisO_comm, hs, AddChar.map_zero_eq_one, one_smul]
      have e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f)) =
          heisO R.ψ (Vc D i) (Wc D i) u (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w f) := by
        unfold Finsupp.sum
        rw [GlobalTheory.SplitScalar.heisO_sum]
        refine Finset.sum_congr rfl fun w hw => ?_
        dsimp only
        rw [hcomm w hw, GlobalTheory.SplitScalar.heisO_smul]
      rw [e1, hL.2 c hc h0, heisO_zero']
  have h0 : P 0 := by
    have hz : IsThetaFunO R.ψ (Vc D i) (Wc D i) 0 := by simpa using theta_smul (0 : ℂ) hth
    refine ⟨⟨hz, fun κ _ _ => by rw [map_zero, smul_zero]⟩, fun _ _ _ _ _ _ _ _ _ _ => avgW_zero _ _ _ _ _ _ _ _,
      ⟨hz, fun c _ _ => ?_⟩⟩
    simp [heisO_zero']
  have hadd : ∀ φ₁ φ₂, P φ₁ → P φ₂ → P (φ₁ + φ₂) := by
    rintro φ₁ φ₂ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩ ⟨⟨t2, T2⟩, C2, ⟨l2, L2⟩⟩
    refine ⟨⟨theta_add t1 t2, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_,
      ⟨theta_add l1 l2, fun c hc h0 => ?_⟩⟩
    · rw [map_add (f := _), T1 κ hκ hκs, T2 κ hκ hκs, smul_add]
    · rw [avgW_add, C1 PP a' ha' tr e he hex κ hκ hκs, C2 PP a' ha' tr e he hex κ hκ hκs, add_zero]
    · simp only [heisO_add', smul_add]
      rw [Finsupp.sum_add, L1 c hc h0, L2 c hc h0, add_zero]
  have hsmul : ∀ (r : ℂ) φ, P φ → P (r • φ) := by
    rintro r φ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩
    refine ⟨⟨theta_smul r t1, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_,
      ⟨theta_smul r l1, fun c hc h0 => ?_⟩⟩
    · rw [map_smul, T1 κ hκ hκs, smul_comm]
    · rw [avgW_smul, C1 PP a' ha' tr e he hex κ hκ hκs, smul_zero]
    · have e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (r • φ)) =
          r • (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w φ) := by
        rw [Finsupp.smul_sum]
        refine Finsupp.sum_congr fun w _ => ?_
        rw [GlobalTheory.SplitScalar.heisO_smul, smul_comm]
      rw [e1, L1 c hc h0, smul_zero]
  refine Submodule.span_induction (p := fun φ _ => P φ) ?_ h0 (fun x y _ _ hx hy => hadd x y hx hy)
    (fun r x _ hx => hsmul r x hx) hf'
  rintro φ ⟨u, hu, rfl⟩
  rw [hae] at hu
  exact hgen u hu

end GlobalTheory.DownLift.PlaceTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeisenbergSpanPreservesTypeRelationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localHeisenbergSpan_preserves_type_relations : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → ∀ (ε : AF D.host.F) (a : AE D), IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε → ∀ f : WO (Vc D i) (Wc D i) → ℂ, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → ∀ f' ∈ locSpan R.ψ (Vc D i) (Wc D i) a f, TypeIn R i t (dropPl Sb v) f' ∧ CleanIn R i t (dropPl Sb v) f' ∧ LikeOff R i t Sb f' := by
  first | exact @GlobalTheory.DownLift.PlaceTranslate.locSpan_pres | exact GlobalTheory.DownLift.PlaceTranslate.locSpan_pres | (intros; apply GlobalTheory.DownLift.PlaceTranslate.locSpan_pres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunctionsTwistPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.GenTwist

section Generic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem suppAt_conj {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]
  exact h i j

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  have : mt V (1 : GA D V) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one]; rfl
  rw [this, sub_self, Matrix.zero_apply, mul_zero]

theorem suppAt_inv {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt e V g⁻¹ := by
  intro i j
  have := congrFun (congrFun (GlobalTheory.SplitScalar.off_smul_mt_inv h) i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  rw [Matrix.sub_apply]
  linear_combination -this

theorem om_form {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D} (ha : IsSplitIdem D a) {g : GA D S} {h : GA D T}
    (hg : SuppAt a S g) (hh : SuppAt a T h) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ℓ, InvForm ψ S T a ℓ → ∀ f, IsThetaFunO ψ S T f → ∀ x,
      ℓ (heisO ψ S T (actO S T g h x) (om (g, h) f)) = s * ℓ (heisO ψ S T x f) := by
  obtain ⟨r, hr, H⟩ := hW.om_split a ha g h hg hh _ _ (GlobalTheory.VecInv.isDetAt_detAt a ha.1 S g)
    (GlobalTheory.VecInv.isDetAt_detAt a ha.1 T h)
  refine ⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 hr.ne') (Circle.coe_ne_zero (splitFacO χS χT
    (GlobalTheory.VecInv.detAt a ha.1 S g) (GlobalTheory.VecInv.detAt a ha.1 T h))), fun ℓ hℓ f hf x => ?_⟩
  rw [← hW.om_heis g h x f hf]
  exact H ℓ (fun u hu f hf => hℓ u hu f hf) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf x)

theorem cross_law {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D} (ha : IsSplitIdem D a) {κ : GA D S} (hκ : SuppAt a S κ)
    {f w Φ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hw : IsThetaFunO ψ S T w) (hw0 : w ≠ 0)
    (hs : HasShape ψ S T a Φ w) {c : ℂ} (hc : c ≠ 0) (ef : om (κ, 1) f = c • f) (ew : om (κ, 1) w = c • w)
    {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T a ℓ) {x x' : WO S T} (hx : IsHalf a x) (hx' : IsHalf a x') :
    coef ψ S T a ℓ f (actO S T κ 1 x) * Φ x' = coef ψ S T a ℓ f x * Φ (actO S T κ 1 x') := by
  obtain ⟨s, hs0, H⟩ := om_form hW ha hκ (suppAt_one a T)
  have hne : ¬ ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x w) = 0 := fun h =>
    hw0 (GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions D ψ S T hW.std a ha w hw h)
  push Not at hne
  obtain ⟨ℓ₀, hℓ₀, x₀, hx₀, hne⟩ := hne
  obtain ⟨c₀, hc₀⟩ := hs ℓ₀ hℓ₀
  have hc0 : c₀ ≠ 0 := by
    rintro rfl
    exact hne (by rw [hc₀ x₀ hx₀, zero_mul])
  have e1 := H ℓ hℓ f hf x
  have e2 := H ℓ₀ hℓ₀ w hw x'
  rw [ef, GlobalTheory.SplitScalar.heisO_smul, map_smul, smul_eq_mul] at e1
  rw [ew, GlobalTheory.SplitScalar.heisO_smul, map_smul, smul_eq_mul, hc₀ _ (GlobalTheory.SplitHecke.isHalf_actO κ 1 hx'), hc₀ _ hx'] at e2
  unfold coef
  rw [if_pos (GlobalTheory.SplitHecke.isHalf_actO κ 1 hx), if_pos hx]
  have e3 : c * Φ (actO S T κ 1 x') = s * Φ x' := mul_left_cancel₀ hc0 (by linear_combination e2)
  apply mul_left_cancel₀ hc
  linear_combination (Φ x') * e1 - (ℓ (heisO ψ S T x f)) * e3

open Classical in
theorem omegaQ_split {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    {PP : Pl D.host.E} (hP : PP ∈ Q) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ Q r ξ k y = omegaQ {PP} r ξ k y * omegaQ (Q.erase PP) r ξ k y := by
  let F : Pl D.host.E → ℂ := fun P => if h : IsUnit (topL r (y P)).det then ((ξ P h.unit : ℂˣ) : ℂ) ^ k else 0
  have key : ∀ Q' : Finset (Pl D.host.E), omegaQ Q' r ξ k y =
      if ∀ P ∈ Q', LowZero r (y P) ∧ IsUnit (topL r (y P)).det then ∏ P ∈ Q', F P else 0 := by
    intro Q'
    unfold omegaQ
    split_ifs with h
    · rw [← Finset.prod_attach Q' F]
      refine Finset.prod_congr rfl fun P _ => ?_
      simp only [F]
      rw [dite_eq_left (h P.1 P.2).2]
    · rfl
  rw [key, key, key]
  by_cases h : ∀ P ∈ Q, LowZero r (y P) ∧ IsUnit (topL r (y P)).det
  · rw [if_pos h, if_pos (fun P hP' => h P (by rw [Finset.mem_singleton.1 hP']; exact hP)),
      if_pos (fun P hP' => h P (Finset.mem_of_mem_erase hP')), Finset.prod_singleton, Finset.mul_prod_erase Q F hP]
  · rw [if_neg h]
    by_cases h1 : ∀ P ∈ ({PP} : Finset (Pl D.host.E)), LowZero r (y P) ∧ IsUnit (topL r (y P)).det
    · rw [if_pos h1, if_neg (fun h2 => h fun P hP' => by
        by_cases e : P = PP
        · exact h1 P (Finset.mem_singleton.2 e)
        · exact h2 P (Finset.mem_erase.2 ⟨e, hP'⟩)), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem idem_over {e : AE D} {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (hv : Over PP v) :
    ∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨v', hv'⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff e).1 he.1
  obtain ⟨PP', h1, h2⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v' e hv'
  obtain rfl : PP' = PP := GlobalTheory.PlaceVec.isIdemAt_inj h1 he
  obtain rfl : v' = v := HeightOneSpectrum.ext (h2.symm.trans hv)
  exact ⟨_, ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ v' 1,
    fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ v' _ hw⟩, hv'.2.2⟩

end Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem step_of_shape (R : RealDat D A Ks) (hW : R.thP_ωP) (i : Fin D.R.m) (t : T)
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ Sb)
    {ε : AF D.host.F} {a : AE D} (ha : IsSplitIdem D a) (hε : IsPlaceIdem D v ε)
    (hae : a + cA D a = algebraMap (AF D.host.F) (AE D) ε)
    {ΛS : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)} (dS : IsSelfDualC (Vc D i) ΛS)
    (dT : IsSelfDualC (Wc D i) ΛT) (hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t))
    {Φ f : WO (Vc D i) (Wc D i) → ℂ} (hΦ : IsSBHalf a (latH (Vc D i) (Wc D i) ΛS ΛT) Φ)
    (hs : HasShape R.ψ (Vc D i) (Wc D i) a Φ (R.vP i t)) (hT : TypeIn R i t Sb f) (hC : CleanIn R i t Sb f)
    (hL : LikeOff R i t Sb f)
    (hsp : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) a ℓ →
      coef R.ψ (Vc D i) (Wc D i) a ℓ f ∈ Submodule.span ℂ (translT (Vc D i) (Wc D i) a Φ)) :
    f ∈ Submodule.span ℂ (StepGen R i t (dropPl Sb v)) := by
  have hψ := (hW i t).std
  refine GlobalTheory.T.thetaFunction_mem_span_of_coefficientSpan D R.ψ _ _ hψ a ha f hT.1 _ _ ?_ ?_ hsp
  · rintro _ ⟨g, f', h1, -, -, rfl⟩
    exact (hW i t).om_pres _ _ h1.1
  · rintro _ ⟨g, hg, rfl⟩ x₁ hx₁
    obtain ⟨f', hf', H⟩ := GlobalTheory.T.exists_localTranslatesSpan_prescribedCoefficient D R.ψ _ _ hψ ΛS ΛT dS dT a ha f hT.1 Φ hΦ x₁ hx₁
    obtain ⟨p1, p2, p3⟩ := GlobalTheory.T.localHeisenbergSpan_preserves_type_relations D G Pl0 T A Ks R hW i t Sb v hv ε a hε hae f hT hC hL f' hf'
    have p4 := GlobalTheory.T.thetaShapeRelation_drop_splitPlace D G Pl0 T A Ks R hψ i t Sb v ε a ha hε hae hth Φ f' hs
      (fun ℓ hℓ => ⟨_, fun x hx => (H ℓ hℓ x hx).trans (mul_comm _ _)⟩) p3
    have hg' : SuppAt a (Wc D i) g⁻¹ := suppAt_inv hg
    obtain ⟨s, hs0, E⟩ := om_form (hW i t) ha (suppAt_one a (Vc D i)) hg'
    refine ⟨s⁻¹ • R.ωP i t (1, g⁻¹) f', Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, f', p1, p2, p4, rfl⟩),
      fun ℓ hℓ x hx => ?_⟩
    have e := E ℓ hℓ f' p1.1 (actO _ _ 1 g x)
    have e' := GlobalTheory.SplitHecke.actO_inv_actO (S := Vc D i) (T := Wc D i) 1 g x
    rw [inv_one] at e'
    rw [e', H ℓ hℓ _ (GlobalTheory.SplitHecke.isHalf_actO 1 g hx)] at e
    rw [GlobalTheory.SplitScalar.heisO_smul, map_smul, smul_eq_mul, e, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

theorem law_vP (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hW : R.thP_ωP) (hv : R.thP_vP) (i : Fin D.R.m) (t : T)
    {κ : GA D (Vc D i)} (hκ : κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) :
    R.ωP i t (κ, 1) (R.vP i t) = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • R.vP i t := by
  have h1 : (1 : GA D (Wc D i)) ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) := one_mem _
  have h := GlobalTheory.VecInv.omega_lifts_vP R hL (hv i t).1.2.inf hW hv i t 1 κ 1
    ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩ ⟨h1.1, h1.2.1, Subgroup.mem_bot.1 h1.2.2⟩
  have h2 := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.datVt i t).P (finE (Vc D i) κ)
  have h3 : Formalism.L2.DIV.ext1 (R.datVt i t).P.H (R.datVt i t).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ)) = 1 := by
    unfold Formalism.L2.DIV.ext1; split_ifs with hm
    · have : (⟨_, hm⟩ : (R.datVt i t).P.H) = 1 := Subtype.ext (Subgroup.mem_bot.1 hm)
      rw [this, map_one]
    · rfl
  rw [h3, one_mul] at h2
  rw [h]
  unfold levChi
  exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t) h2.symm

theorem suppIn_of_suppAt {V : HSp D} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ Sb) {ε : AF D.host.F} {e : AE D} (he : IsSplitIdem D e)
    (hε : IsPlaceIdem D v ε) (hae : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {κ : GA D V} (hκ : SuppAt e V κ) :
    SuppIn Sb V κ := by
  refine ⟨Matrix.ext fun i j => ?_, fun w hw ε' hε' i j => ?_⟩
  · rw [Matrix.map_apply, ← hκ i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul, Matrix.zero_apply]
  · rw [← hκ i j, hae, ← mul_assoc, ← RingHom.map_mul,
      GlobalTheory.PlaceDatum.placeIdem_mul hε' hε (fun h => hw (h ▸ hv)), RingHom.map_zero, zero_mul]

theorem step_twist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∀ PP ∈ R.Pg, ¬ GlobalTheory.DownLift.GenFinite.Over PP v) → (∃ PP ∈ R.Q t, GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t Sb v hv hPg ⟨PP, hPP, hov⟩ f hT hC hL
  classical
  have hc := hG.core
  have hW := hc.thP.ωP
  have hψ := (hW i t).std
  have dS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hc.lev.βV i)
  have dT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hc.lev.βW i)
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : (Wc D i).rank ≤ (Vc D i).rank := rW.trans_le (r_le_V i)
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hc.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hv0 : R.vP i t ≠ 0 := GlobalTheory.AdTh.VecNe.thPVec_ne_zero dS dT hr (hc.thP.vP i t)
  obtain ⟨hvac, e, he', hΘ⟩ := hc.thP.vP i t
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ R.Pg ∨ PP ∈ R.Q t :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have hPP' : PP ∈ P := (hP PP).2 (Or.inr hPP)
  obtain ⟨es, hes, -⟩ := he.1
  have h0 := hes PP hPP'
  obtain ⟨ε, hε, hae⟩ := idem_over h0 hov
  have ha := GlobalTheory.SplitScalar.isSplitIdem_conj h0.1
  have hae' : cA D (es PP) + cA D (cA D (es PP)) = algebraMap (AF D.host.F) (AE D) ε := by
    rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, hae]
  have hne : ∀ PP' ∈ R.Pg, PP' ≠ PP := fun PP' h h' => hPg PP' h (h' ▸ hov)
  have hs : HasShape R.ψ (Vc D i) (Wc D i) (cA D (es PP))
      (adjDat (Vc D i) (Wc D i) (R.βV i) (R.βW i) (es PP) (omegaQ {PP} (Wc D i).rank (R.xiR t) (-1))) (R.vP i t) := by
    refine GlobalTheory.T.productDatumTheta_hasShape_adjoint_place D R.ψ _ _ hψ _ _ dS dT (R.βV i) (R.βW i) P e (es PP) PP he hPP' h0 _
      (fun y => omegaK R.Pg y * omegaQ ((R.Q t).erase PP) (Wc D i).rank (R.xiR t) (-1) y)
      (fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun P' hP' => by rw [Finset.mem_singleton.1 hP']; exact h)
      (fun y y' h => ?_) (R.vacP i) _ hvac.2.theta ?_
    · rw [GlobalTheory.PlaceVec.omegaK_congr R.Pg fun P' hP' => h P' ((hP P').2 (Or.inl hP')) (hne P' hP'),
        GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun P' hP' =>
          h P' ((hP P').2 (Or.inr (Finset.mem_of_mem_erase hP'))) (Finset.ne_of_mem_erase hP')]
    · convert hΘ using 1
      funext x
      unfold adjDat
      congr 1
      rw [omegaQ_split (R.Q t) _ _ _ hPP, mul_left_comm]
  have hΦ : IsSBHalf (cA D (es PP)) (latH (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i))
      (adjDat (Vc D i) (Wc D i) (R.βV i) (R.βW i) (es PP) (omegaQ {PP} (Wc D i).rank (R.xiR t) (-1))) :=
    GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ dS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ dT) (GlobalTheory.SplitScalar.infPart_splitIdem ha) _
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) {PP} _
      fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  refine step_of_shape R hW i t hv ha hε hae' dS dT hth hΦ hs hT hC hL fun ℓ hℓ => ?_
  obtain ⟨c, hB⟩ := hc.lev.βV i
  refine GlobalTheory.T.mem_span_translates_conjugateHalf_twistPlace D _ _ (R.βV i) (R.βW i) hr _ _ _ hB
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ dS | exact dS.1)
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ dT | exact dT.1) (es PP) PP h0 (R.xiR t)
    (GlobalTheory.ChainTw.RModel.xiR_ne R hc.lev t PP hPP) _
    ((GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split D R.ψ _ _ hψ _ _ dS dT _ ha f hT.1).2.1 ℓ hℓ) fun κ k1 k2 k3 k4 _ x x' hx hx' => ?_
  have k5 : ∀ P' ∈ P, P' ≠ PP → redFn (R.βV i) P' (finE (Vc D i) κ) = 1 := fun P' h h' =>
    GlobalTheory.DiagLiftFix.redFn_eq_one_of_ne he hPP' h0 k1 k3 h h'.symm
  have hκ : κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := by
    refine ⟨k2, ⟨⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, k3⟩, ?_⟩, ?_⟩, ?_⟩
    · refine Subgroup.mem_iInf.2 fun P' => Subgroup.mem_iInf.2 fun h => mem_parah.2 ⟨k3, ?_⟩
      rw [k5 P' ((hP P').2 (Or.inl h)) (hne P' h)]
      exact one_mem _
    · refine Subgroup.mem_iInf.2 fun P' => Subgroup.mem_iInf.2 fun h => mem_parah.2 ⟨k3, ?_⟩
      by_cases h' : P' = PP
      · rw [h']
        rw [rW] at k4
        exact k4
      · rw [k5 P' ((hP P').2 (Or.inr h)) h']
        exact one_mem _
    · refine Subgroup.mem_bot.2 (funext fun P' => ?_)
      show upperLeftBlock _ (redFn (R.βV i) P'.1 (finE (Vc D i) κ)) = 1
      rw [k5 P'.1 ((hP P').2 (Or.inl P'.2)) (hne P'.1 P'.2)]
      exact blockDiagonalExtendByOnePrimeField_one _ _
  exact cross_law (hW i t) ha (suppAt_conj k1) hT.1 hth hv0 hs (inv_ne_zero (levChi_ne_zero _ κ))
    (hT.2 κ hκ (suppIn_of_suppAt hv h0.1 hε hae k1)) (law_vP R hc.lev hW hc.thP.vP i t hκ) hℓ hx hx'

end GlobalTheory.DownLift.GenTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunctionsTwistPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localGeneration_thetaFunctions_twistPlace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∀ PP ∈ R.Pg, ¬ GlobalTheory.DownLift.GenFinite.Over PP v) → (∃ PP ∈ R.Q t, GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  first | exact @GlobalTheory.DownLift.GenTwist.step_twist | exact GlobalTheory.DownLift.GenTwist.step_twist | (intros; apply GlobalTheory.DownLift.GenTwist.step_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelTypeMemSpanTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section
namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem transl_mem_span_gen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i))
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : φ ∈ Submodule.span ℂ (Gen R i t)) :
    R.ωP i t (1, g) φ ∈ Submodule.span ℂ (Gen R i t) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', f', hf', rfl⟩ := hx
    refine Submodule.subset_span ⟨g * g', f', hf', ?_⟩
    have hm : ((1, g) : GA D (Vc D i) × GA D (Wc D i)) * (1, g') = (1, g * g') := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [← hm, map_mul, Module.End.mul_apply]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem finLike_of_likeOff_empty (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : LikeOff R i t ∅ f) : FinLike R i t f :=
  ⟨hf.1, fun c hc h0 => hf.2 c (fun u hu => ⟨hc u hu, fun v hv => absurd hv (Finset.notMem_empty v)⟩) h0⟩

theorem mem_span_gen_of_step (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (hst : ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb →
      ∀ f, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → f ∈ Submodule.span ℂ (StepGen R i t (dropPl Sb v)))
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ f, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → f ∈ Submodule.span ℂ (Gen R i t) := by
  classical
  induction Sb using Finset.induction_on with
  | empty =>
    intro f _ _ hL
    refine Submodule.subset_span ⟨1, f, finLike_of_likeOff_empty R i t hL, ?_⟩
    have h1 : ((1, 1) : GA D (Vc D i) × GA D (Wc D i)) = 1 := rfl
    rw [h1, map_one, Module.End.one_apply]
  | insert v s hv ih =>
    intro f hT hC hL
    have h := hst (insert v s) v (Finset.mem_insert_self v s) f hT hC hL
    rw [dropPl_insert hv] at h
    refine (Submodule.span_le.2 ?_) h
    rintro φ ⟨g, f', hT', hC', hL', rfl⟩
    exact transl_mem_span_gen R i t g (ih f' hT' hC' hL')

end GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

theorem gen_of_type_clean : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → GlobalTheory.DownLift.GenFinite.Clean R i t f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.Gen R i t) := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t f hT hC
  obtain ⟨Sb, hL⟩ := GlobalTheory.T.exists_places_thetaFunction_fixedVectorShape D G Pl0 T A Ks R F hG hP i t f hT.1
  refine mem_span_gen_of_step R i t ?_ Sb f ⟨hT.1, fun κ hκ _ => hT.2 κ hκ⟩
    (fun PP a ha tr ε hε _ κ hκ _ => hC PP a ha tr ε hε κ hκ) hL
  intro Sb v hv f hT hC hL
  by_cases hpg : ∃ PP ∈ R.Pg, Over PP v
  · exact GlobalTheory.T.local_generation_thetaFun_at_type_prime D G Pl0 T A Ks R F hG hP i t Sb v hv hpg f hT hC hL
  by_cases hq : ∃ PP ∈ R.Q t, Over PP v
  · exact GlobalTheory.T.localGeneration_thetaFunctions_twistPlace D G Pl0 T A Ks R F hG hP i t Sb v hv (fun PP h ho => hpg ⟨PP, h, ho⟩) hq f hT hC hL
  have hoff : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ Over PP v := by
    rintro PP (h | h) ho
    · exact hpg ⟨PP, h, ho⟩
    · exact hq ⟨PP, h, ho⟩
  by_cases hs : ∃ ε e, IsPlaceIdem D v ε ∧ IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0
  · exact GlobalTheory.T.thetaFunction_localGeneration_splitPlaceOffLevels D G Pl0 T A Ks R F hG hP i t Sb v hv hs hoff f hT hC hL
  · refine GlobalTheory.T.thetaFunction_local_generation_inertPlace_offLevel hH D G Pl0 T A Ks R F hG hP i t Sb v hv ?_ hoff f hT hC hL
    intro ε hε e he
    by_contra hne
    exact hs ⟨ε, e, hε, he, hne⟩

end GlobalTheory.DownLift.GenFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelTypeMemSpanTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_levelType_mem_span_translates : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → GlobalTheory.DownLift.GenFinite.Clean R i t f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.Gen R i t) := by
  first | exact @GlobalTheory.DownLift.GenFinite.gen_of_type_clean | exact GlobalTheory.DownLift.GenFinite.gen_of_type_clean | (intros; apply GlobalTheory.DownLift.GenFinite.gen_of_type_clean <;> assumption)
end
