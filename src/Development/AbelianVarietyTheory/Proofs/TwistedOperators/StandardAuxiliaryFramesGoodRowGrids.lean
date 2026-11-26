module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoxDepthDataMulLineVacuaBesselLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiDepthDatumMulLineVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsOfFlatMapWeilActionNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormBottom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPositionOffBadPlacesFromBesselLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLatticesNonzeroLineVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnfoldingFlatMapNeZeroFullRank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlaceOneCosetOfBesselLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiLevelOneCosetAtGoodPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiMixedPiecesAdmissible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepPiecesAdmissibleSplits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsOfFlatMapWeilActionNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingConditions_of_flatMap_weilAction_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, ∀ h, flatS dV dW s (rat x₀) y (s.om (1, h) Φ) ≠ 0 → Cond dW p (rat x₀) y ψ (fun _ => True) h := by
  first | exact @GlobalTheory.AscFinCond.cond_of_flatS_ne | exact GlobalTheory.AscFinCond.cond_of_flatS_ne | (intros; apply GlobalTheory.AscFinCond.cond_of_flatS_ne <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleMixedModelClassStableFlatVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleMixedModelClassStableFlatVacua
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFinStab

variable {D : D7}

theorem symplO_eq_two (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem heisO_comm_of (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {a b : WO S T} (g : WO S T → ℂ)
    (h : ψ (symplOH S T a b + symplOH S T a b) = 1) :
    heisO ψ S T a (heisO ψ S T b g) = heisO ψ S T b (heisO ψ S T a g) := by
  rw [GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.symplOH_skew S T a b, add_comm b a]
  congr 1
  calc ψ (symplOH S T a b) = ψ ((symplOH S T a b + symplOH S T a b) + -symplOH S T a b) := by congr 1; ring
    _ = ψ (-symplOH S T a b) := by rw [AddChar.map_add_eq_mul, h, one_mul]

theorem heisO_smul'' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (c • g) = c • heisO ψ S T w g := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem fin_of_mxAt {m n : ℕ} {a : Mx D m n} (h : MxAt (fun _ => True) a) : a.map (infPart D) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (h i j)).1

theorem fin_mul_left {k m n : ℕ} (M : Mx D k m) {u : Mx D m n} (hu : u.map (infPart D) = 0) :
    (M * u).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hu, Matrix.mul_zero]

theorem fin_mul_right {k m n : ℕ} {u : Mx D k m} (hu : u.map (infPart D) = 0) (M : Mx D m n) :
    (u * M).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

theorem isHalf_mul_left {e : AE D} {k m n : ℕ} (M : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (M * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hu l j]

theorem isHalf_mul_right {e : AE D} {k m n : ℕ} {u : Mx D k m} (hu : IsHalf e u) (M : Mx D m n) : IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hu i l]

end GlobalTheory.AscFinStab

namespace GlobalTheory.AscFinStab

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ}

def Comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : WO S T) : Prop :=
  ∀ g : WO S T → ℂ, heisO ψ S T a (heisO ψ S T b g) = heisO ψ S T b (heisO ψ S T a g)

theorem mem_cls_of_comm (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ)
    (y : Mx D V₀.rank σ) {Φ : WO V W → ℂ} (hΦ : Φ ∈ cls dV dW p x y ψ) (c : WO V W)
    (hθ : IsThetaFunO ψ V W (heisO ψ V W c Φ))
    (h₁ : ∀ a ∈ p.A₁, Comm ψ V W (dV.extX W a) c) (h₂ : ∀ a ∈ p.A₂, Comm ψ V W (dV.extY W a) c)
    (h₃ : ∀ ξ ∈ p.B₁, Comm ψ V W (dV.ext0 W (dW.incX V₀ ξ)) c)
    (h₄ : ∀ η ∈ p.B₂, Comm ψ V W (dV.ext0 W (dW.incY V₀ η)) c)
    (h₅ : ∀ u ∈ p.Γ₀, Comm ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u)) c)
    (h₆ : ∀ e, IsSplitIdem D e → ∀ u ∈ p.Γ₀, IsHalf e (dV.ext0 W (dW.inc0 V₀ u)) → Comm ψ V W (dV.ext0 W (dW.inc0 V₀ u)) c) :
    heisO ψ V W c Φ ∈ cls dV dW p x y ψ := by
  simp only [cls, Set.mem_ofPred_eq] at hΦ ⊢
  obtain ⟨_, hA₁, hA₂, hB₁, hB₂, hL⟩ := hΦ
  refine ⟨hθ, fun a ha => ?_, fun a ha => ?_, fun ξ hξ => ?_, fun η hη => ?_, ?_⟩
  · rw [h₁ a ha, hA₁ a ha]
  · rw [h₂ a ha, hA₂ a ha, heisO_smul'']
  · rw [h₃ ξ hξ, hB₁ ξ hξ, heisO_smul'']
  · rw [h₄ η hη, hB₂ η hη]
  · unfold IsLatVac
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · obtain ⟨u₀, hu₀, rfl⟩ := AddSubgroup.mem_map.1 hu
      have e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ := hL.1 (dV.ext0 W (dW.inc0 V₀ u₀)) hu
      show heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ
      rw [h₅ u₀ hu₀, e1]
    · obtain ⟨u₀, hu₀, rfl⟩ := AddSubgroup.mem_map.1 hu
      have e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ := hL.2 e he (dV.ext0 W (dW.inc0 V₀ u₀)) hu hh
      show heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ
      rw [h₆ e he u₀ hu₀ hh, e1]

end GlobalTheory.AscFinStab

namespace GlobalTheory.AscFinStab

theorem cls_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, (∀ w : WO V W, w.map (finPart D) = 0 → heisO ψ V W w Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ (∀ w ∈ Ann ψ V₀ W₀ p.Γ₀, heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ VacG ψ V₀ W₀ p.Γ₀ (flatS dV dW s (rat x₀) y Φ) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hlin p hp Φ hΦ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hΦ' := hΦ
  simp only [cls, Set.mem_ofPred_eq] at hΦ'
  obtain ⟨hθ, -, -, -, -, hL⟩ := hΦ'
  have hJ : ∀ a b : WO V₀ W₀,
      symplOH V W (dV.ext0 W (dW.inc0 V₀ a)) (dV.ext0 W (dW.inc0 V₀ b)) = symplOH V₀ W₀ a b := by
    intro a b
    rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclAnisotropic_inclAnisotropic V₀]
  have hfin0 : ∀ u ∈ p.Γ₀, (dV.ext0 W (dW.inc0 V₀ u)).map (infPart D) = 0 := fun u hu =>
    fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.fin₀ u hu))) _
  have comm0 : ∀ {a b : WO V W}, symplOH V W a b = 0 → Comm ψ V W a b := fun h g =>
    heisO_comm_of ψ g (by rw [h, add_zero, AddChar.map_zero_eq_one])
  refine ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩
  · have cr : ∀ {a : WO V W}, a.map (infPart D) = 0 → Comm ψ V W a w := fun ha =>
      comm0 (GlobalTheory.FinTranslate.symplOH_fin_real ha hw)
    exact mem_cls_of_comm dV dW p _ y hΦ w (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ w)
      (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₁.fin a ha)) _))
      (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₂.fin a ha)) _))
      (fun ξ hξ => cr (fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.b₁.fin ξ hξ))) _))
      (fun η hη => cr (fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.b₂.fin η hη))) _))
      (fun u hu => cr (by
        rw [← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]
        exact hfin0 _ (nsmul_mem hu 2)))
      (fun e _ u hu _ => cr (hfin0 u hu))
  · obtain ⟨hw1, hw2⟩ := hw
    have hc : ∀ u : WO V₀ W₀, ψ (symplO V₀ W₀ w u) = 1 →
        Comm ψ V W (dV.ext0 W (dW.inc0 V₀ u)) (dV.ext0 W (dW.inc0 V₀ w)) := by
      intro u hu g
      refine heisO_comm_of ψ g ?_
      rw [hJ, GlobalTheory.FinTranslate.symplOH_skew V₀ W₀ w u, ← neg_add, AddChar.map_neg_eq_inv, ← symplO_eq_two, hu, inv_one]
    exact mem_cls_of_comm dV dW p _ y hΦ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ _)
      (fun a _ => comm0 (dV.wittDecomp_sympl_extIsotropic_extAnisotropic W a _))
      (fun a _ => comm0 (dV.wittDecomp_sympl_extDual_extAnisotropic W a _))
      (fun ξ _ => comm0 (by rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclIsotropic_inclAnisotropic V₀]))
      (fun η _ => comm0 (by rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclDual_inclAnisotropic V₀]))
      (fun u hu => by
        rw [← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]
        exact hc _ (hw1 u hu))
      (fun e he u hu hh => hc u (hw2 e he u hu (by
        have h' := isHalf_mul_right (isHalf_mul_left dW.p0 hh) dV.j0
        have eq : dW.p0 * (dV.ext0 W (dW.inc0 V₀ u)) * dV.j0 = u := by
          rw [dV.matrixExtendByZero_apply, dW.wittDecomp_inclAnisotropicHom_apply]
          simp only [← Matrix.mul_assoc, dW.p0_j0, Matrix.one_mul]
          rw [Matrix.mul_assoc, dV.p0_j0, Matrix.mul_one]
        rwa [eq] at h')))
  · have hfl := GlobalTheory.FlatHeis.flatAt_heisO D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU (rat x₀) y Φ hθ
    unfold VacG IsLatVac
    refine ⟨(GlobalTheory.Unf.Flat.flatLaw D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU x₀ hlin y Φ hθ).2,
      fun u hu => ?_, fun e he u hu hh => ?_⟩
    · have e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ :=
        hL.1 _ (AddSubgroup.mem_map_of_mem _ hu)
      show heisO ψ V₀ W₀ (2 • u) (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) =
        flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ
      rw [← hfl.2.1, map_nsmul (dW.inc0 V₀), map_nsmul (dV.ext0 W), e1]
    · have e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ :=
        hL.2 e he _ (AddSubgroup.mem_map_of_mem _ hu) (isHalf_mul_right (isHalf_mul_left _ hh) _)
      show heisO ψ V₀ W₀ u (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) =
        flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ
      rw [← hfl.2.1, e1]

end GlobalTheory.AscFinStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleMixedModelClassStableFlatVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleMixedModelClass_stable_flat_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, (∀ w : WO V W, w.map (finPart D) = 0 → heisO ψ V W w Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ (∀ w ∈ Ann ψ V₀ W₀ p.Γ₀, heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ VacG ψ V₀ W₀ p.Γ₀ (flatS dV dW s (rat x₀) y Φ) := by
  first | exact @GlobalTheory.AscFinStab.cls_stable | exact GlobalTheory.AscFinStab.cls_stable | (intros; apply GlobalTheory.AscFinStab.cls_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapNonvanishingConditionLocalise
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapNonvanishingConditionLocalise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.LocCond

variable {D : D7}

theorem idAt_mul_idOff {P : GlobalTheory.FinPl.Pl D → Prop} {a b : AE D} (ha : a ∈ idAt D P) (hb : b ∈ idOff D P) :
    a * b = 0 := by
  have h1 := (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 ha
  have h2 := (GlobalTheory.FinPlLoc.mem_idOff_iff P b).1 hb
  calc a * b = (GlobalTheory.FinPlLoc.idem D P * a) * b := by rw [h1]
    _ = a * (GlobalTheory.FinPlLoc.idem D P * b) := by ring
    _ = 0 := by rw [h2, mul_zero]

theorem idOff_true_le {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ idOff D (fun _ => True)) : a ∈ idOff D P := by
  unfold GlobalTheory.FinPl.idOff at *
  rw [Submodule.mem_iInf] at *
  intro w
  exact ha ⟨w.1, trivial⟩

theorem idAt_le_true {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D (fun _ => True) := by
  unfold GlobalTheory.FinPl.idAt at *
  obtain ⟨h0, -⟩ := Ideal.mem_inf.1 ha
  exact Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w => absurd trivial w.2⟩

theorem mul_mem_left' {I : Ideal (AE D)} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hE : ∀ i j, E i j ∈ I) : ∀ i j, (E ⬝ Z) i j ∈ I := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hE i l)

theorem mul_mem_right' {I : Ideal (AE D)} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hZ : ∀ i j, Z i j ∈ I) : ∀ i j, (E ⬝ Z) i j ∈ I := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hZ l j)

theorem mul_eq_zero_of {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hE : ∀ i j, E i j ∈ idOff D P) (hZ : ∀ i j, Z i j ∈ idAt D P) :
    E ⬝ Z = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [mul_comm]; exact idAt_mul_idOff (hZ l j) (hE i l)

theorem off_entries {P : GlobalTheory.FinPl.Pl D → Prop} {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) :
    ∀ i j, (mt S g - 1) i j ∈ idOff D P := fun i j => by
  rw [Matrix.sub_apply]
  exact (GlobalTheory.FinPlLoc.mem_congGrp _ g).1 hg i j

theorem mt_off_mul {P : GlobalTheory.FinPl.Pl D → Prop} {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) {k : ℕ}
    (Z : Matrix (Fin S.rank) (Fin k) (AE D)) (hZ : ∀ i j, Z i j ∈ idAt D P) : mt S g ⬝ Z = Z := by
  calc mt S g ⬝ Z = (mt S g - 1) ⬝ Z + Z := by rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
    _ = Z := by rw [mul_eq_zero_of _ _ (off_entries hg) hZ, zero_add]

end GlobalTheory.AscFin.LocCond


open GlobalTheory.AscFin.LocCond in
theorem GlobalTheory.AscFin.cond_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (P : GlobalTheory.FinPl.Pl D → Prop) (h₁ h₂ : GA D W), h₁ ∈ grpAt W P → h₂ ∈ grpOff W P → Cond dW p x y ψ (fun _ => True) (h₁ * h₂) → Cond dW p x y ψ P h₁ := by
  intro D ψ _ V V₀ W W₀ ρ σ dV dW p x y P h₁ h₂ _ h2 hc
  have e2 := off_entries (inv_mem h2)
  have hinv : mt W (h₁ * h₂)⁻¹ = mt W h₂⁻¹ ⬝ mt W h₁⁻¹ := by
    rw [_root_.mul_inv_rev, GlobalTheory.FinPlLoc.mt_mul]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, a, ha, hoff⟩ := hc.pt
    refine ⟨u, a, ha, fun i j => ?_⟩
    have hk := idOff_true_le (P := P) (hoff i j)
    have hm := mul_mem_left' (mt W h₂⁻¹ - 1) (mt W h₁⁻¹ ⬝ (x ⬝ u.1.1)) e2 i j
    have eq : mt W h₁⁻¹ ⬝ (x ⬝ u.1.1) - x - a =
        (mt W (h₁ * h₂)⁻¹ ⬝ (x ⬝ u.1.1) - x - a) - (mt W h₂⁻¹ - 1) ⬝ (mt W h₁⁻¹ ⬝ (x ⬝ u.1.1)) := by
      rw [hinv, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      abel
    rw [eq, Matrix.sub_apply]
    exact sub_mem hk hm
  · intro N hN hlow hA
    refine hc.shift N (fun i j => idAt_le_true (hN i j)) hlow ?_
    have hZ : ∀ i j, (mt W h₁⁻¹ ⬝ (x ⬝ N)) i j ∈ idAt D P := mul_mem_right' _ _ (mul_mem_right' _ _ hN)
    rw [hinv, Matrix.mul_assoc, mt_off_mul (inv_mem h2) _ hZ]
    exact hA
  · intro ξ hξ ξ' hP heq
    refine hc.iso ξ hξ ξ' (fun i j => idAt_le_true (hP i j)) ?_
    have hZ : ∀ i j, (dW.incX V₀ ξ) i j ∈ idAt D P := by
      rw [HypDec.incX_apply]
      exact mul_mem_right' _ _ hP
    rw [GlobalTheory.FinPlLoc.mt_mul, Matrix.mul_assoc, mt_off_mul h2 _ hZ]
    exact heq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapNonvanishingConditionLocaliseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMapNonvanishingCondition_localise : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (P : GlobalTheory.FinPl.Pl D → Prop) (h₁ h₂ : GA D W), h₁ ∈ grpAt W P → h₂ ∈ grpOff W P → Cond dW p x y ψ (fun _ => True) (h₁ * h₂) → Cond dW p x y ψ P h₁ := by
  first | exact @GlobalTheory.AscFin.cond_loc | exact GlobalTheory.AscFin.cond_loc | (intros; apply GlobalTheory.AscFin.cond_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizerAtPlaceMemDepthCongruenceGridNo
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizerAtPlaceMemDepthCongruenceGridNo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.LevelOffS

variable {D : D7}

theorem valued_algebraMap {v : GlobalTheory.FinPl.Pl D} (y : D.host.F) :
    Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) y) = v.valuation D.host.F y :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y

theorem inv_int {v : GlobalTheory.FinPl.Pl D} {c : 𝓞 D.host.F} (hc : c ∉ v.asIdeal) :
    evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (algebraMap (𝓞 D.host.F) D.host.F c)⁻¹) ∈
      v.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.intValuation c = 1 := le_antisymm (v.intValuation_le_one c)
    (not_lt.1 fun h => hc ((v.intValuation_lt_one_iff_mem c).1 h))
  have h2 : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (algebraMap (𝓞 D.host.F) D.host.F c)) = 1 := by
    rw [valued_algebraMap]
    exact (HeightOneSpectrum.valuation_of_algebraMap v c).trans h1
  rw [map_inv₀, map_inv₀, h2, inv_one]

theorem coe_ne_zero_of_nmem {v : GlobalTheory.FinPl.Pl D} {c : 𝓞 D.host.F} (hc : c ∉ v.asIdeal) :
    algebraMap (𝓞 D.host.F) D.host.F c ≠ 0 := by
  intro h
  apply hc
  rw [show c = 0 from IsFractionRing.injective (𝓞 D.host.F) D.host.F (h.trans (map_zero _).symm)]
  exact zero_mem _

theorem smul_pairA (r : D.host.F) (α : Af D.host.F) : r • pairA D.host.F 0 α = pairA D.host.F 0 (r • α) :=
  Prod.ext (smul_zero (A := Ainf D.host.F) r) rfl

theorem smul_vec_apply (c : 𝓞 D.host.F) {n : ℕ} (x : Fin n → D.host.E) (i : Fin n) :
    (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • x) i = algebraMap (𝓞 D.host.F) D.host.F c • x i := by
  rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
  congr 1

theorem latV_le_smul {S : HSp D} (Λ : Lat S) {v : GlobalTheory.FinPl.Pl D} (𝔪 : Ideal (𝓞 D.host.E)) {c : 𝓞 D.host.F}
    (hc : c ∉ v.asIdeal) (hcm : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ 𝔪) :
    latV S Λ (· = v) ≤ latV S (𝔪 • Λ) (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  rw [AddSubgroup.closure_le]
  rintro _ ⟨α, hα, hαv, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  set cF : D.host.F := algebraMap (𝓞 D.host.F) D.host.F c with hcF
  have hc0 : cF ≠ 0 := coe_ne_zero_of_nmem hc
  refine AddSubgroup.subset_closure ⟨α * algebraMap D.host.F (Af D.host.F) cF⁻¹, fun w => ?_, fun w hw => ?_, 1, rfl,
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • x, Submodule.smul_mem_smul hcm hx, ?_⟩
  · rw [map_mul]
    by_cases hw : w = v
    · subst hw
      exact mul_mem (hα w) (inv_int hc)
    · rw [hαv w hw, zero_mul]
      exact zero_mem _
  · rw [map_mul, hαv w hw, zero_mul]
  · funext i
    rw [smul_vec_apply, one_mul, one_mul, ← TensorProduct.smul_tmul, smul_pairA]
    congr 2
    rw [Algebra.smul_def, mul_left_comm, ← map_mul, mul_inv_cancel₀ hc0, map_one, mul_one]

theorem finPart_finIn (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (GlobalTheory.FinPlLoc.finIn D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [GlobalTheory.FinPlLoc.finIn_tmul, GlobalTheory.FinPlLoc.finPart_pair]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem finIn_mem_idAt (z : Af D.host.F ⊗[D.host.F] D.host.E) : GlobalTheory.FinPlLoc.finIn D z ∈ idAt D (fun _ => True) := by
  unfold GlobalTheory.FinPl.idAt
  exact Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (GlobalTheory.FinPlLoc.infPart_finIn z),
    (Submodule.mem_iInf _).2 fun w => absurd trivial w.2⟩

theorem hatL_mono {n : ℕ} {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ ≤ Λ') :
    Formalism.L2.Herm.hatL (F := D.host.F) Λ ≤ Formalism.L2.Herm.hatL (F := D.host.F) Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_GfC_of_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {κ : GA D S} (h : κ ∈ grpAt S P) : κ ∈ GfC S := by
  unfold GlobalTheory.FinPl.grpAt at h
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at h
  show infHom S κ = 1
  apply Units.ext
  ext i j
  have h1 := GlobalTheory.FinPlLoc.infPart_of_idAt (h i j)
  rw [map_sub, sub_eq_zero] at h1
  change infPart D (mt S κ i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j
  rw [h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem finE_coe {S : HSp D} (κ : GA D S) :
    ((Lev.finE S κ : GL (Fin S.rank) (Lev.EAf D)) : Matrix (Fin S.rank) (Fin S.rank) (Lev.EAf D)) =
      (mt S κ).map ((Lev.swapAE D).comp (finPart D)) := rfl

theorem sub_mem_hatL_of_inK {S : HSp D} (Λ : Lat S) {v : GlobalTheory.FinPl.Pl D} (𝔪 : Ideal (𝓞 D.host.E)) {c : 𝓞 D.host.F}
    (hc : c ∉ v.asIdeal) (hcm : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ 𝔪) {κ : GA D S}
    (hκ : InK S Λ (· = v) κ) (x : Fin S.rank → Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    ((Lev.finE S κ : GL (Fin S.rank) (Lev.EAf D)) : Matrix (Fin S.rank) (Fin S.rank) (Lev.EAf D)) *ᵥ x - x ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) := by
  obtain ⟨z, hz⟩ : ∃ z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E, ∀ i, Lev.swapAE D (z i) = x i :=
    ⟨fun i => (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (x i), fun i => by
      show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
        ((Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (x i)) = x i
      generalize x i = y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]⟩
  set y0 : Fin S.rank → AE D := fun i => GlobalTheory.FinPlLoc.finIn D (z i) with hy0def
  have hφ : ∀ i, (Lev.swapAE D).comp (finPart D) (y0 i) = x i := fun i => by
    rw [RingHom.comp_apply, hy0def, finPart_finIn, hz]
  have hy0 : y0 ∈ latV S Λ (fun _ => True) := by
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D S Λ _ y0 (fun i => finIn_mem_idAt _) ?_
    convert hx using 1
    funext i
    exact hφ i
  set e := GlobalTheory.FinPlLoc.idem D (· = v) with he
  have hey : e • y0 ∈ latV S Λ (· = v) := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt _) hy0
  have hmv : mt S κ *ᵥ (e • y0) ∈ latV S Λ (· = v) := (hκ.2 _ (GlobalTheory.FinPlLoc.latV_idAt hey)).1 hey
  have hgrp := hκ.1
  unfold GlobalTheory.FinPl.grpAt at hgrp
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at hgrp
  have hN : ∀ i j, e * (mt S κ - 1) i j = (mt S κ - 1) i j := fun i j =>
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (by rw [Matrix.sub_apply]; exact hgrp i j)
  have hd : mt S κ *ᵥ (e • y0) - e • y0 = mt S κ *ᵥ y0 - y0 := by
    have h1 : ∀ w : Fin S.rank → AE D, mt S κ *ᵥ w - w = (mt S κ - 1) *ᵥ w := fun w => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [h1, h1, Matrix.mulVec_smul]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hN i j]
  have hd' : mt S κ *ᵥ y0 - y0 ∈ latV S (𝔪 • Λ) (· = v) :=
    latV_le_smul Λ 𝔪 hc hcm (hd ▸ sub_mem hmv hey)
  have hfin := GlobalTheory.LatVHat.latV_mem_hatL D S (𝔪 • Λ) _ _ hd'
  convert hfin using 1
  funext i
  have hx' : x = ⇑((Lev.swapAE D).comp (finPart D)) ∘ y0 := funext fun j => (hφ j).symm
  rw [finE_coe, Pi.sub_apply, Pi.sub_apply, hx', ← RingHom.map_mulVec]
  change _ = (Lev.swapAE D).comp (finPart D) ((mt S κ *ᵥ y0 - y0) i)
  rw [Pi.sub_apply, map_sub]
  rfl

theorem exists_unit_mem_modul {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ G.pl.S0) : ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.modul := by
  classical
  have hex : ∀ u ∈ G.pl.S0, ∃ c ∈ u.asIdeal, c ∉ v.asIdeal := by
    intro u hu
    by_contra h
    push_neg at h
    have huv : u = v := HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top h)
    exact hv (huv ▸ hu)
  choose! f hf hfv using hex
  refine ⟨∏ u ∈ G.pl.S0, f u ^ G.pl.depth sc u, fun hmem => ?_, ?_⟩
  · obtain ⟨u, hu, hu'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact hfv u hu (v.isPrime.mem_of_pow_mem _ hu')
  · show _ ∈ ∏ u ∈ G.pl.S0, (G.pl.w u).asIdeal ^ G.pl.depth sc u
    rw [map_prod]
    apply Ideal.prod_mem_prod
    intro u hu
    rw [map_pow]
    apply Ideal.pow_mem_pow
    have h1 := G.pl.under_w hu
    have h2 : f u ∈ ((G.pl.w u).under (𝓞 D.host.F)).asIdeal := by rw [h1]; exact hf u hu
    exact h2

end GlobalTheory.LevelOffS


open GlobalTheory.LevelOffS in
theorem GlobalTheory.LevelOffS.inK_mem_lev : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → ∀ v, v ∉ G.pl.S0 → ∀ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ → κ ∈ lev G (.grid i 0) := by
  intro D hD T L μ0 hL sc G W M hM i hi v hv κ hκ
  obtain ⟨c, hc, hcm⟩ := exists_unit_mem_modul G hv
  refine Subgroup.mem_inf.2 ⟨mem_GfC_of_grpAt hκ.1, ?_⟩
  rw [Subgroup.mem_comap]
  show _ ∈ GlobalTheory.ChiGrid.congLev D.sp.cm (G.V (.grid i 0)).gram (G.Λ (.grid i 0)) G.modul
  rw [GlobalTheory.ChiGrid.mem_congLev]
  have hle : Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.grid i 0)) ≤ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid i 0)) :=
    hatL_mono Submodule.smul_le_right
  refine ⟨GlobalTheory.DefFree.finE_mem _ κ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩,
    fun x hx => sub_mem_hatL_of_inK _ _ hc hcm hκ x hx⟩
  · have h1 := hle (sub_mem_hatL_of_inK _ _ hc hcm hκ x hx)
    have h2 := add_mem h1 hx
    rwa [sub_add_cancel] at h2
  · have h1 := hle (sub_mem_hatL_of_inK _ _ hc hcm (inK_inv hκ) _ hx)
    have h2 := add_mem h1 hx
    rw [sub_add_cancel, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h2
    exact h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizerAtPlaceMemDepthCongruenceGridNoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizerAtPlace_mem_depthCongruence_gridNode : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → ∀ v, v ∉ G.pl.S0 → ∀ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ → κ ∈ lev G (.grid i 0) := by
  first | exact @GlobalTheory.LevelOffS.inK_mem_lev | exact GlobalTheory.LevelOffS.inK_mem_lev | (intros; apply GlobalTheory.LevelOffS.inK_mem_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleMixedModelSupportedClassSubsetSplitLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleMixedModelSupportedClassSubsetSplitLattice
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.SplitVac

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_eq_halves (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem heisO_add_fix {f : WO S T → ℂ} {w w' : WO S T} (h : heisO ψ S T w f = f) (h' : heisO ψ S T w' f = f)
    (hc : ψ (symplOH S T w w') = 1) : heisO ψ S T (w + w') f = f := by
  have e := GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) w w' f
  rw [h', h, hc, one_smul] at e
  exact e.symm

theorem psi_four {t : AF D.host.F} (h : ψ (t + t) = 1) : ψ ((t + t) + (t + t)) = 1 := by
  rw [AddChar.map_add_eq_mul, h, one_mul]

theorem psi_symplO_two {x y : WO S T} (h : ψ (symplO S T x y) = 1) : ψ (symplO S T x (2 • y)) = 1 := by
  rw [symplO_eq_halves] at h ⊢
  rw [two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_right]
  exact psi_four h

theorem psi_symplOH_two {x y : WO S T} (h : ψ (symplO S T x y) = 1) : ψ (symplOH S T (2 • x) (2 • y)) = 1 := by
  rw [symplO_eq_halves] at h
  rw [two_nsmul, two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
  exact psi_four h

variable {m n k : ℕ} {e : AE D}

theorem isHalf_add' {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := fun i j => by
  rw [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_mul_right' {x : Mx D m n} (hx : IsHalf e x) (M : Mx D n k) : IsHalf e (x * M) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hx i]

theorem isHalf_mul_left' (M : Mx D k m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (M * x) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx l j]

theorem symplOH_half (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplOH S T x y = 0 := by
  have h0 : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hx d a, ← hy c b, map_mul]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) * he
  unfold symplOH symplO
  rw [h0, mul_zero, map_zero, mul_zero]

end GlobalTheory.AscFin.SplitVac

namespace GlobalTheory.AscFin.SplitVac

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ} {dW : HypDec W W₀ σ}
  {p : Pieces V₀ W W₀ ρ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ} {Γ : AddSubgroup (WO V W)} {Φ : WO V W → ℂ}

theorem fix_two (hp : p.Is dV dW x ψ) (hs : Splits dV dW p x y ψ Γ) (hΦ : Φ ∈ cls dV dW p x y ψ) (u : WO V W) (hu : u ∈ Γ) :
    heisO ψ V W (2 • u) Φ = Φ := by
  obtain ⟨hθ, hA1, hA2, hB1, hB2, hvac⟩ := hΦ
  obtain ⟨a, ha, a', ha', ξ, hξ, η, hη, w, hw, rfl, hx', hy'⟩ := hs.comp u hu
  have e1 : 2 • (dV.extX W a + dV.extY W a' + dV.ext0 W (dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w)) =
      dV.extX W (2 • a) + (dV.extY W (2 • a') + (dV.ext0 W (dW.incX V₀ (2 • ξ)) +
        (dV.ext0 W (dW.incY V₀ (2 • η)) + dV.ext0 W (dW.inc0 V₀ (2 • w))))) := by
    simp only [map_nsmul, map_add (f := _), nsmul_add]
    abel
  show heisO ψ V W _ Φ = Φ
  rw [e1]
  have fX : heisO ψ V W (dV.extX W (2 • a)) Φ = Φ := hA1 _ (nsmul_mem ha 2)
  have fY : heisO ψ V W (dV.extY W (2 • a')) Φ = Φ := by
    rw [hA2 _ (nsmul_mem ha' 2), map_nsmul, psi_symplO_two hx', one_smul]
  have fP : heisO ψ V W (dV.ext0 W (dW.incX V₀ (2 • ξ))) Φ = Φ := by
    rw [hB1 _ (nsmul_mem hξ 2), map_nsmul, psi_symplO_two hy', one_smul]
  have fQ : heisO ψ V W (dV.ext0 W (dW.incY V₀ (2 • η))) Φ = Φ := hB2 _ (nsmul_mem hη 2)
  have fR : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ (2 • w))) Φ = Φ := by
    have h := hvac.1 _ (AddSubgroup.mem_map_of_mem ((dV.ext0 W).comp (dW.inc0 V₀)) hw)
    rw [AddMonoidHom.comp_apply, ← map_nsmul, ← map_nsmul] at h
    exact h
  have cAB : ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1 := (hp.dualA a (hp.a₁.fin a ha)).1 ha a' ha'
  have cXY : ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1 := (hp.dualB ξ (hp.b₁.fin ξ hξ)).1 hξ η hη
  refine heisO_add_fix fX (heisO_add_fix fY (heisO_add_fix fP (heisO_add_fix fQ fR ?_) ?_) ?_) ?_
  · rw [HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_inclDual_inclAnisotropic, AddChar.map_zero_eq_one]
  · rw [GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic,
      HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, add_zero, map_nsmul, map_nsmul]
    exact psi_symplOH_two cXY
  · simp only [GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.wittDecomp_sympl_extDual_extAnisotropic, add_zero, AddChar.map_zero_eq_one]
  · rw [GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
      HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, add_zero, add_zero, add_zero,
      map_nsmul, map_nsmul]
    exact psi_symplOH_two cAB

theorem fix_half (hs : Splits dV dW p x y ψ Γ) (hΦ : Φ ∈ cls dV dW p x y ψ) (e : AE D) (he : IsSplitIdem D e) (u : WO V W)
    (hu : u ∈ Γ) (hh : IsHalf e u) : heisO ψ V W u Φ = Φ := by
  obtain ⟨hθ, hA1, hA2, hB1, hB2, hvac⟩ := hΦ
  obtain ⟨a, ha, a', ha', ξ, hξ, η, hη, w, hw, rfl, hx', hy'⟩ := hs.comp u hu
  have he0 : e * cA D e = 0 := he.2.1
  have e1 : dV.extX W a + dV.extY W a' + dV.ext0 W (dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w) =
      dV.extX W a + (dV.extY W a' + (dV.ext0 W (dW.incX V₀ ξ) +
      (dV.ext0 W (dW.incY V₀ η) + dV.ext0 W (dW.inc0 V₀ w)))) := by
    rw [map_add (f := _), map_add (f := _)]
    abel
  obtain ⟨z, hz⟩ : ∃ z, dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w = z := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, dV.extX W a + dV.extY W a' + dV.ext0 W z = U := ⟨_, rfl⟩
  rw [hz, hU] at hh
  have hUa : U * dV.jX = a := by
    rw [← hU]
    simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc,
      HypDec.pX_jX, HypDec.pY_jX, HypDec.p0_jX, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hUa' : U * dV.jY = a' := by
    rw [← hU]
    simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc,
      HypDec.pX_jY, HypDec.pY_jY, HypDec.p0_jY, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
  have hUz : U * dV.j0 = z := by
    rw [← hU]
    simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc,
      HypDec.pX_j0, HypDec.pY_j0, HypDec.p0_j0, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
  have hzξ : dW.pX * z = ξ := by
    rw [← hz]
    simp only [HypDec.incX_apply, HypDec.incY_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc,
      HypDec.pX_jX, HypDec.pX_jY, HypDec.pX_j0, Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hzη : dW.pY * z = η := by
    rw [← hz]
    simp only [HypDec.incX_apply, HypDec.incY_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc,
      HypDec.pY_jX, HypDec.pY_jY, HypDec.pY_j0, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  have hzw : dW.p0 * z = w := by
    rw [← hz]
    simp only [HypDec.incX_apply, HypDec.incY_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc,
      HypDec.p0_jX, HypDec.p0_jY, HypDec.p0_j0, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  have hzh : IsHalf e z := hUz ▸ isHalf_mul_right' hh _
  have hX : IsHalf e (dV.extX W a) := by
    rw [HypDec.extX_apply, ← hUa]; exact isHalf_mul_right' (isHalf_mul_right' hh _) _
  have hY : IsHalf e (dV.extY W a') := by
    rw [HypDec.extY_apply, ← hUa']; exact isHalf_mul_right' (isHalf_mul_right' hh _) _
  have hP : IsHalf e (dV.ext0 W (dW.incX V₀ ξ)) := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, ← hzξ]
    exact isHalf_mul_right' (isHalf_mul_left' _ (isHalf_mul_left' _ hzh)) _
  have hQ : IsHalf e (dV.ext0 W (dW.incY V₀ η)) := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, ← hzη]
    exact isHalf_mul_right' (isHalf_mul_left' _ (isHalf_mul_left' _ hzh)) _
  have hR : IsHalf e (dV.ext0 W (dW.inc0 V₀ w)) := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, ← hzw]
    exact isHalf_mul_right' (isHalf_mul_left' dW.j0 (isHalf_mul_left' dW.p0 hzh)) dV.p0
  have fX : heisO ψ V W (dV.extX W a) Φ = Φ := hA1 _ ha
  have fY : heisO ψ V W (dV.extY W a') Φ = Φ := by rw [hA2 _ ha', hx', one_smul]
  have fP : heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) Φ = Φ := by rw [hB1 _ hξ, hy', one_smul]
  have fQ : heisO ψ V W (dV.ext0 W (dW.incY V₀ η)) Φ = Φ := hB2 _ hη
  have fR : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ = Φ := by
    have h := hvac.2 e he ((dV.ext0 W).comp (dW.inc0 V₀) w) (AddSubgroup.mem_map_of_mem ((dV.ext0 W).comp (dW.inc0 V₀)) hw)
      (by rw [AddMonoidHom.comp_apply]; exact hR)
    rw [AddMonoidHom.comp_apply] at h
    exact h
  have z0 : ∀ {s t : WO V W}, IsHalf e s → IsHalf e t → ψ (symplOH V W s t) = 1 := fun hs ht => by
    rw [symplOH_half he0 hs ht, AddChar.map_zero_eq_one]
  show heisO ψ V W _ Φ = Φ
  rw [e1]
  exact heisO_add_fix fX (heisO_add_fix fY (heisO_add_fix fP (heisO_add_fix fQ fR (z0 hQ hR))
    (z0 hP (isHalf_add' hQ hR))) (z0 hY (isHalf_add' hP (isHalf_add' hQ hR))))
    (z0 hX (isHalf_add' hY (isHalf_add' hP (isHalf_add' hQ hR))))

theorem cls_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ)
    (Γ : AddSubgroup (WO V W)), p.Is dV dW x ψ → Splits dV dW p x y ψ Γ → ∀ Φ ∈ cls dV dW p x y ψ, VacG ψ V W Γ Φ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hs _ hΦ =>
    ⟨hΦ.1, fun u hu => fix_two hp hs hΦ u hu, fun e he u hu hh => fix_half hs hΦ e he u hu hh⟩

end GlobalTheory.AscFin.SplitVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleMixedModelSupportedClassSubsetSplitLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleMixedModelSupportedClass_subset_splitLatticeVacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Γ : AddSubgroup (WO V W)), p.Is dV dW x ψ → Splits dV dW p x y ψ Γ → ∀ Φ ∈ cls dV dW p x y ψ, VacG ψ V W Γ Φ := by
  first | exact @GlobalTheory.AscFin.SplitVac.cls_vac | exact GlobalTheory.AscFin.SplitVac.cls_vac | (intros; apply GlobalTheory.AscFin.SplitVac.cls_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardAuxiliaryFramesGoodRowGrids
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.Unf.FB (selFirst lastE mul_mul_mul_of_gram)

namespace GlobalTheory.AscFin.GoodStd

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem xLast_rat {V V₀ A L : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) : ∃ x₀ : Matrix (Fin V.rank) (Fin (σ + 1)) D.host.E,
      LinearIndependent D.host.E x₀.transpose ∧ xLast d (vecB o ζ) = rat x₀ := by
  set x₀ : Matrix (Fin V.rank) (Fin (σ + 1)) D.host.E := d.e * selFirst D σ + d.i₀ * vecMulVec (vecB o ζ) (lastE D σ) with hx₀
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  have hrat : xLast d (vecB o ζ) = rat x₀ := by
    funext k j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [hx₀, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV, vecB, hne]
    · simp [hx₀, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV, vecB]
  have hgram : x₀ᴴ * V.gram * x₀ = (vecMulVec ζ (lastE D σ))ᴴ * L.gram * vecMulVec ζ (lastE D σ) := by
    have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) d.ee
    have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) d.i₀e
    have hX0 : d.eᴴ * V.gram * d.i₀ = 0 := by
      have := congrArg conjTranspose d.i₀e
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
    have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) d.iso
    have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) o.isoB
    have hz : vecMulVec (vecB o ζ) (lastE D σ) = o.iB * vecMulVec ζ (lastE D σ) := by
      rw [vecB, mul_vecMulVec]
    rw [hx₀, hz]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
      h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  refine ⟨x₀, ?_, hrat⟩
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : x₀ *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : d.e'ᴴ * V.gram * d.i₀ = 0 := by
    have := congrArg conjTranspose d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (d.e'ᴴ * V.gram) * x₀ = selFirst D σ := by
    rw [hx₀, Matrix.mul_add, ← Matrix.mul_assoc, d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul, add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec ζ (lastE D σ))ᴴ * L.gram * vecMulVec ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← hgram, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec] at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 hζ.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

theorem loc_cls {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : x = rat x₀) (y : Mx D V₀.rank σ)
    (p : Pieces V₀ W W₀ ρ σ) (Γ : AddSubgroup (WO V W)) (K : Subgroup (GA D W)) (hψ : IsStdChar D ψ (-1))
    (hli : LinearIndependent D.host.E x₀.transpose) (hp : p.Is dV dW x ψ) (hs : Splits dV dW p x y ψ Γ)
    (hfin : K ≤ GfC W) (hcpt : IsCompact (K : Set (GA D W)))
    (hopn : IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)))
    (hfix : ∀ f, VacG ψ V W Γ f → ∀ k ∈ K, s.om (1, k) f = f)
    (hsupp : ∀ h, Cond dW p x y ψ (fun _ => True) h → (∀ κ ∈ K, Cond dW p x y ψ (fun _ => True) (h * κ)) →
      ∃ r ∈ Rgrp W x, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) :
    Loc dV dW s x y (cls dV dW p x y ψ) p.Γ₀ K ∧ ∀ Φ ∈ cls dV dW p x y ψ, VacG ψ V W Γ Φ := by
  subst hx
  have hvac : ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, VacG ψ V W Γ Φ := fun Φ hΦ =>
    GlobalTheory.T.doubleMixedModelSupportedClass_subset_splitLatticeVacua D ψ hψ V V₀ W W₀ ρ σ dV dW p (rat x₀) y Γ hp hs Φ hΦ
  have hst := fun Φ hΦ => GlobalTheory.T.doubleMixedModelClass_stable_flat_vacua D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ
  refine ⟨⟨fun Φ hΦ => hΦ.1, fun Φ hΦ => (hst Φ hΦ).1, fun Φ hΦ => (hst Φ hΦ).2.1, fun Φ hΦ => (hst Φ hΦ).2.2, hfin,
    hcpt, hopn, fun Φ hΦ k hk => hfix Φ (hvac Φ hΦ) k hk, ?_, GlobalTheory.T.exists_unfolding_flatMap_ne_zero_fullRank D ψ hψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp⟩, hvac⟩
  intro Φ hΦ h hne
  refine hsupp h (GlobalTheory.T.unfoldingConditions_of_flatMap_weilAction_ne_zero D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ h hne) fun κ hκ =>
    GlobalTheory.T.unfoldingConditions_of_flatMap_weilAction_ne_zero D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ (h * κ) ?_
  have e : s.om (1, h * κ) Φ = s.om (1, h) Φ := by
    have : ((1 : GA D V), h * κ) = (1, h) * (1, κ) := by simp
    rw [this, map_mul, Module.End.mul_apply, hfix Φ (hvac Φ hΦ) κ hκ]
  rwa [e]

end GlobalTheory.AscFin.GoodStd

namespace GlobalTheory.AscFin.GoodStd

theorem std_good : GlobalTheory.SepRows.DepFixed → All fun {_} _ _ _ {G} W _ =>
    ∀ (v : CoreVol G) (F : GlobalTheory.Asc.Frames G), Std F → F.Good v W (lineLat F) := by
  intro hDF D hQ T L μ0 hL sc G W M hM v F hF
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have cj := GlobalTheory.T.weil_datum_conjugation_dictionary_row_grid hDF D hQ T L μ0 hL sc G W M hM
  have gl := GlobalTheory.T.depthCongruenceSubgroup_compactOpen_places_to_adeles D hQ T L μ0 hL sc G W M hM
  have kv := GlobalTheory.T.latticeStabilizerAtPlace_mem_depthCongruence_gridNode D hQ T L μ0 hL sc G W M hM
  have lt := GlobalTheory.T.last_seesaw_lattices_nonzero_line_vacua D hQ T L μ0 hL sc G W M hM F hF
  refine ⟨?_, ?_, lt.1, fun h => lt.2 v h⟩
  · intro ρ h s hs
    obtain ⟨hbase, -, hx, -⟩ := GlobalTheory.Unf.base_point D _ _ ρ (F.dJ ρ h)
    obtain ⟨hpIs, hspl⟩ := GlobalTheory.T.besselToFourierJacobi_mixedPieces_admissible D hQ T L μ0 hL sc G W M hM F hF ρ h
    have gd := GlobalTheory.T.goodPosition_and_incAdj_mem_latO_iff_mem_intAt D hQ T L μ0 hL sc G W M hM F hF ρ h
    have g0 := gl (2 * ρ + 1) (by omega)
    have hsupp : ∀ g, Cond (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (fun _ => True) g →
        (∀ κ ∈ lev G (.grid (2 * ρ + 1) 0),
          Cond (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (fun _ => True) (g * κ)) →
        ∃ r ∈ Rgrp _ (xZero (F.dJ ρ h)), ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), g = r * a * k := by
      intro g hc hcK
      refine g0.2 (Rgrp _ (xZero (F.dJ ρ h))) g ?_ ?_
      · intro w hw h₁ hh₁ h₂ hh₂ e
        obtain ⟨g1, g2, g3⟩ := gd w hw
        refine GlobalTheory.T.goodPlace_oneCoset_of_besselLevel D W.ψ hψ _ _ _ _ ρ (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (vecB (F.oB ρ h) (F.ζ (ρ + 1)))
          _ _ _ _ w g1 g2 g3 h₁ hh₁ ?_
        intro κ hκ
        have hκl : κ ∈ lev G (.grid (2 * ρ + 1) 0) := kv (2 * ρ + 1) (by omega) w hw κ hκ
        have hcomm : κ * h₂ = h₂ * κ := ((GlobalTheory.FinPl.localComponents D (· = w)).2 _).2.1 κ hκ.1 h₂ hh₂
        have e' : g * κ = (h₁ * κ) * h₂ := by rw [e, mul_assoc, ← hcomm, mul_assoc]
        have hc' := hcK κ hκl
        rw [e'] at hc'
        exact GlobalTheory.T.flatMapNonvanishingCondition_localise D W.ψ hψ _ _ _ _ ρ ρ (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) _ _ (· = w) (h₁ * κ) h₂
          (mul_mem hh₁ hκ.1) hh₂ hc'
      · intro h₁ hh₁ h₂ hh₂ e
        exact GlobalTheory.T.besselLevel_oneCoset_at_exceptionalPlaces D hQ T L μ0 hL sc G W M hM F hF ρ h h₁ hh₁
          (GlobalTheory.T.flatMapNonvanishingCondition_localise D W.ψ hψ _ _ _ _ ρ ρ (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) _ _ (fun v => v ∈ G.pl.S0) h₁ h₂ hh₁ hh₂
            (e ▸ hc))
    obtain ⟨hloc, hvac⟩ := loc_cls (F.dB ρ h) (F.dJ ρ h) s (xZero (F.dJ ρ h)) (F.dJ ρ h).e hx (yBF F ρ h) (pcBF W F ρ h)
      (latRow G (2 * ρ + 1)) (lev G (.grid (2 * ρ + 1) 0)) hψ hbase.1 hpIs hspl g0.1.1 g0.1.2.1 g0.1.2.2
      (fun f hf k hk => by rw [hs]; exact (cj (2 * ρ + 1) (by omega)).2.2.2.2.2.2 f hf k hk) hsupp
    exact ⟨_, _, hloc, hvac, GlobalTheory.T.boxDepthData_mul_lineVacua_besselLevel D hQ T L μ0 hL sc G W M hM F hF ρ h⟩
  · intro σ h h' s hs
    obtain ⟨x₀, hli, hx⟩ := xLast_rat (F.dB σ h') (F.oB σ h') (F.ζ (σ + 1)) (F.line (σ + 1))
    obtain ⟨hpIs, hspl⟩ := GlobalTheory.T.fourierJacobi_step_pieces_admissible_splits D hQ T L μ0 hL sc G W M hM F hF σ h h'
    have gd := GlobalTheory.T.standard_frames_successive_levels D hQ T L μ0 hL sc G W M hM F hF σ h h'
    have lat := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hQ T L μ0 hL sc G W M hM F hF).2.1 σ h'
    have g0 := gl (2 * σ + 2) (by omega)
    have hsupp : ∀ g, Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun _ => True) g →
        (∀ κ ∈ lev G (.grid (2 * σ + 2) 0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun _ => True) (g * κ)) →
        ∃ r ∈ Rgrp _ (xFB F σ h'), ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid (2 * σ + 2) 0), g = r * a * k := by
      intro g hc _
      refine g0.2 (Rgrp _ (xFB F σ h')) g ?_ ?_
      · intro w hw h₁ hh₁ h₂ hh₂ e
        obtain ⟨g1, g2⟩ := gd w hw
        exact GlobalTheory.T.fourierJacobiLevel_oneCoset_at_goodPlace D W.ψ hψ _ _ _ _ _ _ σ (F.dJ (σ + 1) h) (F.dB σ h') (F.oB σ h') (F.ζ (σ + 1)) (F.line (σ + 1))
          (pcFB W F σ h h') _ _ _ _ (G.Λ (.core (2 * σ + 2))) _ w g1 g2 (G.sp.P_is (2 * σ + 2) (by omega)).sd lat.2.2.1
          (lat.2.2.2 w) h₁ hh₁
          (GlobalTheory.T.flatMapNonvanishingCondition_localise D W.ψ hψ _ _ _ _ (σ + 1) σ (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') _ _ (· = w) h₁ h₂ hh₁ hh₂
            (e ▸ hc))
      · intro h₁ hh₁ h₂ hh₂ e
        exact GlobalTheory.T.one_coset_decomposition_statement D hQ T L μ0 hL sc G W M hM F hF σ h h' h₁ hh₁
          (GlobalTheory.T.flatMapNonvanishingCondition_localise D W.ψ hψ _ _ _ _ (σ + 1) σ (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') _ _ (fun v => v ∈ G.pl.S0)
            h₁ h₂ hh₁ hh₂ (e ▸ hc))
    obtain ⟨hloc, hvac⟩ := loc_cls (F.dJ (σ + 1) h) (F.dB σ h') s (xFB F σ h') x₀ hx 0 (pcFB W F σ h h')
      (latRow G (2 * σ + 2)) (lev G (.grid (2 * σ + 2) 0)) hψ hli hpIs hspl g0.1.1 g0.1.2.1 g0.1.2.2
      (fun f hf k hk => by rw [hs]; exact (cj (2 * σ + 2) (by omega)).2.2.2.2.2.2 f hf k hk) hsupp
    exact ⟨_, _, hloc, hvac, GlobalTheory.T.fourierJacobi_depthDatum_mul_lineVacuum_isVacuum D hQ T L μ0 hL sc G W M hM F hF σ h h'⟩

end GlobalTheory.AscFin.GoodStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardAuxiliaryFramesGoodRowGridsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAuxiliaryFrames_good_row_grids : GlobalTheory.SepRows.DepFixed → All fun {_} _ _ _ {G} W _ => ∀ (v : CoreVol G) (F : GlobalTheory.Asc.Frames G), Std F → F.Good v W (lineLat F) := by
  first | exact @GlobalTheory.AscFin.GoodStd.std_good | exact GlobalTheory.AscFin.GoodStd.std_good | (intros; apply GlobalTheory.AscFin.GoodStd.std_good <;> assumption)
end
