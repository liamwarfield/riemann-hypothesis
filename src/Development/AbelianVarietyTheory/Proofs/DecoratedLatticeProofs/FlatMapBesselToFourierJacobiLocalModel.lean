module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelIntegratesFreeEntries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesTranslations
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFreeEntryTranslationLawsBesselToJaco
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFlatMapLocalUnipotentTranslationLaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorValuesThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorValuesThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

namespace GlobalTheory.LocModTheta

theorem flat_model_theta : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ Ψ, IsThetaFunO ψ B.V₀ J.W₀ (L₀ Ψ) := by
  intro D _hFL hFlat _hOm k _ _ _ _ _ _ p ν hν ψ ψk hchar ρ B J st s _hs n n' _ _ _ _ c FA F₀ FV G₀ FW _hCore hBes _hJac Tm hTm L₀ hL Ψ
  have hstd : IsStdChar D ψ (-1) := st.weil.std
  have hcont : Continuous ψk := ((GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hstd).2.1 ψk hchar).1
  have hc : c = 2 * ρ := by have := hBes.1; omega
  obtain ⟨Φ₀, hΦ₀, hfl⟩ := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k ψk ν hcont hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  rw [← hL ⟨Φ₀, hΦ₀⟩ Ψ hfl.symm]
  exact ((hFlat ψ (fun _ => True)).1 ρ B J st).Heisenberg₂.theta (Tm ⟨Φ₀, hΦ₀⟩) (hTm.theta _)

end GlobalTheory.LocModTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorValuesThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFlatMap_factor_values_thetaFunctions : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ Ψ, IsThetaFunO ψ B.V₀ J.W₀ (L₀ Ψ) := by
  first | exact @GlobalTheory.LocModTheta.flat_model_theta | exact GlobalTheory.LocModTheta.flat_model_theta | (intros; apply GlobalTheory.LocModTheta.flat_model_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzLinearStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobiFlatSchwartz_linear : ∀ (D : D7), FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (f g : WO B.V J.W → ℂ) (a : ℂ), IsThetaFunO ψ B.V J.W f → IsThetaFunO ψ B.V J.W g → flatBF st (f + g) = flatBF st f + flatBF st g ∧ flatBF st (a • f) = a • flatBF st f := by
  exact @GlobalTheory.FlatLin.flatBF_linear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiFactorsLocalFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelAllNonFreeUnreadEntries
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelAllNonFreeUnreadEntries
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor.LowStage

section Shear
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

variable {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

end Shear

section Transv
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def tv (i j : Fin c) (h : i ≠ j) (a : k) : GL (Fin c) k :=
  ⟨transvection i j a, transvection i j (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

end Transv

section PiLocalization₂
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)

open Classical in
def evStage (i : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  (evAll n n' c ρ).filter fun e => ∀ q, e.2 = Sum.inr q → q.val ≤ i

variable {n n' c ρ}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

end PiLocalization₂

section
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ}

private theorem mem_evC_iff (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ _root_.GlobalTheory.FlatFactor.evC n n' c ρ ↔
      (∃ i : Fin (c + 1), e.2 = Sum.inr i ∧ (i : ℕ) < ρ ∧ ¬_root_.GlobalTheory.RootEx.Free (ρ + 1) e) ∨
        ∃ l : Fin c, e.1 = Sum.inr l ∧ ρ ≤ (l : ℕ) ∧ ∀ i : Fin (c + 1), e.2 = Sum.inr i → (i : ℕ) = ρ := by
  unfold _root_.GlobalTheory.FlatFactor.evC
  simp only [Finset.mem_filter_univ]

private theorem mem_evAll_iff (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ ↔
      ¬_root_.GlobalTheory.RootEx.Free (ρ + 1) e ∧ ¬_root_.GlobalTheory.FlatFactor.IsRead n n' c ρ e := by
  unfold _root_.GlobalTheory.FlatFactor.evAll
  simp only [Finset.mem_filter_univ]

private theorem evC_subset_evAll :
    _root_.GlobalTheory.FlatFactor.evC n n' c ρ ⊆ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ := by
  intro e hC
  rw [mem_evC_iff] at hC
  rw [mem_evAll_iff]
  obtain ⟨r | r, q | q⟩ := e <;>
    simp [_root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.FlatFactor.IsRead] at hC ⊢ <;> omega

private theorem mem_itB_iff (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ _root_.GlobalTheory.FlatFactor.itB n n' c ρ ↔
      _root_.GlobalTheory.RootEx.Free (ρ + 1) e ∧ ∀ i : Fin (c + 1), e.2 = Sum.inr i → ρ ≤ (i : ℕ) := by
  unfold _root_.GlobalTheory.FlatFactor.itB
  simp only [Finset.mem_filter_univ]

private theorem disjoint_evAll_itB :
    Disjoint (_root_.GlobalTheory.FlatFactor.evAll n n' c ρ) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) := by
  refine Finset.disjoint_left.mpr fun e h1 h2 => ?_
  rw [mem_evAll_iff] at h1
  rw [mem_itB_iff] at h2
  exact h1.1 h2.1

private theorem exists_inr_lt_le_of_mem_evAll_notMem_evC
    {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} (he : e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ)
    (hC : e ∉ _root_.GlobalTheory.FlatFactor.evC n n' c ρ) :
    ∃ (L : Fin c) (I : Fin (c + 1)), e = (Sum.inr L, Sum.inr I) ∧ ρ < (I : ℕ) ∧ (I : ℕ) ≤ L := by
  rw [mem_evAll_iff] at he
  rw [mem_evC_iff] at hC
  obtain ⟨r | r, q | q⟩ := e <;>
    simp [_root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.FlatFactor.IsRead] at he hC ⊢ <;> omega
end

variable {k : Type} [Field k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
private theorem embA_tv_eq_one_add_single (i j : Fin c) (h : i ≠ j) (a : k) :
    ((_root_.GlobalTheory.RootEx.embA n (_root_.GlobalTheory.FlatFactor.LowStage.tv i j h a) : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = 1 + single (Sum.inr i) (Sum.inr j) a := by
  simp only [_root_.GlobalTheory.RootEx.embA, _root_.GlobalTheory.FlatFactor.LowStage.tv]
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem comp_left_mul_mem_SB {m m' : Type} [Fintype m] [DecidableEq m]
    [Fintype m'] (A : GL m k) {Θ : Matrix m m' k → ℂ} (hΘ : Θ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix m m' k)) :
    (fun t => Θ ((A : Matrix m m k) * t)) ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix m m' k) := by
  obtain ⟨hlc, hcs⟩ := hΘ
  let φ : Matrix m m' k ≃ₜ Matrix m m' k :=
    { toFun := fun t => (A : Matrix m m k) * t
      invFun := fun t => ((A⁻¹ : GL m k) : Matrix m m k) * t
      left_inv := fun t => by
        simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      right_inv := fun t => by
        simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  exact ⟨hlc.comp_continuous φ.continuous, hcs.comp_homeomorph φ⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable [MeasurableSpace k] [BorelSpace k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
private theorem killsKernel_rowShear_invariant_lemma_10 (ν : Measure k) [ν.IsAddHaarMeasure]
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (l : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (ev : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (i₀ j : Fin c) (hρ : ρ ≤ (i₀ : ℕ))
    (hij : (i₀ : ℕ) < j)
    (hcov : ∀ e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ,
      (∀ q : Fin (c + 1), e.2 = Sum.inr q → (q : ℕ) ≤ i₀) → e ∈ ev)
    (hker : _root_.GlobalTheory.FlatFactor.KerRed ν ev (_root_.GlobalTheory.FlatFactor.itB n n' c ρ)
      (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l)
    (s : k) (Θ Θ' : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΘ' : ∀ t, (Θ' : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t =
      (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) ((1 + single (Sum.inr i₀) (Sum.inr j) s : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t)) :
    l Θ' = l Θ := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  haveI : T2Space k := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  set it := _root_.GlobalTheory.FlatFactor.itB n n' c ρ
  set β := _root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) with hβdef
  have key : ∀ t, _root_.GlobalTheory.FlatFactor.red ν ev it β
      ((Θ' - Θ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
        Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t = 0 := by
    intro t
    set X := _root_.GlobalTheory.FlatFactor.fill ev it β t with hXdef
    have hX : ∀ a r q, X a r q = if h : (r, q) ∈ it then a ⟨(r, q), h⟩ else if (r, q) ∈ ev then β r q else t r q :=
      fun _ _ _ => rfl
    have hXc : Continuous X := _root_.GlobalTheory.FlatFactor.continuous_fill ev it β t
    let f : ↥it → (↥it → k) → k := fun p a =>
      if p.1.1 = Sum.inr i₀ then s * X a (Sum.inr j) p.1.2 else 0
    let rk : ↥it → ℕ := fun p => Sum.elim (fun _ => 0) (fun r : Fin c => c - (r : ℕ)) p.1.1
    have hfm : ∀ p, Measurable (f p) := by
      intro p
      by_cases hp : p.1.1 = Sum.inr i₀
      · simp only [f, hp, if_true]
        exact (continuous_const.mul ((continuous_apply _).comp
          ((continuous_apply _).comp hXc))).measurable
      · simp only [f, hp, if_false]
        exact measurable_const
    have hfd : ∀ (p : ↥it) (x y : ↥it → k), (∀ q, rk q < rk p → x q = y q) → f p x = f p y := by
      intro p x y hxy
      by_cases hp : p.1.1 = Sum.inr i₀
      · simp only [f, hp, if_true, hX]
        split_ifs with h1 h2
        · congr 1
          apply hxy
          simp only [rk, hp, Sum.elim_inr]
          omega
        · rfl
        · rfl
      · simp only [f, hp, if_false]
    have hmp := _root_.GlobalTheory.SgLoc.TriShift.measurePreserving_triangular ν rk f hfm hfd
    have hshear : ∀ a, X (fun p => a p + f p a) = (1 + single (Sum.inr i₀) (Sum.inr j) s : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * X a := by
      intro a
      ext r q
      rw [_root_.Matrix.add_mul, _root_.Matrix.one_mul, _root_.Matrix.add_apply]
      by_cases hr : r = Sum.inr i₀
      · subst hr
        rw [single_mul_apply_same, hX, hX]
        by_cases hit : (Sum.inr i₀, q) ∈ it
        · simp only [hit, dite_true, f, if_true]
        · simp only [hit, dite_false]
          have hz : X a (Sum.inr j) q = 0 := by
            rw [mem_itB_iff] at hit
            have hnit : (Sum.inr j, q) ∉ it := by
              rw [mem_itB_iff]
              rcases q with q | q <;> simp [_root_.GlobalTheory.RootEx.Free] at hit ⊢ <;> omega
            have hev : (Sum.inr j, q) ∈ ev := by
              apply hcov
              · rw [mem_evAll_iff]
                rcases q with q | q <;> simp [_root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.FlatFactor.IsRead] at hit ⊢ <;> omega
              · intro q' hq'
                simp only at hq'
                subst hq'
                simp [_root_.GlobalTheory.RootEx.Free] at hit
                omega
            rw [hX, dite_eq_right hnit, if_pos hev]
            rcases q with q | q
            · simp [hβdef, _root_.GlobalTheory.RootEx.basePt]
            · simp [_root_.GlobalTheory.RootEx.Free] at hit
              simp [hβdef, _root_.GlobalTheory.RootEx.basePt] <;> omega
          rw [hz, mul_zero, add_zero]
      · rw [single_mul_apply_of_ne (h := hr), add_zero, hX, hX]
        split_ifs with h1 <;> simp [f, hr]
    have hI : ∀ Φ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
        Integrable (fun a => (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a))
          (Measure.pi fun _ => ν) := by
      intro Φ
      obtain ⟨hlc, hcs⟩ := Φ.2
      exact (hlc.continuous.comp hXc).integrable_of_hasCompactSupport
        (_root_.GlobalTheory.FlatFactor.hasCompactSupport_comp_fill ev it β t _ hcs)
    have hcomp : ∫ a, (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X (fun p => a p + f p a))
          ∂(Measure.pi fun _ => ν) =
        ∫ a, (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a) ∂(Measure.pi fun _ => ν) := by
      have hg' : AEStronglyMeasurable (fun a => (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a))
          (Measure.map (fun a p => a p + f p a) (Measure.pi fun _ => ν)) := by
        rw [hmp.map_eq]
        exact (hI Θ).aestronglyMeasurable
      calc _ = ∫ y, (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X y)
            ∂(Measure.map (fun a p => a p + f p a) (Measure.pi fun _ => ν)) :=
              (integral_map hmp.measurable.aemeasurable hg').symm
        _ = _ := by rw [hmp.map_eq]
    change ∫ a, ((Θ' - Θ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
      Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a) ∂(Measure.pi fun _ => ν) = 0
    simp only [Submodule.coe_sub, Pi.sub_apply]
    rw [integral_sub (hI Θ') (hI Θ), sub_eq_zero]
    simp only [hΘ', ← hshear]
    exact hcomp
  have h := hker (Θ' - Θ) key
  rw [map_sub, sub_eq_zero] at h
  exact h

variable {k : Type} [Field k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] in
private theorem twist_invariant_of_lowerEntry_lemma_4 (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] {M : Type} [AddCommGroup M] [Module ℂ M]
    (l : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hTw : _root_.GlobalTheory.FlatFactor.TwLaw ρ ψ l)
    (ev : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (L : Fin c) (I : Fin (c + 1))
    (hρI : ρ < (I : ℕ)) (hIL : (I : ℕ) ≤ L)
    (hcov : ∀ e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ,
      (∀ q : Fin (c + 1), e.2 = Sum.inr q → (q : ℕ) < I) → e ∈ ev)
    (hker : _root_.GlobalTheory.FlatFactor.KerRed ν ev (_root_.GlobalTheory.FlatFactor.itB n n' c ρ)
      (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l)
    (b : k) (Θ Θ' : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΘ' : ∀ t, (Θ' : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t =
      (ψ (b * (t (Sum.inr L) (Sum.inr I) -
        _root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) (Sum.inr L) (Sum.inr I))) : ℂ) *
        (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t) :
    l Θ' = l Θ := by
  set i₀ : Fin c := ⟨(I : ℕ) - 1, by omega⟩ with hi₀
  have hi₀v : (i₀ : ℕ) = (I : ℕ) - 1 := rfl
  have hi₀L : i₀ ≠ L := by
    intro h
    rw [Fin.ext_iff, hi₀v] at h
    omega
  have hsucc : i₀.succ = I := by
    ext
    rw [Fin.val_succ, hi₀v]
    omega
  set u := _root_.GlobalTheory.FlatFactor.LowStage.tv i₀ L hi₀L b with hu
  have hg : ((_root_.GlobalTheory.RootEx.embA n u : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = 1 + single (Sum.inr i₀) (Sum.inr L) b :=
    embA_tv_eq_one_add_single _ _ _ _
  have hginv : (((_root_.GlobalTheory.RootEx.embA n u)⁻¹ : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = 1 + single (Sum.inr i₀) (Sum.inr L) (-b) := by
    rw [← map_inv, show u⁻¹ = _root_.GlobalTheory.FlatFactor.LowStage.tv i₀ L hi₀L (-b) from Units.ext rfl]
    exact embA_tv_eq_one_add_single _ _ _ _
  have hmem : _root_.GlobalTheory.RootEx.embA n u ∈ _root_.GlobalTheory.RootEx.N k n c (ρ + 1) := by
    rw [_root_.GlobalTheory.RootEx.Model.mem_N_iff]
    intro r s hrs
    rw [hg, _root_.Matrix.add_apply, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    simp [_root_.GlobalTheory.RootEx.lev] at hrs
    omega
  have hblock : ∀ i j : Fin c, (i : ℕ) < ρ → ρ ≤ (j : ℕ) →
      (u : Matrix (Fin c) (Fin c) k) i j = 0 := by
    intro i j hi hj
    have hne : i ≠ j := by
      intro h
      subst h
      omega
    have hne' : i ≠ i₀ := by
      intro h
      rw [Fin.ext_iff, hi₀v] at h
      omega
    simp [hu, _root_.GlobalTheory.FlatFactor.LowStage.tv, Matrix.transvection, Matrix.one_apply, hne,
      Matrix.single_apply, hne', Ne.symm hne']
  obtain ⟨Θu, hΘu⟩ : ∃ Θu : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      ∀ t, (Θu : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t =
        (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
          ((((_root_.GlobalTheory.RootEx.embA n u)⁻¹ : GL (n ⊕ Fin c) k) :
            Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) :=
    ⟨⟨_, comp_left_mul_mem_SB _ Θ.2⟩, fun _ => rfl⟩
  set β := _root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) (Sum.inr L) (Sum.inr I) with hβ
  have hchar : ∀ t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k,
      _root_.GlobalTheory.RootEx.ch (((_root_.GlobalTheory.RootEx.embA n u : GL (n ⊕ Fin c) k) :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) - _root_.GlobalTheory.RootEx.ch t =
        b * t (Sum.inr L) (Sum.inr I) := by
    intro t
    rw [hg, _root_.Matrix.add_mul, _root_.Matrix.one_mul]
    simp only [_root_.GlobalTheory.RootEx.ch, _root_.Matrix.add_apply, Finset.sum_add_distrib,
      add_sub_cancel_left]
    rw [Fintype.sum_eq_single i₀, single_mul_apply_same, hsucc]
    intro i hi
    exact single_mul_apply_of_ne (h := by simpa using hi) ..
  have hI' : (I : ℕ) = (i₀ : ℕ) + 1 := by
    rw [hi₀v]
    omega
  have hlt : (i₀ : ℕ) < L := by omega
  have hβv : β = if (L : ℕ) = (i₀ : ℕ) + 1 then 1 else 0 := by
    rw [hβ]
    simp [_root_.GlobalTheory.RootEx.basePt, hI']
  have hsum : _root_.GlobalTheory.RootEx.simpleSum (_root_.GlobalTheory.RootEx.embA n u) = b * β := by
    unfold _root_.GlobalTheory.RootEx.simpleSum
    rw [hg, hβv, Fintype.sum_eq_single i₀, Fintype.sum_eq_single L]
    · by_cases h : (L : ℕ) = (i₀ : ℕ) + 1 <;>
        simp [h, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff] <;> omega
    · intro j hj
      by_cases h : (j : ℕ) = (i₀ : ℕ) + 1 <;>
        simp [h, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hj] <;> omega
    · intro i hi
      apply Finset.sum_eq_zero
      intro j _
      by_cases h : (j : ℕ) = (i : ℕ) + 1 <;>
        simp [h, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hi] <;> omega
  have hTw' := hTw u hmem hblock Θ Θu ((ψ (b * β) : ℂ) • Θ') hΘu (by
    intro t
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΘ', hchar, ← mul_assoc, ← Circle.coe_mul,
      ← AddChar.map_add_eq_mul,
      show b * β + b * (t (Sum.inr L) (Sum.inr I) - β) = b * t (Sum.inr L) (Sum.inr I) by ring])
  have hinv : l Θu = l Θ :=
    killsKernel_rowShear_invariant_lemma_10 ν l ev i₀ L (by omega) (by omega)
      (fun e he hcol => hcov e he fun q hq => by have := hcol q hq; omega) hker (-b) Θ Θu
      (fun t => by rw [hΘu, hginv])
  rw [hinv, map_smul, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, hsum, neg_add_cancel,
    AddChar.map_zero_eq_one, Circle.coe_one, one_smul] at hTw'
  exact hTw'.symm

theorem _root_.GlobalTheory.FlatFactor.LowStage.kerRed_evAll : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → _root_.GlobalTheory.FlatFactor.TwLaw ρ ψ l → _root_.GlobalTheory.FlatFactor.KerRed ν (_root_.GlobalTheory.FlatFactor.evC n n' c ρ) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l → _root_.GlobalTheory.FlatFactor.KerRed ν (_root_.GlobalTheory.FlatFactor.evAll n n' c ρ) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ l _ hTw hC
  haveI := hν
  have hstage_sub : ∀ j, _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j ⊆
      _root_.GlobalTheory.FlatFactor.evAll n n' c ρ := fun j => Finset.filter_subset _ _
  have hmem_stage : ∀ (j : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))),
      e ∈ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j ↔
        e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ ∧
          ∀ q : Fin (c + 1), e.2 = Sum.inr q → (q : ℕ) ≤ j := fun j e => Finset.mem_filter
  have hsub : ∀ j, _root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j ⊆
      _root_.GlobalTheory.FlatFactor.evAll n n' c ρ :=
    fun j => Finset.union_subset evC_subset_evAll (hstage_sub j)
  have hdisj : ∀ j, Disjoint (_root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪
      _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) :=
    fun j => disjoint_evAll_itB.mono_left (hsub j)
  have hstep : ∀ j, _root_.GlobalTheory.FlatFactor.KerRed ν
      (_root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j)
      (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l := by
    intro j
    induction j with
    | zero =>
      refine _root_.GlobalTheory.FlatFactor.KerRedStep.kerRed_extend k ψ ν hψ hψ1 hν _ _ M l _ _ _ _ _
        Finset.subset_union_left Finset.Subset.rfl (hdisj 0) hC ?_ (fun e h1 h2 => absurd h1 h2)
      intro e he heC
      exfalso
      rcases Finset.mem_union.1 he with h | h
      · exact heC h
      obtain ⟨L, I, rfl, hρI, hIL⟩ := exists_inr_lt_le_of_mem_evAll_notMem_evC (hstage_sub 0 h) heC
      have := ((hmem_stage 0 _).1 h).2 I rfl
      omega
    | succ j ih =>
      refine _root_.GlobalTheory.FlatFactor.KerRedStep.kerRed_extend k ψ ν hψ hψ1 hν _ _ M l _ _ _ _ _ ?_
        Finset.Subset.rfl (hdisj (j + 1)) ih ?_ (fun e h1 h2 => absurd h1 h2)
      · refine Finset.union_subset_union Finset.Subset.rfl fun e he => (hmem_stage _ e).2
          ⟨((hmem_stage _ e).1 he).1, fun q hq => ?_⟩
        have := ((hmem_stage _ e).1 he).2 q hq
        omega
      intro e he hne
      have heC : e ∉ _root_.GlobalTheory.FlatFactor.evC n n' c ρ := fun h => hne (Finset.mem_union_left _ h)
      have hest : e ∈ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ (j + 1) := by
        rcases Finset.mem_union.1 he with h | h
        · exact absurd h heC
        · exact h
      obtain ⟨L, I, rfl, hρI, hIL⟩ := exists_inr_lt_le_of_mem_evAll_notMem_evC (hstage_sub _ hest) heC
      have hI1 : (I : ℕ) ≤ j + 1 := ((hmem_stage _ _).1 hest).2 I rfl
      have hI2 : ¬ (I : ℕ) ≤ j := fun h => hne (Finset.mem_union_right _ ((hmem_stage _ _).2
        ⟨hstage_sub _ hest, fun q hq => by
          have hqI := Sum.inr_injective hq
          subst hqI
          exact h⟩))
      intro b Θ Θ' hΘ'
      exact twist_invariant_of_lowerEntry_lemma_4 ψ ν l hTw _ L I hρI hIL
        (fun e' he' hcol => Finset.mem_union_right _ ((hmem_stage _ _).2 ⟨he', fun q hq => by
          have := hcol q hq
          omega⟩)) ih b Θ Θ' hΘ'
  have hall : _root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ c =
      _root_.GlobalTheory.FlatFactor.evAll n n' c ρ := by
    apply Finset.Subset.antisymm (hsub c)
    intro e he
    exact Finset.mem_union_right _ ((hmem_stage _ _).2 ⟨he, fun q _ => Nat.lt_succ_iff.1 q.2⟩)
  rw [← hall]
  exact hstep c

end GlobalTheory.FlatFactor.LowStage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelAllNonFreeUnreadEntriesStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatFactorReduction_kernel_all_nonFreeUnread_entries : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → GlobalTheory.FlatFactor.TwLaw ρ ψ l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evC n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l := by
  first | exact @GlobalTheory.FlatFactor.LowStage.kerRed_evAll | exact GlobalTheory.FlatFactor.LowStage.kerRed_evAll | (intros; apply GlobalTheory.FlatFactor.LowStage.kerRed_evAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqZeroOfFlatMapColumnZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqZeroOfFlatMapColumnZero
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.FlatRed
open GlobalTheory.FlatFactor GlobalTheory.LocFlat

theorem integral_pi_subtype_iff {k α : Type} [MeasurableSpace k] {P Q : α → Prop} {i1 : Fintype (Subtype P)}
    {i2 : Fintype (Subtype Q)} (h : ∀ a, P a ↔ Q a) (ν : Measure k) (F : (Subtype P → k) → ℂ)
    (G : (Subtype Q → k) → ℂ) (hFG : ∀ a, F a = G (fun e => a ⟨e.1, (h e.1).2 e.2⟩)) :
    ∫ a, F a ∂(Measure.pi fun _ => ν) = ∫ e, G e ∂(Measure.pi fun _ => ν) := by
  obtain rfl : P = Q := funext fun a => propext (h a)
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  obtain rfl : F = G := funext hFG
  rfl

def readPart {k : Type} {n n' : Type} {c : ℕ} (ρ : ℕ) (h : ρ < c + 1)
    (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix n (n' ⊕ Unit) k :=
  Matrix.of fun r q => Sum.elim (fun s => t (.inl r) (.inl s)) (fun _ => t (.inl r) (.inr ⟨ρ, h⟩)) q

section
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_itFree (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) : e ∈ itFree n n' c ρ ↔ Free (ρ + 1) e := by
  simp [itFree]

theorem mem_evAll (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ evAll n n' c ρ ↔ ¬ Free (ρ + 1) e ∧ ¬ IsRead n n' c ρ e := by
  simp [evAll]

variable {k : Type} [Field k]

theorem fill_eq (ρ : ℕ) (h : ρ < c + 1) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (a : {e // e ∈ itFree n n' c ρ} → k) :
    fill (evAll n n' c ρ) (itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) t a =
      affPt (ρ + 1) (readPart ρ h t).toCols₁ (fun e => a ⟨e.1, (mem_itFree ρ e.1).2 e.2⟩) +
        colAt n' c (ρ + 1) (fun r => readPart ρ h t r (Sum.inr ())) := by
  ext r q
  simp only [fill, affPt, Matrix.of_apply, Matrix.add_apply]
  by_cases hF : Free (ρ + 1) (r, q)
  · rw [dite_eq_left ((mem_itFree ρ _).2 hF), dite_eq_left hF]
    rcases r with r | l <;> rcases q with s | i
    · exact hF.elim
    · have h1 : ρ + 1 < i.val + 1 := hF
      have h2 : i.val ≠ ρ := by omega
      simp [basePt, colAt, h2]
    · simp [basePt, colAt]
    · have h1 : l.val < i.val := hF
      have h2 : l.val ≠ i.val := by omega
      simp [basePt, colAt, h2]
  · rw [dite_eq_right (fun hh => hF ((mem_itFree ρ _).1 hh)), dite_eq_right hF]
    by_cases hR : IsRead n n' c ρ (r, q)
    · rw [if_neg (fun hh => ((mem_evAll ρ _).1 hh).2 hR)]
      rcases r with r | l <;> rcases q with s | i
      · simp [basePt, colAt, readPart]
      · have h1 : i.val = ρ := hR
        obtain rfl : i = ⟨ρ, h⟩ := Fin.ext h1
        simp [basePt, colAt, readPart]
      · exact hR.elim
      · exact hR.elim
    · rw [if_pos ((mem_evAll ρ _).2 ⟨hF, hR⟩)]
      rcases r with r | l <;> rcases q with s | i
      · exact (hR trivial).elim
      · have h1 : i.val ≠ ρ := hR
        simp [basePt, colAt, h1]
      · simp [basePt, colAt]
      · simp [basePt, colAt]

theorem ch_add_colAt (p : ℕ) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : n → k) :
    ch (z + colAt n' c p y) = ch z := by
  simp [ch, colAt]

end

theorem red_eq_zero_of_flCol : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ → ∀ Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, (∀ x, GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ x = 0) → ∀ t, GlobalTheory.FlatFactor.red ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) (fun t => (ψ (-ch t) : ℂ) * Φ t) t = 0 := by
  intro k _ _ _ _ _ _ ψ ν n n' _ _ _ _ c ρ hc Φ hΦ t
  have h : ρ < c + 1 := by omega
  rw [← hΦ (readPart ρ h t)]
  unfold red flCol opE
  refine integral_pi_subtype_iff (mem_itFree ρ) ν _ _ fun a => ?_
  beta_reduce
  rw [fill_eq ρ h t a, ch_add_colAt, mul_comm]

end GlobalTheory.FlatRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqZeroOfFlatMapColumnZeroStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_eq_zero_of_flatMapColumn_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ → ∀ Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, (∀ x, GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ x = 0) → ∀ t, GlobalTheory.FlatFactor.red ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) (fun t => (ψ (-ch t) : ℂ) * Φ t) t = 0 := by
  first | exact @GlobalTheory.FlatRed.red_eq_zero_of_flCol | exact GlobalTheory.FlatRed.red_eq_zero_of_flCol | (intros; apply GlobalTheory.FlatRed.red_eq_zero_of_flCol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFactorThroughFlatMapFourierJacobiColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFactorThroughFlatMapFourierJacobiColumn
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LocFlat

section Lin
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

open Classical in
theorem flCol_integrand_integrable (ψ : AddChar k Circle) (hψ : Continuous ψ) (ν : Measure k)
    (hν : ν.IsAddHaarMeasure) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x : Matrix n (n' ⊕ Unit) k) :
    Integrable (fun e => Φ (ptCol p x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))
      (Measure.pi fun _ => ν) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have := GlobalTheory.SplitWeil.secondCountable k
  have := hν
  have hemb : Topology.IsClosedEmbedding (fun e => ptCol (c := c) p x e) := by
    have hslice : Topology.IsClosedEmbedding (Prod.mk x.toCols₁ :
        ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → _) :=
      Function.LeftInverse.isClosedEmbedding (f := Prod.snd) (fun _ => rfl)
        continuous_snd (Continuous.prodMk_right x.toCols₁)
    exact (Homeomorph.addRight (colAt n' c p fun r => x r (Sum.inr ()))).isClosedEmbedding.comp
      ((isClosedEmbedding_affPt_uncurry p).comp hslice)
  have hch : Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k =>
      ((ψ (-ch (affPt p (0 : Matrix n n' k) e)) : Circle) : ℂ) := by
    refine continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_))
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_affPt_uncurry p).comp (Continuous.prodMk_right (0 : Matrix n n' k))).matrix_elem _ _
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hΦ.1.continuous.comp hemb.continuous).mul hch
  · exact (hΦ.2.comp_isClosedEmbedding hemb).mul_right

theorem flCol_add_of_SB (ψ : AddChar k Circle) (hψ : Continuous ψ) (ν : Measure k)
    (hν : ν.IsAddHaarMeasure) (p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (h₁ : Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (h₂ : Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    flCol ψ ν p (Φ₁ + Φ₂) = flCol ψ ν p Φ₁ + flCol ψ ν p Φ₂ := by
  funext x
  simp only [flCol_eq_integral, Pi.add_apply, add_mul]
  exact integral_add (flCol_integrand_integrable ψ hψ ν hν p Φ₁ h₁ x)
    (flCol_integrand_integrable ψ hψ ν hν p Φ₂ h₂ x)

theorem flCol_smul (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (a : ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) :
    flCol ψ ν p (a • Φ) = a • flCol ψ ν p Φ := by
  funext x
  simp only [flCol_eq_integral, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

end Lin

theorem flCol_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), (∀ x, GlobalTheory.LocFlat.flCol ψ ν p Φ.1 x = 0) → L Φ = 0) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν p Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1 hpc M _ _ L hL
  have hSB := (flat_SB_onto k ψ ν hψ hν n n' c p hp1).1 hpc
  let F : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) :=
    { toFun := fun Φ => ⟨flCol ψ ν p Φ.1, hSB.1 Φ.1 Φ.2⟩
      map_add' := fun Φ₁ Φ₂ => Subtype.ext (flCol_add_of_SB ψ hψ ν hν p Φ₁.1 Φ₂.1 Φ₁.2 Φ₂.2)
      map_smul' := fun a Φ => Subtype.ext (flCol_smul ψ ν p a Φ.1) }
  have hFs : Function.Surjective F := fun Ψ => by
    obtain ⟨Φ, hΦ, h⟩ := hSB.2 Ψ.1 Ψ.2
    exact ⟨⟨Φ, hΦ⟩, Subtype.ext h⟩
  have hker : LinearMap.ker F ≤ LinearMap.ker L := fun Φ hΦ => by
    rw [LinearMap.mem_ker] at hΦ ⊢
    apply hL
    intro x
    have := congrArg (fun Ψ : SB (Matrix n (n' ⊕ Unit) k) => Ψ.1 x) hΦ
    simpa [F] using this
  refine ⟨((LinearMap.ker F).liftQ L hker).comp (F.quotKerEquivOfSurjective hFs).symm.toLinearMap, ?_⟩
  intro Φ Ψ hΨ
  have hΨF : Ψ = F Φ := Subtype.ext hΨ
  subst hΨF
  have h2 : (F.quotKerEquivOfSurjective hFs).symm (F Φ) = Submodule.Quotient.mk Φ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h2]
  rfl

end GlobalTheory.LocFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFactorThroughFlatMapFourierJacobiColumnStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_flatMapFourierJacobiColumn : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), (∀ x, GlobalTheory.LocFlat.flCol ψ ν p Φ.1 x = 0) → L Φ = 0) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν p Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.LocFlat.flCol_factor | exact GlobalTheory.LocFlat.flCol_factor | (intros; apply GlobalTheory.LocFlat.flCol_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiFactorsLocalFlat
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.FlatFactor

theorem ch_add_mat {k : Type} [Field k] {n n' : Type} {c : ℕ} (a b : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch (a + b) = ch a + ch b := by
  simp [ch, Finset.sum_add_distrib]

theorem continuous_ch {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n n' : Type} {c : ℕ} :
    Continuous (ch : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → k) :=
  continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

theorem kerRed_empty {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) (β : Matrix m m' k)
    (l : SB (Matrix m m' k) →ₗ[ℂ] M) : KerRed ν ∅ ∅ β l := by
  intro Θ h
  have hΘ : Θ = 0 := by
    ext t
    have ht := h t
    simp only [red] at ht
    haveI : IsEmpty {e : m × m' // e ∈ (∅ : Finset (m × m'))} := ⟨fun e => Finset.notMem_empty _ e.2⟩
    rw [Measure.pi_of_empty (x := isEmptyElim), integral_dirac] at ht
    have hf : fill ∅ ∅ β t isEmptyElim = t := by ext r q; simp [fill]
    rw [hf] at ht
    simpa using ht
  rw [hΘ, map_zero]

theorem mem_SB_addChar_mul (ψ : AddChar k Circle) (hψ : Continuous ψ) {X : Type} [TopologicalSpace X]
    (f : X → k) (hf : Continuous f) (Θ : X → ℂ) (hΘ : Θ ∈ SB X) :
    (fun t => (ψ (f t) : ℂ) * Θ t) ∈ SB X :=
  ⟨((GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous hf).mul hΘ.1,
    hΘ.2.mul_left⟩

end

end GlobalTheory.FlatFactor

open GlobalTheory.FlatFactor in
theorem GlobalTheory.FlatFactor.flCol_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν n n' _ _ _ _ c ρ M _ _ L hc H1 H2 H3 H4
  set Mt := Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k
  set β : Mt := basePt c (0 : Matrix n n' k)
  have tw : ∀ (f : Mt → k), Continuous f → ∀ Θ : SB Mt, (fun t => (ψ (f t) : ℂ) * Θ.1 t) ∈ SB Mt :=
    fun f hf Θ => mem_SB_addChar_mul ψ hψc f hf Θ.1 Θ.2
  let T : SB Mt → SB Mt := fun Θ => ⟨fun t => (ψ (ch t) : ℂ) * Θ.1 t, tw _ continuous_ch Θ⟩
  let L' : SB Mt →ₗ[ℂ] M :=
    { toFun := fun Θ => L (T Θ)
      map_add' := fun Θ₁ Θ₂ => by
        show L (T (Θ₁ + Θ₂)) = L (T Θ₁) + L (T Θ₂)
        rw [← map_add (f := _)]; congr 1; apply Subtype.ext; funext t
        show (ψ (ch t) : ℂ) * (Θ₁.1 t + Θ₂.1 t) = (ψ (ch t) : ℂ) * Θ₁.1 t + (ψ (ch t) : ℂ) * Θ₂.1 t
        ring
      map_smul' := fun a Θ => by
        show L (T (a • Θ)) = a • L (T Θ)
        rw [← map_smul]; congr 1; apply Subtype.ext; funext t
        show (ψ (ch t) : ℂ) * (a * Θ.1 t) = a * ((ψ (ch t) : ℂ) * Θ.1 t)
        ring }
  have hL' : ∀ Θ, L' Θ = L (T Θ) := fun _ => rfl

  have hTw : TwLaw ρ ψ L' := by
    intro u hN hblk Θ Θ' Θ'' h' h''
    rw [hL', hL']
    have := H4 u hN hblk (T Θ'') (T Θ') (fun t => by
      simp only [T, h', h'']
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3; ring)
    exact this

  have hS1 : KerRed ν (evC n n' c ρ) (itB n n' c ρ) β L' := by
    refine GlobalTheory.T.kernelReduction_extend_evaluated_integrated k ψ ν hψc hψ1 hν _ _ M L' β ∅ ∅ _ _ (Finset.empty_subset _) (Finset.empty_subset _) ?_
      (kerRed_empty ν β L') ?_ ?_
    · rw [Finset.disjoint_left]
      rintro ⟨r, q⟩ h1 h2
      simp only [evC, itB, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with ⟨i, hq, -, hfr⟩ | ⟨l, hr, hl, hq⟩
      · exact hfr h2.1
      · subst hr
        rcases q with q | q
        · simp [Free] at h2; omega
        · have := hq q rfl; simp [Free] at h2; omega
    · rintro ⟨r, q⟩ he - b Θ Θ' hΘ
      simp only [evC, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [hL', hL']
      rcases he with he | he
      · exact H1 r q he b (T Θ) (T Θ') (fun t => by simp only [T, hΘ]; ring)
      · exact H2 r q he b (T Θ) (T Θ') (fun t => by simp only [T, hΘ]; ring)
    · rintro ⟨r, q⟩ he - a Θ Θ' hΘ
      simp only [itB, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [hL', hL']
      set E : Mt := Matrix.single r q a
      let Φ' : SB Mt := ⟨fun t => (ψ (ch (t + E)) : ℂ) * Θ'.1 t, tw _ (continuous_ch.comp (continuous_add_const E)) Θ'⟩
      have h3 := H3 r q he.1 he.2 a (T Θ) Φ' (fun t => by
        show (ψ (ch (t + E)) : ℂ) * Θ'.1 t = (ψ (ch (t + E)) : ℂ) * Θ.1 (t + E)
        rw [hΘ])
      have hT : T Θ' = (ψ (-ch E) : ℂ) • Φ' := by
        ext t
        show (ψ (ch t) : ℂ) * Θ'.1 t = (ψ (-ch E) : ℂ) * ((ψ (ch (t + E)) : ℂ) * Θ'.1 t)
        have hm : ∀ x y : k, (ψ x : ℂ) * ψ y = ψ (x + y) := by
          intro x y; rw [AddChar.map_add_eq_mul, Circle.coe_mul]
        rw [← mul_assoc, hm, ch_add_mat, show -ch E + (ch t + ch E) = ch t by ring]
      rw [hT, map_smul, h3, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
  have hS2 := GlobalTheory.T.flatFactorReduction_kernel_all_nonFreeUnread_entries k ψ ν hψc hψ1 hν n n' c ρ M L' hc hTw hS1
  have hS3 := GlobalTheory.T.flatFactorReduction_kernel_integrates_free_entries k ψ ν hψc hψ1 hν n n' c ρ M L' hc hTw hS2
  refine GlobalTheory.T.exists_factor_through_flatMapFourierJacobiColumn k ψ ν hψc hν n n' c (ρ + 1) (by omega) (by omega) M L ?_
  intro Φ hΦ
  let Θ : SB Mt := ⟨fun t => (ψ (-ch t) : ℂ) * Φ.1 t, tw _ continuous_ch.neg Φ⟩
  have hΘ : T Θ = Φ := by
    ext t
    simp only [T, Θ]
    rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
      Circle.coe_one, one_mul]
  have := hS3 Θ (GlobalTheory.T.partialReduction_eq_zero_of_flatMapColumn_zero k ψ ν n n' c ρ hc Φ.1 hΦ)
  rw [hL', hΘ] at this
  exact this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiFactorsLocalFlatStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_fourierJacobi_factors_local_flat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.FlatFactor.flCol_factor | exact GlobalTheory.FlatFactor.flCol_factor | (intros; apply GlobalTheory.FlatFactor.flCol_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatBFLoc

theorem flatBF_of_laws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatBF D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hψk ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW hco hbe hja Tm hTm
  obtain ⟨hcont, hne⟩ := (GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ st.weil.std).2.1 ψk hψk
  have hc : c = 2 * ρ := by have := hbe.1; omega
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ) :=
    { toFun := fun Φ => flatBF st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add (f := _)]
        exact (GlobalTheory.T.besselToJacobiFlatSchwartz_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ') 1 (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (GlobalTheory.T.besselToJacobiFlatSchwartz_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ) a (hTm.theta Φ) (hTm.theta Φ)).2 }
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.flatMap_fourierJacobi_factors_local_flat k ψk ν hcont hne hν n n' c ρ (WO B.V₀ J.W₀ → ℂ) L hc
    (GlobalTheory.T.localFlatMap_dualColumn_multiplicationLaws D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (GlobalTheory.T.flat_bessel_to_fourierJacobi_row_mul_laws D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (GlobalTheory.T.localFlatMap_freeEntry_translationLaws_besselToJacobi D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (GlobalTheory.T.besselFlatMap_local_unipotent_translation_law D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
  have hL : ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ := hL₀
  refine ⟨L₀, ⟨?_, ?_, ?_⟩, hL⟩
  · exact GlobalTheory.T.localFlatMap_factor_values_thetaFunctions D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact GlobalTheory.T.localFlatMap_factor_intertwines_translations D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact GlobalTheory.T.localFlatMap_factor_intertwines_multiplication D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL

end GlobalTheory.FlatBFLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_besselToFourierJacobi_localModel : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatBF D := by
  first | exact @GlobalTheory.FlatBFLoc.flatBF_of_laws | exact GlobalTheory.FlatBFLoc.flatBF_of_laws | (intros; apply GlobalTheory.FlatBFLoc.flatBF_of_laws <;> assumption)
end
