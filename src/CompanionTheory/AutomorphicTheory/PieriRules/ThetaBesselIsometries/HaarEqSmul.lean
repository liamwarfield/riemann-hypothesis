module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsFunctional
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselDegree

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem haar_eq_smul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsUnit P.det)
    (hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hν : PI.BesselPeriodGGP.IsHaarOn (GG k r) ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν = c • (Formalism.REAL.muG ε).map (phi ε P) := _root_.GlobalTheory.BesselDegree.haar_eq_smul (k := k) (r := r) (ε := ε) (P := P) hP hH ν hν

theorem schur_fdeg : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → ∃ c : ℝ, 0 < c ∧ ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * Formalism.QuantumDeterminants.fdegHC mu) ∧ ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
  intro hy k r ε μG hμ
  have hHC : HCFdegG := hy.2.2.2.2.2.2
  by_cases hQ : ∃ Q, PI.UpqRep.IsCayleyU k r ε Q
  swap
  · refine ⟨1, one_pos, fun mu R hR => absurd ?_ hQ⟩
    obtain ⟨Q, hQ, -⟩ := hR.2
    exact ⟨Q, hQ⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hP : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hH : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  obtain ⟨a, ha0, hat, ha⟩ := haar_eq_smul hP hH μG hμ
  obtain ⟨c, hc, hF⟩ := hHC k r ε ⟨Q, hQ⟩
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hme : MeasurableEmbedding (phi ε Q) :=
    (phi_closedEmbedding (ε := ε) Formalism.REAL.isClosedEmbeddingMatrix hP).measurableEmbedding
  refine ⟨c / a.toReal, div_pos hc hapos, fun mu R hR => ?_⟩
  have hDS := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hR Q hQ
  obtain ⟨hd, hS⟩ := hF mu R.H _ hR.3 hR.1 hDS
  have hd' : 0 < c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu := by
    rw [div_mul_eq_mul_div]; exact div_pos hd hapos
  have key : ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
    intro v w v' w'
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [ha]
    constructor
    · refine Integrable.smul_measure ?_ hat
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, R.σ (Matrix.of (phi ε Q g)) v⟫_ℂ * star ⟪w', R.σ (Matrix.of (phi ε Q g)) v'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := h2
      rw [h3, div_mul_eq_mul_div, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  exact ⟨fun w hw => Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd' key hw, key⟩

end GlobalTheory.BesselDegree
end
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosure
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosure
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SmMapAct

open PI.UpqRep

variable {k r : ℕ}

def SemiBd (R : Rep k r) (f : R.H → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), 0 ≤ C ∧ (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ R.sm, f v ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

theorem sum_norm_nonneg (R : Rep k r) (Ws : List (List (Mx k r))) (v : R.H) :
    0 ≤ (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
  exact norm_nonneg _

theorem semiBd_of_cw {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp}
    (h : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B) : SemiBd R (fun v => ‖B v‖) := by
  obtain ⟨C, Ws, h1, h2⟩ := h
  exact ⟨max C 0, Ws, le_max_right _ _, h1, fun v hv => (h2 v hv).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sum_norm_nonneg R Ws v))⟩

theorem cw_of_semiBd {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp} {f : R.H → ℝ}
    (h : SemiBd R f) (hle : ∀ v ∈ R.sm, ‖B v‖ ≤ f v) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B := by
  obtain ⟨C, Ws, _, h1, h2⟩ := h
  exact ⟨C, Ws, h1, fun v hv => (hle v hv).trans (h2 v hv)⟩

theorem SemiBd.add {R : Rep k r} {f g : R.H → ℝ} (hf : SemiBd R f) (hg : SemiBd R g) :
    SemiBd R (fun v => f v + g v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  obtain ⟨C', Ws', h0', h1', h2'⟩ := hg
  refine ⟨C + C', Ws ++ Ws', add_nonneg h0 h0', ?_, fun v hv => ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact h1 w h
    · exact h1' w h
  · have a := h2 v hv
    have b := h2' v hv
    have c := sum_norm_nonneg R Ws v
    have d := sum_norm_nonneg R Ws' v
    rw [List.map_append, List.sum_append]
    nlinarith [mul_nonneg h0 d, mul_nonneg h0' c]

theorem SemiBd.mul {R : Rep k r} {f : R.H → ℝ} (hf : SemiBd R f) {a : ℝ} (ha : 0 ≤ a) :
    SemiBd R (fun v => a * f v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  refine ⟨a * C, Ws, mul_nonneg ha h0, h1, fun v hv => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 v hv) ha

theorem semiBd_sum {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) (Ws : List (List (Mx k r)))
    (hWs : ∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) :
    SemiBd R (fun v => (Ws.map fun w => ‖dsigW (k := k) (r := r) R'.σ w (T v)‖).sum) := by
  induction Ws with
  | nil => exact ⟨0, [], le_rfl, by simp, fun v _ => by simp⟩
  | cons w Ws ih =>
    have h1 := semiBd_of_cw R (hT.cont w (hWs w List.mem_cons_self))
    have h2 := ih (fun w' hw' => hWs w' (List.mem_cons_of_mem _ hw'))
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

theorem cw_comp {Wp : Type} [NormedAddCommGroup Wp] {R R' : Rep k r} {T : R.H → R'.H} {Bm : R'.H → Wp}
    (hT : SmMap R R' T) (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := semiBd_of_cw R' hB
  exact cw_of_semiBd R ((semiBd_sum hT Ws h1).mul h0) (fun v hv => h2 _ (hT.mem v hv))

theorem smMap_comp {R R' R'' : Rep k r} {T : R.H → R'.H} {T' : R'.H → R''.H}
    (hT : SmMap R R' T) (hT' : SmMap R' R'' T') : SmMap R R'' (fun v => T' (T v)) := by
  refine ⟨fun v hv => hT'.mem _ (hT.mem v hv), ?_, ?_, ?_⟩
  · intro v hv w hw
    rw [hT.add v hv w hw, hT'.add _ (hT.mem v hv) _ (hT.mem w hw)]
  · intro a v hv
    rw [hT.smul a v hv, hT'.smul a _ (hT.mem v hv)]
  · intro W hW
    exact cw_comp (Bm := fun v => dsigW (k := k) (r := r) R''.σ W (T' v)) hT (hT'.cont W hW)

section DS

variable {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}

theorem dsigW_mem (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W v ∈ R.sm := by
  induction W with
  | nil => exact hv
  | cons X W ih =>
    exact ((GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X (hW X List.mem_cons_self)).1 _
      (ih (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)))).1

theorem dsig_lin (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ)
    {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (a • v + w) =
      a • dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ X w := by
  have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X hX).1
  have h1 := ((h v hv).2.const_smul a).add (h w hw).2
  refine HasDerivAt.deriv ?_
  convert h1 using 1
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul]

theorem dsigW_lin (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) (a : ℂ) {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v + w) =
      a • dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    show dsig R.σ X (dsigW R.σ W (a • v + w)) = _
    rw [ih hW']
    exact dsig_lin hK hR (hW X List.mem_cons_self) a (dsigW_mem hK hR W hW' hv) (dsigW_mem hK hR W hW' hw)

theorem inLie_conj {g X : Mx k r} (hg : g ∈ GG k r) (hX : InLieHpk k r X) : InLieHpk k r (g⁻¹ * X * g) := _root_.GlobalTheory.SmMapAct.inLie_conj (g := g) (X := X) hg hX

theorem norm_sigma (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) (v : R.H) : ‖R.σ g v‖ = ‖v‖ := by
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, _⟩, hds⟩ := hR.2
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hPQ : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  have hx' : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ g hPQ hH hg
  have hm := hds.2.2.1.2.1 (P₀ * g * P₀⁻¹) hx' v
  have e2 : P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = g := by
    calc P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * g * (P₀⁻¹ * P₀) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  simp only [e2] at hm
  exact hm

theorem dsigW_sigma (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (R.σ g v) =
      R.σ g (dsigW (k := k) (r := r) R.σ (W.map fun X => g⁻¹ * X * g) v) := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hW'' : ∀ Y ∈ W.map (fun X => g⁻¹ * X * g), InLieHpk k r Y := by
      intro Y hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW' Z hZ)
    have hdet : IsUnit g.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
    have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e : g * (g⁻¹ * X * g) * g⁻¹ = X := by
      calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR _ (inLie_conj hg (hW X List.mem_cons_self))).2.1 _
      (dsigW_mem hK hR _ hW'' hv) g hg
    rw [e] at h
    show dsig R.σ X (dsigW R.σ W (R.σ g v)) = R.σ g (dsig R.σ (g⁻¹ * X * g) _)
    rw [ih hW', h]

theorem smMap_sigma (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) :
    SmMap R R (fun v => R.σ g v) := by
  refine ⟨?_, fun v _ w _ => map_add (R.σ g) v w, fun a v _ => map_smul (R.σ g) a v, ?_⟩
  · intro v hv
    exact PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv g hg
  · intro W hW
    refine ⟨1, [W.map fun X => g⁻¹ * X * g], ?_, fun v hv => ?_⟩
    · intro w hw Y hY
      rw [List.mem_singleton.mp hw] at hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW Z hZ)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      rw [dsigW_sigma hK hR hg W hW hv, norm_sigma hR hg]

theorem smMap_lin (hK : PI.KFinSmooth) {R₀ : Rep k r} (hR : R.IsDG ε mu) {T T' : R₀.H → R.H} (a : ℂ)
    (hT : SmMap R₀ R T) (hT' : SmMap R₀ R T') : SmMap R₀ R (fun v => a • T v + T' v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    exact Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add
      (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a (hT.mem v hv)) (hT'.mem v hv)
  · intro v hv w hw
    rw [hT.add v hv w hw, hT'.add v hv w hw, smul_add]
    abel
  · intro b v hv
    rw [hT.smul b v hv, hT'.smul b v hv, smul_add, smul_comm]
  · intro W hW
    refine cw_of_semiBd R₀ (((semiBd_of_cw R₀ (hT.cont W hW)).mul (norm_nonneg a)).add
      (semiBd_of_cw R₀ (hT'.cont W hW))) (fun v hv => ?_)
    rw [dsigW_lin hK hR W hW a (hT.mem v hv) (hT'.mem v hv)]
    exact (norm_add_le _ _).trans (by rw [norm_smul])

end DS

theorem smMap_act : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → R''.IsDG ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  intro hK k r ε mu mu' mu'' R R' R'' hR hR' _
  exact ⟨fun g hg => smMap_sigma hK hR hg, fun T T' hT hT' => smMap_comp hT hT',
    fun T T' a hT hT' => smMap_lin hK hR' a hT hT', fun Wp _ T Bm hT hB => cw_comp hT hB⟩

end GlobalTheory.SmMapAct
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosureStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.smooth_maps_closure : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → R''.IsDG ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  first | exact @GlobalTheory.SmMapAct.smMap_act | exact GlobalTheory.SmMapAct.smMap_act | (intros; apply GlobalTheory.SmMapAct.smMap_act <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CapelliKFiniteCoefficient
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem comp_eq_sum_inner_smul_rankOne {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ Wp) (c : OrthonormalBasis κ ℂ Wq)
    (P : H →L[ℂ] Wp) (A : H →L[ℂ] H) (Q : Wq →L[ℂ] H) :
    P.comp (A.comp Q) = ∑ p : ι × κ, ⟪ContinuousLinearMap.adjoint P (b p.1), A (Q (c p.2))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (b p.1) := _root_.GlobalTheory.comp_eq_sum_inner_smul_rankOne (H := H) (Wp := Wp) (Wq := Wq) (ι := ι) (κ := κ) b c P A Q

theorem isCoef_of_translate_smul_exists : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → (∀ f : Mx k r → (Wq →L[ℂ] Wp), PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f → ∃ s, IsCoef R l l' f s) ∧ (∀ F s (t : ℂ), IsCoef R l l' F s → IsCoef R l l' (fun g => t • F g) (t * s)) ∧ ((∃ x ∈ R.TK, l x ≠ 0) → (∃ y ∈ R.TK, l' y ≠ 0) → ∀ s : ℂ, ∃ F, IsCoef R l l' F s) := by
  intro hK k r ε mu R Wp _ _ _ _ Wq _ _ _ _ l l' hR
  obtain ⟨hmul, hone, hinner, -, -, hTK, hKF, -, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  refine ⟨?_, ?_, ?_⟩
  · rintro f ⟨a, ha, b, hb, P, Q, hQ, hP, h⟩
    obtain ⟨hai, ha1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha
    obtain ⟨hbi, -, hb2⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hb
    let e := stdOrthonormalBasis ℂ Wp
    let c := stdOrthonormalBasis ℂ Wq
    let φ := (finProdFinEquiv (m := Module.finrank ℂ Wp) (n := Module.finrank ℂ Wq)).symm
    refine ⟨_, _, fun i => R.σ a (ContinuousLinearMap.adjoint P (e (φ i).1)),
      fun i => R.σ b⁻¹ (Q (c (φ i).2)), fun i => (innerSL ℂ (c (φ i).2)).smulRight (e (φ i).1),
      fun i => ⟨hTK a ha _ (hKF _ (hP _)), hTK _ hbi _ (hKF _ (hQ _))⟩, fun g hg => ?_, rfl⟩
    have hc : a * (a⁻¹ * g * b⁻¹) * b = g := by
      calc a * (a⁻¹ * g * b⁻¹) * b = (a * a⁻¹) * g * (b⁻¹ * b) := by simp only [Matrix.mul_assoc]
        _ = g := by rw [ha1, hb2, Matrix.one_mul, Matrix.mul_one]
    have h1 : f g = P.comp ((R.σ (a⁻¹ * g * b⁻¹)).comp Q) := by
      have := h (a⁻¹ * g * b⁻¹)
      simpa only [hc] using this
    have hm : a⁻¹ * g * b⁻¹ ∈ GG k r :=
      Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hai hg) hbi
    have h2 : ∀ u v, ⟪u, R.σ (a⁻¹ * g * b⁻¹) v⟫_ℂ = ⟪R.σ a u, R.σ g (R.σ b⁻¹ v)⟫_ℂ := by
      intro u v
      rw [← hinner a ha, ← hmul a ha _ hm, ← hmul g hg _ hbi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ha1,
        Matrix.one_mul]
    rw [h1, comp_eq_sum_inner_smul_rankOne e c]
    simp only [h2]
    exact (φ.sum_comp (fun p => ⟪R.σ a (ContinuousLinearMap.adjoint P (e p.1)), R.σ g (R.σ b⁻¹ (Q (c p.2)))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (e p.1))).symm
  · rintro F s t ⟨m, x, y, X, hxy, hF, hs⟩
    refine ⟨m, x, y, fun i => t • X i, hxy, fun g hg => ?_, ?_⟩
    · simp only [hF g hg, Finset.smul_sum, smul_smul, mul_comm]
    · simp only [hs, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_right]
  · rintro ⟨x, hx, hx0⟩ ⟨y, hy, hy0⟩ s
    have h1 : ⟪l x, l x⟫_ℂ ≠ 0 := fun h => hx0 (inner_self_eq_zero.mp h)
    have h2 : ⟪l' y, l' y⟫_ℂ ≠ 0 := fun h => hy0 (inner_self_eq_zero.mp h)
    refine ⟨fun g => ∑ _i : Fin 1, ⟪x, R.σ g y⟫_ℂ •
        ((s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x)),
      1, fun _ => x, fun _ => y,
      fun _ => (s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x),
      fun _ => ⟨hx, hy⟩, fun g _ => rfl, ?_⟩
    rw [Fin.sum_univ_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_smul_right, inner_smul_right, div_mul_cancel₀ _ (mul_ne_zero h2 h1)]

end GlobalTheory
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorBesselTransfer
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorBesselTransfer
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_sum_of_add_on_sm {k r : ℕ} (R : Rep k r) {Wp : Type} [AddCommGroup Wp] [Module ℂ Wp] (l : R.H → Wp)
    (hadd : ∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) (hsmul : ∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v)
    {α : Type} (s : Finset α) (f : α → R.H) (hf : ∀ i, f i ∈ R.sm) : l (∑ i ∈ s, f i) = ∑ i ∈ s, l (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
    simpa using hsmul 0 0 h0
  | insert a s ha ih =>
    have hs : ∑ i ∈ s, f i ∈ R.sm := R.smSub.sum_mem fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ (hf a) _ hs, ih]

theorem herm_smul_eq_sum_of_tensRaw : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ om l lI β hR hRI hT hadd hsmul hl a w hw g hg
  have hσw : R.σ g w ∈ R.sm := (rep_basic_of_isDS hK k r ε mu R hR).2.2.2.1 g hg w hw
  have htm : ∀ c, tm R a w c ∈ R.sm := fun c => R.smSub.smul_mem (a c) hw
  have hact : ∀ c, act ρ R g (tm R a w) c = (ρ g *ᵥ a) c • R.σ g w := by
    intro c
    simp only [act, tm, map_smul, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  have hx : ∀ c, act ρ R g (tm R a w) c ∈ R.sm := fun c => by
    rw [hact]; exact R.smSub.smul_mem _ hσw
  set y : ∀ I, (RI I).H := fun I => (RI I).σ g (∑ c, pr I c (tm R a w c)) with hy
  have hyeq : ∀ I, ∑ c, pr I c (act ρ R g (tm R a w) c) = y I := fun I => hT.pr_eq I g hg _ htm
  have hysm : ∀ I, y I ∈ (RI I).sm := fun I => by
    rw [← hyeq]
    exact (RI I).smSub.sum_mem fun c _ => (hT.pr_sm I c).mem _ (hx c)
  have hdec : ∀ c, ∑ I, io I c (y I) = (ρ g *ᵥ a) c • R.σ g w := fun c => by
    rw [← hact, ← hT.sum_io_pr _ hx c]
    simp only [hyeq]
  have hev : ∀ I, ev Γ R om (fun c => io I c (y I)) ∈ R.sm := fun I =>
    R.smSub.sum_mem fun i _ => R.smSub.sum_mem fun j _ => R.smSub.smul_mem _ ((hT.io_sm I j).mem _ (hysm I))
  have hsum : ∑ I, ev Γ R om (fun c => io I c (y I)) = Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • R.σ g w := by
    simp only [ev]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ I, ∑ j, (star (om i) * Γ i j) • io I j (y I)
        = ∑ j, (star (om i) * Γ i j * (ρ g *ᵥ a) j) • R.σ g w := fun i => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.smul_sum, hdec, smul_smul]
    simp only [this, ← Finset.sum_smul]
    congr 1
    generalize ρ g *ᵥ a = b
    simp only [Formalism.QuantumDeterminants.herm, Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [← hsmul _ _ hσw, ← hsum, map_sum_of_add_on_sm R l hadd hsmul _ _ hev]
  exact Finset.sum_congr rfl fun I _ => hl I _ (hysm I)

end GlobalTheory
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorBesselTransferStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_bessel_transfer : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  first | exact @GlobalTheory.herm_smul_eq_sum_of_tensRaw | exact GlobalTheory.herm_smul_eq_sum_of_tensRaw | (intros; apply GlobalTheory.herm_smul_eq_sum_of_tensRaw <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorRawOfFrep
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorRawOfFrep
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensorKFinite

variable {k r : ℕ} {ι : Type} [Fintype ι]

theorem smMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have h := hT.smul 0 0 R.smSub.zero_mem
  simpa using h

theorem kfin_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm)
    (hA : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, R'.σ g (T c y) = ∑ i, a i • T i (R.σ g y))
    (c : ι) (y : R.H) (hy : R.KFin y) : R'.KFin (T c y) := _root_.GlobalTheory.TensorKFinite.kfin_of_family (R := R) (R' := R') T hT hK hA c y hy

theorem tk_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm) (hTK : ∀ v ∈ R.TK, v ∈ R.sm)
    (hF : ∀ c y, R.KFin y → R'.KFin (T c y))
    (hB : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, T c (R.σ g y) = ∑ i, a i • R'.σ g (T i y))
    (c : ι) (y : R.H) (hy : y ∈ R.TK) : T c y ∈ R'.TK := _root_.GlobalTheory.TensorKFinite.tk_of_family (R := R) (R' := R') T hT hK hTK hF hB c y hy

theorem inv_rows [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Matrix ι ι ℂ) (h : A * B = 1)
    (u v : ι → V) (huv : ∀ i, u i = ∑ j, B i j • v j) (c : ι) : v c = ∑ i, A c i • u i := by
  simp_rw [huv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply]
  simp

end GlobalTheory.TensorKFinite


open GlobalTheory.TensorKFinite in
theorem GlobalTheory.tensor_decomposition_kfinite : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ I c y, (RI I).KFin y → R.KFin (io I c y)) ∧ (∀ I c x, R.KFin x → (RI I).KFin (pr I c x)) ∧ (∀ I c, ∀ y ∈ (RI I).TK, io I c y ∈ R.TK) ∧ (∀ I c, ∀ x ∈ R.TK, pr I c x ∈ (RI I).TK) := by
  intro hKS k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hRσ, hRT, -, hRK, -, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε mu R hR
  have hIT : ∀ I, ∀ v ∈ (RI I).TK, v ∈ (RI I).sm := fun I =>
    (GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.1
  have hIK : ∀ I, ∀ v, (RI I).KFin v → v ∈ (RI I).sm := fun I v hv =>
    hIT I v ((GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.2.2.1 v hv)
  have hRK' : ∀ v, R.KFin v → v ∈ R.sm := fun v hv => hRT v (hRK v hv)
  obtain ⟨-, -, h1, hmul, -⟩ := hF
  have hinv : ∀ g ∈ GG k r, ρ g⁻¹ * ρ g = 1 ∧ ρ g * ρ g⁻¹ = 1 := fun g hg => by
    obtain ⟨a, b, c⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    exact ⟨by rw [← hmul _ a _ hg, c, h1], by rw [← hmul _ hg _ a, b, h1]⟩
  have ioB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      io I c ((RI I).σ g y) = ∑ i, ρ g c i • R.σ g (io I i y) := fun I g hg c y hy =>
    congrFun (hT.io_eq I g hg y hy) c
  have ioA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      R.σ g (io I c y) = ∑ i, ρ g⁻¹ c i • io I i ((RI I).σ g y) := fun I g hg c y hy =>
    inv_rows _ _ (hinv g hg).1 (fun i => io I i ((RI I).σ g y)) (fun i => R.σ g (io I i y))
      (fun i => ioB I g hg i y hy) c
  have prA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      (RI I).σ g (pr I c x) = ∑ i, (ρ g)ᵀ c i • pr I i (R.σ g x) := fun I g hg c x hx => by
    have hs : ∀ e, (Pi.single c x : ι → R.H) e ∈ R.sm := fun e => by
      by_cases he : e = c
      · subst he; simpa using hx
      · rw [Pi.single_eq_of_ne he]; exact R.smSub.zero_mem
    have h := hT.pr_eq I g hg (Pi.single c x) hs
    have e1 : ∑ e, pr I e ((Pi.single c x : ι → R.H) e) = pr I c x := by
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        rw [Pi.single_eq_of_ne he, smMap_zero (hT.pr_sm I e)]
      · simp
    have e2 : ∀ i, act ρ R g (Pi.single c x) i = ρ g i c • R.σ g x := fun i => by
      unfold act
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        simp [Pi.single_eq_of_ne he]
      · simp
    rw [e1] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2, (hT.pr_sm I i).smul _ _ (hRσ g hg x hx), Matrix.transpose_apply]
  have prB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      pr I c (R.σ g x) = ∑ i, (ρ g⁻¹)ᵀ c i • (RI I).σ g (pr I i x) := fun I g hg c x hx =>
    inv_rows _ _ (by rw [← Matrix.transpose_mul, (hinv g hg).2, Matrix.transpose_one])
      (fun i => (RI I).σ g (pr I i x)) (fun i => pr I i (R.σ g x)) (fun i => prA I g hg i x hx) c
  have K1 : ∀ I c y, (RI I).KFin y → R.KFin (io I c y) := fun I =>
    kfin_of_family (io I) (hT.io_sm I) (hIK I) fun g hg c y hy => ⟨_, ioA I g hg c y hy⟩
  have K2 : ∀ I c x, R.KFin x → (RI I).KFin (pr I c x) := fun I =>
    kfin_of_family (pr I) (hT.pr_sm I) hRK' fun g hg c y hy => ⟨_, prA I g hg c y hy⟩
  exact ⟨K1, K2,
    fun I => tk_of_family (io I) (hT.io_sm I) (hIK I) (hIT I) (K1 I) fun g hg c y hy => ⟨_, ioB I g hg c y hy⟩,
    fun I => tk_of_family (pr I) (hT.pr_sm I) hRK' hRT (K2 I) fun g hg c y hy => ⟨_, prB I g hg c y hy⟩⟩
end
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorRawOfFrepStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_raw_of_frep : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ I c y, (RI I).KFin y → R.KFin (io I c y)) ∧ (∀ I c x, R.KFin x → (RI I).KFin (pr I c x)) ∧ (∀ I c, ∀ y ∈ (RI I).TK, io I c y ∈ R.TK) ∧ (∀ I c, ∀ x ∈ R.TK, pr I c x ∈ (RI I).TK) := by
  first | exact @GlobalTheory.tensor_decomposition_kfinite | exact GlobalTheory.tensor_decomposition_kfinite | (intros; apply GlobalTheory.tensor_decomposition_kfinite <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapVanishing
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapVanishing
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselConv

open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

section

variable {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem ae_mem_prod {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have := hW.1; have := hN.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)

theorem pi_inv_contOn [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    ContinuousOn (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} := _root_.GlobalTheory.BesselConv.pi_inv_contOn (z := z) (u := u) (π := π) hT hπ

theorem beInt_aesm [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (w v : H) :
    AEStronglyMeasurable (beInt z c π σ w v) (μW.prod μN) := _root_.GlobalTheory.BesselConv.beInt_aesm (ε := ε) (lam := lam) (σ := σ) (z := z) (u := u) (π := π) (μW := μW) (μN := μN) hσ c hT hπ hW hN w v

theorem norm_beInt_le (σ : Mx k r → (H →L[ℂ] H)) {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    (w v : H) (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z) :
    ‖beInt z c π σ w v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ := by
  have h1 : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by
      rw [piW_unitary hT hπ _ (uw_inv hp).1 ξ, one_mul]
  unfold beInt
  rw [norm_smul, norm_mul, norm_star, psi_norm, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end

theorem be_conv_of_growth (hG : GrowthS) : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  intro Hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS v hv
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, hGh, hq⟩ := hS
  obtain ⟨C, Ws, hWs, hb⟩ := GlobalTheory.BesselDecay.decay_TK Hy k r ε mu h R hR hgap hok v hv
  have hA : AG k r < aOf r h - 1 := by
    have h4 := hok.2.2.2
    have : 0 ≤ AG k r := by unfold AG; positivity
    have : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  have hI := hG k r z μW μN μG νq _ hz hT hW hN hGh hq hA
  rw [neg_sub] at hI
  have hbd : ∀ w ∈ R.sm, ∀ᵐ p ∂(μW.prod μN), ‖beInt z Formalism.QuantumDeterminants.cStd π R.σ w v p‖ ≤
      C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum *
        B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) := by
    intro w hw
    filter_upwards [ae_mem_prod hW hN] with p hp
    exact (norm_beInt_le R.σ _ hT hπ w v p hp.1).trans
      (hb w hw _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hp.1.1 hp.2.1))
  refine ⟨fun w hw => ?_, C * ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
    B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) ∂(μW.prod μN), Ws, hWs, fun w hw => ?_⟩
  · exact Integrable.mono' (hI.const_mul _) (beInt_aesm hR.2 _ hT hπ hW hN w v) (hbd w hw)
  · refine (norm_integral_le_of_norm_le (hI.const_mul _) (hbd w hw)).trans (le_of_eq ?_)
    rw [integral_const_mul]; ring

theorem be_conv : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) :=
  be_conv_of_growth GlobalTheory.T.besselGrowth_stabilizer_unipotent

end GlobalTheory.BesselConv
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapVanishingStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  first | exact @GlobalTheory.BesselConv.be_conv | exact GlobalTheory.BesselConv.be_conv | (intros; apply GlobalTheory.BesselConv.be_conv <;> assumption)
end Gp91
end
end
