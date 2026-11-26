module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwayActOfTAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitW

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinBase
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cw_eInf_k (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (eInf F • Z) = d.cw w Z := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, St.piInf_smul, eInf_fst_apply, map_one, one_mul]
theorem cw_finOne_k (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (finOne F • Z) = 0 := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, Place.piInf_finOne, Matrix.zero_apply]
theorem cw_zero_iff_k {p q : Type} (Z : Matrix p q (AE F E)) : (∀ w, d.cw w Z = 0) ↔ eInf F • Z = 0 := by
  constructor
  · intro h
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h w]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · rw [smul_smul, finOne_mul_eInf, zero_smul, smul_zero]
  · intro h w
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k d w Z, h]
    ext i j
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
theorem cw_one_iff_k {p : Type} [DecidableEq p] (M : Matrix p p (AE F E)) :
    (∀ w, d.cw w M = 1) ↔ eInf F • M = eInf F • (1 : Matrix p p (AE F E)) := by
  have h1 : ∀ w, d.cw w (1 : Matrix p p (AE F E)) = 1 := fun w => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  constructor
  · intro h
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h w, h1 w]
    · rw [smul_smul, smul_smul, finOne_mul_eInf, zero_smul, zero_smul]
  · intro h w
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k d w M, h, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h1 w]
def InvFin_k (f : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X
def InvInf_k (G : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, finOne F • Z = 0 → G (X + Z) = G X
def fcrd_k (X : Mx F E d.m d.n) : Fin d.m × Fin d.n × Fin 2 → Af F := fun k => (d.crd X k).2
theorem gram_add_left_k (X X' Z : Mx F E d.m d.n) : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_add, Matrix.add_mul]
theorem gram_add_right_k (X Z Z' : Mx F E d.m d.n) : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
theorem gram_smul_left_k (c : AF F) (X Z : Mx F E d.m d.n) : d.gram (c • X) Z = c • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul]
theorem gram_smul_right_k (c : AF F) (X Z : Mx F E d.m d.n) : d.gram X (c • Z) = c • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  have : (c • Z).map (cA σ) = c • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  rw [this, Matrix.mul_smul]
theorem gram_fin_inf_k {X Z : Mx F E d.m d.n} (hX : eInf F • X = 0) (hZ : finOne F • Z = 0) : d.gram X Z = 0 := by
  have eX : X = finOne F • X := by
    conv_lhs => rw [← smul_split X, hX, zero_add]
  rw [eX, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, hZ]
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem gram_inf_fin_k {X Z : Mx F E d.m d.n} (hX : finOne F • X = 0) (hZ : eInf F • Z = 0) : d.gram X Z = 0 := by
  have eZ : Z = finOne F • Z := by
    conv_lhs => rw [← smul_split Z, hZ, zero_add]
  rw [eZ, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hX]
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem tt_add_k (M M' : Mx F E d.n d.n) : d.tt (M + M') = d.tt M + d.tt M' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add (f := _)]
theorem crd_add_k (X Z : Mx F E d.m d.n) (k) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, map_add (f := _), Finsupp.add_apply]
theorem crd_smul_k (c : AF F) (X : Mx F E d.m d.n) (k) : d.crd (c • X) k = c * d.crd X k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
theorem cmb_crd_k (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem cmb_smul_k (c : AF F) (x : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (fun k => c * x k) = c • d.cmb x := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Matrix.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul]
theorem fcrd_invInf_k (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d (fun X => g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X)) := by
  intro X Z hZ
  show g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (X + Z)) = g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X)
  congr 1
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_add_k]
  change (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  have : (d.crd Z k).2 = 0 := by
    rw [← finOne_snd_mul (d.crd Z k), ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_smul_k, hZ]
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  rw [this, add_zero]
theorem invInf_fcrd_k {G : Mx F E d.m d.n → ℂ} (hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G) (X : Mx F E d.m d.n) :
    G X = G (d.cmb fun k => pairA F 0 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X k)) := by
  set Y := d.cmb fun k => pairA F 0 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X k) with hY
  have hp : ∀ c : AF F, finOne F * c = pairA F 0 c.2 := fun c =>
    Prod.ext (finOne_fst_mul c) (finOne_snd_mul c)
  have e1 : finOne F • X = Y := by
    conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_crd_k d X]
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_smul_k]
    simp only [hp, hY, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k]
  have e2 : finOne F • Y = Y := by
    rw [hY, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_smul_k]
    congr 1
    funext k
    rw [hp]
    rfl
  have h := hG Y (X - Y) (by rw [smul_sub, e1, e2, sub_self])
  rw [add_sub_cancel] at h
  exact h
def StepF_k (x : d.G) (A B : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ) : Prop :=
  (∀ f, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f → _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d (A f)) ∧ ∀ G, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G → _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d (B G) ∧
    ∀ f, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f → ∀ Φ ∈ d.sch, d.T Φ = (fun X => f X * G X) → d.T (d.om x Φ) = fun X => A f X * B G X
theorem step_comp_k {x x' : d.G} {A A' B B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x A B) (h' : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x' A' B') : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun G hG => ⟨(h.2 _ (h'.2 G hG).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 G hG).2 f hf Φ hΦ hT
  have hΦ' : d.om x' Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x' Φ hΦ
  have e2 := (h.2 (B' G) (h'.2 G hG).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) hΦ' e1
  rw [map_mul, mul_apply_eq_comp]
  exact e2
theorem key_split_k {f G A' B' : Mx F E d.m d.n → ℂ} (hf : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f) (hA : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d A') (hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G)
    (hB : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d B') (h : ∀ X, f X * G X = A' X * B' X) : ∀ X Y, f X * G Y = A' X * B' Y := by
  intro X Y
  have hW1 : eInf F • X + finOne F • Y = X + finOne F • (Y - X) := by
    calc eInf F • X + finOne F • Y = (eInf F • X + finOne F • X) + finOne F • (Y - X) := by rw [smul_sub]; abel
      _ = X + finOne F • (Y - X) := by rw [smul_split]
  have hW2 : eInf F • X + finOne F • Y = Y + eInf F • (X - Y) := by
    calc eInf F • X + finOne F • Y = (eInf F • Y + finOne F • Y) + eInf F • (X - Y) := by rw [smul_sub]; abel
      _ = Y + eInf F • (X - Y) := by rw [smul_split]
  have hfin : ∀ w, d.cw w (finOne F • (Y - X)) = 0 := fun w => _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_finOne_k d w _
  have hinf : finOne F • (eInf F • (X - Y)) = 0 := by rw [smul_smul, finOne_mul_eInf, zero_smul]
  have e := h (eInf F • X + finOne F • Y)
  rw [hW1, hf X _ hfin, hA X _ hfin, ← hW1, hW2, hG Y _ hinf, hB Y _ hinf] at e
  exact e
theorem step_conj_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {x₁ x₂ x' : d.G} {A₁ A₂ B₁ B₂ B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h₁ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x₁ A₁ B₁) (h₂ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x₂ A₂ B₂) (h' : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d (x₁ * x' * x₂) id B := by
  have hc := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d h₁ h') h₂
  have h0 := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d h₁ h₂
  refine ⟨fun G => if h : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 then
      (G h.choose / B₁ (B₂ G) h.choose) • B₁ (B' (B₂ G)) else 0,
    fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only
    split_ifs with h
    · intro X Z hZ
      simp only [Pi.smul_apply, smul_eq_mul]
      have e := (hc.2 G hG).1 X Z hZ
      simp only [Function.comp_apply] at e
      rw [e]
    · intro X Z _
      rfl
  · have e := (hc.2 G hG).2 f hf Φ hΦ hTΦ
    have e0 := (h0.2 G hG).2 f hf Φ hΦ hTΦ
    rw [h1, map_one, one_apply_eq_self, hTΦ] at e0
    have key := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.key_split_k d hf (h0.1 f hf) hG (h0.2 G hG).1 (fun X => congrFun e0 X)
    by_cases hz : (∀ X, f X = 0) ∨ ∀ X, G X = 0
    · have hΦ0 : Φ = 0 := (hT.1 F E σ d).2.2 Φ hΦ (by
        rw [hTΦ]
        funext X
        rcases hz with hz | hz <;> simp [hz])
      subst hΦ0
      have hT0 : d.T 0 = 0 := by
        funext X
        have hschr : ∀ p : (d.κ → AF F) × (d.κ → AF F), schr d.B.ψ p (0 : d.Fn) = 0 := by
          intro p
          funext x
          simp [schr]
        simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Darboux.rho, hschr,
          map_zero, Pi.zero_apply]
      rw [map_zero, hT0]
      funext X
      rcases hz with hz | hz
      · simp [hz]
      · have hn : ¬ ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 := fun ⟨X₀, h, _⟩ => h (hz X₀)
        simp [dite_eq_right hn]
    · push Not at hz
      obtain ⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩ := hz
      have hex : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 := by
        refine ⟨X₁, hX₁, fun h0' => ?_⟩
        have := key u₀ X₁
        simp only [Function.comp_apply] at this
        rw [h0', mul_zero] at this
        exact mul_ne_zero hu₀ hX₁ this
      have hB0 := hex.choose_spec.2
      have hA : ∀ u, A₁ (A₂ f) u = f u * (G hex.choose / B₁ (B₂ G) hex.choose) := by
        intro u
        have := key u hex.choose
        simp only [Function.comp_apply] at this
        rw [mul_div_assoc', eq_div_iff hB0]
        linear_combination -this
      rw [e]
      funext X
      simp only [Function.comp_apply, id_eq, dite_eq_left hex, Pi.smul_apply, smul_eq_mul, hA]
      ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinTop
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinSteps
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem stepN_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eInf F • β = 0) :
    _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id (fun G X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X) := by
  have hβ' : β = finOne F • β := by
    conv_lhs => rw [← smul_split β, hβ, zero_add]
  have hβM : ∀ M : Mx F E d.n d.n, finOne F • M = 0 → β * M = 0 := fun M hM => by
    rw [hβ', Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_zero]
  refine ⟨fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    show d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram (X + Z) (X + Z)))) * G (X + Z) =
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X
    rw [hG X Z hZ]
    have e : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
        hβM (d.gram X Z) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]),
        hβM (d.gram Z X) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]),
        hβM (d.gram Z Z) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram])]
      simp
    rw [e]
  · funext X
    rw [((hT.2.1 F E σ d) Φ hΦ).1 x β hx X, hTΦ]
    simp only [id]
    ring
theorem stepM_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eInf F • a'.1 = eInf F • (1 : Mx F E d.n d.n)) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B := by
  set M : Mx F E d.n d.n := (a'⁻¹).1 with hM
  have hMe : eInf F • M = eInf F • (1 : Mx F E d.n d.n) := by
    have h1 : a'.1 * M = 1 := by rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc eInf F • M = (eInf F • (1 : Mx F E d.n d.n)) * M := by rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (eInf F • a'.1) * M := by rw [ha]
      _ = eInf F • (1 : Mx F E d.n d.n) := by rw [Matrix.smul_mul, h1]
  refine ⟨fun G X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * G (X * Mᵀ),
    fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    show _ * G ((X + Z) * Mᵀ) = _ * G (X * Mᵀ)
    rw [Matrix.add_mul, hG _ _ (by rw [← Matrix.smul_mul, hZ, Matrix.zero_mul])]
  · funext X
    rw [((hT.2.1 F E σ d) Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hf' : f (X * Mᵀ) = f X := by
      have e : X * Mᵀ = X + X * (M - 1)ᵀ := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      refine hf X _ ((_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d _).2 ?_)
      rw [← Matrix.mul_smul, Matrix.transpose_sub, smul_sub, ← Matrix.transpose_smul, ← Matrix.transpose_smul, hMe,
        sub_self, Matrix.mul_zero]
    beta_reduce
    rw [hf']
    simp only [id]
    ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinW
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem stepW_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) : ∃ A B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d w A B := by
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  have := hν.1
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hsm : ∀ c : AF F, Continuous fun Z : Mx F E d.m d.n => c • Z := fun c =>
    continuous_pi fun i => continuous_pi fun j =>
      Continuous.fun_smul (f := fun _ : Mx F E d.m d.n => c) (g := fun Z : Mx F E d.m d.n => Z i j) continuous_const
        ((continuous_apply j).comp (continuous_apply i))
  let VI : AddSubgroup (Mx F E d.m d.n) :=
    { carrier := {Z | finOne F • Z = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, ha, neg_zero] }
  let VF : AddSubgroup (Mx F E d.m d.n) :=
    { carrier := {Z | eInf F • Z = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, ha, neg_zero] }
  have hVI : IsClosed ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (hsm (finOne F)) continuous_const
  have hVF : IsClosed ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (hsm (eInf F)) continuous_const
  haveI : LocallyCompactSpace VI := hVI.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace VF := hVF.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology VI :=
    TopologicalSpace.Subtype.secondCountableTopology ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : SecondCountableTopology VF :=
    TopologicalSpace.Subtype.secondCountableTopology ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace VI := Subtype.borelSpace (fun x' => x' ∈ ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  haveI : BorelSpace VF := Subtype.borelSpace (fun x' => x' ∈ ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  have h₁ : ∀ Z : Mx F E d.m d.n, eInf F • Z ∈ VI := fun Z => by
    show finOne F • eInf F • Z = 0
    rw [smul_smul, finOne_mul_eInf, zero_smul]
  have h₂ : ∀ Z : Mx F E d.m d.n, finOne F • Z ∈ VF := fun Z => by
    show eInf F • finOne F • Z = 0
    rw [smul_smul, eInf_mul_finOne, zero_smul]
  let Φs : VI × VF ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => p.1.1 + p.2.1
      invFun := fun Z => (⟨eInf F • Z, h₁ Z⟩, ⟨finOne F • Z, h₂ Z⟩)
      left_inv := fun p => by
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
        have ha' : finOne F • a = 0 := ha
        have hb' : eInf F • b = 0 := hb
        have ea : eInf F • a = a := by
          conv_rhs => rw [← smul_split a]
          rw [ha', add_zero]
        have eb : finOne F • b = b := by
          conv_rhs => rw [← smul_split b]
          rw [hb', zero_add]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show eInf F • (a + b) = a
          rw [smul_add, ea, hb', add_zero]
        · show finOne F • (a + b) = b
          rw [smul_add, eb, ha', zero_add]
      right_inv := fun Z => smul_split Z
      map_add' := fun p q => by
        show p.1.1 + q.1.1 + (p.2.1 + q.2.1) = p.1.1 + p.2.1 + (q.1.1 + q.2.1)
        abel
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := ((hsm (eInf F)).subtype_mk h₁).prodMk ((hsm (finOne F)).subtype_mk h₂) }
  obtain ⟨C, -, hC⟩ := KFock.integral_split ν (Measure.addHaar : Measure VI) (Measure.addHaar : Measure VF) Φs
  refine ⟨fun f X => (C : ℂ) * ∫ a : VI, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1 ∂Measure.addHaar,
    fun G X => ∫ b : VF, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1 ∂Measure.addHaar, fun f hf => ?_,
    fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    have hZ' := (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d Z).1 hZ
    dsimp only
    congr 2
    funext a
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_fin_inf_k d hZ' a.2, add_zero]
  · intro X Z hZ
    dsimp only
    congr 1
    funext b
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_inf_fin_k d hZ b.2, add_zero]
  · funext X
    rw [(hT.2.2.1 F E σ d) ν hν ε w hw Φ hΦ X, hTΦ, hC]
    have hpt : ∀ p : VI × VF, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Φs p))) * (f (Φs p) * G (Φs p)) =
        (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.1.1)) * f p.1.1) * (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.2.1)) * G p.2.1) := by
      intro p
      have e1 : Φs p = p.1.1 + p.2.1 := rfl
      have hf' : f (p.1.1 + p.2.1) = f p.1.1 := hf p.1.1 p.2.1 ((_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d _).2 p.2.2)
      have hG' : G (p.1.1 + p.2.1) = G p.2.1 := by rw [add_comm]; exact hG p.2.1 p.1.1 p.1.2
      rw [e1, hf', hG', _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.tt_add_k, mul_add, AddChar.map_add_eq_mul]
      ring
    simp only [hpt]
    rw [integral_prod_mul (μ := (Measure.addHaar : Measure VI)) (ν := (Measure.addHaar : Measure VF))
      (fun a : VI => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1)
      (fun b : VF => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1)]
    ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem step_of_triv_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hD : _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k) (x : d.G) (hx : ∀ w, d.cw w (inFrame d.b x) = 1) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have he : eInf F • inFrame d.b x = eInf F • (1 : Matrix _ _ (AE F E)) := (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_one_iff_k d _).1 hx
  obtain ⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩ :=
    hD F E σ d ε w₀ hw₀ (eInf F) eInf_mul_self x he
  obtain ⟨AW, BW, hW⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepW_k d hT hA ε w₀ hw₀
  have hW3 := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d hW hW) hW
  have h4' : w₀ * (w₀ * w₀ * w₀) = 1 := by simpa only [mul_assoc] using _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf hw₀
  obtain ⟨BC, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_conj_k d hT hW hW3 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepN_k d hT x₂ c h2 hc) h4'
  have hinv : w₀⁻¹ = w₀ * w₀ * w₀ := (eq_inv_of_mul_eq_one_left (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf hw₀)).symm
  obtain ⟨BM, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepM_k d hT x₃ a a' h3 ha'
  have hall := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepN_k d hT x₁ t h1 ht) hC) hM) (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepN_k d hT x₄ b h4 hb)
  rw [hxe, hinv]
  exact ⟨_, hall⟩
end SDf
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem finAct_step_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) {B : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ} (hB : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B) :
    ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F),
      ∀ f : Mx F E d.m d.n → ℂ, (∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X) → ∀ Φ ∈ d.sch,
        d.T Φ = (fun X => f X * g fun k => (d.crd X k).2) → d.T (d.om x Φ) = fun X => f X * g' fun k => (d.crd X k).2 := by
  intro g hg
  set G : Mx F E d.m d.n → ℂ := fun X => g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X) with hGdef
  have hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_invInf_k d g
  have hBG := (hB.2 G hG).1
  set g₁ : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ := fun y => B G (d.cmb fun k => pairA F 0 (y k)) with hg₁
  have hfc : ∀ y, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (d.cmb fun k => pairA F 0 (y k)) = y := fun y => by
    funext k
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k, _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
    rfl
  have hBg : ∀ X, B G X = g₁ (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X) := fun X => _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.invInf_fcrd_k d hBG X
  by_cases hg0 : g = 0
  · refine ⟨0, (SB _).zero_mem, fun f hf Φ hΦ hTΦ => ?_⟩
    have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ, hg0]; funext X; simp)
    subst hΦ0
    rw [map_zero, d.T_zero]
    funext X
    simp
  refine ⟨g₁, ?_, fun f hf Φ hΦ hTΦ => ?_⟩
  swap
  · have e := (hB.2 G hG).2 f hf Φ hΦ hTΦ
    rw [e]
    funext X
    simp only [id]
    rw [hBg X]
    rfl
  obtain ⟨φ, v₀, hv₀⟩ := exists_schwartz_ne (κ := Fin d.m × Fin d.n × Fin 2) F
  set f₀ : Mx F E d.m d.n → ℂ := fun X => φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1 with hf₀d
  have hf₀ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f₀ := by
    intro X Z hZ
    have hZ' := (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d Z).1 hZ
    show (φ fun k => _) = φ fun k => _
    congr 1
    funext k
    have : (d.crd Z k).1 = 0 := by
      rw [← eInf_fst_mul (d.crd Z k), ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_smul_k, hZ']
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_add_k]
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((d.crd X k).1 + (d.crd Z k).1) = _
    rw [this, add_zero]
  have hmem : (fun X => f₀ X * G X) ∈ d.schM := by
    show (fun c => f₀ (d.cmb c) * G (d.cmb c)) ∈ schA F (Fin d.m × Fin d.n × Fin 2)
    have e : (fun c => f₀ (d.cmb c) * G (d.cmb c)) = pureA F (⇑φ) g := by
      funext c
      show (φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd (d.cmb c) k).1) *
        g (fun k => (d.crd (d.cmb c) k).2) = _
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
      rfl
    rw [e]
    exact Submodule.subset_span ⟨φ, g, hg, rfl⟩
  obtain ⟨Φ₀, hΦ₀, hTΦ₀⟩ := (hT.1 F E σ d).2.1 _ hmem
  have e := (hB.2 G hG).2 f₀ hf₀ Φ₀ hΦ₀ hTΦ₀
  have hm := (hT.1 F E σ d).1 _ (d.om_sch x Φ₀ hΦ₀)
  rw [e] at hm
  have hs := slice_mem _ hm (fun k => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k))
  have e2 : (fun y : Fin d.m × Fin d.n × Fin 2 → Af F =>
      (fun X => id f₀ X * B G X) (d.cmb fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k)) (y k))) =
      φ v₀ • g₁ := by
    funext y
    simp only [id, Pi.smul_apply, smul_eq_mul]
    rw [hBg]
    have h1 : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (d.cmb fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k)) (y k)) = y := by
      funext k
      simp only [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k, _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
      rfl
    rw [h1]
    congr 1
    show (φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd (d.cmb _) k).1) = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
    congr 1
    funext k
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (v₀ k)
  have hs' : φ v₀ • g₁ ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := by
    rw [← e2]
    exact hs
  have := (SB (Fin d.m × Fin d.n × Fin 2 → Af F)).smul_mem (φ v₀)⁻¹ hs'
  rwa [smul_smul, inv_mul_cancel₀ hv₀, one_smul] at this
end SDf
theorem finAct_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k → _root_.PositivityTheory.SiegelWeilFormula.FinAct_k := by
  intro hT hA hD F E _ _ _ _ _ σ d x hx
  obtain ⟨B, hB⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_of_triv_k d hT hA hD x hx
  exact _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.finAct_step_k d hT x hB
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayAw
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayAwStep
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cw_mul_k (w : InfinitePlace F) {p q r : Type} [Fintype q] (M : Matrix p q (AE F E)) (N : Matrix q r (AE F E)) :
    d.cw w (M * N) = d.cw w M * d.cw w N := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  exact Matrix.map_mul
theorem cw_one_k (w : InfinitePlace F) {p : Type} [DecidableEq p] : d.cw w (1 : Matrix p p (AE F E)) = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_transpose_k (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w Mᵀ = (d.cw w M)ᵀ := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.transpose_map]
theorem cw_eW_self_k (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w (eW w • M) = d.cw w M := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, piInf_eW]
theorem cw_eW_ne_k {w w' : InfinitePlace F} (h : w' ≠ w) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w' (eW w • M) = 0 := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, piInf_eW, h]
theorem eW_smul_eq_iff_k (w : InfinitePlace F) {p q : Type} (M M' : Matrix p q (AE F E)) :
    eW w • M = eW w • M' ↔ d.cw w M = d.cw w M' := by
  constructor
  · intro h
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k d w M, h, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k]
  · intro h
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      by_cases hw : w' = w
      · subst hw
        rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k, h]
      · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw]
    · rw [finOne_eW_smul, finOne_eW_smul]
theorem eW_smul_of_supp_k {w : InfinitePlace F} {p q : Type} {Z : Matrix p q (AE F E)}
    (hZ : ∀ w', w' ≠ w → d.cw w' Z = 0) (hf : finOne F • Z = 0) : eW w • Z = Z := by
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    by_cases hw : w' = w
    · subst hw
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw, hZ w' hw]
  · rw [finOne_eW_smul, hf]
theorem gram_smul_right_k (a : AF F) (X Z : Mx F E d.m d.n) : d.gram X (a • Z) = a • d.gram X Z := by
  have : (a • Z).map (cA σ) = a • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, this, Matrix.mul_smul]
theorem gram_smul_left_k (a : AF F) (X Z : Mx F E d.m d.n) : d.gram (a • X) Z = a • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul]
theorem gram_add_k (X Z : Mx F E d.m d.n) :
    d.gram (X + Z) (X + Z) = d.gram X X + (d.gram X Z + d.gram Z X + d.gram Z Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.map_add _ (map_add _)]
  abel
theorem cw_eq_one_of_k (w : InfinitePlace F) {M : Mx F E d.n d.n} (h : eW w • M = eW w • (1 : Mx F E d.n d.n)) :
    d.cw w M = 1 := by
  rw [(_root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_eq_iff_k d w M 1).1 h, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k]
namespace Step
variable {d} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem stepN_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eW w • β = 0) :
    R.StepOK w x id (fun Ψ X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * Ψ X) := by
  have hP := hT.2.1 F E σ d
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    have hZe : eW w • Z = Z := _root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_of_supp_k d hZ hf
    have h1 : d.gram X Z = eW w • d.gram X Z := by
      calc d.gram X Z = d.gram X (eW w • Z) := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_right_k d _ X Z
    have h2 : d.gram Z X = eW w • d.gram Z X := by
      calc d.gram Z X = d.gram (eW w • Z) X := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_left_k d _ Z X
    have h3 : d.gram Z Z = eW w • d.gram Z Z := by
      calc d.gram Z Z = d.gram (eW w • Z) Z := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_left_k d _ Z Z
    have key : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.gram_add_k, h1, h2, h3, ← smul_add, ← smul_add, Matrix.mul_add, Matrix.mul_smul, ← Matrix.smul_mul, hβ,
        Matrix.zero_mul, add_zero]
    simp only
    rw [key, hΨ X Z hZ hf]
  · funext X
    rw [(hP Φ hΦ).1 x β hx X, hTΦ]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    ring
theorem stepM_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eW w • a'.1 = eW w • (1 : Mx F E d.n d.n)) :
    R.StepOK w x id (fun Ψ X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * Ψ (X * (a'⁻¹).1ᵀ)) := by
  have hP := hT.2.1 F E σ d
  have hc : d.cw w (a'⁻¹).1 = 1 := by
    have h1 : d.cw w a'.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eq_one_of_k d w ha
    have h2 : d.cw w ((a'⁻¹).1 * a'.1) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k]
    rwa [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, h1, Matrix.mul_one] at h2
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    simp only
    rw [Matrix.add_mul, hΨ (X * (a'⁻¹).1ᵀ) (Z * (a'⁻¹).1ᵀ) (fun w' hw' => by rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, hZ w' hw', Matrix.zero_mul])
      (by rw [← Matrix.smul_mul, hf, Matrix.zero_mul])]
  · funext X
    rw [(hP Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hl : R.loc w (X * (a'⁻¹).1ᵀ) = R.loc w X := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_transpose_k, hc, Matrix.transpose_one, Matrix.mul_one]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id, hl]
    ring
end Step
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Step
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem away_smul_k {Ψ : d.MF} (hΨ : d.IsAwayW w Ψ) (c : ℂ) : d.IsAwayW w (c • Ψ) := by
  intro X Z hZ hf
  simp only [Pi.smul_apply, hΨ X Z hZ hf]
theorem away_zero_k : d.IsAwayW w (0 : d.MF) := fun _ _ _ _ => rfl
theorem tens_key_k {f g : d.LF} {Ψ Ψ' : d.MF} (hΨ : d.IsAwayW w Ψ) (hΨ' : d.IsAwayW w Ψ')
    (h : R.tens w f Ψ = R.tens w g Ψ') : ∀ u X, f u * Ψ X = g u * Ψ' X := by
  intro u X
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u
  have := congrFun h (X + Z)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hZ3, hΨ X Z hZ1 hZ2, hΨ' X Z hZ1 hZ2] at this
  exact this
theorem away_conj_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {x₁ x₂ x' : d.G} {A₁ A₂ : d.LF → d.LF} {B₁ B₂ B' : d.MF → d.MF}
    (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂) (h' : R.StepOK w x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, R.StepOK w (x₁ * x' * x₂) id B := by
  have hsch := d.om_sch
  have hc := R.step_comp w hsch (R.step_comp w hsch h₁ h') h₂
  have h0 := R.step_comp w hsch h₁ h₂
  refine ⟨fun Ψ => if h : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 then
      (Ψ h.choose / B₁ (B₂ Ψ) h.choose) • B₁ (B' (B₂ Ψ)) else 0,
    fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only
    split_ifs with h
    · exact _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_smul_k w (hc.2 Ψ hΨ).1 _
    · exact _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_zero_k w
  · have e := (hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
    have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
    rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
    have key : ∀ u X, f u * Ψ X = A₁ (A₂ f) u * B₁ (B₂ Ψ) X := _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.tens_key_k R w hΨ (h0.2 Ψ hΨ).1 e0
    by_cases hz : (∀ u, f u = 0) ∨ ∀ X, Ψ X = 0
    · have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by
        rw [hTΦ]
        funext X
        rcases hz with hz | hz <;> simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hz])
      subst hΦ0
      rw [map_zero, d.T_zero]
      funext X
      rcases hz with hz | hz
      · simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hz]
      · have hn : ¬ ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 := fun ⟨X₀, h, _⟩ => h (hz X₀)
        simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, dif_neg hn]
    · push_neg at hz
      obtain ⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩ := hz
      have hex : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 := by
        refine ⟨X₁, hX₁, fun h0' => ?_⟩
        have := key u₀ X₁
        rw [h0', mul_zero] at this
        exact mul_ne_zero hu₀ hX₁ this
      have hB0 := hex.choose_spec.2
      have hA : ∀ u, A₁ (A₂ f) u = f u * (Ψ hex.choose / B₁ (B₂ Ψ) hex.choose) := by
        intro u
        have := key u hex.choose
        rw [mul_div_assoc', eq_div_iff hB0]
        linear_combination -this
      rw [e]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id_eq, dif_pos hex, Pi.smul_apply, smul_eq_mul, hA]
      ring
end Step
theorem awayAct_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k → _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k := by
  intro hT hA hD F E _ _ _ _ _ σ d R w x hx
  have hsch := d.om_sch
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have he : eW w • inFrame d.b x = eW w • (1 : Matrix _ _ (AE F E)) :=
    (_root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_eq_iff_k d w _ _).2 (by rw [hx, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k])
  obtain ⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩ :=
    hD F E σ d ε w₀ hw₀ (eW w) (eW_mul_self w) x he
  obtain ⟨C, s, BW, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  have hW3 := R.step_comp w hsch (R.step_comp w hsch hW hW) hW
  have h4' : w₀ * (w₀ * w₀ * w₀) = 1 := by
    simpa only [mul_assoc] using _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀
  obtain ⟨BC, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_conj_k R w hT hW hW3 (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₂ c h2 hc) h4'
  have hinv : w₀⁻¹ = w₀ * w₀ * w₀ := (eq_inv_of_mul_eq_one_left (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀)).symm
  have hall := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₁ t h1 ht) hC)
    (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepM_k R w hT x₃ a a' h3 ha')) (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₄ b h4 hb)
  rw [hxe, hinv]
  exact ⟨_, fun Ψ hΨ => ⟨(hall.2 Ψ hΨ).1, fun f hf Φ hΦ hTΦ => (hall.2 Ψ hΨ).2 f hf Φ hΦ hTΦ⟩⟩
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDec
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem inFrame_inv_of_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (h : inFrame d.b x * N = 1) : inFrame d.b x⁻¹ = N := by
  calc inFrame d.b x⁻¹ = inFrame d.b x⁻¹ * (inFrame d.b x * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_one_k, Matrix.one_mul]
theorem adDecomp_k : _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k := by
  intro F E _ _ _ _ _ σ d ε w hw e he x hx
  obtain ⟨ε₀, hε₀⟩ := d.ok.frame.1
  have hcm : IsCMExt F E σ := d.ok.good.cm
  set X := inFrame d.b x with hXdef
  set A := X.toBlocks₁₁ with hA
  set B := X.toBlocks₁₂ with hB
  set C := X.toBlocks₂₁ with hC
  set D := X.toBlocks₂₂ with hD
  have hXb : X = fromBlocks A B C D := (fromBlocks_toBlocks X).symm
  have heA : e • A = e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    rw [hA, ← smul_toBlocks₁₁, hx, smul_toBlocks₁₁, one_toBlocks₁₁]
  have heB : e • B = 0 := by
    rw [hB, ← smul_toBlocks₁₂, hx, smul_toBlocks₁₂, one_toBlocks₁₂, smul_zero]
  have heC : e • C = 0 := by
    rw [hC, ← smul_toBlocks₂₁, hx, smul_toBlocks₂₁, one_toBlocks₂₁, smul_zero]
  have heD : e • D = e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    rw [hD, ← smul_toBlocks₂₂, hx, smul_toBlocks₂₂, one_toBlocks₂₂]
  have hε₀2 : (ε₀ : ℤ) * (ε₀ : ℤ) = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  obtain ⟨t, ht, het, hunit⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator hcm (ε₀ : ℤ) hε₀2 X (_root_.PositivityTheory.SiegelWeilFormula.KAway.isUnit_det_inFrame_k d x) e he heA
  obtain ⟨x₁, hx₁⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM t) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) t).2 ht)
  have hx₁i : inFrame d.b x₁⁻¹ = nM (-t) := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d x₁ _ (by
    rw [hx₁, nM, nM, fromBlocks_multiply]; simp [fromBlocks_one])
  set A' := A - t * C with hA'
  set B' := B - t * D with hB'
  have hY : inFrame d.b (x₁⁻¹ * x) = fromBlocks A' B' C D := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hx₁i, ← hXdef, hXb, nM, fromBlocks_multiply]
    simp [hA', hB', sub_eq_add_neg]
  have h11 := upper_block_rank_one_update (cA σ).toRingHom (ε₀ : ℤ) _ (_root_.PositivityTheory.SiegelWeilFormula.KAway.inU_inFrame_k hε₀ (x₁⁻¹ * x))
  rw [hY, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁] at h11
  have hA'u : IsUnit A'.det := hunit
  set c₀ := C * A'⁻¹ with hc₀
  set c := ((ε : ℤ) : AE F E) • c₀ with hcdef
  have hcc := cond_c (cA σ).toRingHom (ε₀ : ℤ) A' C hA'u hε₀2 h11 (ε : ℤ)
  obtain ⟨x₂, hx₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM c) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) c).2 hcc)
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hwi : inFrame d.b w⁻¹ = fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d w _ (by
    rw [hw, fromBlocks_multiply]; simp [smul_smul, hεε, fromBlocks_one])
  have hL : inFrame d.b (w * x₂ * w⁻¹) = fromBlocks 1 0 c₀ 1 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hw, hx₂, hwi, nM, fromBlocks_multiply, fromBlocks_multiply]
    simp [hcdef, smul_smul, hεε]
  have hLi : inFrame d.b (w * x₂ * w⁻¹)⁻¹ = fromBlocks 1 0 (-c₀) 1 := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d _ _ (by
    rw [hL, fromBlocks_multiply]; simp [fromBlocks_one])
  have hcA : c₀ * A' = C := by rw [hc₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA'u, Matrix.mul_one]
  have hZ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x)) = fromBlocks A' B' 0 (D - c₀ * B') := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hLi, hY, fromBlocks_multiply]
    simp [hcA, sub_eq_add_neg, add_comm]
  obtain ⟨hz1, hz2⟩ := blkUpper (cA σ).toRingHom (ε₀ : ℤ) A' B' (D - c₀ * B') (by rw [← hZ]; exact _root_.PositivityTheory.SiegelWeilFormula.KAway.inU_inFrame_k hε₀ _)
  have hbb := cond_b (cA σ).toRingHom (ε₀ : ℤ) (cA_cA hcm) A' B' (D - c₀ * B') hA'u hz1 hz2
  obtain ⟨x₄, hx₄⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM (A'⁻¹ * B')) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) _).2 hbb)
  have hx₄i : inFrame d.b x₄⁻¹ = nM (-(A'⁻¹ * B')) := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d x₄ _ (by
    rw [hx₄, nM, nM, fromBlocks_multiply]; simp [fromBlocks_one])
  have hx₃ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹) = fromBlocks A' 0 0 (D - c₀ * B') := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hZ, hx₄i, nM, fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv_cancel_left _ _ hA'u]
  have hdet := _root_.PositivityTheory.SiegelWeilFormula.KAway.isUnit_det_inFrame_k d ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹)
  rw [hx₃, det_fromBlocks_zero₁₂] at hdet
  have hDu : IsUnit (D - c₀ * B').det := isUnit_of_mul_isUnit_right hdet
  have heB' : e • B' = 0 := by rw [hB', smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, heB, sub_zero]
  refine ⟨x₁, x₂, (w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹, x₄, t, c, A'⁻¹ * B', nonsingInvUnit A' hA'u,
    nonsingInvUnit (D - c₀ * B') hDu, by group, hx₁, hx₂, hx₃, hx₄, het, ?_, ?_, ?_, ?_⟩
  · rw [hcdef, smul_comm, hc₀, ← Matrix.smul_mul, heC, Matrix.zero_mul, smul_zero]
  · rw [← Matrix.mul_smul, heB', Matrix.mul_zero]
  · change e • (A - t * C) = _
    rw [smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, sub_zero, heA]
  · change e • (D - c₀ * B') = _
    rw [smul_sub, ← Matrix.mul_smul, heB', Matrix.mul_zero, sub_zero, heD]
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.SiegelWeilFormula.KAway
theorem awayAct_of_tAll_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KAway.awayAct_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KAway.adDecomp_k
theorem finAct_of_tAll_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KAway.finAct_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KAway.adDecomp_k
end PositivityTheory.SiegelWeilFormula.KAway
end
