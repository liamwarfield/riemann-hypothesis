module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueChainsKernelDatumSourceSideLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalisedWeylLatticeIffTargetPairingIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesFormTrueChains

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelDatumLatticeTargetSideTrueChains
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldFormValueMemPolynomialModel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldFormValueMemPolynomialModel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.KerVal

theorem fm_succ_mem_valQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (x : (((I.tw l l0 Z).fm u μ).lat (i + 1)).V) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)), ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = ((I.tw l l0 Z).fm u μ).emb (i + 1) x c' := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hBs hUnf hJets u μ i hi x c'
  obtain ⟨n, hw, hn, hnat, hds⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  have hlam : ∀ j τ, Col2.lamT (B.hcW u) j τ = lamTG ((I.tw l l0 Z).fm u μ) j τ := by
    intro j τ
    unfold Col2.lamT lamTG
    show Col2.shW _ _ = Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) j) _
    obtain ⟨c, hc⟩ := B.R.t_odd
    have h1 : (B.R.t + 1) / 2 = c + 1 := by omega
    have h2 : j * (B.R.t + 1) / 2 = j * (c + 1) := by
      rw [show j * (B.R.t + 1) = 2 * (j * (c + 1)) by rw [hc]; ring]; omega
    simp only [Col2.shW, Formalism.L2.Forms.shW]
    congr 1
    funext r
    show _ + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)) = _ - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [h1, h2]
    push_cast
    ring
  have hP : ((x.1 c').1 : Formalism.L2.DIV.Pol B.LL (Tau B.R) (B.R.N (i + 1))) ∈ polV (I.rec7 l Z) u (i + 1) := by
    have h1 := VV_le_WtPol (K := B.LL) (Col2.lamT (B.hcW u) (i + 1)) (x.1 c').2
    have e : (fun τ r => (Col2.lamT (B.hcW u) (i + 1) τ).natW r) = extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
      funext τ r
      rw [hlam]
      refine (hnat τ r).trans ?_
      congr 1
      funext τ' r'
      exact hw τ' r'
    rw [e] at h1
    exact h1
  refine ⟨Submodule.Quotient.mk ⟨_, hP⟩, ?_⟩
  funext y
  show evP O u μ (i + 1) ⟨_, hP⟩ y = _
  show (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(((I.rec7 l Z).chTw u μ).sDiv i τ))) *
    GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL (x.1 c').1) ((O u μ).frm (i + 1) y) = _
  simp only [(O u μ).frm_de (i + 1) hi y]
  rw [hStd.frm u μ (i + 1) y]
  show _ = Formalism.L2.Col.evFr (gramC (1 : Matrix (Fin _) (Fin _) _) (embAt B.embLL B.tauLL)) (shiftOf (Col2.lamT (B.hcW u) (i + 1))) B.embLL (x.1 c').1 y
  refine Eq.trans ?_ (Formalism.L2.Col.evFr_apply _ _ _ _ _).symm
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    exact ((congrArg DomWeight.detShift (hlam (i + 1) τ)).trans (hds τ)).symm
  · exact GlobalTheory.PdvKm.evFr_map _ _ _ _

end GlobalTheory.Mem.KerVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldFormValueMemPolynomialModelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientField_form_value_mem_polynomialModel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (x : (((I.tw l l0 Z).fm u μ).lat (i + 1)).V) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)), ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = ((I.tw l l0 Z).fm u μ).emb (i + 1) x c' := by
  first | exact @GlobalTheory.Mem.KerVal.fm_succ_mem_valQ | exact GlobalTheory.Mem.KerVal.fm_succ_mem_valQ | (intros; apply GlobalTheory.Mem.KerVal.fm_succ_mem_valQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldFormOfPolynomialModelValue
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldFormOfPolynomialModelValue
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem form_of_rat_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) → (∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c') → ∃ x, ((I.tw l l0 Z).fm u μ).emb (i + 1) x = φ := by
  intro B X I _hOk _hPins l Z l0 Y O Pl Bs _hQp hStd _hBas _hBsLL _hUnf _hJets u μ i hi φ hφ hv
  have hlam : lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) = lamT (B.hcW u) (i + 1) := by
    funext τ
    show Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) (i+1)) (((i+1) * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) (i+1)) (-(((i+1 : ℕ) : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : (B.R.t + 1) / 2 = k + 1 := by omega
    have e2 : (i+1) * (B.R.t + 1) / 2 = (i+1) * (k + 1) := by
      rw [show B.R.t + 1 = (k + 1) * 2 by omega, ← mul_assoc, Nat.mul_div_cancel _ two_pos]
    unfold Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
    congr 1
    funext j
    rw [e1, e2, Nat.cast_mul, sub_eq_add_neg]
  obtain ⟨nn, h1, -, h3, h4⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  change ∀ τ r, (lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) τ).natW r = _ at h3
  change ∀ τ, (lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) τ).detShift = _ at h4
  rw [hlam] at h3 h4
  have hnat : (fun τ r => (lamT (B.hcW u) (i + 1) τ).natW r) = extNu (B.R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
    funext τ r
    refine (h3 τ r).trans ?_
    congr 1
    funext τ' r'
    exact h1 τ' r'
  haveI hLL : Infinite B.LL := Infinite.of_injective (fun n : ℕ => (n : B.LL)) (fun a b h => by
    have := congrArg B.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hVV : Formalism.L2.DIV.VV B.LL (lamT (B.hcW u) (i + 1)) = polV (I.rec7 l Z) u (i + 1) := by
    rw [GlobalTheory.PdvKm.VV_eq_WtPol, hnat]; rfl
  have key : ∀ c', ∃ z : Formalism.L2.DIV.VV B.LL (lamT (B.hcW u) (i + 1)),
      evV B.fields.emb 1 (lamT (B.hcW u) (i + 1)) B.embLL z = φ c' := by
    intro c'
    obtain ⟨v', hv'⟩ := hv c'
    obtain ⟨⟨Q, hQ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v'
    refine ⟨⟨Q, hVV ▸ hQ⟩, ?_⟩
    rw [← hv']
    clear hnat h3 h1 hlam hφ hv hv'
    show _ = evP O u μ (i + 1) ⟨Q, hQ⟩
    funext y
    rw [evV_apply]
    show _ = (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(twB (I.rec7 l Z) u μ (i + 1) τ))) *
      GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL Q) ((O u μ).frm (i + 1) y)
    have hde : ∀ τ, ((I.rec7 l Z).chTw u μ).de (i + 1) y τ = (y.1 τ).det := fun τ => by
      rw [(O u μ).frm_de (i + 1) hi y τ, hStd.frm u μ (i + 1) y]
      rfl
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.one_mul, shiftOf, twB, GL3Theta.evFr, hStd.frm u μ (i + 1) y, hde, Pi.one_apply]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact congrArg (fun e : ℤ => (y.1 τ).det ^ e) (h4 τ)
  choose z hz using key
  let o : Frames (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb)) :=
    ⟨fun _ => 1, fun τ => by simp⟩
  have hinv : ∀ c' (g : (I.stp u μ (i + 1)).Stab c'),
      (I.stp u μ (i + 1)).rho B.fields.emb (lamT (B.hcW u) (i + 1)) c'.1 g.1 (z c') = z c' := by
    intro c' g
    apply evV_injective B.fields.emb 1 (lamT (B.hcW u) (i + 1)) B.embLL o
    have e1 := Law.evV_rho (I.stp u μ (i + 1)) B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) c'.1 g.1 (z c')
    have e2 := (hφ c').2 g
    refine e1.trans ?_
    refine (congrArg ((I.stp u μ (i + 1)).tr B.fields.emb B.embLL c'.1 g.1) (hz c')).trans ?_
    exact e2.trans (hz c').symm
  refine ⟨⟨z, hinv⟩, ?_⟩
  funext c'
  exact hz c'

end GlobalTheory.Mem.Col2.TC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldFormOfPolynomialModelValueStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientField_form_of_polynomialModel_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) → (∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c') → ∃ x, ((I.tw l l0 Z).fm u μ).emb (i + 1) x = φ := by
  first | exact @GlobalTheory.Mem.Col2.TC.form_of_rat_values | exact GlobalTheory.Mem.Col2.TC.form_of_rat_values | (intros; apply GlobalTheory.Mem.Col2.TC.form_of_rat_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationFormLatticeIffClassValuesWeylLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationFormLatticeIffClassValuesWeylLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LocW

theorem pos_add {x y : WithTop ℤ} (hx : 0 ≤ x) (hy : 0 < y) : 0 < x + y := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    induction y using WithTop.recTopCoe with
    | top => simp
    | coe k =>
      have h1 : (0:ℤ) ≤ m := by exact_mod_cast hx
      have h2 : (0:ℤ) < k := by exact_mod_cast hy
      exact_mod_cast (by omega : (0:ℤ) < m + k)

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (w : Pl.Pl)

theorem val_nonneg_int (a : 𝓞 K) : (0 : WithTop ℤ) ≤ Pl.val w (a : K) := by
  let v : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ) := Pl.val w
  have hi : IsIntegral ℤ (a : K) := RingOfIntegers.isIntegral_coe a
  have h2 : IsIntegral v.integer (a : K) := hi.tower_top
  exact (Valuation.integer.integers v).mem_of_integral h2

def primeW : Ideal (𝓞 K) where
  carrier := {a | (0 : WithTop ℤ) < Pl.val w (a : K)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at *
    exact pos_add (val_nonneg_int Pl w c) ha

theorem mem_primeW (a : 𝓞 K) : a ∈ primeW Pl w ↔ (0 : WithTop ℤ) < Pl.val w (a : K) := Iff.rfl

theorem val_eq_zero_of_not_mem (a : 𝓞 K) (ha : a ∉ primeW Pl w) : Pl.val w (a : K) = 0 := by
  rw [mem_primeW, not_lt] at ha
  exact le_antisymm ha (val_nonneg_int Pl w a)

instance primeW_isPrime : (primeW Pl w).IsPrime where
  ne_top' := by
    intro h
    have : (1 : 𝓞 K) ∈ primeW Pl w := h ▸ Submodule.mem_top
    rw [mem_primeW] at this
    simp at this
  mem_or_mem' := by
    intro a b hab
    by_contra hn
    push Not at hn
    have ha := val_eq_zero_of_not_mem Pl w a hn.1
    have hb := val_eq_zero_of_not_mem Pl w b hn.2
    rw [mem_primeW] at hab
    simp only [map_mul, AddValuation.map_mul, ha, hb, add_zero] at hab
    exact lt_irrefl _ hab

theorem primeW_ne_bot : primeW Pl w ≠ ⊥ := by
  intro h
  have hl : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ primeW Pl w := by
    rw [mem_primeW]
    push_cast
    rw [Pl.val_resChar w]
    exact WithTop.coe_lt_coe.mpr (by have := Pl.ramIdx_pos w; omega)
  rw [h, Submodule.mem_bot] at hl
  have := (Pl.resChar_prime w).ne_zero
  exact this (by exact_mod_cast hl)

theorem exists_den (t : K) (ht : (0 : WithTop ℤ) ≤ Pl.val w t) :
    ∃ a s : 𝓞 K, Pl.val w (s : K) = 0 ∧ (s : K) * t = a := by
  have hS : (primeW Pl w).primeCompl ≤ nonZeroDivisors (𝓞 K) :=
    Ideal.primeCompl_le_nonZeroDivisors _
  let R := Localization.subalgebra.ofField K (primeW Pl w).primeCompl hS
  have : IsLocalization.AtPrime R (primeW Pl w) :=
    Localization.subalgebra.isLocalization_ofField K _ hS
  have : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) (primeW_ne_bot Pl w) R
  have memR : ∀ r : R, ∃ a s : 𝓞 K, s ∉ primeW Pl w ∧ (r : K) = (a : K) * (s : K)⁻¹ := by
    intro r
    obtain ⟨a, s, hs, e⟩ := r.2
    exact ⟨a, s, hs, e⟩
  rcases eq_or_ne t 0 with h0 | h0
  · exact ⟨0, 1, by simp, by simp [h0]⟩
  rcases ValuationRing.isInteger_or_isInteger R t with ⟨r, hr⟩ | ⟨r, hr⟩
  · obtain ⟨a, s, hs, e⟩ := memR r
    have hs0 : (s : K) ≠ 0 := by
      intro h; apply hs; rw [mem_primeW, h]; simp
    refine ⟨a, s, val_eq_zero_of_not_mem Pl w s hs, ?_⟩
    have : (r : K) = t := hr
    rw [← this, e]; field_simp
  · obtain ⟨a, s, hs, e⟩ := memR r
    have hs0 : (s : K) ≠ 0 := by
      intro h; apply hs; rw [mem_primeW, h]; simp
    have hrt : (r : K) = t⁻¹ := hr
    by_cases ha : a ∈ primeW Pl w
    · exfalso
      have hat : (a : K) = t⁻¹ * s := by rw [← hrt, e]; field_simp
      have h1 : Pl.val w (a : K) = Pl.val w t⁻¹ := by
        rw [hat, AddValuation.map_mul, val_eq_zero_of_not_mem Pl w s hs, add_zero]
      have h2 : Pl.val w t + Pl.val w t⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ h0, AddValuation.map_one]
      rw [mem_primeW, h1] at ha
      have := pos_add ht ha
      rw [h2] at this
      exact lt_irrefl _ this
    · have ha0 : (a : K) ≠ 0 := by
        intro h; apply ha; rw [mem_primeW, h]; simp
      refine ⟨s, a, val_eq_zero_of_not_mem Pl w a ha, ?_⟩
      have : t = (s : K) * (a : K)⁻¹ := by
        rw [← inv_inv t, ← hrt, e]; field_simp
      rw [this]; field_simp

end GlobalTheory.LocW


open GlobalTheory.LocW in
theorem GlobalTheory.Mem.Col2.GStep.locW_latOf_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (Pl : Rows.Places K) (w : Pl.Pl) (p : ℕ) [Fact p.Prime] (iL : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖iL x‖ ≤ 1) → ∀ x : S.FormsK emb lam h, x ∈ locW Pl w (S.latOf emb lam h fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  intro E K ι _ _ _ _ _ _ _ n S emb lam h Pl w p _ iL _ x
  classical
  letI : Fintype S.Cl := h.fintypeCl
  have smulK : ∀ (b : 𝓞 K) (v : VV K lam), b • v = (b : K) • v := fun b v =>
    (algebraMap_smul K b v).symm
  constructor
  · intro hx c
    unfold locW at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hy c)
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul t y _ hy => exact Submodule.smul_mem _ t hy
  · intro hall
    have gen : ∀ (M : Submodule (𝓞 K) (VV K lam)) (y : VV K lam),
        y ∈ Submodule.span (intW Pl w) (M : Set (VV K lam)) →
        ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧ s • y ∈ M := by
      intro M y hy
      induction hy using Submodule.span_induction with
      | mem v hv => exact ⟨1, by simp, by rw [smulK]; push_cast; rw [one_smul]; exact hv⟩
      | zero => exact ⟨1, by simp, by rw [smulK, smul_zero]; exact Submodule.zero_mem _⟩
      | add u v _ _ hu hv =>
        obtain ⟨s1, h1, m1⟩ := hu
        obtain ⟨s2, h2, m2⟩ := hv
        refine ⟨s1 * s2, by push_cast; rw [AddValuation.map_mul, h1, h2, add_zero], ?_⟩
        have e0 : (s1 * s2) • (u + v) = (s1 * s2) • u + (s1 * s2) • v := by
          rw [smulK, smulK, smulK, smul_add]
        rw [e0]
        have e1 : (s1 * s2) • u = s2 • (s1 • u) := by
          rw [smulK, smulK, smulK, smul_smul]; push_cast; rw [mul_comm]
        have e2 : (s1 * s2) • v = s1 • (s2 • v) := by
          rw [smulK, smulK, smulK, smul_smul]; push_cast; rfl
        rw [e1, e2]
        exact Submodule.add_mem _ (Submodule.smul_mem _ s2 m1) (Submodule.smul_mem _ s1 m2)
      | smul t u _ hu =>
        obtain ⟨s, hs, m⟩ := hu
        obtain ⟨a, s', hs', e⟩ := exists_den Pl w (t : K) t.2
        refine ⟨s' * s, by push_cast; rw [AddValuation.map_mul, hs, hs', add_zero], ?_⟩
        have : (s' * s) • (t • u) = a • (s • u) := by
          rw [smulK, smulK, smulK, Subring.smul_def, smul_smul, smul_smul, ← e]
          congr 1
          push_cast
          ring
        rw [this]
        exact Submodule.smul_mem _ a m
    have key : ∀ c, ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧
        s • x.1 c ∈ delAtr emb lam (S.Lsh c.1 (S.rep c)) := fun c => gen _ _ (hall c)
    have common : ∀ F : Finset S.Cl, ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧
        ∀ c ∈ F, s • x.1 c ∈ delAtr emb lam (S.Lsh c.1 (S.rep c)) := by
      intro F
      induction F using Finset.induction_on with
      | empty => exact ⟨1, by simp, by simp⟩
      | insert c F _ ih =>
        obtain ⟨s1, h1, m1⟩ := ih
        obtain ⟨s2, h2, m2⟩ := key c
        refine ⟨s1 * s2, by push_cast; rw [AddValuation.map_mul, h1, h2, add_zero], ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.mp hc' with rfl | hc'
        · have e : (s1 * s2) • x.1 c' = s1 • (s2 • x.1 c') := by
            rw [smulK, smulK, smulK, smul_smul]; push_cast; rfl
          rw [e]; exact Submodule.smul_mem _ s1 m2
        · have e : (s1 * s2) • x.1 c' = s2 • (s1 • x.1 c') := by
            rw [smulK, smulK, smulK, smul_smul]; push_cast; rw [mul_comm]
          rw [e]; exact Submodule.smul_mem _ s2 (m1 c' hc')
    obtain ⟨s, hs, hsm⟩ := common Finset.univ
    have hsx : s • x ∈ S.latOf emb lam h (fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
      intro c
      exact hsm c (Finset.mem_univ c)
    have hs0 : (s : K) ≠ 0 := by
      intro h0; rw [h0, AddValuation.map_zero] at hs; exact WithTop.top_ne_zero hs
    have hinv : Pl.val w (s : K)⁻¹ = 0 := by
      have := AddValuation.map_mul (Pl.val w) (s : K) (s : K)⁻¹
      rw [mul_inv_cancel₀ hs0, AddValuation.map_one, hs, zero_add] at this
      exact this.symm
    let u : intW Pl w := ⟨(s : K)⁻¹, by show (0 : WithTop ℤ) ≤ _; rw [hinv]⟩
    have hx : x = u • (s • x) := by
      apply Subtype.ext
      funext c
      show x.1 c = (s : K)⁻¹ • (s • x.1 c)
      rw [smulK, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [hx]
    unfold locW
    exact Submodule.smul_mem _ u (Submodule.subset_span hsx)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationFormLatticeIffClassValuesWeylLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_formLattice_iff_classValues_weylLattice : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (Pl : Rows.Places K) (w : Pl.Pl) (p : ℕ) [Fact p.Prime] (iL : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖iL x‖ ≤ 1) → ∀ x : S.FormsK emb lam h, x ∈ locW Pl w (S.latOf emb lam h fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.locW_latOf_iff | exact GlobalTheory.Mem.Col2.GStep.locW_latOf_iff | (intros; apply GlobalTheory.Mem.Col2.GStep.locW_latOf_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelDatumLatticeTargetSideTrueChains
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 1000000 in
theorem kerEnt_latT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, (∃ y ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat (i + 1)).L, ((I.tw l l0 Z).fm u μ).emb (i + 1) y = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) ∧ ∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c' ∧ ∀ J, ‖prTC Pl O Bs u μ w i c' v' J‖ ≤ 1) := by
  intro B X I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi φ
  have hL1 := fun x => GlobalTheory.T.localisation_formLattice_iff_classValues_weylLattice (I.stp u μ (i + 1)) B.fields.emb (lamT (B.hcW u) (i + 1)) ((l.fmL u μ).fam (i + 1))
    B.places w _ (Pl.iL w) (Pl.iL_int w) x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, fun c' => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [← (((I.tw l l0 Z).fm u μ).emb_basis (i + 1)).2, ← ((((I.tw l l0 Z).fm u μ).lat (i + 1)).b.sum_repr y), map_sum]
        exact Submodule.sum_mem _ fun a _ => by
          rw [LinearMap.map_smulₛₗ]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · obtain ⟨v', hv'⟩ := GlobalTheory.T.coefficientField_form_value_mem_polynomialModel I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ i hi y c'
      exact ⟨v', hv', (GlobalTheory.T.mem_localisedWeylLattice_iff_targetPairing_integral I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi c' (y.1 c') v' hv').1
        ((hL1 y).1 hy c')⟩
  · rintro ⟨hF, hc⟩
    obtain ⟨x, rfl⟩ := GlobalTheory.T.exists_coefficientField_form_of_polynomialModel_values I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ i hi φ hF
      (fun c' => (hc c').imp fun _ h => h.1)
    refine ⟨x, (hL1 x).2 fun c' => ?_, rfl⟩
    obtain ⟨v', hv', hn⟩ := hc c'
    exact (GlobalTheory.T.mem_localisedWeylLattice_iff_targetPairing_integral I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi c' (x.1 c') v' hv').2 hn

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelDatumLatticeTargetSideTrueChainsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatum_lattice_target_side_trueChains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, (∃ y ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat (i + 1)).L, ((I.tw l l0 Z).fm u μ).emb (i + 1) y = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) ∧ ∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c' ∧ ∀ J, ‖prTC Pl O Bs u μ w i c' v' J‖ ≤ 1) := by
  first | exact @GlobalTheory.Mem.Col2.TC.kerEnt_latT | exact GlobalTheory.Mem.Col2.TC.kerEnt_latT | (intros; apply GlobalTheory.Mem.Col2.TC.kerEnt_latT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TargetPairingSizesInCoefficientFieldValueGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TargetPairingSizesInCoefficientFieldValueGroup
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerVal
open MvPolynomial

theorem deX_map {Lt k k' : Type} [Fintype Lt] [CommRing k] [CommRing k'] (f : k →+* k') (N : ℕ) (nu : Lt → YoungDiagram)
    (y : Lt → Fin N → ℕ → k) : MvPolynomial.map f (GL3Columns.DeX N nu y) = GL3Columns.DeX N nu (fun s a j => f (y s a j)) := by
  unfold GL3Columns.DeX
  simp only [map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => congrArg Matrix.det ?_
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, map_C, map_X]

theorem dual_map_eval {σ V k : Type} [Field k] (χ : Module.Dual k (MvPolynomial σ k)) (p : MvPolynomial σ (MvPolynomial V k)) (x : V → k) :
    MvPolynomial.eval x (∑ m ∈ p.support, AddMonoidAlgebra.coeff p m * C (χ (monomial m 1))) = χ (MvPolynomial.map (MvPolynomial.eval x) p) := by
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, eval_C, map_monomial]
  rw [show monomial m (MvPolynomial.eval x (AddMonoidAlgebra.coeff p m)) = (MvPolynomial.eval x (AddMonoidAlgebra.coeff p m)) • (monomial m 1 : MvPolynomial σ k) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, smul_eq_mul]

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7} (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram)

def uFr : Bool × HH D → Fin N → ℕ → MvPolynomial (GL3Theta.FrV D N) (Cw D w) :=
  fun s a j => if h : j < N then X (tauPl D s, a, ⟨j, h⟩) else 0

def canPol (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) : MvPolynomial (GL3Theta.FrV D N) (Cw D w) :=
  ∑ m ∈ (GL3Columns.DeX N nu (uFr w N)).support, AddMonoidAlgebra.coeff (GL3Columns.DeX N nu (uFr w N)) m * C (χ (monomial m 1))

theorem canM_apply (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) (y : FrP D w N) :
    canM D w N nu χ y = χ (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s))) := rfl

theorem canM_eq_eval (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) (y : FrP D w N) :
    canM D w N nu χ y = MvPolynomial.eval (fun v : GL3Theta.FrV D N => y v.1 v.2.1 v.2.2) (canPol w N nu χ) := by
  have e1 : (fun s a j => MvPolynomial.eval (fun v : GL3Theta.FrV D N => y v.1 v.2.1 v.2.2) (uFr w N s a j)) =
      fun s => GL3Columns.colsOf (y (tauPl D s)) := by
    funext s a j
    unfold uFr GL3Columns.colsOf
    split_ifs <;> simp
  unfold canPol
  rw [dual_map_eval, deX_map, e1, canM_apply]

theorem canM_ker (hfit : ∀ s c, (nu s).colLen c ≤ N) (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)))
    (h0 : ∀ y, canM D w N nu χ y = 0) (J : KM.ColChoice N nu) :
    χ (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N nu J)) = 0 := by
  refine GL3Columns.wwInj_holds D (D.what₂.places.resChar w) N nu χ (fun y => ?_) J
  let e := Equiv.ofBijective (tauPl D) (Formalism.L2.DIV.tauPl_bijective D)
  have h1 : χ (GL3Columns.DeX N nu fun s => GL3Columns.colsOf ((fun τ (a b : Fin N) => y (e.symm τ) a (b : ℕ)) (tauPl D s))) = 0 :=
    h0 (fun τ (a b : Fin N) => y (e.symm τ) a (b : ℕ))
  refine Eq.trans (congrArg χ ?_) h1
  unfold GL3Columns.DeX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => congrArg Matrix.det ?_
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (hfit s c)
  have hs : e.symm (tauPl D s) = s := e.symm_apply_apply s
  simp only [Matrix.of_apply, GL3Columns.colsOf, dif_pos hj, hs]

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7} (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram)

theorem colsOf_map {k k' : Type} [CommRing k] [CommRing k'] (f : k →+* k') {M : ℕ} (Y : Matrix (Fin M) (Fin M) k) (a : Fin M) (j : ℕ) :
    f (GL3Columns.colsOf Y a j) = GL3Columns.colsOf (Y.map f) a j := by
  unfold GL3Columns.colsOf
  split_ifs <;> simp

theorem onMin_canInv_mem (hfit : ∀ s c, (nu s).colLen c ≤ N) (F : FrP D w N → Cw D w) (hF : F ∈ LinearMap.range (canM D w N nu))
    (hrat : ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) D.what₂.LL, ∃ x, F (fun τ => (y τ).map (P.iL w)) = P.iL w x)
    (J : KM.ColChoice N nu) : ∃ b : D.what₂.LL, onMin D w N nu (canInv D w N nu F) J = P.iL w b := by
  set ψ := canInv D w N nu F with hψdef
  have hψ : canM D w N nu ψ = F := canInv_spec D w N nu F hF
  letI : Algebra D.what₂.LL (Cw D w) := (P.iL w).toAlgebra
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap D.what₂.LL (Cw D w))
    (LinearMap.ker_eq_bot.2 (P.iL w).injective)
  let ρ : Cw D w → Cw D w := fun z => P.iL w (π z)
  have ρ_add : ∀ a b, ρ (a + b) = ρ a + ρ b := fun a b => by
    simp only [ρ, map_add (f := _)]
  have ρ_mul : ∀ x z, ρ (P.iL w x * z) = P.iL w x * ρ z := fun x z => by
    have : P.iL w x * z = x • z := by rw [Algebra.smul_def]; rfl
    simp only [ρ, this, map_smul, smul_eq_mul, map_mul]
  have ρ_fix : ∀ x, ρ (P.iL w x) = P.iL w x := fun x => by
    have := LinearMap.congr_fun hπ x
    simp only [ρ]
    exact congrArg (P.iL w) this
  let ψ' : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)) :=
    (MvPolynomial.basisMonomials _ (Cw D w)).constr (Cw D w) fun m => ρ (ψ (monomial m 1))
  have ψ'_mon : ∀ m, ψ' (monomial m 1) = ρ (ψ (monomial m 1)) := fun m => by
    have := (MvPolynomial.basisMonomials ((Bool × HH D) × ℕ × Fin N) (Cw D w)).constr_basis (Cw D w)
      (fun m => ρ (ψ (monomial m 1))) m
    rw [MvPolynomial.coe_basisMonomials] at this
    exact this
  have key : ∀ q : MvPolynomial ((Bool × HH D) × ℕ × Fin N) D.what₂.LL,
      ψ' (MvPolynomial.map (P.iL w) q) = ρ (ψ (MvPolynomial.map (P.iL w) q)) := by
    intro q
    induction q using MvPolynomial.induction_on' with
    | monomial m x =>
      have e : MvPolynomial.map (P.iL w) (monomial m x) = P.iL w x • (monomial m 1 : MvPolynomial _ (Cw D w)) := by
        rw [map_monomial, smul_monomial, smul_eq_mul, mul_one]
      rw [e, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ρ_mul, ψ'_mon]
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, ρ_add]
  have hpt : ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) D.what₂.LL,
      canM D w N nu ψ' (fun τ => (y τ).map (P.iL w)) = canM D w N nu ψ (fun τ => (y τ).map (P.iL w)) := by
    intro y
    have e : (GL3Columns.DeX N nu fun s => GL3Columns.colsOf ((fun τ => (y τ).map (P.iL w)) (tauPl D s))) =
        MvPolynomial.map (P.iL w) (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s))) := by
      rw [deX_map]
      congr 1
      funext s a j
      rw [colsOf_map]
    rw [canM_apply, canM_apply, e, key, ← e]
    change ρ (canM D w N nu ψ (fun τ => (y τ).map (P.iL w))) = canM D w N nu ψ (fun τ => (y τ).map (P.iL w))
    obtain ⟨x, hx⟩ := hrat y
    rw [hψ, hx, ρ_fix]
  have hCZ : Set.Infinite (Set.range (Nat.cast : ℕ → Cw D w)) := Set.infinite_range_of_injective Nat.cast_injective
  have hpol : canPol w N nu (ψ' - ψ) = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → Cw D w)) (fun _ => hCZ) fun x hx => ?_
    choose n hn using fun v => hx v (Set.mem_univ v)
    have e : (fun v : GL3Theta.FrV D N => x v) = fun v => ((fun τ => (Matrix.of fun a b => ((n (τ, a, b) : ℕ) : D.what₂.LL)).map (P.iL w)) :
        FrP D w N) v.1 v.2.1 v.2.2 := by
      funext v
      simp [hn]
    have h1 := canM_eq_eval w N nu (ψ' - ψ) (fun τ => (Matrix.of fun a b => ((n (τ, a, b) : ℕ) : D.what₂.LL)).map (P.iL w))
    simp only [map_sub, Pi.sub_apply, hpt, sub_self] at h1
    rw [map_zero, show x = _ from e]
    exact h1.symm
  have h0 : ∀ y, canM D w N nu (ψ' - ψ) y = 0 := fun y => by
    rw [canM_eq_eval, hpol, map_zero]
  have hJ := canM_ker w N nu hfit (ψ' - ψ) h0 J
  have eJ : MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J) =
      MvPolynomial.map (P.iL w) (MvPolynomial.map (Int.castRingHom D.what₂.LL) (KM.nablaX N nu J)) := by
    rw [MvPolynomial.map_map, RingHom.ext_int ((P.iL w).comp (Int.castRingHom _)) (Int.castRingHom _)]
  rw [LinearMap.sub_apply, sub_eq_zero, eJ, key] at hJ
  exact ⟨π (ψ (MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J))), by
    show ψ (MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J)) = _
    rw [eJ]
    exact hJ.symm⟩

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

theorem colLen_le_of_fits {D : D7} {N : ℕ} {nu : Bool × HH D → YoungDiagram} {ν : D.what₂.Tau → Fin N → ℕ} (h : NuFits D nu ν) :
    ∀ s c, (nu s).colLen c ≤ N := by
  intro s c
  by_contra hc
  have hm : (N, c) ∈ nu s := (nu s).mem_iff_lt_colLen.2 (lt_of_not_ge hc)
  have h1 := (nu s).mem_iff_lt_rowLen.1 hm
  rw [h.2 s N le_rfl] at h1
  exact Nat.not_lt_zero _ h1

theorem tgtFun_rat {D : D7} (P : Examples₂.EntPl D) (Bs : PlaceMatrixFamily D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ)
    (c' : (D.chTw u μ).cls (i + 1)) (hE : ∀ τ j k, ∃ x : D.what₂.LL, Bs u μ w (i + 1) c' τ j k = P.iL w x) (v : polV D u (i + 1))
    (y : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.what₂.LL) :
    ∃ x, tgtFun P Bs u μ w i c' v (fun τ => (y τ).map (P.iL w)) = P.iL w x := by
  choose B' hB' using hE
  have hB : Bs u μ w (i + 1) c' = fun τ => (Matrix.of (B' τ)).map (P.iL w) := by
    funext τ
    ext j k
    exact hB' τ j k
  refine ⟨(∏ τ, (Matrix.of (B' τ)).det ^ (-(D.chTw u μ).sDiv i τ)) *
    MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Matrix.of (B' k.1) * y k.1) k.2.1 k.2.2)
      (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL), ?_⟩
  show (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-(D.chTw u μ).sDiv i τ)) *
    MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Bs u μ w (i + 1) c' k.1 * (y k.1).map (P.iL w)) k.2.1 k.2.2)
      (MvPolynomial.map (P.iL w) (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL)) = _
  rw [hB, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  · have h2 := MvPolynomial.eval₂_comp_left (P.iL w) (RingHom.id D.what₂.LL)
      (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Matrix.of (B' k.1) * y k.1) k.2.1 k.2.2)
      (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL)
    refine Eq.trans ?_ h2.symm
    rw [MvPolynomial.eval_map, RingHom.comp_id]
    congr 1
    funext k
    rw [Function.comp_apply, ← Matrix.map_mul]
    rfl

end GlobalTheory.KerVal

theorem GlobalTheory.KerVal.prTC_val : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v' : ValQ O u μ (i + 1)) (J : KM.ColChoice ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i)), ∃ b : (I.rec7 l Z).what₂.LL, ‖prTC Pl O Bs u μ w i c' v' J‖ = ‖Pl.iL w b‖ := by
  intro B X I _ _ l Z _ Y O Pl Bs _ _ _ hEnt _ _ u μ w hw i hi c' v' J
  obtain ⟨b, hb⟩ := GlobalTheory.KerVal.onMin_canInv_mem Pl w _ _
    (GlobalTheory.KerVal.colLen_le_of_fits (nuFits_tgt (I.rec7 l Z) u i hi))
    (tgtFun Pl Bs u μ w i c' (secC O u μ (i + 1) v'))
    (canT_of Pl Bs (GlobalTheory.T.toy_entPl_canOnto _ Pl) u μ w i hi c' (secC O u μ (i + 1) v'))
    (GlobalTheory.KerVal.tgtFun_rat Pl Bs u μ w i c' (hEnt u μ w hw (i + 1) hi c') (secC O u μ (i + 1) v')) J
  exact ⟨b, congrArg norm hb⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TargetPairingSizesInCoefficientFieldValueGroupStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.targetPairing_sizes_in_coefficientField_valueGroup : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v' : ValQ O u μ (i + 1)) (J : KM.ColChoice ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i)), ∃ b : (I.rec7 l Z).what₂.LL, ‖prTC Pl O Bs u μ w i c' v' J‖ = ‖Pl.iL w b‖ := by
  first | exact @GlobalTheory.KerVal.prTC_val | exact GlobalTheory.KerVal.prTC_val | (intros; apply GlobalTheory.KerVal.prTC_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntryHypOfTrueColumnChoices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntHyp_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → KerEntHyp Pl O Bs Y (I.tw l l0 Z) := fun I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8 =>
  ⟨GlobalTheory.T.targetPairing_sizes_in_coefficientField_valueGroup I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.trueChains_kernelDatum_sourceSideLattice I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.kernelDatum_lattice_target_side_trueChains I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.kernelEntries_form_true_chains I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8⟩

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntryHypOfTrueColumnChoicesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntryHyp_of_trueColumnChoices : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → KerEntHyp Pl O Bs Y (I.tw l l0 Z) := by
  first | exact @GlobalTheory.Mem.Col2.TC.kerEntHyp_true | exact GlobalTheory.Mem.Col2.TC.kerEntHyp_true | (intros; apply GlobalTheory.Mem.Col2.TC.kerEntHyp_true <;> assumption)
end
