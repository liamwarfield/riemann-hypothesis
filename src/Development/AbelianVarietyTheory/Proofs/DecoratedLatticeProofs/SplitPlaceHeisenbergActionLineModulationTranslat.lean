module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TraceInverseGramConjSmulEq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Model

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')

include l in
theorem tau_gram (h : IsLineVec L' ζ') :
    l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have hn := l.norm
  have hm : B.ζ = -(l.τ *ᵥ ζ') := by rw [l.map, neg_neg]
  have h0 := h.2
  rw [hm, star_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, Matrix.star_mulVec, ← dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc] at hn
  refine Matrix.ext fun i j => ?_
  obtain rfl := Subsingleton.elim i default
  obtain rfl := Subsingleton.elim j default
  generalize l.τᴴ * (B.L.gram * l.τ) = M at hn ⊢
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique, Pi.star_apply] at hn h0
  have hz : ζ' default ≠ 0 := fun e => h0 (by rw [e]; simp)
  have hz' : star (ζ' default) ≠ 0 := star_ne_zero.2 hz
  rw [Matrix.smul_apply, smul_eq_mul]
  apply mul_right_cancel₀ hz
  apply mul_left_cancel₀ hz'
  rw [hn]; ring


end GlobalTheory.Unf.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualPickDot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def iota (p : SplitPt D k) : D.host.E →+* k := p.pr.comp (incA D)

def dualPick {m : Type} [DecidableEq m] (g : m → k) : m → k := by
  classical
  exact if h : ∃ i, g i ≠ 0 then Pi.single h.choose (g h.choose)⁻¹ else 0

theorem dualPick_dot {m : Type} [Fintype m] [DecidableEq m] (g : m → k) (hg : g ≠ 0) : dualPick g ⬝ᵥ g = 1 := by
  classical
  have h : ∃ i, g i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hg (funext h')
  unfold dualPick
  rw [dite_eq_left h]
  simp only [single_dotProduct]
  exact inv_mul_cancel₀ h.choose_spec

variable {n : Type} [Fintype n] [DecidableEq n]

def wRow (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) : WO W₀ L' :=
  Matrix.of fun i j => p.sec (iota p (ζ' i) * (t ᵥ* β.b') j)

def wCol (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) : WO W₀ L' :=
  Matrix.of fun i j => cA D (p.sec (dualPick ((L'.gram.map (iota p)) *ᵥ fun i => iota p (ζ' i)) i *
    ((iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) j)))

end GlobalTheory.FinPl.LineAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfPointNegMultipliesByCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfPointNegMultipliesByCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct.ConjModul

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_sec (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem pr_trace (p : SplitPt D k) {m : ℕ} (M : Mx D m m) : p.pr M.trace = (M.map p.pr).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

theorem map_rat (p : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat M).map p.pr = M.map (iota p) := by
  ext i j; rfl


open GlobalTheory.FinPl.LineAct in
set_option maxHeartbeats 1600000 in
theorem conj_half_modul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf (cA D p.e) ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t)) ∧ ∀ x : WO W₀ S₀, IsHalf p.e x → ψ (symplO W₀ S₀ x ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t))) = (χ (-((fun j => rd β γ₀ x (Sum.inr 0) j) ⬝ᵥ t)) : ℂ) := by
  intro D k _ _ _ _ p ψ χ hχ n n'' _ _ _ _ S₀ A L W₀ o ζ hζ β γ γ₀ hγ t
  refine ⟨fun i j => ?_, fun x _ => ?_⟩
  · rw [OrthDec.resT_symm_apply]
    simp only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.neg_apply, mul_neg, Matrix.mul_apply, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [wCol, Matrix.of_apply]
    rw [mul_left_comm, ← map_mul, e_mul_sec]
  · have hy : (o.resT W₀) ((o.resT W₀).symm (0, -wCol p ζ β t)) = (0, -wCol p ζ β t) := AddEquiv.apply_symm_apply _ _
    rw [OrthDec.symplO_resT, hy]
    have h0 : symplO W₀ A ((o.resT W₀) x).1 0 = 0 := by
      rw [symplO_eq, hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]
    rw [h0, zero_add, symplO_eq, OrthDec.resT_apply, hO_eq_trace]
    set T := (giA W₀ ⬝ (adj (-wCol p ζ β t) ⬝ (gA L ⬝ (o.pB ⬝ x)))).trace with hT
    set u' : Fin L.rank → k := dualPick ((L.gram.map (iota p)) *ᵥ fun i => iota p (ζ i)) with hu'
    set v : Fin W₀.rank → k := fun j => (iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) j with hv
    have hadj : adj (-wCol p ζ β t) = Matrix.of fun i j => -p.sec (u' j * v i) := by
      ext i j
      simp only [adj, wCol, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.of_apply, map_neg,
        Formalism.L2.Theta.cA_cA, hu', hv]
    have hZ : p.e • adj (-wCol p ζ β t) = adj (-wCol p ζ β t) := by
      rw [hadj]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_neg, e_mul_sec]
    have heT : p.e * T = T := by
      conv_rhs => rw [hT, ← hZ]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hc : p.e * (incA D D.host.xi0 * T) = incA D D.host.xi0 * T := by rw [mul_left_comm, heT]
    have key : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * T)) =
        (χ (p.pr (incA D D.host.xi0 * T)) : ℂ) := by
      rw [hχ, p.sec_pr, hc]; rfl
    rw [key]
    have hxi : iota p D.host.xi0 ≠ 0 := (map_ne_zero (iota p)).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    set ζb : Fin L.rank → k := fun i => iota p (ζ i) with hζb
    set R := rd β γ₀ x with hR
    set η : n → k := fun j => R (Sum.inr 0) j with hη
    have hx : x.map p.pr = γ₀.b * R * β.b' := by
      rw [hR, rd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, γ₀.bb', Matrix.one_mul, Matrix.mul_assoc, β.bb',
        Matrix.mul_one]
    have hvec : (fun m => p.pr (ratV (vecB o ζ) m)) = (o.iB.map (iota p)) *ᵥ ζb := by
      funext m
      exact RingHom.map_mulVec (iota p) o.iB ζ m
    have hQ : o.qB.map (iota p) * γ₀.b = fromCols 0 (replicateCol (Fin 1) ζb) := by
      rw [hγ, Matrix.mul_fromCols, OrthDec.jA, map_rat, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qB_iA,
        Matrix.map_zero _ (map_zero _), Matrix.zero_mul]
      congr 1
      ext i j
      simp only [Matrix.mul_apply, Matrix.replicateCol_apply]
      change (o.qB.map (iota p) *ᵥ fun m => p.pr (ratV (vecB o ζ) m)) i = ζb i
      rw [hvec, Matrix.mulVec_mulVec, ← Matrix.map_mul, o.qB_iB, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    have hQR : fromCols (0 : Matrix (Fin L.rank) n'' k) (replicateCol (Fin 1) ζb) * R = vecMulVec ζb η := by
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_sum_type, vecMulVec_apply, hη]
    have hqx : o.qB.map (iota p) * x.map p.pr = vecMulVec ζb (η ᵥ* β.b') := by
      rw [hx, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, hQR, vecMulVec_mul]
    have hg : L.gram.map (iota p) *ᵥ ζb ≠ 0 := by
      intro h0
      apply hζ.2
      have h1 : L.gram *ᵥ ζ = 0 := by
        funext i
        apply (iota p).injective
        rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
        exact congrFun h0 i
      rw [h1, dotProduct_zero]
    have hu1 : u' ⬝ᵥ (L.gram.map (iota p) *ᵥ ζb) = 1 := dualPick_dot _ hg
    have hZb : (Matrix.of fun i j => -p.sec (u' j * v i)).map p.pr = -vecMulVec v u' := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_neg, p.pr_sec, Matrix.neg_apply, vecMulVec_apply, mul_comm]
    have hv' : v = (iota p D.host.xi0)⁻¹ • ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) := rfl
    have hGi : (W₀.gram⁻¹).map (iota p) * W₀.gram.map (iota p) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (gram_isUnit_det W₀), Matrix.map_one _ (map_zero _) (map_one _)]
    have hval : p.pr (incA D D.host.xi0 * T) = -(η ⬝ᵥ t) := by
      rw [map_mul, hT, pr_trace, hadj]
      simp only [Matrix.map_mul, giA, gA, OrthDec.pB, map_rat, hZb]
      rw [hqx, Matrix.mul_vecMulVec, Matrix.neg_mul, Matrix.vecMulVec_mul_vecMulVec, hu1, one_smul, Matrix.mul_neg,
        Matrix.mul_vecMulVec, Matrix.trace_neg, Matrix.trace_vecMulVec, hv', Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        hGi, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul, dotProduct_comm, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul, β.b'b, Matrix.vecMul_one]
      change iota p D.host.xi0 * -((iota p D.host.xi0)⁻¹ * (η ⬝ᵥ t)) = -(η ⬝ᵥ t)
      field_simp
    rw [hval]

end GlobalTheory.FinPl.LineAct.ConjModul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfPointNegMultipliesByCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateHalfPoint_neg_multiplies_by_character : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf (cA D p.e) ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t)) ∧ ∀ x : WO W₀ S₀, IsHalf p.e x → ψ (symplO W₀ S₀ x ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t))) = (χ (-((fun j => rd β γ₀ x (Sum.inr 0) j) ⬝ᵥ t)) : ℂ) := by
  first | exact @GlobalTheory.FinPl.LineAct.ConjModul.conj_half_modul | exact GlobalTheory.FinPl.LineAct.ConjModul.conj_half_modul | (intros; apply GlobalTheory.FinPl.LineAct.ConjModul.conj_half_modul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaSplitHalfPointMultipliesByCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaSplitHalfPointMultipliesByCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaRowChar

variable {D : D7}

theorem half_mul_right {m n r : ℕ} {f : AE D} {M : Mx D m n} (h : IsHalf f M) (N : Mx D n r) : IsHalf f (M ⬝ N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i _]

theorem half_mul_left {m n r : ℕ} {f : AE D} {M : Mx D n r} (N : Mx D m n) (h : IsHalf f M) : IsHalf f (N ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

theorem half_smul {m n : ℕ} {f : AE D} {M : Mx D m n} (c : AE D) (h : IsHalf f M) : IsHalf f (c • M) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, h i j]

theorem half_adj {m n : ℕ} {f : AE D} {M : Mx D m n} (h : IsHalf f M) : IsHalf (cA D f) (adj M) := by
  intro i j
  show cA D f * cA D (M j i) = cA D (M j i)
  rw [← map_mul, h j i]

theorem trace_half {n : ℕ} {f : AE D} {M : Mx D n n} (h : IsHalf f M) : f * M.trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, h _ _]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_sec (p : GlobalTheory.FinPl.SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem wRow_half {n : Type} [Fintype n] [DecidableEq n] (p : GlobalTheory.FinPl.SplitPt D k) {W₀ L' : HSp D}
    (ζ' : Fin L'.rank → D.host.E) (β : GlobalTheory.FinPl.Frame p W₀ n) (t : n → k) :
    IsHalf p.e (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := by
  intro i j
  exact e_mul_sec p _

theorem trace_vecMulVec_mul {R : Type} [CommRing R] {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    (u : a → R) (v : b → R) (X : Matrix b c R) (J : Matrix c a R) :
    (vecMulVec u v * X * J).trace = v ⬝ᵥ (X *ᵥ (J *ᵥ u)) := by
  rw [Matrix.mul_assoc, Matrix.mulVec_mulVec]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KappaRowChar

end

namespace GlobalTheory.KappaRowChar

open GlobalTheory.FinPl.LineAct (iota)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_trace {n : Type} [Fintype n] [DecidableEq n] (p : GlobalTheory.FinPl.SplitPt D k) {W₀ L' : HSp D} {a b : ℕ}
    (τ : Matrix (Fin a) (Fin L'.rank) D.host.E) (ζ' : Fin L'.rank → D.host.E) (ζ : Fin a → D.host.E) (hτ : τ *ᵥ ζ' = -ζ)
    (β : GlobalTheory.FinPl.Frame p W₀ n) (t : n → k) (x : Mx D W₀.rank b) (iB : Matrix (Fin b) (Fin a) D.host.E) :
    p.pr (((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).trace =
      -(t ⬝ᵥ (β.b' *ᵥ (x.map p.pr *ᵥ (iB.map (iota p) *ᵥ fun i => iota p (ζ i))))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show p.pr (((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).trace =
      ((((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).map p.pr).trace from by
    simp only [Matrix.trace, Matrix.diag, map_sum]; rfl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  have hτm : (rat τ : Mx D a L'.rank).map p.pr = τ.map (iota p) := rfl
  have hwm : (GlobalTheory.FinPl.LineAct.wRow p ζ' β t).map p.pr = vecMulVec (fun i => iota p (ζ' i)) (t ᵥ* β.b') := by
    ext i j
    simp only [Matrix.map_apply, GlobalTheory.FinPl.LineAct.wRow, Matrix.of_apply, p.pr_sec, vecMulVec_apply]
  have hjm : (rat iB : Mx D b a).map p.pr = iB.map (iota p) := rfl
  have ha : τ.map (iota p) *ᵥ (fun i => iota p (ζ' i)) = -(fun i => iota p (ζ i)) := by
    funext i
    have h := RingHom.map_mulVec (iota p) τ ζ' i
    rw [hτ] at h
    simp only [Pi.neg_apply, map_neg] at h ⊢
    exact h.symm
  rw [hτm, hwm, hjm, Matrix.mul_vecMulVec, ← Matrix.mul_assoc, trace_vecMulVec_mul, ha, Matrix.mulVec_neg,
    Matrix.mulVec_neg, dotProduct_neg, Matrix.dotProduct_mulVec t]

end GlobalTheory.KappaRowChar

namespace GlobalTheory.KappaRowChar

open GlobalTheory.FinPl.LineAct (iota)


set_option maxHeartbeats 1600000 in
theorem kappa_wRow_char : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf (cA D p.e) ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) ∧ ∀ x : WO B.V₀ W₀, IsHalf p.e x → ψ (symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)))) = (χ (-(t ⬝ᵥ fun i => rd α₀ β x i (Sum.inr 0))) : ℂ) := by
  intro D k _ _ _ _ p ψ χ hχ n n' _ _ _ _ ρ B L' W₀ ζ' l α α₀ β hsum t
  have hwh : IsHalf p.e (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := wRow_half p ζ' β t
  have hmh : IsHalf p.e ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := half_mul_left _ hwh
  have hk : l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) = incA D (-D.host.xi0⁻¹) •
      (giA W₀ ⬝ (adj ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ gA B.L)) := rfl
  have hu : (B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)) =
      l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
  refine ⟨?_, fun x _ => ?_⟩
  · rw [hu, hk]
    exact half_mul_right (half_smul _ (half_mul_left _ (half_mul_right (half_adj hmh) _))) _
  · have h0 : symplO B.A W₀ ((B.o.resS W₀) x).1 0 = 0 := by simp [symplO, hO]
    have hxi : incA D D.host.xi0 * cA D (incA D (-D.host.xi0⁻¹)) = 1 := by
      have hne := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
      rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, neg_inv, neg_neg,
        mul_inv_cancel₀ hne, map_one]
    have hxi' : ∀ T : AE D, incA D D.host.xi0 * (cA D (incA D (-D.host.xi0⁻¹)) * T) = T := fun T => by
      rw [← mul_assoc, hxi, one_mul]
    have hs : symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) =
        Algebra.trace (AF D.host.F) (AE D)
          (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ B.o.jB)).trace := by
      rw [OrthDec.symplO_resS, AddEquiv.apply_symm_apply, h0, zero_add, symplO, hO_eq_trace, hk]
      simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
        giA_gA_cancel, trace_smul, smul_eq_mul, OrthDec.resS_apply]
      rw [hxi']
    rw [hs, show B.o.jB = (rat B.o.iB : Mx D B.V₀.rank B.L.rank) from rfl]
    have hc := trace_half (half_mul_right hmh (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank)))
    have hsec : p.sec (p.pr (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝
        (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank))).trace) =
        (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝
          (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank))).trace := by
      rw [p.sec_pr]; exact hc
    show psiE ψ _ = _
    rw [← hsec, ← hχ, pr_trace p l.τ ζ' B.ζ l.map β t x B.o.iB]
    have hb : ∀ r, α₀.b r (Sum.inr 0) = (B.o.iB.map (iota p) *ᵥ fun i => iota p (B.ζ i)) r := by
      intro r
      rw [hsum]
      simp only [fromCols_apply_inr, replicateCol_apply, ratV, vecB]
      exact RingHom.map_mulVec (iota p) B.o.iB B.ζ r
    have hcol : (fun i => rd α₀ β x i (Sum.inr 0)) =
        β.b' *ᵥ (x.map p.pr *ᵥ (B.o.iB.map (iota p) *ᵥ fun i => iota p (B.ζ i))) := by
      funext i
      rw [Matrix.mulVec_mulVec]
      simp only [rd, Matrix.mul_apply, hb]
      rfl
    rw [hcol]

end GlobalTheory.KappaRowChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaSplitHalfPointMultipliesByCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_splitHalfPoint_multiplies_by_character : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf (cA D p.e) ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) ∧ ∀ x : WO B.V₀ W₀, IsHalf p.e x → ψ (symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)))) = (χ (-(t ⬝ᵥ fun i => rd α₀ β x i (Sum.inr 0))) : ℂ) := by
  first | exact @GlobalTheory.KappaRowChar.kappa_wRow_char | exact GlobalTheory.KappaRowChar.kappa_wRow_char | (intros; apply GlobalTheory.KappaRowChar.kappa_wRow_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHalfPointTranslatesLastFrameRow
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHalfPointTranslatesLastFrameRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

theorem neg_wRow_half_rd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf p.e ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) ∧ ∀ i j, rd β γ₀ ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) i j = Sum.elim (fun _ => 0) (fun _ => -t j) i := by
  intro D k _ _ _ _ p n n'' _ _ _ _ S₀ A L W₀ o ζ β γ γ₀ hsum t
  have hes : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.neg_apply, wRow, Matrix.of_apply, mul_left_comm, mul_neg, hes, mul_neg]
  · set c : Fin S₀.rank → k := fun i => p.pr (ratV (vecB o ζ) i) with hc
    have hmap : Matrix.map (o.jB * -wRow p ζ β t : Mx D S₀.rank W₀.rank) p.pr = -vecMulVec c (t ᵥ* β.b') := by
      refine Matrix.ext fun a b => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.map_apply, Matrix.mul_apply, map_sum, Matrix.neg_apply, vecMulVec_apply, hc]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ratV, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.neg_apply, wRow, Matrix.of_apply, map_neg, p.pr_sec, mul_neg, mul_assoc]
      rfl
    have hcol : (γ₀.b' *ᵥ c) i = Sum.elim (fun _ => 0) (fun _ => 1) i := by
      have h := congrFun (congrFun γ₀.b'b i) (Sum.inr 0)
      rw [hsum, Matrix.mul_apply] at h
      simp only [fromCols_apply_inr, replicateCol_apply] at h
      refine h.trans ?_
      rcases i with i | i
      · simp
      · obtain rfl := Subsingleton.elim i 0
        simp
    rw [rd, hmap, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, β.b'b,
      Matrix.vecMul_one, Matrix.neg_apply, vecMulVec_apply, hcol]
    rcases i with i | i <;> simp

end GlobalTheory.FinPl.LineAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHalfPointTranslatesLastFrameRowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_halfPoint_translates_lastFrameRow : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf p.e ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) ∧ ∀ i j, rd β γ₀ ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) i j = Sum.elim (fun _ => 0) (fun _ => -t j) i := by
  exact GlobalTheory.FinPl.LineAct.neg_wRow_half_rd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaConjugateHalfPointTranslatesLastColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaConjugateHalfPointTranslatesLastColumn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct.ColTrans

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adelicConj_adelicConj_eq_self (x : AE D) : cA D (cA D x) = x := by
  have := congrFun (congrFun (adj_adj (D := D) (m := 1) (n := 1) (Matrix.of fun _ _ => x)) 0) 0
  simpa [adj] using this

theorem e_mul_sec (p : SplitPt D k) (x : k) : p.e * p.sec x = p.sec x := by
  rw [← p.sec_pr, p.pr_sec]

theorem map_pr_rat (p : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat M : Mx D m n).map p.pr = M.map (iota p) := by
  ext i j; rfl

theorem matrix_mul_replicateCol_eq_replicateCol_mulVec {R : Type} [CommRing R] {m l : Type} [Fintype l] (A : Matrix m l R) (x : l → R) :
    A * replicateCol (Fin 1) x = replicateCol (Fin 1) (A *ᵥ x) := by
  ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem adj_wCol (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) :
    adj (wCol p ζ' β t) = Matrix.of fun i j => p.sec (dualPick ((L'.gram.map (iota p)) *ᵥ fun i => iota p (ζ' i)) j *
      ((iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) i)) := by
  ext i j
  simp only [adj, wCol, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, adelicConj_adelicConj_eq_self]

end GlobalTheory.FinPl.LineAct.ColTrans

namespace GlobalTheory.FinPl.LineAct
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)
open GlobalTheory.FinPl.LineAct.ColTrans


set_option maxHeartbeats 2000000 in
theorem kappa_wCol_translate : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ'), IsLineVec L' ζ' → ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf p.e ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) ∧ ∀ i j, rd α₀ β ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) i j = Sum.elim (fun _ => 0) (fun _ => -t i) j := by
  intro D k _ _ _ _ p n n' _ _ _ _ ρ B L' W₀ ζ' l hL α α₀ β hsum t
  set ι := iota p with hι
  set g' : Fin L'.rank → k := (L'.gram.map ι) *ᵥ fun i => ι (ζ' i) with hg'
  set v : Fin W₀.rank → k := fun j => (ι D.host.xi0)⁻¹ * ((W₀.gram.map ι) *ᵥ (β.b *ᵥ t)) j with hv
  have hadj : adj (wCol p ζ' β t) = Matrix.of fun i j => p.sec (dualPick g' j * v i) := adj_wCol p ζ' β t
  have hu : (B.o.resS W₀).symm (0, l.κ W₀ (wCol p ζ' β t)) =
      (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Link.κ, ofAdj, adj_mul]
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  rw [hu]
  constructor
  · have hA : p.e • adj (wCol p ζ' β t) = adj (wCol p ζ' β t) := by
      rw [hadj]; ext i j; simp [e_mul_sec]
    intro i j
    have : p.e • ((incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB)) =
        (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) := by
      conv_rhs => rw [← hA]
      rw [Matrix.mul_smul (incA D (-D.host.xi0⁻¹) • giA W₀) p.e (adj (wCol p ζ' β t)),
        Matrix.smul_mul p.e ((incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t))]
    exact congrFun (congrFun this i) j
  · generalize hUdef : (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝
        (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) = U
    replace hUdef := hUdef.symm
    have hR : adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB = rat (l.τᴴ * B.L.gram * B.o.qB) := by
      rw [← rat_conjTranspose, gA, OrthDec.pB, ← rat_mul, ← rat_mul]
    have hX : (incA D (-D.host.xi0⁻¹) • giA W₀ : Mx D W₀.rank W₀.rank).map p.pr =
        ι (-D.host.xi0⁻¹) • (W₀.gram⁻¹).map ι := by
      ext i j; simp [giA, rat, hι, iota]
    have hW : (adj (wCol p ζ' β t)).map p.pr = vecMulVec v (dualPick g') := by
      rw [hadj]; ext i j; simp [vecMulVec, p.pr_sec, mul_comm]
    have hUm : U.map p.pr = (ι (-D.host.xi0⁻¹) • (W₀.gram⁻¹).map ι) * vecMulVec v (dualPick g') *
        (l.τᴴ * B.L.gram * B.o.qB).map ι := by
      rw [hUdef, hR, Matrix.map_mul, Matrix.map_mul, hX, hW, map_pr_rat]
    have hUA : U ⬝ B.o.jA = 0 := by
      simp only [hUdef, Matrix.mul_assoc, OrthDec.pB_jA, Matrix.mul_zero]

    have hrat : (l.τᴴ * B.L.gram * B.o.qB) *ᵥ vecB B.o B.ζ =
        -((D.host.xi0 * star D.host.xi0) • (L'.gram *ᵥ ζ')) := by
      have hz : B.ζ = -(l.τ *ᵥ ζ') := by rw [l.map, neg_neg]
      rw [vecB, Matrix.mulVec_mulVec, Matrix.mul_assoc, B.o.qB_iB, Matrix.mul_one, hz, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, GlobalTheory.Unf.Model.tau_gram l hL, Matrix.smul_mulVec]
    have hgi : ∀ i, g' i = ι ((L'.gram *ᵥ ζ') i) := fun i => (RingHom.map_mulVec ι _ _ i).symm
    have hg0 : g' ≠ 0 := by
      intro h0
      apply hL.2
      have h1 : L'.gram *ᵥ ζ' = 0 := by
        funext i
        apply ι.injective
        rw [← hgi, h0, Pi.zero_apply, Pi.zero_apply, map_zero]
      rw [h1, dotProduct_zero]
    have hxi : ι D.host.xi0 ≠ 0 := fun h => GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D ((iota p).injective (h.trans (map_zero _).symm))
    have hGG : (W₀.gram⁻¹).map ι * W₀.gram.map ι = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (gram_isUnit_det W₀), Matrix.map_one _ (map_zero _) (map_one _)]
    have hcol : U.map p.pr *ᵥ (fun i => p.pr (ratV (vecB B.o B.ζ) i)) = -(β.b *ᵥ t) := by
      have h1 : (fun i => p.pr (ratV (vecB B.o B.ζ) i)) = ι ∘ vecB B.o B.ζ := rfl
      have h2 : (l.τᴴ * B.L.gram * B.o.qB).map ι *ᵥ (ι ∘ vecB B.o B.ζ) =
          (-(ι (D.host.xi0 * star D.host.xi0))) • g' := by
        funext i
        rw [← RingHom.map_mulVec, hrat, Pi.smul_apply, hgi]
        simp [map_neg, map_mul]
      have h3 : vecMulVec v (dualPick g') *ᵥ g' = v := by
        rw [Matrix.vecMulVec_mulVec, dualPick_dot g' hg0, MulOpposite.op_one, one_smul]
      have h4 : v = (ι D.host.xi0)⁻¹ • ((W₀.gram.map ι) *ᵥ (β.b *ᵥ t)) := rfl
      rw [h1, hUm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h3, h4,
        Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec,
        smul_smul, smul_smul, ← neg_one_smul k (β.b *ᵥ t)]
      congr 1
      have hs : ι (star D.host.xi0) = -ι D.host.xi0 := by rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]
      rw [map_mul, hs, map_neg, map_inv₀]
      field_simp
    have hrd : rd α₀ β U = fromCols 0 (replicateCol (Fin 1) (-t)) := by
      have hb : α₀.b = _ := hsum
      rw [rd, hb, Matrix.mul_assoc, Matrix.mul_fromCols, Matrix.mul_fromCols, ← Matrix.mul_assoc (U.map p.pr),
        ← Matrix.map_mul, hUA, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, matrix_mul_replicateCol_eq_replicateCol_mulVec,
        matrix_mul_replicateCol_eq_replicateCol_mulVec, hcol, Matrix.mulVec_neg, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]
    intro i j
    rw [hrd]
    cases j with
    | inl j => simp
    | inr j => simp

end GlobalTheory.FinPl.LineAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaConjugateHalfPointTranslatesLastColumnStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_conjugateHalfPoint_translates_lastColumn : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ'), IsLineVec L' ζ' → ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf p.e ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) ∧ ∀ i j, rd α₀ β ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) i j = Sum.elim (fun _ => 0) (fun _ => -t i) j := by
  exact @GlobalTheory.FinPl.LineAct.kappa_wCol_translate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHeisenbergActionLineModulationTranslat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Generic

variable {p : SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] {α : Frame p S n'} {β : Frame p T n} {LS : Lat S} {LT : Lat T} {f₀ f : WO S T → ℂ}
  {Ψ Ψ' : Matrix n n' k → ℂ}

theorem over_trans (h : Over ψ α β LS LT f₀ Ψ f) {x : WO S T} (hx : IsHalf p.e x) (hΨ' : Ψ' ∈ SB (Matrix n n' k))
    (he : ∀ t, IsHalf p.e t → Ψ' (rd α β t) = Ψ (rd α β (t + x))) : Over ψ α β LS LT f₀ Ψ' (heisO ψ S T x f) := by
  obtain ⟨hS, hT, hV, hΨ, hex, hall⟩ := h
  have hsb := GlobalTheory.FinPl.OverProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have hfun : extFun α β Ψ' = fun t => extFun α β Ψ (t + x) := by
    funext t
    have hc : IsHalf p.e (t + x) ↔ IsHalf p.e t := forall_congr' fun i => forall_congr' fun j => by
      rw [Matrix.add_apply, mul_add, hx i j, add_left_inj]
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht, if_pos (hc.2 ht), he t ht]
    · rw [if_neg ht, if_neg (fun h' => ht (hc.1 h'))]
  refine ⟨hS, hT, hV, hΨ', hex, fun Tm hTm => ?_⟩
  show heisO ψ S T x f = Tm (extFun α β Ψ')
  rw [hall Tm hTm, hfun, hTm.trans _ hsb x hx]

theorem over_modul (h : Over ψ α β LS LT f₀ Ψ f) {y : WO S T} (hy : IsHalf (cA D p.e) y)
    (hΨ' : Ψ' ∈ SB (Matrix n n' k))
    (he : ∀ t, IsHalf p.e t → Ψ' (rd α β t) = ψ (symplO S T t y) * Ψ (rd α β t)) :
    Over ψ α β LS LT f₀ Ψ' (heisO ψ S T y f) := by
  obtain ⟨hS, hT, hV, hΨ, hex, hall⟩ := h
  have hsb := GlobalTheory.FinPl.OverProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have hfun : extFun α β Ψ' = fun t => ψ (symplO S T t y) * extFun α β Ψ t := by
    funext t
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht, if_pos ht, he t ht]
    · rw [if_neg ht, if_neg ht, mul_zero]
  refine ⟨hS, hT, hV, hΨ', hex, fun Tm hTm => ?_⟩
  show heisO ψ S T y f = Tm (extFun α β Ψ')
  rw [hall Tm hTm, hfun, hTm.modul _ hsb y hy]

end Generic

section SBLemmas

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_mul_mem {Ψ : Matrix n n' k → ℂ} {a g : (n → k) → ℂ} (hg : IsLocallyConstant g)
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) :
    tensCol Ψ (fun y => g y * a y) ∈ SB (Matrix n (n' ⊕ Fin 1) k) := by
  have e : tensCol Ψ (fun y => g y * a y) =
      (fun x : Matrix n (n' ⊕ Fin 1) k => g fun i => x i (Sum.inr 0)) * tensCol Ψ a := by
    funext x; simp only [tensCol, Pi.mul_apply]; ring
  rw [e]
  exact ⟨(hg.comp_continuous (by fun_prop)).mul h.1, h.2.mul_left⟩

theorem tensRow_mul_mem {Ψ : Matrix n' n k → ℂ} {b g : (n → k) → ℂ} (hg : IsLocallyConstant g)
    (h : tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) :
    tensRow Ψ (fun y => g y * b y) ∈ SB (Matrix (n' ⊕ Fin 1) n k) := by
  have e : tensRow Ψ (fun y => g y * b y) =
      (fun x : Matrix (n' ⊕ Fin 1) n k => g (x (Sum.inr 0))) * tensRow Ψ b := by
    funext x; simp only [tensRow, Pi.mul_apply]; ring
  rw [e]
  exact ⟨(hg.comp_continuous (by fun_prop)).mul h.1, h.2.mul_left⟩

theorem tensCol_sub_mem {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ} (t : n → k)
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) :
    tensCol Ψ (fun y => a (y - t)) ∈ SB (Matrix n (n' ⊕ Fin 1) k) := by
  let M : Matrix n (n' ⊕ Fin 1) k := Matrix.of fun i j => Sum.elim (fun _ => 0) (fun _ => t i) j
  have e : tensCol Ψ (fun y => a (y - t)) = tensCol Ψ a ∘ Homeomorph.subRight M := by
    funext x
    simp only [tensCol, Function.comp_apply, Homeomorph.subRight_apply]
    congr 2
    all_goals first | (ext i j; simp [M]) | (funext i; simp [M])
  rw [e]
  exact ⟨h.1.comp_continuous (Homeomorph.subRight M).continuous, h.2.comp_homeomorph _⟩

theorem tensRow_sub_mem {Ψ : Matrix n' n k → ℂ} {b : (n → k) → ℂ} (t : n → k)
    (h : tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) :
    tensRow Ψ (fun y => b (y - t)) ∈ SB (Matrix (n' ⊕ Fin 1) n k) := by
  let M : Matrix (n' ⊕ Fin 1) n k := Matrix.of fun i j => Sum.elim (fun _ => 0) (fun _ => t j) i
  have e : tensRow Ψ (fun y => b (y - t)) = tensRow Ψ b ∘ Homeomorph.subRight M := by
    funext x
    simp only [tensRow, Function.comp_apply, Homeomorph.subRight_apply]
    congr 2
    all_goals first | (ext i j; simp [M]) | (funext i; simp [M])
  rw [e]
  exact ⟨h.1.comp_continuous (Homeomorph.subRight M).continuous, h.2.comp_homeomorph _⟩

end SBLemmas

end GlobalTheory.FinPl.LineAct

end

noncomputable section
namespace GlobalTheory.FinPl.LineAct

theorem line_act : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧ ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (σ : ℕ) (B : BesLev D (σ + 1)) (B' : BesLev D σ) (W₀ : HSp D) (l : Link B B'.L B'.ζ) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ → IsStdChar D ψ (-1) → ∀ t : n → k,
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a y) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => b (η - t)) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) ∧
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => a (y - t)) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b η) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) := by
  intro D k _ _ _ _ p ψ χ hχ
  refine ⟨-1, Or.inr rfl, ?_⟩
  intro n n' n'' _ _ _ _ _ _ σ B B' W₀ l α α₀ β γ γ₀ hα hγ hstd t
  have hχc := (GlobalTheory.T.splitPlace_stdChar_continuous_nontrivial D k p ψ χ hχ hstd).1
  have hχl := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar χ hχc
  have hlc : IsLocallyConstant fun y : n → k => (χ (-1 * (t ⬝ᵥ y)) : ℂ) :=
    hχl.comp_continuous (continuous_const.mul (continuous_const.dotProduct continuous_id))
  have hlc' : IsLocallyConstant fun η : n → k => (χ (-1 * (η ⬝ᵥ t)) : ℂ) :=
    hχl.comp_continuous (continuous_const.mul (continuous_id.dotProduct continuous_const))
  constructor
  · obtain ⟨h1h, h1m⟩ := GlobalTheory.T.kappa_splitHalfPoint_multiplies_by_character D k p ψ χ hχ n n' (σ + 1) B B'.L W₀ B'.ζ l α α₀ β hα t
    obtain ⟨h1ah, h1ar⟩ := GlobalTheory.T.neg_halfPoint_translates_lastFrameRow D k p n n'' B'.V₀ B'.A B'.L W₀ B'.o B'.ζ β γ γ₀ hγ t
    refine ⟨wRow p B'.ζ β t, fun L₁ L₂ f₁ Ψ₁ a Ξ h => ?_, fun L₂' L₃ f₂ Ψ₂ b Ξ h => ?_⟩
    · refine over_modul h h1h (tensCol_mul_mem hlc h.2.2.2.1) fun x hx => ?_
      rw [h1m x hx]
      simp only [tensCol, neg_one_mul]
      ring
    · refine over_trans h h1ah (tensRow_sub_mem t h.2.2.2.1) fun x hx => ?_
      simp only [tensRow, GlobalTheory.FinPl.OverProof.rd_add]
      congr 1
      · congr 1; ext i j; simp [Matrix.add_apply, h1ar]
      · congr 1; funext j; simp [Matrix.add_apply, h1ar, sub_eq_add_neg]
  · obtain ⟨h2h, h2r⟩ := GlobalTheory.T.kappa_conjugateHalfPoint_translates_lastColumn D k p n n' (σ + 1) B B'.L W₀ B'.ζ l B'.line α α₀ β hα t
    obtain ⟨h2bh, h2bm⟩ := GlobalTheory.T.conjugateHalfPoint_neg_multiplies_by_character D k p ψ χ hχ n n'' B'.V₀ B'.A B'.L W₀ B'.o B'.ζ B'.line β γ γ₀ hγ t
    refine ⟨wCol p B'.ζ β t, fun L₁ L₂ f₁ Ψ₁ a Ξ h => ?_, fun L₂' L₃ f₂ Ψ₂ b Ξ h => ?_⟩
    · refine over_trans h h2h (tensCol_sub_mem t h.2.2.2.1) fun x hx => ?_
      simp only [tensCol, GlobalTheory.FinPl.OverProof.rd_add]
      congr 1
      · congr 1; ext i j; simp [Matrix.add_apply, h2r]
      · congr 1; funext i; simp [Matrix.add_apply, h2r, sub_eq_add_neg]
    · refine over_modul h h2bh (tensRow_mul_mem hlc' h.2.2.2.1) fun x hx => ?_
      rw [h2bm x hx]
      simp only [tensRow, neg_one_mul]
      ring
end GlobalTheory.FinPl.LineAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHeisenbergActionLineModulationTranslatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_heisenbergAction_line_modulation_translation : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧ ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (σ : ℕ) (B : BesLev D (σ + 1)) (B' : BesLev D σ) (W₀ : HSp D) (l : Link B B'.L B'.ζ) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ → IsStdChar D ψ (-1) → ∀ t : n → k,
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a y) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => b (η - t)) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) ∧
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => a (y - t)) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b η) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) := by
  first | exact @GlobalTheory.FinPl.LineAct.line_act | exact GlobalTheory.FinPl.LineAct.line_act | (intros; apply GlobalTheory.FinPl.LineAct.line_act <;> assumption)
end
