module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
public import Formalism.RealPlaceAnalysis.FinalF

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HJMulVecGen
noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

variable (I : Formalism.MainNotions.S.AutInst)

theorem phi_star (v : NumberField.InfinitePlace I.F) (a : I.E) : I.φ v (star a) = star (I.φ v a) :=
  I.cm.cmUnram.2.1 (I.φ v) a

theorem gram_real (v : NumberField.InfinitePlace I.F) :
    ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = I.J.map (I.φ v) := by
  have h : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have e : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h, Matrix.conjTranspose_one]
  rw [← I.P_spec v]
  calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹
      = (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = I.J.map (I.φ v) := by rw [e, h, Matrix.one_mul, Matrix.mul_one]

theorem hJ_mulVec_gen {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℂ) :
    hJ ε (A *ᵥ u) (A *ᵥ w) = star u ⬝ᵥ ((Aᴴ * Formalism.REAL.Jm ε * A) *ᵥ w) := by
  simp only [hJ, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem rv_hJ (v : NumberField.InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  simp only [rv]
  rw [hJ_mulVec_gen, gram_real I v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Pi.star_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, phi_star I v]
  ring

variable {I}

theorem rv_frame {r : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E} (hF : IsFrame I e f z)
    (v : NumberField.InfinitePlace I.F) :
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (e b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (f a)) (rv I v (f b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (f b)) = if a = b then 1 else 0) ∧
    (∀ a, hJ (I.ε v) (rv I v (e a)) (rv I v z) = 0 ∧ hJ (I.ε v) (rv I v (f a)) (rv I v z) = 0) ∧
    hJ (I.ε v) (rv I v z) (rv I v z) ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, ?_⟩
  · rw [rv_hJ, h1, map_zero]
  · rw [rv_hJ, h2, map_zero]
  · rw [rv_hJ, h3]
    split_ifs <;> simp
  · rw [rv_hJ, rv_hJ, (h4 a).1, (h4 a).2, map_zero]
    exact ⟨rfl, rfl⟩
  · rw [rv_hJ]
    exact (map_ne_zero _).mpr h5

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousUMatApply
noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Lin

variable {n r : ℕ}

theorem spanLt_mono (e : Fin r → Fin n → ℂ) {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b := by
  unfold spanLt
  exact Submodule.span_mono (Set.image_mono fun b (hb : b.1 < a) => lt_of_lt_of_le hb h)

theorem mulVec_eq_sub_add (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    g *ᵥ x = (g - 1) *ᵥ x + x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]

theorem sub_mem_spanLt {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) : (g - 1) *ᵥ x ∈ spanLt e a := by
  have key : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin (g - 1)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact spanLt_mono e (le_of_lt hb) (hg.1 b)
  exact key hx

theorem mem_spanLt_of_inS {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) : g *ᵥ x ∈ spanLt e a := by
  rw [mulVec_eq_sub_add g x]
  exact Submodule.add_mem _ (sub_mem_spanLt hg a hx) hx

theorem inv_preserves {W : Submodule ℂ (Fin n → ℂ)} {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1)
    (hW : ∀ x ∈ W, g *ᵥ x ∈ W) : ∀ x ∈ W, g' *ᵥ x ∈ W := by
  let f : W →ₗ[ℂ] W := (Matrix.mulVecLin g).restrict (fun x hx => hW x hx)
  have hf : Function.Injective f := by
    intro a b hab
    have h2 : g *ᵥ (a : Fin n → ℂ) = g *ᵥ (b : Fin n → ℂ) := congrArg Subtype.val hab
    have h3 := congrArg (fun y => g' *ᵥ y) h2
    simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h3
    exact Subtype.ext h3
  have hs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf
  intro x hx
  obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
  have hy' : g *ᵥ (y : Fin n → ℂ) = x := congrArg Subtype.val hy
  rw [← hy', Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact y.2

theorem mul_sub_one_mulVec (g g' : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (g * g' - 1) *ᵥ x = g *ᵥ ((g' - 1) *ᵥ x) + (g - 1) *ᵥ x := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, mul_sub, mul_one,
    Matrix.one_mulVec] <;> abel

theorem inv_sub_one_mulVec {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1) (x : Fin n → ℂ) :
    (g' - 1) *ᵥ x = -(g' *ᵥ ((g - 1) *ᵥ x)) := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
    neg_sub]

theorem inS_one (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InS e z 1 := by
  unfold InS
  refine ⟨fun a => ?_, ?_⟩ <;> simp

theorem inS_mul {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (hg' : InS e z g') : InS e z (g * g') := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [mul_sub_one_mulVec]
    exact Submodule.add_mem _ (mem_spanLt_of_inS hg _ (hg'.1 a)) (hg.1 a)
  · rw [mul_sub_one_mulVec]
    exact Submodule.add_mem _ (mem_spanLt_of_inS hg _ hg'.2) hg.2

theorem inS_inv {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (h1 : g' * g = 1) : InS e z g' := by
  have hp : ∀ (a : ℕ), ∀ x ∈ spanLt e a, g' *ᵥ x ∈ spanLt e a := fun a =>
    inv_preserves h1 (fun x hx => mem_spanLt_of_inS hg a hx)
  refine ⟨fun a => ?_, ?_⟩
  · rw [inv_sub_one_mulVec h1]
    exact Submodule.neg_mem _ (hp _ _ (hg.1 a))
  · rw [inv_sub_one_mulVec h1]
    exact Submodule.neg_mem _ (hp _ _ hg.2)

theorem inN_one (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InN ε e z 1 := by
  unfold InN
  exact ⟨inS_one e z, fun y _ => by simp⟩

theorem inN_mul {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InN ε e z g) (hg' : InN ε e z g') : InN ε e z (g * g') := by
  refine ⟨inS_mul hg.1 hg'.1, fun y hy => ?_⟩
  rw [mul_sub_one_mulVec]
  exact Submodule.add_mem _ (mem_spanLt_of_inS hg.1 _ (hg'.2 y hy)) (hg.2 y hy)

theorem inN_inv {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InN ε e z g) (h1 : g' * g = 1) : InN ε e z g' := by
  refine ⟨inS_inv hg.1 h1, fun y hy => ?_⟩
  rw [inv_sub_one_mulVec h1]
  exact Submodule.neg_mem _
    (inv_preserves h1 (fun x hx => mem_spanLt_of_inS hg.1 r hx) _ (hg.2 y hy))

theorem isClosed_sub_mem (x : Fin n → ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ x ∈ W} := by
  have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (g - 1) *ᵥ x :=
    (continuous_id.sub continuous_const).matrix_mulVec continuous_const
  exact W.closed_of_finiteDimensional.preimage hc

theorem isClosed_inN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  have h1 : {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} =
      ((⋂ a : Fin r, {g | (g - 1) *ᵥ e a ∈ spanLt e a.1}) ∩ {g | (g - 1) *ᵥ z ∈ spanLt e r}) ∩
        ⋂ y ∈ {y : Fin n → ℂ | ∀ a, hJ ε (e a) y = 0}, {g | (g - 1) *ᵥ y ∈ spanLt e r} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, InN, InS]
  rw [h1]
  exact ((isClosed_iInter fun a => isClosed_sub_mem _ _).inter (isClosed_sub_mem _ _)).inter
    (isClosed_biInter fun y _ => isClosed_sub_mem _ _)

theorem hJ_mulVec {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (x y : Fin n → ℂ) : hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  unfold hJ
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg']

theorem fix_span {W : Set (Fin n → ℂ)} {g : Matrix (Fin n) (Fin n) ℂ} (hW : ∀ x ∈ W, g *ᵥ x = x) :
    ∀ x ∈ Submodule.span ℂ W, g *ᵥ x = x := by
  intro x hx
  have hle : Submodule.span ℂ W ≤ LinearMap.ker (Matrix.mulVecLin g - LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    simp [hW y hy]
  have hx' := hle hx
  simpa [sub_eq_zero] using hx'

theorem conj_sub_one {h x h' : Matrix (Fin n) (Fin n) ℂ} (hh : h * h' = 1) :
    h * x * h' - 1 = h * (x - 1) * h' := by
  rw [mul_sub, sub_mul, mul_one, hh]

theorem inN_conj {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
    {h h' x : Matrix (Fin n) (Fin n) ℂ} (hU : Formalism.REAL.inUJ ε h) (hh : h * h' = 1) (hh' : h' * h = 1)
    (he : ∀ a, h *ᵥ e a = e a) (hz : h *ᵥ z = z) (hx : InN ε e z x) : InN ε e z (h * x * h') := by
  have hfix : ∀ (a : ℕ), ∀ v ∈ spanLt e a, h *ᵥ v = v := fun a =>
    fix_span (fun v hv => by obtain ⟨b, _, rfl⟩ := hv; exact he b)
  have h'e : ∀ v, h *ᵥ v = v → h' *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, hh', Matrix.one_mulVec]
  have key : ∀ v, (h * x * h' - 1) *ᵥ v = h *ᵥ ((x - 1) *ᵥ (h' *ᵥ v)) := fun v => by
    rw [conj_sub_one hh]
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, h'e _ (he a), hfix a.1 _ (hx.1.1 a)]
    exact hx.1.1 a
  · rw [key, h'e _ hz, hfix r _ hx.1.2]
    exact hx.1.2
  · have hy' : ∀ a, hJ ε (e a) (h' *ᵥ y) = 0 := fun a => by
      rw [← hJ_mulVec hU, he a, Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]
      exact hy a
    rw [key, hfix r _ (hx.2 _ hy')]
    exact hx.2 _ hy'

end Lin

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

theorem uMat_mul {n : ℕ} {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat (g * h) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat h := rfl

theorem uMat_one {n : ℕ} {ε : Fin n → Bool} : Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inUJ {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε (Formalism.MainNotions.S.uMat g) := g.2

theorem continuous_uMat_apply (v : NumberField.InfinitePlace I.F) :
    Continuous fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v) := (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)

variable {r : ℕ}

def NSub (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Subgroup I.Ginf where
  carrier := Ninf I e z
  one_mem' := fun v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ (I.ε v)))
    rw [uMat_one]; exact inN_one _ _ _
  mul_mem' := fun {a b} ha hb v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat (a v * b v))
    rw [uMat_mul]; exact inN_mul (ha v) (hb v)
  inv_mem' := fun {a} ha v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat ((a v)⁻¹))
    exact inN_inv (ha v) (uMat_inv_mul (a v))

def HSub (S : Set (Fin I.n → I.E)) : Subgroup I.Ginf where
  carrier := Hset I S
  one_mem' := fun v x _ => by
    show Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ (I.ε v)) *ᵥ _ = _
    rw [uMat_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb v x hx => by
    show Formalism.MainNotions.S.uMat (a v * b v) *ᵥ _ = _
    rw [uMat_mul, ← Matrix.mulVec_mulVec, hb v x hx, ha v x hx]
  inv_mem' := fun {a} ha v x hx => by
    show Formalism.MainNotions.S.uMat ((a v)⁻¹) *ᵥ _ = _
    conv_lhs => rw [← ha v x hx]
    rw [Matrix.mulVec_mulVec, uMat_inv_mul, Matrix.one_mulVec]

theorem isClosed_Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : IsClosed (Ninf I e z) := by
  have h1 : Ninf I e z = ⋂ v, (fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v)) ⁻¹'
      {g | InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) g} := by
    ext s
    simp only [Ninf, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h1]
  exact isClosed_iInter fun v => (isClosed_inN _ _ _).preimage (continuous_uMat_apply I v)

theorem isClosed_Hset (S : Set (Fin I.n → I.E)) : IsClosed (Hset I S) := by
  have h1 : Hset I S = ⋂ v, ⋂ x ∈ S, {s : I.Ginf | Formalism.MainNotions.S.uMat (s v) *ᵥ rv I v x = rv I v x} := by
    ext s
    simp only [Hset, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h1]
  refine isClosed_iInter fun v => isClosed_biInter fun x _ => ?_
  exact isClosed_eq ((continuous_uMat_apply I v).matrix_mulVec continuous_const) continuous_const

theorem measure_subFacts : SubFacts := by
  intro I r e f z
  refine ⟨NSub I e z, HSub I (frameSet I e f z), rfl, rfl, isClosed_Ninf I e z, isClosed_Hset I _, ?_⟩
  intro h hh x hx
  have hh' : h ∈ Hset I (frameSet I e f z) := hh
  have hx' : x ∈ Ninf I e z := hx
  show ∀ v, InN _ _ _ (Formalism.MainNotions.S.uMat ((h * x * h⁻¹) v))
  intro v
  show InN _ _ _ (Formalism.MainNotions.S.uMat (h v * x v * (h v)⁻¹))
  rw [uMat_mul, uMat_mul]
  exact inN_conj (uMat_inUJ _) (uMat_mul_inv _) (uMat_inv_mul _)
    (fun a => hh' v _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_range_self a))))
    (hh' v _ (Set.mem_union_right _ rfl)) (hx' v)

end Inst

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDefs
noncomputable section

open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

def instFvec {I : Formalism.MainNotions.S.AutInst} {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) :
    Fin r ⊕ Fin r ⊕ Unit → Fin I.n → I.E
  | Sum.inl a => e a
  | Sum.inr (Sum.inl a) => f a
  | Sum.inr (Sum.inr _) => z

def instBmat (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) : Matrix (Fin I.n) (Fin r ⊕ Fin r ⊕ Unit) ℂ :=
  Matrix.of fun i j => rv I v (instFvec e f z j) i

def InstExpFix : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ), X.IsHermitian → ∀ w : Fin n → ℂ,
    NormedSpace.exp X *ᵥ w = w ↔ X *ᵥ w = 0

def InstAdaptBasis : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) ι ℂ),
    IsUnit (Bᴴ * Formalism.REAL.Jm ε * B) →
    ∃ (A : Matrix (Fin n) (Fin n) ℂ) (ε' : Fin n → Bool) (T : Finset (Fin n)),
      Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε' ∧
      (∀ i ∈ T, ∃ c : ι → ℂ, A *ᵥ Pi.single i 1 = B *ᵥ c) ∧
      (∀ j : ι, ∃ c : Fin n → ℂ, (∀ i ∉ T, c i = 0) ∧ B *ᵥ Pi.single j 1 = A *ᵥ c)

def InstPlaceDecomp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) ι ℂ),
    IsUnit (Bᴴ * Formalism.REAL.Jm ε * B) →
    ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inUJ ε g → g * B = B →
    ∃ k p σ : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inUJ ε k ∧ Formalism.REAL.inUJ ε p ∧ Formalism.REAL.inUJ ε σ ∧
      k * B = B ∧ p * B = B ∧ σ * B = B ∧ g = k * p ∧ σ * σ = 1 ∧ σ * p * σ * p = 1 ∧
      ∃ C : Set (Formalism.REAL.UJ ε), IsCompact C ∧ (1 : Formalism.REAL.UJ ε) ∈ interior C ∧
        ∀ x y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.uMat y * k = k * Formalism.MainNotions.S.uMat x → (y ∈ C ↔ x ∈ C)

def InstFrameGram : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E), IsFrame I e f z →
    ∀ v, IsUnit ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z)

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HaarSub
open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem generic_haar_subgroup : GenHaarSub := by
  intro G _ _ _ _ _ _ _ _ K hK
  haveI : LocallyCompactSpace K := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hm : haarSub K hK = (Measure.haar : Measure K).map Subtype.val := rfl
  have hmeas : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hcpt : ∀ C : Set G, IsCompact C → haarSub K hK C < ⊤ := by
    intro C hC
    rw [hm, Measure.map_apply hmeas hC.isClosed.measurableSet]
    exact (hK.isClosedEmbedding_subtypeVal.isCompact_preimage hC).measure_lt_top
  haveI : IsFiniteMeasureOnCompacts (haarSub K hK) := ⟨hcpt⟩
  refine ⟨inferInstance, ?_, ?_, ?_, hcpt, ?_⟩
  · intro h0
    rw [hm, Measure.map_eq_zero_iff hmeas.aemeasurable] at h0
    exact isOpen_univ.measure_ne_zero (Measure.haar : Measure K) Set.univ_nonempty (by simp [h0])
  · rw [hm, Measure.map_apply hmeas hK.isOpen_compl.measurableSet]
    have hpre : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_not]
      exact x.2
    rw [hpre, measure_empty]
  · intro s hs
    rw [hm, Measure.map_map (measurable_const_mul s) hmeas]
    have hcomp : (fun x => s * x) ∘ (Subtype.val : K → G) =
        Subtype.val ∘ (fun y : K => (⟨s, hs⟩ : K) * y) := by
      funext y
      rfl
    rw [hcomp, ← Measure.map_map hmeas (measurable_const_mul _)]
    congr 1
    first
      | exact map_mul_left_eq_self (Measure.haar : Measure K) _
      | exact Measure.IsMulLeftInvariant.map_mul_left_eq_self _
  · intro U hU h1
    rw [hm, Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage continuous_subtype_val).measure_pos (Measure.haar : Measure K) ⟨1, by simpa using h1⟩

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstLeftInvMuInf
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

instance instSFiniteMuInf (I : Formalism.MainNotions.S.AutInst) : SFinite (muInf I) := by
  unfold muInf; infer_instance

instance instLeftInvMuInf (I : Formalism.MainNotions.S.AutInst) : (muInf I).IsMulLeftInvariant := by
  unfold muInf; infer_instance

theorem instConj_of (hm : GenModOne) (hd : InstDecomp) (h4 : SubFacts) : InstConj := by
  intro I r e f z hfr N H hN hNset hHset h hh
  obtain ⟨N', H', hN', hH', -, -, hnorm'⟩ := h4 I r e f z
  have hmemN : ∀ x, x ∈ N ↔ x ∈ N' := fun x => by
    rw [← SetLike.mem_coe, hNset, ← hN', SetLike.mem_coe]
  have hmemH : ∀ x, x ∈ H ↔ x ∈ Hset I (frameSet I e f z) := fun x => by
    rw [← SetLike.mem_coe, hHset]
  have hmemH' : ∀ x, x ∈ H ↔ x ∈ H' := fun x => by
    rw [hmemH, ← hH', SetLike.mem_coe]
  refine hm I.Ginf N H hN ?_ ?_ h hh
  · intro g hg x hx
    exact (hmemN _).mpr (hnorm' g ((hmemH' g).mp hg) x ((hmemN x).mp hx))
  · intro g hg
    obtain ⟨k, hk, p, hp, σ, hσ, hkp, hσp, C, hC⟩ := hd I r e f z hfr g ((hmemH g).mp hg)
    exact ⟨k, (hmemH k).mpr hk, p, (hmemH p).mpr hp, σ, (hmemH σ).mpr hσ, hkp, hσp, C, hC⟩

theorem target_of (h1 : GenHaarSub) (h2 : GenSemi) (h3 : GenWeil) (h4 : SubFacts) (h5 : InstConj)
    (h6 : InstProper) : PI.ScMuExists.Target := by
  intro I r e f z hee hff hef hz hzz
  have hfr : IsFrame I e f z := ⟨hee, hff, hef, hz, hzz⟩
  obtain ⟨N, H, hNset, hHset, hN, hH, hnorm⟩ := h4 I r e f z
  obtain ⟨hNσ, hN0, hNc, hNinv, -, -⟩ := h1 I.Ginf N hN
  obtain ⟨hHσ, hH0, hHc, hHinv, -, -⟩ := h1 I.Ginf H hH
  have hconj := h5 I r e f z hfr N H hN hNset hHset
  have hprop := h6 I r e f z hfr N H hNset hHset
  obtain ⟨hSf, hSmeas, hSc, hSinv, hSpos, hScpt⟩ := h2 I.Ginf N H hN hH hnorm hconj hprop
  have := hSf
  obtain ⟨ν, hν⟩ := h3 I.Ginf (muInf I) (mulMeas (haarSub N hN) (haarSub H hH))
    ((N : Set I.Ginf) * (H : Set I.Ginf)) hSmeas hSc hSinv hSpos hScpt
  refine ⟨haarSub N hN, haarSub H hH, ν, ?_, ?_, hν⟩
  · refine ⟨hNσ, hN0, ?_, ?_⟩
    · rw [← hNset]
      exact hNc
    · intro s hs
      rw [← hNset] at hs
      exact hNinv s hs
  · refine ⟨hHσ, hH0, ?_, ?_⟩
    · rw [show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset]
      exact hHc
    · intro s hs
      rw [show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset] at hs
      exact hHinv s hs

theorem target_of_steps (h1 : GenHaarSub) (h2 : GenSemi) (h3 : GenWeil) (h4 : SubFacts) (hm : GenModOne)
    (hd : InstDecomp) (h6 : InstProper) : PI.ScMuExists.Target := by
  have h5 : InstConj := instConj_of hm hd h4
  exact target_of h1 h2 h3 h4 h5 h6

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ModOne
open MeasureTheory
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Conj

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjSub (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N) (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) :
    N ≃* N where
  toFun x := ⟨g * x * g⁻¹, h1 x x.2⟩
  invFun x := ⟨g⁻¹ * x * g, h2 x x.2⟩
  left_inv x := Subtype.ext (show g⁻¹ * (g * (x : G) * g⁻¹) * g = x by group)
  right_inv x := Subtype.ext (show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x by group)
  map_mul' x y := Subtype.ext (show g * ((x : G) * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group)

theorem continuous_conjSub (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) : Continuous (conjSub N g h1 h2) := by
  show Continuous fun x : N => (⟨g * x * g⁻¹, h1 x x.2⟩ : N)
  exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

theorem continuous_conjSub_symm (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) : Continuous (conjSub N g h1 h2).symm := by
  show Continuous fun x : N => (⟨g⁻¹ * x * g, h2 x x.2⟩ : N)
  exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

variable [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem conj_eq_smul (N : Subgroup G) (hN : IsClosed (N : Set G)) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) :
    ∃ c : ℝ≥0, (haarSub N hN).map (fun x => g * x * g⁻¹) = c • haarSub N hN := by
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := by
    first
      | exact TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
      | exact Topology.IsInducing.subtypeVal.secondCountableTopology
      | exact inducing_subtype_val.secondCountableTopology
      | infer_instance
  have hφc := continuous_conjSub N g h1 h2
  have hφs := continuous_conjSub_symm N g h1 h2
  haveI := MulEquiv.isHaarMeasure_map (Measure.haar : Measure N) (conjSub N g h1 h2) hφc hφs
  refine ⟨Measure.haarScalarFactor ((Measure.haar : Measure N).map (conjSub N g h1 h2)) Measure.haar, ?_⟩
  have hc : Measurable (fun x : G => g * x * g⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hcomp : (fun x : G => g * x * g⁻¹) ∘ (Subtype.val : N → G) = Subtype.val ∘ (conjSub N g h1 h2) :=
    rfl
  unfold haarSub
  rw [Measure.map_map hc measurable_subtype_coe, hcomp,
    ← Measure.map_map measurable_subtype_coe hφc.measurable]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul ((Measure.haar : Measure N).map (conjSub N g h1 h2))
    Measure.haar]
  rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable]

end Conj

theorem genModOne_of (hHaar : GenHaarSub) : GenModOne := by
  intro G _ _ _ _ _ _ _ _ N H hN hnorm hdec h hh
  obtain ⟨_, _, _, _, hfin, hpos⟩ := hHaar G N hN
  have hm : ∀ a : G, Measurable (fun x : G => a * x * a⁻¹) := fun a =>
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hcomp : ∀ a b : G, (fun x : G => a * b * x * (a * b)⁻¹) =
      (fun x : G => a * x * a⁻¹) ∘ (fun x : G => b * x * b⁻¹) := fun a b => by
    funext x
    simp only [Function.comp, mul_inv_rev, mul_assoc]
  have hmap : ∀ a b : G, (haarSub N hN).map (fun x => a * b * x * (a * b)⁻¹) =
      ((haarSub N hN).map (fun x => b * x * b⁻¹)).map (fun x => a * x * a⁻¹) := fun a b => by
    rw [Measure.map_map (hm a) (hm b), hcomp]
  have hid : ∀ a : G, (haarSub N hN).map (fun x => a * a⁻¹ * x * (a * a⁻¹)⁻¹) = haarSub N hN :=
    fun a => by
      simp only [mul_inv_cancel, one_mul, inv_one, mul_one]
      exact Measure.map_id'
  have hsc : ∀ g ∈ H, ∃ c : ℝ≥0, (haarSub N hN).map (fun x => g * x * g⁻¹) = c • haarSub N hN :=
    fun g hg => conj_eq_smul N hN g (hnorm g hg) (fun x hx => by
      simpa using hnorm g⁻¹ (H.inv_mem hg) x hx)
  obtain ⟨k, hk, p, hp, σ, hσ, hkp, hσp, C, hC, hC1, hCk⟩ := hdec h hh
  have hCpos : 0 < haarSub N hN C :=
    lt_of_lt_of_le (hpos _ isOpen_interior hC1) (measure_mono interior_subset)
  have hCfin : haarSub N hN C < ⊤ := hfin C hC
  have key : ∀ a b : ℝ≥0∞, a * haarSub N hN C = b * haarSub N hN C → a = b := fun a b hab => by
    first
      | exact (ENNReal.mul_left_inj hCpos.ne' hCfin.ne).mp hab
      | exact (ENNReal.mul_eq_mul_right hCpos.ne' hCfin.ne).mp hab
      | (rw [mul_comm a, mul_comm b] at hab; exact (ENNReal.mul_right_inj hCpos.ne' hCfin.ne).mp hab)
      | (rw [mul_comm a, mul_comm b] at hab; exact (ENNReal.mul_eq_mul_left hCpos.ne' hCfin.ne).mp hab)
  have cancel : ∀ c d : ℝ≥0, c • haarSub N hN = d • haarSub N hN → c = d := fun c d hcd => by
    have e := congrArg (fun μ : Measure G => μ C) hcd
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    exact_mod_cast key _ _ e
  have hk1 : (haarSub N hN).map (fun x => k * x * k⁻¹) = haarSub N hN := by
    obtain ⟨ck, hck⟩ := hsc k hk
    have hpre : (fun x : G => k * x * k⁻¹) ⁻¹' C = C := Set.ext fun x => hCk x
    have e1 : (haarSub N hN).map (fun x => k * x * k⁻¹) C = haarSub N hN C := by
      rw [Measure.map_apply (hm k) hC.measurableSet, hpre]
    rw [hck] at e1
    have e3 : (ck : ℝ≥0∞) * haarSub N hN C = 1 * haarSub N hN C := by
      simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e1
      rw [one_mul]
      exact e1
    have hck1 : ck = 1 := by exact_mod_cast key _ _ e3
    rw [hck, hck1, one_smul]
  have hp1 : (haarSub N hN).map (fun x => p * x * p⁻¹) = haarSub N hN := by
    obtain ⟨cp, hcp⟩ := hsc p hp
    obtain ⟨cs, hcs⟩ := hsc σ hσ
    obtain ⟨cs', hcs'⟩ := hsc σ⁻¹ (H.inv_mem hσ)
    have e1 : (cs' * cs) • haarSub N hN = (1 : ℝ≥0) • haarSub N hN := by
      have e := hid σ
      rw [hmap, hcs', Measure.map_smul _ (hm σ).aemeasurable, hcs, smul_smul] at e
      rw [e, one_smul]
    have hss : cs' * cs = 1 := cancel _ _ e1
    have hpinv : (fun x : G => p⁻¹ * x * p⁻¹⁻¹) =
        (fun x : G => σ * p * σ⁻¹ * x * (σ * p * σ⁻¹)⁻¹) := by
      rw [hσp]
    have e2 : (haarSub N hN).map (fun x => p⁻¹ * x * p⁻¹⁻¹) = (cs' * cp * cs) • haarSub N hN := by
      rw [hpinv, hmap (σ * p) σ⁻¹, hcs', Measure.map_smul _ (hm (σ * p)).aemeasurable,
        hmap σ p, hcp, Measure.map_smul _ (hm σ).aemeasurable, hcs, smul_smul, smul_smul]
    have e3 : (cs' * cp * cs * cp) • haarSub N hN = (1 : ℝ≥0) • haarSub N hN := by
      have e := hid p
      rw [hmap p p⁻¹, e2, Measure.map_smul _ (hm p).aemeasurable, hcp, smul_smul] at e
      rw [e, one_smul]
    have hcp1 : cp = 1 := by
      have h4 := cancel _ _ e3
      have h5 : cp * cp = 1 := by
        calc cp * cp = (cs' * cs) * (cp * cp) := by rw [hss, one_mul]
          _ = cs' * cp * cs * cp := by ring
          _ = 1 := h4
      have h6 : (cp : ℝ) * cp = 1 := by exact_mod_cast h5
      have h7 : (cp : ℝ) = 1 := by nlinarith [cp.2]
      exact_mod_cast h7
    rw [hcp, hcp1, one_smul]
  rw [hkp, hmap, hp1, hk1]

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
