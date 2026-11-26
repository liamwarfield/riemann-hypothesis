module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
noncomputable section

open scoped MatrixGroups
open Matrix

namespace GlobalTheory.KZ.ES

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Lev (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f

def IntC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V

def SmallC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V.nonunits

def Prim (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop :=
  IntC X V f ∧ ∃ r : ℚ, V.valuation ((X.exp f).coeff r) = 1

def Dom (X : Tower Ω ε) (V : ValuationSubring Ω) (W : ValuationSubring X.K) : Prop :=
  (∀ f, IntC X V f → f ∈ W) ∧ (∀ f, SmallC X V f → W.valuation f < 1) ∧ ∀ f, Prim X V f → W.valuation f = 1

def Gauss {F L : Type} [Field F] [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (W : ValuationSubring L) : Prop :=
  (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ ∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) →
    (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1

def FrobV (V : ValuationSubring Ω) (q : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ((q : ℕ) : Ω) ∈ V.nonunits ∧ ∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1

def Nq (X : Tower Ω ε) (M q : ℕ) (f : X.K) : X.K :=
  ∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f

def DiagMod (M q : ℕ) (γ : SL(2, ℤ)) : Prop :=
  (en γ 0 1 : ZMod M) = 0 ∧ (en γ 1 0 : ZMod M) = 0 ∧ (en γ 1 1 : ZMod M) = q

def levF (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω (AlgebraicClosure X.K) :=
  IntermediateField.adjoin Ω (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f})

def rootF (X : Tower Ω ε) (M₀ M m : ℕ) (U : X.K) : IntermediateField (levF X M₀) (AlgebraicClosure X.K) :=
  IntermediateField.adjoin (levF X M₀) (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f} ∪
    {y | ∃ γ ∈ CongruenceSubgroup.Gamma M₀, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) U)})

theorem lev_jK (X : Tower Ω ε) (M : ℕ) : Lev X M X.jK := fun γ _ => X.j_inv γ

end GlobalTheory.KZ.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.ClsMod

variable {l : ℕ} [Fact l.Prime] {G : Type} [AddCommGroup G]

abbrev Q (l : ℕ) [Fact l.Prime] (n : ℕ) (G : Type) [AddCommGroup G] : Type :=
  (ℤ_[l] ⊗[ℤ] G) ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] G)))

theorem idl_pow_eq_ker (n : ℕ) : (idl l) ^ n = RingHom.ker (PadicInt.toZModPow (p := l) n) := by
  rw [PadicInt.ker_toZModPow, Ideal.span_singleton_pow]

theorem smul_mem_of_toZModPow {n : ℕ} {a : ℤ_[l]} (ha : PadicInt.toZModPow n a = 0) (m : ℤ_[l] ⊗[ℤ] G) :
    a • m ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] G)) :=
  Submodule.smul_mem_smul (by rw [idl_pow_eq_ker]; exact ha) trivial

instance neZero_pow (n : ℕ) : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem mk_tmul (n : ℕ) (c : ℤ_[l]) (g : G) :
    (Submodule.Quotient.mk (c ⊗ₜ[ℤ] g) : Q l n G) =
      Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] (((PadicInt.toZModPow n c).val : ℕ) • g)) := by
  rw [Submodule.Quotient.eq]
  have h : c ⊗ₜ[ℤ] g - (1 : ℤ_[l]) ⊗ₜ[ℤ] (((PadicInt.toZModPow n c).val : ℕ) • g)
      = (c - ((PadicInt.toZModPow n c).val : ℤ_[l])) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] g) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul,
      nsmul_eq_mul, mul_one]
  rw [h]
  apply smul_mem_of_toZModPow
  rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]

theorem exists_mk (n : ℕ) (y : Q l n G) : ∃ g : G, Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] g) = y := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c g => exact ⟨_, (mk_tmul n c g).symm⟩
  | add x y hx hy =>
    obtain ⟨gx, hx⟩ := hx
    obtain ⟨gy, hy⟩ := hy
    exact ⟨gx + gy, by rw [TensorProduct.tmul_add, Submodule.Quotient.mk_add, hx, hy, Submodule.Quotient.mk_add]⟩

abbrev H (l n : ℕ) (G : Type) [AddCommGroup G] : AddSubgroup G := (nsmulAddMonoidHom (α := G) (l ^ n)).range

def psi (n : ℕ) : ℤ_[l] →+ (G →+ G ⧸ H l n G) :=
  (ZMod.lift (l ^ n) ⟨zmultiplesHom (G →+ G ⧸ H l n G) (QuotientAddGroup.mk' (H l n G)), by
    ext g
    simp only [zmultiplesHom_apply, AddMonoidHom.zsmul_apply, QuotientAddGroup.mk'_apply, AddMonoidHom.zero_apply]
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨g, by rw [nsmulAddMonoidHom_apply, ← natCast_zsmul, Nat.cast_pow]⟩⟩).comp (PadicInt.toZModPow n).toAddMonoidHom

theorem psi_one (n : ℕ) (g : G) : psi (l := l) n 1 g = QuotientAddGroup.mk g := by
  have e : (1 : ZMod (l ^ n)) = ((1 : ℤ) : ZMod (l ^ n)) := by simp
  simp only [psi, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_one]
  rw [e, ZMod.lift_coe]
  simp

def phi (n : ℕ) : ℤ_[l] ⊗[ℤ] G →+ G ⧸ H l n G :=
  TensorProduct.liftAddHom (psi n) (fun r c g => by rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul])

theorem phi_tmul (n : ℕ) (c : ℤ_[l]) (g : G) : phi n (c ⊗ₜ[ℤ] g) = psi n c g :=
  TensorProduct.liftAddHom_tmul _ _ _ _

theorem phi_eq_zero (n : ℕ) (x : ℤ_[l] ⊗[ℤ] G) (hx : x ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] G))) :
    phi n x = 0 := by
  refine Submodule.smul_induction_on hx (fun a ha m hm => ?_) (fun x y hx hy => by rw [map_add (f := _), hx, hy, add_zero])
  clear hm
  rw [idl_pow_eq_ker, RingHom.mem_ker] at ha
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul c g =>
    rw [TensorProduct.smul_tmul', phi_tmul, smul_eq_mul]
    simp [psi, ha]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, add_zero]

theorem mk_eq_iff (n : ℕ) (g g' : G) :
    (Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] g) : Q l n G) = Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] g') ↔
      ∃ h : G, g = g' + (l ^ n) • h := by
  constructor
  · intro e
    rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub] at e
    have h0 := phi_eq_zero n _ e
    rw [phi_tmul, psi_one, QuotientAddGroup.eq_zero_iff] at h0
    obtain ⟨h, hh⟩ := h0
    refine ⟨h, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hh
    rw [hh]; abel
  · rintro ⟨h, rfl⟩
    rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub, add_sub_cancel_left, TensorProduct.tmul_smul,
      ← Nat.cast_smul_eq_nsmul ℤ_[l]]
    apply smul_mem_of_toZModPow
    rw [map_natCast, ZMod.natCast_self]

end GlobalTheory.KZ.ClsMod


open GlobalTheory.KZ.ClsMod in
theorem GlobalTheory.KZ.H3.cls_props : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, (∀ y, ∃ f, X.cls l n f = y) ∧ (∀ f f' : X.Kˣ, X.cls l n f = X.cls l n f' ↔ ∃ g : X.Kˣ, f = f' * g ^ (l ^ n)) ∧ (∀ f f' : X.Kˣ, X.cls l n (f * f') = X.cls l n f + X.cls l n f') ∧ X.cls l n 1 = 0 ∧ (∀ (c : ℤ_[l]) (f : X.Kˣ), c • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n c).val)) ∧ (∀ (φ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = X.cls l n (Units.map φ.toMonoidHom f)) ∧ (∀ (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x = X.cls l (n + 1) f → AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) := by
  intro Ω _ _ ε X l _ n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨g, hg⟩ := exists_mk n y
    exact ⟨Additive.toMul g, hg⟩
  · intro f f'
    unfold Tower.cls
    rw [mk_eq_iff]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨Additive.toMul h, ?_⟩
      apply Additive.ofMul.injective
      rw [hh, ofMul_mul, ofMul_pow]; rfl
    · rintro ⟨g, rfl⟩
      exact ⟨Additive.ofMul g, by rw [ofMul_mul, ofMul_pow]⟩
  · intro f f'
    unfold Tower.cls
    rw [ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]
  · unfold Tower.cls
    rw [ofMul_one, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]
  · intro c f
    unfold Tower.cls
    rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, mk_tmul, ofMul_pow]
  · intro φ x f hx
    rw [AdicCompletion.eval_apply] at hx ⊢
    have e := AdicCompletion.map_val_apply (idl l)
      (LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))) (n := n) x
    refine (e.trans ?_)
    rw [hx, Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
    rfl
  · intro x f hx
    rw [AdicCompletion.eval_apply] at hx ⊢
    rw [← AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) x, hx]
    rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowPropertiesStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerUnitClassModPrimePow_properties : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, (∀ y, ∃ f, X.cls l n f = y) ∧ (∀ f f' : X.Kˣ, X.cls l n f = X.cls l n f' ↔ ∃ g : X.Kˣ, f = f' * g ^ (l ^ n)) ∧ (∀ f f' : X.Kˣ, X.cls l n (f * f') = X.cls l n f + X.cls l n f') ∧ X.cls l n 1 = 0 ∧ (∀ (c : ℤ_[l]) (f : X.Kˣ), c • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n c).val)) ∧ (∀ (φ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = X.cls l n (Units.map φ.toMonoidHom f)) ∧ (∀ (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x = X.cls l (n + 1) f → AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) := by
  first | exact @GlobalTheory.KZ.H3.cls_props | exact GlobalTheory.KZ.H3.cls_props | (intros; apply GlobalTheory.KZ.H3.cls_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.MobLaws

theorem det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h0
  have hy : 0 < z.im := hz
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  have hd := det_pos g
  rcases him with hc | hc
  · rw [hc] at hre hd; simp at hre; rw [hre] at hd; simp at hd
  · linarith

theorem im_mob (g : GQ) (z : ℂ) : (mob g z).im =
    (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) * z.im /
      Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := by
  rw [mob, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ratCast_re, Complex.ratCast_im]
  push_cast
  rw [div_sub_div_same]
  congr 1
  ring

theorem mob_mem (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  show 0 < (mob g z).im
  rw [im_mob]
  have hy : 0 < z.im := hz
  have hd : (0:ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) := by exact_mod_cast det_pos g
  exact div_pos (mul_pos hd hy) (Complex.normSq_pos.2 (den_ne g hz))

theorem complex_mobius_fraction_clear_denom (a b c d N D : ℂ) (hD : D ≠ 0) :
    (a * (N / D) + b) / (c * (N / D) + d) = (a * N + b * D) / (c * N + d * D) := by
  have e1 : a * (N / D) + b = (a * N + b * D) / D := by field_simp
  have e2 : c * (N / D) + d = (c * N + d * D) / D := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hD]

theorem mob_mul (g h : GQ) {z : ℂ} (hz : z ∈ Hs) : mob (g * h) z = mob g (mob h z) := by
  have h1 := den_ne h hz
  unfold mob
  rw [complex_mobius_fraction_clear_denom _ _ _ _ _ _ h1]
  simp only [ent_mul]
  push_cast
  congr 1 <;> ring

theorem mob_one (z : ℂ) : mob 1 z = z := by
  simp [mob, ent]

theorem mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold mob
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

theorem toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.2]; norm_num
  apply Subtype.ext; apply Units.ext; ext i j
  simp [toGQ, h, ofSL]

theorem toGQ_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (hm : 0 < m.det) (hm' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have h : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos hm hm'
  apply Subtype.ext; apply Units.ext
  simp only [toGQ, h, hm, hm', dif_pos]
  ext i j
  simp [Matrix.mul_apply]

end GlobalTheory.KZ.MobLaws

namespace GlobalTheory.KZ

theorem mob_laws : (∀ (g : GQ), ∀ z ∈ Hs, mob g z ∈ Hs) ∧ (∀ (g h : GQ), ∀ z ∈ Hs, mob (g * h) z = mob g (mob h z)) ∧ (∀ z, mob 1 z = z) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ (∀ γ : SL(2, ℤ), toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ) ∧ (∀ m m' : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det → 0 < m'.det → toGQ (m * m') = toGQ m * toGQ m') :=
  ⟨fun g _ hz => MobLaws.mob_mem g hz, fun g h _ hz => MobLaws.mob_mul g h hz, MobLaws.mob_one,
    MobLaws.mob_diff, MobLaws.toGQ_SL, MobLaws.toGQ_mul⟩

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glTwoPosRatMobius_basic_laws : (∀ (g : GQ), ∀ z ∈ Hs, mob g z ∈ Hs) ∧ (∀ (g h : GQ), ∀ z ∈ Hs, mob (g * h) z = mob g (mob h z)) ∧ (∀ z, mob 1 z = z) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ (∀ γ : SL(2, ℤ), toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ) ∧ (∀ m m' : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det → 0 < m'.det → toGQ (m * m') = toGQ m * toGQ m') := by
  first | exact @GlobalTheory.KZ.mob_laws | exact GlobalTheory.KZ.mob_laws | (intros; apply GlobalTheory.KZ.mob_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem specialLinearGroup_map_intCast_zmod_surjective :
    ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) :
      SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) :=
  fun M => GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) M

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjectiveStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective : ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) := by
  first | exact @GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | exact GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | (intros; apply GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_mono (χ : kˣ →* ℂˣ) (x y : k) (h : valuation k y ≤ valuation k x) (hx : Triv χ x) :
    Triv χ y := fun u hu hle => hx u hu (hle.trans h)

theorem triv_add (χ : kˣ →* ℂˣ) (x y : k) (hx : Triv χ x) (hy : Triv χ y) : Triv χ (x + y) := by
  intro u hu hle
  rcases le_total (valuation k x) (valuation k y) with h | h
  · exact hy u hu (hle.trans ((Valuation.map_add _ x y).trans (max_le h le_rfl)))
  · exact hx u hu (hle.trans ((Valuation.map_add _ x y).trans (max_le le_rfl h)))

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ hle
  have : (u : k) - 1 = 0 := by simpa using hle
  have hu : u = 1 := Units.ext (by simpa [sub_eq_zero] using this)
  simp [hu]

theorem triv_neg (χ : kˣ →* ℂˣ) (x : k) (hx : Triv χ x) : Triv χ (-x) :=
  triv_mono χ x (-x) (by rw [Valuation.map_neg]) hx

theorem triv_mul (χ η : kˣ →* ℂˣ) (x : k) (h1 : Triv χ x) (h2 : Triv η x) : Triv (χ * η) x := by
  intro u hu hle
  simp [h1 u hu hle, h2 u hu hle]

theorem triv_inv (χ : kˣ →* ℂˣ) (x : k) (h : Triv χ x) : Triv χ⁻¹ x := by
  intro u hu hle
  simp [h u hu hle]

def trivSubgroup (χ : kˣ →* ℂˣ) : AddSubgroup k where
  carrier := {x | Triv χ x}
  add_mem' := fun {a b} ha hb => triv_add χ a b ha hb
  zero_mem' := triv_zero χ
  neg_mem' := fun {a} ha => triv_neg χ a ha

theorem triv_mem_nhds (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : {x : k | Triv χ x} ∈ nhds (0 : k) := by
  have hemb : Topology.IsEmbedding (Units.val : kˣ → k) := Units.isEmbedding_val₀
  obtain ⟨U, hUo, hU⟩ := hemb.isOpen_iff.mp hχ
  have h1 : (1 : k) ∈ U := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' U) := by rw [hU]; simp
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hUo.mem_nhds h1)
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  refine ⟨γ, fun x hx u _ hle => ?_⟩
  have hmem : (u : k) ∈ U := hγ (lt_of_le_of_lt hle hx)
  have : u ∈ (Units.val ⁻¹' U) := hmem
  rw [hU] at this
  simpa using this

theorem triv_isOpen_isClosed (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    IsOpen {x : k | Triv χ x} ∧ IsClosed {x : k | Triv χ x} := by
  have ho : IsOpen ((trivSubgroup χ : AddSubgroup k) : Set k) :=
    AddSubgroup.isOpen_of_mem_nhds _ (triv_mem_nhds χ hχ)
  exact ⟨ho, AddSubgroup.isClosed_of_isOpen _ ho⟩

theorem ev_of_val (χ : kˣ →* ℂˣ) (x : k) (h : valuation k x = 1) :
    ev χ x = (χ (Units.mk0 x (fun h0 => by simp [h0] at h)) : ℂ) := by
  simp [ev, h]

theorem ev_mul (χ : kˣ →* ℂˣ) (x y : k) (hx : valuation k x = 1) (hy : valuation k y = 1) :
    ev χ (x * y) = ev χ x * ev χ y := by
  have hxy : valuation k (x * y) = 1 := by simp [hx, hy]
  rw [ev_of_val χ _ hxy, ev_of_val χ _ hx, ev_of_val χ _ hy, ← Units.val_mul, ← map_mul]
  congr 3
  ext
  simp

theorem ev_congr (χ : kˣ →* ℂˣ) (x y : k) (hx : valuation k x = 1) (hy : valuation k y = 1)
    (h : Triv χ (x - y)) : ev χ x = ev χ y := by
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx
  have hy0 : y ≠ 0 := fun h0 => by simp [h0] at hy
  set u : kˣ := Units.mk0 x hx0 / Units.mk0 y hy0 with hu
  have huv : (u : k) = x / y := by simp [hu]
  have hu1 : valuation k (u : k) = 1 := by rw [huv, map_div₀, hx, hy, div_one]
  have hsub : (u : k) - 1 = (x - y) / y := by rw [huv]; field_simp
  have hle : valuation k ((u : k) - 1) ≤ valuation k (x - y) := by
    rw [hsub, map_div₀, hy, div_one]
  have hχu : χ u = 1 := h u hu1 hle
  have hxe : Units.mk0 x hx0 = u * Units.mk0 y hy0 := by rw [hu]; simp
  rw [ev_of_val χ _ hx, ev_of_val χ _ hy, hxe, map_mul, hχu, one_mul]

theorem ev_of_triv_one (χ : kˣ →* ℂˣ) (x : k) (h : Triv χ 1) : ev χ x = 1 := by
  by_cases hx : valuation k x = 1
  · rw [ev_of_val χ _ hx]
    have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx
    have hle : valuation k ((Units.mk0 x hx0 : k) - 1) ≤ valuation k (1 : k) := by
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> simp [hx]
    rw [h _ (by simpa using hx) hle]
    simp
  · simp [ev, hx]

end

theorem triv_ev_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k y ≤ valuation k x → Triv χ x → Triv χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), Triv χ x → Triv χ y → Triv χ (x + y)) ∧ (∀ χ : kˣ →* ℂˣ, Triv χ 0) ∧ (∀ (χ η : kˣ →* ℂˣ) (x : k), Triv χ x → Triv η x → Triv (χ * η) x) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ x → Triv χ⁻¹ x) ∧ (∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → IsOpen {x : k | Triv χ x} ∧ IsClosed {x : k | Triv χ x}) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → ev χ (x * y) = ev χ x * ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → Triv χ (x - y) → ev χ x = ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ 1 → ev χ x = 1) := by
  intro k _ _ _ _
  exact ⟨fun χ x y h hx => triv_mono χ x y h hx, fun χ x y => triv_add χ x y, triv_zero,
    fun χ η x => triv_mul χ η x, fun χ x => triv_inv χ x, fun χ hχ => triv_isOpen_isClosed χ hχ,
    fun χ x y => ev_mul χ x y, fun χ x y => ev_congr χ x y, fun χ x => ev_of_triv_one χ x⟩

end GlobalTheory.PsType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePrStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k y ≤ valuation k x → Triv χ x → Triv χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), Triv χ x → Triv χ y → Triv χ (x + y)) ∧ (∀ χ : kˣ →* ℂˣ, Triv χ 0) ∧ (∀ (χ η : kˣ →* ℂˣ) (x : k), Triv χ x → Triv η x → Triv (χ * η) x) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ x → Triv χ⁻¹ x) ∧ (∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → IsOpen {x : k | Triv χ x} ∧ IsClosed {x : k | Triv χ x}) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → ev χ (x * y) = ev χ x * ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → Triv χ (x - y) → ev χ x = ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ 1 → ev χ x = 1) := by
  first | exact @GlobalTheory.PsType.triv_ev_props | exact GlobalTheory.PsType.triv_ev_props | (intros; apply GlobalTheory.PsType.triv_ev_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPowerUnitsTowerClosureProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPowerUnitsTowerClosureProperties
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.UnClosure

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem one_mem (X : Tower Ω ε) (m : ℕ) : 1 ∈ X.Un m := by
  intro W _
  exact ⟨1, by simp⟩

theorem mul_mem (X : Tower Ω ε) (m : ℕ) (f g : X.Kˣ) (hf : f ∈ X.Un m) (hg : g ∈ X.Un m) :
    f * g ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  obtain ⟨b, hb⟩ := hg W hW
  refine ⟨a * b, ?_⟩
  have e : ((f * g : X.Kˣ) : X.K) / ((a * b : X.Kˣ) : X.K) ^ m
      = ((f : X.K) / (a : X.K) ^ m) * ((g : X.K) / (b : X.K) ^ m) := by
    push_cast; rw [mul_pow]; field_simp
  rw [e, map_mul, ha, hb, one_mul]

theorem inv_mem (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) : f⁻¹ ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a⁻¹, ?_⟩
  have e : ((f⁻¹ : X.Kˣ) : X.K) / ((a⁻¹ : X.Kˣ) : X.K) ^ m = ((f : X.K) / (a : X.K) ^ m)⁻¹ := by
    push_cast; rw [inv_pow]; field_simp
  rw [e, map_inv₀, ha, inv_one]

theorem pow_mem_self (X : Tower Ω ε) (m : ℕ) (g : X.Kˣ) : g ^ m ∈ X.Un m := by
  intro W _
  refine ⟨g, ?_⟩
  have e : ((g ^ m : X.Kˣ) : X.K) / (g : X.K) ^ m = 1 := by
    push_cast; exact div_self (pow_ne_zero _ g.ne_zero)
  rw [e, map_one]

theorem mem_of_mem_mul (X : Tower Ω ε) (m k : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un (m * k)) : f ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a ^ k, ?_⟩
  have e : ((a ^ k : X.Kˣ) : X.K) ^ m = (a : X.K) ^ (m * k) := by
    push_cast; rw [← pow_mul, mul_comm]
  rw [e]; exact ha

theorem pow_mem (X : Tower Ω ε) (m k : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) : f ^ k ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a ^ k, ?_⟩
  have e : ((f ^ k : X.Kˣ) : X.K) / ((a ^ k : X.Kˣ) : X.K) ^ m = ((f : X.K) / (a : X.K) ^ m) ^ k := by
    push_cast; rw [div_pow, ← pow_mul, ← pow_mul, mul_comm m k]
  rw [e, map_pow, ha, one_pow]

theorem val_eq_one_of_pow {K : Type} [Field K] (W : ValuationSubring K) (x : K) (m : ℕ) (hm : 0 < m)
    (h : W.valuation (x ^ m) = 1) : W.valuation x = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff.1 h).resolve_right hm.ne'

theorem mem_of_pow_mem (X : Tower Ω ε) (m k : ℕ) (g : X.Kˣ) (hm : 0 < m) (hg : g ^ m ∈ X.Un (m * k)) :
    g ∈ X.Un k := by
  intro W hW
  obtain ⟨a, ha⟩ := hg W hW
  refine ⟨a, val_eq_one_of_pow W _ m hm ?_⟩
  have e : ((g : X.K) / (a : X.K) ^ k) ^ m = ((g ^ m : X.Kˣ) : X.K) / (a : X.K) ^ (m * k) := by
    push_cast; rw [div_pow, ← pow_mul, mul_comm k m]
  rw [e]; exact ha

end GlobalTheory.KZ.UnClosure

namespace GlobalTheory.KZ.UnClosure

theorem un_closure : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ), 1 ∈ X.Un m ∧ (∀ f g, f ∈ X.Un m → g ∈ X.Un m → f * g ∈ X.Un m) ∧ (∀ f, f ∈ X.Un m → f⁻¹ ∈ X.Un m) ∧
      (∀ g : X.Kˣ, g ^ m ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un (m * k) → f ∈ X.Un m) ∧
      (∀ (k : ℕ) f, f ∈ X.Un m → f ^ k ∈ X.Un m) ∧
      ∀ (k : ℕ) (g : X.Kˣ), 0 < m → g ^ m ∈ X.Un (m * k) → g ∈ X.Un k := by
  intro Ω _ _ _ ε X _ _ m
  exact ⟨one_mem X m, mul_mem X m, inv_mem X m, pow_mem_self X m, fun k f hf => mem_of_mem_mul X m k f hf,
    fun k f hf => pow_mem X m k f hf, fun k g hm hg => mem_of_pow_mem X m k g hm hg⟩

end GlobalTheory.KZ.UnClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPowerUnitsTowerClosurePropertiesStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPowerUnitsTower_closure_properties : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 1 ∈ X.Un m ∧ (∀ f g, f ∈ X.Un m → g ∈ X.Un m → f * g ∈ X.Un m) ∧ (∀ f, f ∈ X.Un m → f⁻¹ ∈ X.Un m) ∧ (∀ g : X.Kˣ, g ^ m ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un (m * k) → f ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un m → f ^ k ∈ X.Un m) ∧ ∀ (k : ℕ) (g : X.Kˣ), 0 < m → g ^ m ∈ X.Un (m * k) → g ∈ X.Un k := by
  first | exact @GlobalTheory.KZ.UnClosure.un_closure | exact GlobalTheory.KZ.UnClosure.un_closure | (intros; apply GlobalTheory.KZ.UnClosure.un_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansion
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.MonExp

noncomputable def ex (w : ℕ) (i : Fin (w + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))

theorem ex_zero (w : ℕ) (i : Fin (w + 1)) : ex w i 0 = i := by
  simp [ex]

theorem ex_one (w : ℕ) (i : Fin (w + 1)) : ex w i 1 = w - i := by
  simp [ex]

theorem ex_inj (w : ℕ) {i j : Fin (w + 1)} (h : ex w i = ex w j) : i = j := by
  apply Fin.ext
  have := congrArg (fun d => d 0) h
  simpa [ex_zero] using this

theorem mon_eq (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) :
    mon R w i = MvPolynomial.monomial (ex w i) 1 := by
  rw [mon, ex, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]

theorem C_mul_mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) (c : R) :
    MvPolynomial.C c * mon R w i = MvPolynomial.monomial (ex w i) c := by
  rw [mon_eq, MvPolynomial.C_mul_monomial, mul_one]

theorem coeff_sum_mon (R : Type) [CommRing R] (w : ℕ) (c : Fin (w + 1) → R) (j : Fin (w + 1)) :
    AddMonoidAlgebra.coeff (∑ i, MvPolynomial.C (c i) * mon R w i) (ex w j) = c j := by
  rw [MvPolynomial.coeff_sum]
  simp_rw [C_mul_mon, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h; exact hij (ex_inj w h)
  · simp

theorem mon_hom (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) : (mon R w i).IsHomogeneous w := by
  have h := (MvPolynomial.isHomogeneous_X_pow (R := R) (0 : Fin 2) (i : ℕ)).mul
    (MvPolynomial.isHomogeneous_X_pow (R := R) (1 : Fin 2) (w - (i : ℕ)))
  have hi : (i : ℕ) + (w - (i : ℕ)) = w := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.isLt)
  rw [hi] at h
  exact h

theorem hom_expand (R : Type) [CommRing R] (w : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p.IsHomogeneous w) :
    p = ∑ i : Fin (w + 1), MvPolynomial.C (AddMonoidAlgebra.coeff p (ex w i)) * mon R w i := by
  ext d
  by_cases hd : ∃ j : Fin (w + 1), ex w j = d
  · obtain ⟨j, rfl⟩ := hd
    rw [coeff_sum_mon]
  · have h0 : AddMonoidAlgebra.coeff p d = 0 := by
      apply hp.coeff_eq_zero
      intro hdeg
      apply hd
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      refine ⟨⟨d 0, by omega⟩, ?_⟩
      ext k
      fin_cases k
      · simp [ex_zero]
      · simp [ex_one]; omega
    rw [h0, MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [C_mul_mon, MvPolynomial.coeff_monomial, if_neg]
    intro h; exact hd ⟨i, h⟩

theorem polySlash_monomial_isHomogeneous (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)) :
    (slP m (mon ℤ w k)).IsHomogeneous w := by
  have hl : ∀ j : Fin 2, ((m j 0 : ℤ) • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) +
      (m j 1 : ℤ) • MvPolynomial.X 1).IsHomogeneous 1 := by
    intro j
    have hs : ∀ (a : ℤ) (v : Fin 2), (a • (MvPolynomial.X v : MvPolynomial (Fin 2) ℤ)).IsHomogeneous 1 := by
      intro a v
      rw [MvPolynomial.smul_eq_C_mul]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 2) a).mul (MvPolynomial.isHomogeneous_X ℤ v)
    exact (hs _ 0).add (hs _ 1)
  have h := ((hl 0).pow (k : ℕ)).mul ((hl 1).pow (w - (k : ℕ)))
  have hi : 1 * (k : ℕ) + 1 * (w - (k : ℕ)) = w := by
    have := Nat.lt_succ_iff.mp k.isLt; omega
  rw [hi] at h
  simpa [slP, mon, map_mul, map_pow, MvPolynomial.aeval_X] using h

theorem map₃ (R : Type) [CommRing R] (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)) :
    MvPolynomial.map (Int.castRingHom R) (slP m (mon ℤ w k)) = slP m (mon R w k) := by
  simp [slP, mon, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.smul_eq_C_mul]

theorem map_mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) :
    MvPolynomial.map (Int.castRingHom R) (mon ℤ w i) = mon R w i := by
  simp [mon]

end GlobalTheory.KZ.MonExp


open GlobalTheory.KZ.MonExp in
theorem GlobalTheory.KZ.H3.mon_expand : ∀ (R : Type) [CommRing R] (w : ℕ), (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)), slP m (mon R w k) = ∑ i, MvPolynomial.C ((cf w m i k : ℤ) : R) * mon R w i) ∧ (∀ p : MvPolynomial (Fin 2) R, p.IsHomogeneous w → p = ∑ i : Fin (w + 1), MvPolynomial.C (AddMonoidAlgebra.coeff p (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) * mon R w i) ∧ (∀ i, (mon R w i).IsHomogeneous w) ∧ (∀ (u : Fin 2 → R) (i : Fin (w + 1)), MvPolynomial.eval u (mon R w i) = u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) ∧ (∀ c : Fin (w + 1) → R, ∑ i, MvPolynomial.C (c i) * mon R w i = 0 → c = 0) := by
  intro R _ w
  refine ⟨?_, fun p hp => hom_expand R w p hp, mon_hom R w, ?_, ?_⟩
  · intro m k
    have hz := hom_expand ℤ w _ (polySlash_monomial_isHomogeneous w m k)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map₃, hz, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.map_C, map_mon]
    rfl
  · intro u i
    simp [mon]
  · intro c hc
    funext j
    have := coeff_sum_mon R w c j
    rw [hc, MvPolynomial.coeff_zero] at this
    exact this.symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansionStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.binaryMonomialDegree_subst_expansion : ∀ (R : Type) [CommRing R] (w : ℕ), (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)), slP m (mon R w k) = ∑ i, MvPolynomial.C ((cf w m i k : ℤ) : R) * mon R w i) ∧ (∀ p : MvPolynomial (Fin 2) R, p.IsHomogeneous w → p = ∑ i : Fin (w + 1), MvPolynomial.C (AddMonoidAlgebra.coeff p (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) * mon R w i) ∧ (∀ i, (mon R w i).IsHomogeneous w) ∧ (∀ (u : Fin 2 → R) (i : Fin (w + 1)), MvPolynomial.eval u (mon R w i) = u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) ∧ (∀ c : Fin (w + 1) → R, ∑ i, MvPolynomial.C (c i) * mon R w i = 0 → c = 0) := by
  first | exact @GlobalTheory.KZ.H3.mon_expand | exact GlobalTheory.KZ.H3.mon_expand | (intros; apply GlobalTheory.KZ.H3.mon_expand <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentProperties
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.EpsProj

variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}

omit [Fintype G] in
theorem pow_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (n : ℕ) :
    S (u ^ n) ∧ χ (u ^ n) = χ u ^ n := by
  induction n with
  | zero => simp [h1, c1]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ⟨hm _ _ ih.1 hu, by rw [cm _ _ ih.1 hu, ih.2]⟩

theorem inv_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) :
    S u⁻¹ ∧ χ u⁻¹ = (χ u)⁻¹ ∧ ‖χ u‖ = 1 := by
  have hc : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hi : u⁻¹ = u ^ (Fintype.card G - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hc), pow_card_eq_one]
  have hS : S u⁻¹ := by rw [hi]; exact (pow_spec h1 hm c1 cm hu _).1
  refine ⟨hS, ?_, ?_⟩
  · have := cm _ _ hu hS
    rw [mul_inv_cancel, c1] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  · have := (pow_spec h1 hm c1 cm hu (Fintype.card G)).2
    rw [pow_card_eq_one, c1] at this
    exact Complex.norm_eq_one_of_pow_eq_one this.symm hc

theorem eps_mul (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (y : G) :
    eps S χ (u⁻¹ * y) = χ u * eps S χ y := by
  obtain ⟨hi, ci, -⟩ := inv_spec h1 hm c1 cm hu
  unfold eps
  by_cases hy : S y
  · rw [if_pos hy, if_pos (hm _ _ hi hy), cm _ _ hi hy, ci, mul_inv, inv_inv, mul_div_assoc]
  · have : ¬ S (u⁻¹ * y) := fun h => hy (by simpa using hm _ _ hu h)
    rw [if_neg hy, if_neg this, mul_zero]

omit [Group G] in
theorem sum_ite_card : ∑ y, (if S y then (1 : ℂ) else 0) = (Nat.card {u // S u} : ℂ) := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_eps_chi (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) :
    ∑ y, eps S χ y * χ y = 1 := by
  haveI : Nonempty {u // S u} := ⟨⟨1, h1⟩⟩
  have hc : (Nat.card {u // S u} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∀ y, eps S χ y * χ y = (if S y then (1 : ℂ) else 0) / (Nat.card {u // S u} : ℂ) := by
    intro y
    unfold eps
    by_cases hy : S y
    · have hn : χ y ≠ 0 := by
        intro h
        have := (inv_spec h1 hm c1 cm hy).2.2
        rw [h] at this
        simp at this
      rw [if_pos hy, if_pos hy]
      field_simp
    · simp [hy]
  simp_rw [this]
  rw [← Finset.sum_div, sum_ite_card, div_self hc]

theorem isProj_eps (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) : IsProj (eps S χ) := by
  refine ⟨?_, ?_⟩
  · funext x
    unfold conv
    have : ∀ y, eps S χ y * eps S χ (y⁻¹ * x) = eps S χ y * χ y * eps S χ x := by
      intro y
      by_cases hy : S y
      · rw [eps_mul h1 hm c1 cm hy, mul_assoc]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_mul, sum_eps_chi h1 hm c1 cm, one_mul]
  · intro x
    unfold eps
    by_cases hx : S x
    · obtain ⟨hi, ci, hn⟩ := inv_spec h1 hm c1 cm hx
      rw [if_pos hx, if_pos hi, ci, map_div₀, map_inv₀, map_natCast, Complex.inv_eq_conj hn]
    · have : ¬ S x⁻¹ := fun h => hx (by simpa using (inv_spec h1 hm c1 cm h).1)
      rw [if_neg hx, if_neg this, map_zero]

theorem mem_range_iff {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) (x : M) :
    x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x := by
  constructor
  · rintro ⟨z, rfl⟩ u hu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [op, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun y => ?_
    have := eps_mul h1 hm c1 cm hu (u * y)
    rw [inv_mul_cancel_left] at this
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
    rw [← this]
  · intro h
    refine ⟨x, ?_⟩
    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply]
    have : ∀ y, eps S χ y • ρ y x = (eps S χ y * χ y) • x := by
      intro y
      by_cases hy : S y
      · rw [h y hy, smul_smul]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_smul, sum_eps_chi h1 hm c1 cm, one_smul]

theorem eps_spec : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (S : G → Prop) (χ : G → ℂ), S 1 → (∀ u v, S u → S v → S (u * v)) → χ 1 = 1 → (∀ u v, S u → S v → χ (u * v) = χ u * χ v) → IsProj (eps S χ) ∧ eps S χ 1 = ((Nat.card {u // S u} : ℂ))⁻¹ ∧ (∀ x : M, x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x) ∧ ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℂ x → (∀ i u, S u → ρ u (x i) = χ u • x i) → n ≤ rk ρ (eps S χ) := by
  intro G _ _ M _ _ _ ρ S χ h1 hm c1 cm
  refine ⟨isProj_eps h1 hm c1 cm, ?_, mem_range_iff ρ h1 hm c1 cm, ?_⟩
  · simp only [eps, if_pos h1, c1, inv_one, one_div]
  · intro n x hx h
    have hmem : ∀ i, x i ∈ LinearMap.range (op ρ (eps S χ)) :=
      fun i => (mem_range_iff ρ h1 hm c1 cm _).2 (h i)
    have hli : LinearIndependent ℂ (fun i => (⟨x i, hmem i⟩ : LinearMap.range (op ρ (eps S χ)))) :=
      LinearIndependent.of_comp (LinearMap.range (op ρ (eps S χ))).subtype hx
    simpa [rk] using hli.fintype_card_le_finrank

end GlobalTheory.BadShare.EpsProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentPropertiesStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupCharacterIdempotent_properties : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (S : G → Prop) (χ : G → ℂ), S 1 → (∀ u v, S u → S v → S (u * v)) → χ 1 = 1 → (∀ u v, S u → S v → χ (u * v) = χ u * χ v) → IsProj (eps S χ) ∧ eps S χ 1 = ((Nat.card {u // S u} : ℂ))⁻¹ ∧ (∀ x : M, x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x) ∧ ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℂ x → (∀ i u, S u → ρ u (x i) = χ u • x i) → n ≤ rk ρ (eps S χ) := by
  first | exact @GlobalTheory.BadShare.EpsProj.eps_spec | exact GlobalTheory.BadShare.EpsProj.eps_spec | (intros; apply GlobalTheory.BadShare.EpsProj.eps_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Klm
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.klm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Kl l →ₗ[ℤ_[l]] X.Kl l :=
  LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))

def Tower.Lev (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (M : ℕ) : Submodule ℤ_[l] (X.Kl l) :=
  Submodule.span ℤ_[l] {x | ∃ f : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) ∧
    x = (1 : ℤ_[l]) ⊗ₜ Additive.ofMul f}

end GlobalTheory.KZ
end
end
