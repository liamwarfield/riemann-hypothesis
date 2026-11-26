module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierNegativeVectorTermNear
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierNegativeVectorTermNear
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ScalW

theorem znear_term : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) - hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := by
  intro D X u
  obtain ⟨c, hc, hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' := X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u with hz'
  have hm' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  refine ⟨c * c, Nat.Coprime.mul_left hc hc, ?_⟩
  intro y hy
  have hcz : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' ∈ X.B.I.Lf := by
    have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (GlobalTheory.St.G.FrameClose.nat_smul_mem c hz0) (GlobalTheory.St.G.FrameClose.mL_le _ hm')
  obtain ⟨t1, ht1, e1⟩ := GlobalTheory.St.G.FrameClose.zmod_of_mL hm' hy
  rw [GlobalTheory.St.G.FrameClose.hA_nat_left, GlobalTheory.St.G.FrameClose.hA_sub_left] at e1
  have hs : hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E := GlobalTheory.St.G.FrameClose.hA_int hz0 hy
  have hs' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E :=
    mul_mem (natCast_mem _ c) hs
  have e : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I z' y • z' - hA X.B.I X.z0 y • X.z0) =
      t1 • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z')) +
      ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0)) := by
    simp only [smul_smul, smul_sub, Nat.cast_mul]
    have e2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t1 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y := by
      linear_combination e1
    have e3 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        t1 * ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) +
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      linear_combination (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e2
    rw [e3, add_smul, show (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) by ring]
    abel
  rw [e]
  refine add_mem ?_ ?_
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, ht1⟩ : IntAf X.B.I.F X.B.I.E) (Submodule.subset_span ⟨_, hcz, rfl⟩)
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, hs'⟩ : IntAf X.B.I.F X.B.I.E) hm'

end GlobalTheory.ScalW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierNegativeVectorTermNearStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_multiplier_negativeVector_term_near : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) - hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := by
  first | exact @GlobalTheory.ScalW.znear_term | exact GlobalTheory.ScalW.znear_term | (intros; apply GlobalTheory.ScalW.znear_term <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryScalarBlendSelfAdjointIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryScalarBlendSelfAdjointIdempotent
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitTorus

theorem hform_mulVec_two {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M M' : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M' *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M') x y := by
  have e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v) := by
    intro N u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

theorem hform_single {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (N : Matrix n n A) (i j : n) :
    Formalism.UG.hform σ N (Pi.single i 1) (Pi.single j 1) = N i j := by
  simp [Formalism.UG.hform, Pi.single_apply]

theorem matrix_eq_of_hform {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (N N' : Matrix n n A) (h : ∀ x y, Formalism.UG.hform σ N x y = Formalism.UG.hform σ N' x y) : N = N' := by
  ext i j
  rw [← hform_single σ N i j, ← hform_single σ N' i j, h]

theorem unit_of_proj {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J P : Matrix n n A) (c : A) (hPP : P * P = P) (hSA : Formalism.UG.cT σ P * J = J * P) (hc : c * σ c = 1) :
    (c • 1 + (1 - c) • P) * (σ c • 1 + (1 - σ c) • P) = 1 ∧
    (σ c • 1 + (1 - σ c) • P) * (c • 1 + (1 - c) • P) = 1 ∧
    Formalism.UG.cT σ (c • 1 + (1 - c) • P) * J * (c • 1 + (1 - c) • P) = J := by
  have hcT : Formalism.UG.cT σ (c • (1 : Matrix n n A) + (1 - c) • P) = σ c • 1 + (1 - σ c) • Formalism.UG.cT σ P := by
    ext i j
    by_cases h : j = i
    · subst h; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]
  refine ⟨?_, ?_, ?_⟩
  · simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]
    calc _ = (c * σ c) • (1 : Matrix n n A) + (1 - c * σ c) • P := by module
      _ = 1 := by rw [hc, sub_self, zero_smul, add_zero, one_smul]
  · simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]
    calc _ = (c * σ c) • (1 : Matrix n n A) + (1 - c * σ c) • P := by module
      _ = 1 := by rw [hc, sub_self, zero_smul, add_zero, one_smul]
  · rw [hcT]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hSA,
      Matrix.mul_assoc, hPP, smul_smul]
    calc _ = (c * σ c) • J + (1 - c * σ c) • (J * P) := by module
      _ = J := by rw [hc, sub_self, zero_smul, add_zero, one_smul]

end GlobalTheory.UnitTorus

open GlobalTheory.UnitTorus in
theorem GlobalTheory.unitTorus_unit : ∀ (I : AutInst) (P : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (c : I.E ⊗[I.F] Af I.F), (∀ y, P *ᵥ (P *ᵥ y) = P *ᵥ y) → (∀ x y, hA I (P *ᵥ x) y = hA I x (P *ᵥ y)) → c * sigA I c = 1 → ∃ h : I.Gf, I.fmat h = c • 1 + (1 - c) • P ∧ I.fmat h⁻¹ = sigA I c • 1 + (1 - sigA I c) • P := by
  intro I P c hP hSA hc
  have hPP : P * P = P := by
    ext i j
    have := congrFun (hP (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec] at this
    simpa using this
  have hSA' : Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P := by
    have := matrix_eq_of_hform (sigA I) (Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * 1)
      (Formalism.UG.cT (sigA I) 1 * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P) (fun x y => by
        rw [← hform_mulVec_two, ← hform_mulVec_two, one_mulVec, one_mulVec]
        exact hSA x y)
    simpa [Formalism.UG.cT_one] using this
  obtain ⟨h1, h2, h3⟩ := unit_of_proj (sigA I) _ P c hPP hSA' hc
  exact ⟨⟨⟨_, _, h1, h2⟩, h3⟩, rfl, rfl⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryScalarBlendSelfAdjointIdempotentStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_scalarBlend_selfAdjoint_idempotent : ∀ (I : AutInst) (P : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (c : I.E ⊗[I.F] Af I.F), (∀ y, P *ᵥ (P *ᵥ y) = P *ᵥ y) → (∀ x y, hA I (P *ᵥ x) y = hA I x (P *ᵥ y)) → c * sigA I c = 1 → ∃ h : I.Gf, I.fmat h = c • 1 + (1 - c) • P ∧ I.fmat h⁻¹ = sigA I c • 1 + (1 - sigA I c) • P := by
  first | exact @GlobalTheory.unitTorus_unit | exact GlobalTheory.unitTorus_unit | (intros; apply GlobalTheory.unitTorus_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierHyperbolicTermsNearRefere
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierHyperbolicTermsNearRefere
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW.EfNear

variable {D : D7} (X : HidaSetting D)

theorem nat_smul_mL (k : ℕ) {x : VA X.B.I} (hx : x ∈ mL X.B.I X.B.g) :
    (k : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx k

theorem dvd_smul_mL {d M : ℕ} (hd : d ∣ M) {x : VA X.B.I}
    (hx : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g) :
    (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (k : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), mul_smul]
  exact nat_smul_mL X k hx

theorem term_near {v0 w0 v w y : VA X.B.I} (hw0 : w0 ∈ X.B.I.Lf) (hy : y ∈ X.B.I.Lf) {c1 c2 c3 : ℕ}
    (h1 : (c1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (v0 - v) ∈ mL X.B.I X.B.g)
    (h2 : (c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (w0 - w) ∈ mL X.B.I X.B.g)
    (h3 : (c3 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v ∈ X.B.I.Lf) :
    ((c1 * c2 * c3 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I w y • v - hA X.B.I w0 y • v0) ∈
      mL X.B.I X.B.g := by
  have e : hA X.B.I w y • v - hA X.B.I w0 y • v0 =
      -(hA X.B.I w0 y • (v0 - v)) - hA X.B.I (w0 - w) y • v := by
    rw [GlobalTheory.St.G.FrameClose.hA_sub_left, smul_sub, sub_smul]; abel
  rw [e, smul_sub]
  refine sub_mem ?_ ?_
  · refine dvd_smul_mL X (dvd_mul_of_dvd_left (dvd_mul_right c1 c2) c3) ?_
    rw [smul_neg, smul_comm]
    refine neg_mem ?_
    have := (mL X.B.I X.B.g).smul_mem (⟨_, GlobalTheory.St.G.FrameClose.hA_int hw0 hy⟩ : IntAf X.B.I.F X.B.I.E) h1
    rwa [Subring.smul_def] at this
  · refine dvd_smul_mL X (d := c2 * c3) ⟨c1, by ring⟩ ?_
    have e2 : ((c2 * c3 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (w0 - w) y • v) =
        hA X.B.I ((c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (w0 - w)) y •
          ((c3 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) := by
      rw [GlobalTheory.St.G.FrameClose.hA_nat_left, smul_smul, smul_smul, Nat.cast_mul]
      congr 1; ring
    rw [e2]
    exact Formalism.L2.SG.PoincareInHH.Cut.GU.smul_mL X (GlobalTheory.St.G.FrameClose.zmod_of_mL h2 hy) h3

end GlobalTheory.ScalW.EfNear

namespace GlobalTheory.ScalW


open GlobalTheory.ScalW.EfNear in
theorem ef_near_ref : ∀ (D : D7) (X : HidaSetting D), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, ∀ a, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a - hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g ∧ (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
  intro D X
  choose c1 hc1 h1 using fun a => (X.basisApprox a).1
  choose c2 hc2 h2 using fun a => (X.basisApprox a).2
  choose c3 hc3 h3 using fun a => GlobalTheory.St.G.FrameClose.den_of_inAt (X.vectorsInLattice.1 a).1 (X.basisApprox a).1
  choose c4 hc4 h4 using fun a => GlobalTheory.St.G.FrameClose.den_of_inAt (X.vectorsInLattice.1 a).2 (X.basisApprox a).2
  refine ⟨∏ a, c1 a * c2 a * c3 a * c4 a,
    Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left (hc1 a) (hc2 a)) (hc3 a)) (hc4 a), ?_⟩
  intro y hy a
  have hdvd : c1 a * c2 a * c3 a * c4 a ∣ ∏ b, c1 b * c2 b * c3 b * c4 b :=
    Finset.dvd_prod_of_mem (fun b => c1 b * c2 b * c3 b * c4 b) (Finset.mem_univ a)
  constructor
  · refine dvd_smul_mL X (d := c1 a * c2 a * c3 a) (dvd_trans ⟨c4 a, rfl⟩ hdvd) ?_
    exact term_near X (v0 := X.e0 a) (w0 := X.f0 a) (v := eV X a) (w := fV X a) (X.vectorsInLattice.1 a).2 hy (h1 a) (h2 a) (h3 a)
  · refine dvd_smul_mL X (d := c2 a * c1 a * c4 a) (dvd_trans ⟨c3 a, by ring⟩ hdvd) ?_
    exact term_near X (v0 := X.f0 a) (w0 := X.e0 a) (v := fV X a) (w := eV X a) (X.vectorsInLattice.1 a).1 hy (h2 a) (h1 a) (h4 a)

end GlobalTheory.ScalW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierHyperbolicTermsNearRefereStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_multiplier_hyperbolic_terms_near_reference : ∀ (D : D7) (X : HidaSetting D), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, ∀ a, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a - hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g ∧ (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
  first | exact @GlobalTheory.ScalW.ef_near_ref | exact GlobalTheory.ScalW.ef_near_ref | (intros; apply GlobalTheory.ScalW.ef_near_ref <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WordElementConjOrthProjHyperbolicNegativeSpanEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WordElementConjOrthProjHyperbolicNegativeSpanEq
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW.Conj

theorem fixInv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : VA X.B.I)
    (h : X.B.I.fmat (X.xu u) *ᵥ v = v) : X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Formalism.L2.SG.PoincareInHH.Cut.fmat_inv_mul X, Matrix.one_mulVec]

theorem prj_conj : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : VA X.B.I), X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y) = ∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a + ∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) := by
  intro D X u y
  have hE : ∀ a, X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.eV X a = GlobalTheory.ScalW.eV X a :=
    fun a => fixInv X u _ (X.xu_fix u a).1
  have hF : ∀ a, X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.fV X a = GlobalTheory.ScalW.fV X a :=
    fun a => fixInv X u _ (X.xu_fix u a).2
  simp only [GlobalTheory.ScalW.prj, GlobalTheory.St.G.FrameClose.hA_move, hE, hF, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_sum, Matrix.mulVec_smul]

end GlobalTheory.ScalW.Conj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WordElementConjOrthProjHyperbolicNegativeSpanEqStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordElement_conj_orthProjHyperbolicNegativeSpan_eq : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : VA X.B.I), X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y) = ∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a + ∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) := by
  first | exact @GlobalTheory.ScalW.Conj.prj_conj | exact GlobalTheory.ScalW.Conj.prj_conj | (intros; apply GlobalTheory.ScalW.Conj.prj_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjReferenceFrameOnFlagBasisModLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjReferenceFrameOnFlagBasisModLevel
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RefProjFlag

open Formalism.L2.SG.PoincareInHH.Cut.GU

variable {D : D7} (X : HidaSetting D)

theorem hA_zero_right' (u : VA X.B.I) : hA X.B.I u 0 = 0 := by
  have h := Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right X.B.I u 0 0
  rwa [zero_smul, zero_mul] at h

theorem intsmul_Lf' {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {y : VA X.B.I}
    (hy : y ∈ X.B.I.Lf) : t • y ∈ X.B.I.Lf :=
  X.B.I.Lf.smul_mem ⟨t, ht⟩ hy

theorem orthProjReferenceFrame_mem_finiteAdelicLattice {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf := by
  have he : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hf : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  refine sub_mem (add_mem (Submodule.sum_mem _ fun a _ => ?_) (Submodule.sum_mem _ fun a _ => ?_)) ?_
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (hf a) hy) (he a)
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (he a) hy) (hf a)
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I hz hy) hz

theorem orthProjReferenceFrame_mem_levelMultiple_of_coeff_congr {y : VA X.B.I} (hf : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) y))
    (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) y)) (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 y)) :
    GlobalTheory.ScalW.prj0 X y ∈ mL X.B.I X.B.g :=
  sub_mem (add_mem (sum_mL X _ _ hf fun a => (X.vectorsInLattice.1 a).1) (sum_mL X _ _ he fun a => (X.vectorsInLattice.1 a).2))
    (smul_mL X hz X.vectorsInLattice.2.1)

theorem sub_orthProjReferenceFrame_mem_levelMultiple_of_congr (b : VA X.B.I) (α β : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (γ : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hb : b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0) ∈ mL X.B.I X.B.g)
    (hα : ∀ a, ZMod' X.B.I X.B.g (α a - hA X.B.I (X.f0 a) b))
    (hβ : ∀ a, ZMod' X.B.I X.B.g (β a - hA X.B.I (X.e0 a) b))
    (hγ : ZMod' X.B.I X.B.g (γ - hA X.B.I X.z0 b)) : GlobalTheory.ScalW.prj0 X b - b ∈ mL X.B.I X.B.g := by
  have e : GlobalTheory.ScalW.prj0 X b - b = (γ - hA X.B.I X.z0 b) • X.z0
      - (b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0))
      - ∑ a, (α a - hA X.B.I (X.f0 a) b) • X.e0 a - ∑ a, (β a - hA X.B.I (X.e0 a) b) • X.f0 a := by
    simp only [GlobalTheory.ScalW.prj0, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [e]
  exact sub_mem (sub_mem (sub_mem (smul_mL X hγ X.vectorsInLattice.2.1) hb) (sum_mL X _ _ hα fun a => (X.vectorsInLattice.1 a).1))
    (sum_mL X _ _ hβ fun a => (X.vectorsInLattice.1 a).2)

theorem orthProjReferenceFrame_flagE_sub_mem_levelMultiple (c : Fin D.R.rS) : GlobalTheory.ScalW.prj0 X (X.e0 c) - X.e0 c ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ (fun a => if a = c then sigA X.B.I 1 else 0) 0 0 ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Zsw_ite X 1 (X.gramIntegral c a).2.2
  · intro a; exact Z0 X (X.gramIntegral a c).1
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).1)

theorem orthProjReferenceFrame_flagF_sub_mem_levelMultiple (c : Fin D.R.rS) : GlobalTheory.ScalW.prj0 X (X.f0 c) - X.f0 c ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ 0 (fun a => if a = c then 1 else 0) 0 ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.gramIntegral a c).2.1
  · intro a; exact Zswap X (X.gramIntegral a c).2.2
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).2)

theorem orthProjReferenceFrame_flagZ_sub_mem_levelMultiple : GlobalTheory.ScalW.prj0 X X.z0 - X.z0 ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ 0 0 (-1) ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.formsAtZero.2 a).2
  · intro a; exact Z0 X (X.formsAtZero.2 a).1
  · have := Zneg X X.formsAtZero.1
    rw [neg_add, add_comm] at this
    rwa [sub_eq_add_neg]

theorem orthProjReferenceFrame_middle_mem_levelMultiple (c c' : Fin D.R.k) : GlobalTheory.ScalW.prj0 X (X.bw c + X.bwd c') ∈ mL X.B.I X.B.g := by
  refine orthProjReferenceFrame_mem_levelMultiple_of_coeff_congr X (fun a => ?_) (fun a => ?_) ?_
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g ((X.weightVectorsIntegral c).2.2 a).2.1 ((X.weightVectorsIntegral c').2.2 a).2.2.2
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g ((X.weightVectorsIntegral c).2.2 a).1 ((X.weightVectorsIntegral c').2.2 a).2.2.1
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g (X.weightVectorsIntegral c).1 (X.weightVectorsIntegral c').2.1

theorem flagVec_Lf (j : ℕ) : flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf := by
  unfold flagVec
  split_ifs
  · exact (X.vectorsInLattice.1 _).1
  · exact add_mem (X.vectorsInLattice.2.2 _).1 (X.vectorsInLattice.2.2 _).2
  · exact X.vectorsInLattice.2.1
  · exact (X.vectorsInLattice.1 _).2
  · exact zero_mem _

theorem prj0_flagVec_mem_mL_or_sub_mem_mL : ∀ (D : D7) (X : HidaSetting D), (∀ y ∈ X.B.I.Lf, GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf) ∧
    ∀ j : ℕ, flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf ∧
      (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) ∈ mL X.B.I X.B.g) ∧
      (¬ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k) →
        GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ mL X.B.I X.B.g) := by
  intro D X
  refine ⟨fun y hy => orthProjReferenceFrame_mem_finiteAdelicLattice X hy, fun j => ⟨flagVec_Lf X j, ?_, ?_⟩⟩
  · rintro ⟨h1, h2⟩
    have h3 : ¬ j < D.R.rS := by omega
    have h4 : j - D.R.rS < D.R.k := by omega
    rw [flagVec, dite_eq_right h3, dite_eq_left h4]
    exact orthProjReferenceFrame_middle_mem_levelMultiple X _ _
  · intro h
    unfold flagVec
    split_ifs with h1 h2 h3 h4
    · exact orthProjReferenceFrame_flagE_sub_mem_levelMultiple X _
    · exact absurd ⟨by omega, by omega⟩ h
    · exact orthProjReferenceFrame_flagZ_sub_mem_levelMultiple X
    · exact orthProjReferenceFrame_flagF_sub_mem_levelMultiple X _
    · simp only [GlobalTheory.ScalW.prj0, hA_zero_right', zero_smul, Finset.sum_const_zero, add_zero, sub_zero]
      exact zero_mem _

end GlobalTheory.RefProjFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjReferenceFrameOnFlagBasisModLevelStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthProjReferenceFrame_on_flagBasis_mod_level : ∀ (D : D7) (X : HidaSetting D), (∀ y ∈ X.B.I.Lf, GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf) ∧ ∀ j : ℕ, flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf ∧ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) ∈ mL X.B.I X.B.g) ∧ (¬ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k) → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ mL X.B.I X.B.g) := by
  first | exact @GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL | exact GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL | (intros; apply GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanSelfAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanSelfAdjoint
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalW


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem prj_selfAdjoint : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x y : VA X.B.I),
    hA X.B.I (GlobalTheory.ScalW.prj X u x) y = hA X.B.I x (GlobalTheory.ScalW.prj X u y) := by
  intro D X u x y
  have hT : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hsum : ∀ (w : VA X.B.I) (g : Fin D.R.rS → VA X.B.I), hA X.B.I w (∑ a, g a) = ∑ a, hA X.B.I w (g a) :=
    fun w g => map_sum (hL X.B.I w) g Finset.univ
  have hd : ∀ c, divN X.B.I (D.mem u).A.T c = divN X.B.I (D.mem u).A.T 1 * c := by
    intro c; unfold divN; ring
  have hs : sigA X.B.I (divN X.B.I (D.mem u).A.T 1) = divN X.B.I (D.mem u).A.T 1 := by
    have h2 := congrArg (sigA X.B.I) (gmul_divN X.B.I _ hT 1)
    rw [map_mul, map_natCast, map_one] at h2
    rw [← divN_gmul X.B.I _ hT (sigA X.B.I _), h2]
  rw [hA_symm X.B.I y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [prj, hA_sub_right, hA_add_right, hA_smul_right, hsum, map_sub, map_add (f := _), map_sum, map_mul]
  rw [hd (hA X.B.I (zV X u) x), hd (hA X.B.I (zV X u) y), map_mul, hs]
  simp only [← hA_symm]
  rw [add_comm (∑ a, _ * hA X.B.I x (eV X a))]
  simp only [mul_comm (hA X.B.I x _)]
  ring

end GlobalTheory.ScalW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanSelfAdjointStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthProjHyperbolicNegativeSpan_selfAdjoint : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x y : VA X.B.I), hA X.B.I (GlobalTheory.ScalW.prj X u x) y = hA X.B.I x (GlobalTheory.ScalW.prj X u y) := by
  first | exact @GlobalTheory.ScalW.prj_selfAdjoint | exact GlobalTheory.ScalW.prj_selfAdjoint | (intros; apply GlobalTheory.ScalW.prj_selfAdjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixDiagonalModLevelOfDiagonalAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixDiagonalModLevelOfDiagonalAction
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameDiag

theorem hatL_eq (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩

theorem coord_zmod (I : AutInst) (g : ℕ) {β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : IsFrame β I.L) {v : VA I}
    (hv : v ∈ mL I g) (i : Fin I.n) :
    ZMod' I g ((((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v) i) := by
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.RowIndex.mem_mL.1 hv
  have hz' : z ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := by rw [hatL_eq]; exact hz
  refine ⟨_, (hβ z).1 hz' i, ?_⟩
  rw [Matrix.mulVec_smul]
  rfl

theorem diag_mod_in_frame : ∀ (I : AutInst) (g : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (Y : I.Gf) (d : Fin I.n → Formalism.L2.Herm.intAf I.F I.E), IsLiftFrame I g b β → (∀ y ∈ I.Lf, I.fmat Y *ᵥ y ∈ I.Lf) → (∀ y ∈ I.Lf, I.fmat Y⁻¹ *ᵥ y ∈ I.Lf) → (∀ j : Fin I.n, I.fmat Y *ᵥ b j.val - (d j).1 • b j.val ∈ mL I g) → ∃ x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), frGL β x = (Y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∧ ∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - Matrix.diagonal d) i j).1 := by
  intro I g b β Y d hβ hY hYi hd
  have hK : Y ∈ I.Kset := by
    intro y
    refine ⟨fun hy => hY y hy, fun hy => ?_⟩
    have h := hYi _ hy
    have e : I.fmat Y⁻¹ * I.fmat Y = 1 := by
      show (((Y⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * _ = 1
      rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rwa [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at h
  obtain ⟨x, hx⟩ := (kset_iff I hβ.1 Y).1 hK
  refine ⟨x, hx, fun i j => ?_⟩
  have hconj : β⁻¹ * frGL β x * β = intGL I.F I.E I.n x := by
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hx] at hconj
  set col : VA I := fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) l j with hcol
  have hw : I.fmat Y *ᵥ col - (d j).1 • col ∈ mL I g := by
    have h1 := hβ.2 j
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.RowIndex.mem_mL.1 h1
    have h2 : I.fmat Y *ᵥ (col - b j.val) ∈ mL I g := by
      rw [show col - b j.val = _ from hz']
      exact Formalism.L2.SG.Pf.unitaryCongruence.mL_mv I hY g le_rfl z hz
    have h3 : (d j).1 • (col - b j.val) ∈ mL I g := (mL I g).smul_mem (d j) h1
    have e : I.fmat Y *ᵥ col - (d j).1 • col =
        (I.fmat Y *ᵥ b j.val - (d j).1 • b j.val) + I.fmat Y *ᵥ (col - b j.val) - (d j).1 • (col - b j.val) := by
      rw [Matrix.mulVec_sub, smul_sub]
      abel
    rw [e]
    exact sub_mem (add_mem (hd j) h2) h3
  have key := coord_zmod I g hβ.1 hw i
  convert key using 1
  have eA : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ (I.fmat Y *ᵥ col)) i =
      ((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) i j).1 := by
    rw [Matrix.mulVec_mulVec]
    show ((((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * I.fmat Y) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _
    rw [← Units.val_mul, ← Units.val_mul, hconj]
    rfl
  have eB : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ col) i =
      if i = j then 1 else 0 := by
    show (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, eA, eB, Matrix.sub_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    simp
  · simp

end GlobalTheory.FrameDiag

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixDiagonalModLevelOfDiagonalActionStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrix_diagonal_mod_level_of_diagonal_action : ∀ (I : AutInst) (g : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (Y : I.Gf) (d : Fin I.n → Formalism.L2.Herm.intAf I.F I.E), IsLiftFrame I g b β → (∀ y ∈ I.Lf, I.fmat Y *ᵥ y ∈ I.Lf) → (∀ y ∈ I.Lf, I.fmat Y⁻¹ *ᵥ y ∈ I.Lf) → (∀ j : Fin I.n, I.fmat Y *ᵥ b j.val - (d j).1 • b j.val ∈ mL I g) → ∃ x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), frGL β x = (Y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∧ ∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - Matrix.diagonal d) i j).1 := by
  first | exact @GlobalTheory.FrameDiag.diag_mod_in_frame | exact GlobalTheory.FrameDiag.diag_mod_in_frame | (intros; apply GlobalTheory.FrameDiag.diag_mod_in_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarBlendProjectionMemStabilizerAndCommutes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarBlendProjectionMemStabilizerAndCommutes
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalW

theorem hMat_mem_hfin_comm : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (h : X.B.I.Gf), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) → GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u → X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c → h ∈ Hfin X u ∧ ∀ h' ∈ Hfin X u, h * h' = h' * h := by
  intro D X u c h hef hz hh
  have hfixV : ∀ v ∈ fixSet X u, GlobalTheory.ScalW.prj X u (incl X.B.I v) = incl X.B.I v := by
    rintro v ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hv)
    · exact (hef a).1
    · exact (hef a).2
    · rw [Set.mem_singleton_iff.1 hv]; exact hz
  have hmem : h ∈ Hfin X u := by
    intro v hv
    show X.B.I.fmat h *ᵥ incl X.B.I v = incl X.B.I v
    rw [hh, hMat_mulVec, hfixV v hv, ← add_smul, add_sub_cancel, one_smul]
  refine ⟨hmem, fun h' hh' => ?_⟩
  have hg : ∀ v ∈ fixSet X u, X.B.I.fmat h' *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u ⟨h', hh'⟩
  have hgi : ∀ v ∈ fixSet X u, X.B.I.fmat h'⁻¹ *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix_inv X u ⟨h', hh'⟩
  have hE := Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix X u
  have hF := Formalism.L2.SG.PoincareInHH.Cut.fR_mem_fix X u
  have hZ := Formalism.L2.SG.PoincareInHH.Cut.zR_mem_fix X u
  have hmv : ∀ v, v ∈ fixSet X u → ∀ y, hA X.B.I (incl X.B.I v) (X.B.I.fmat h' *ᵥ y) = hA X.B.I (incl X.B.I v) y := by
    intro v hv y
    rw [GlobalTheory.St.G.FrameClose.hA_move, hgi v hv]
  have hprj : ∀ y, prj X u (X.B.I.fmat h' *ᵥ y) = prj X u y := by
    intro y
    simp only [prj, eV, fV, zV, hmv _ (hE _), hmv _ (hF _), hmv _ hZ]
  have hprj2 : ∀ y, X.B.I.fmat h' *ᵥ prj X u y = prj X u y := by
    intro y
    simp only [prj, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, eV, fV, zV,
      hg _ (hE _), hg _ (hF _), hg _ hZ]
  have hM : X.B.I.fmat (h * h') = X.B.I.fmat (h' * h) := by
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, hh]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMat_mulVec, hMat_mulVec, hprj, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hprj2]
  exact Subtype.ext (Units.ext hM)

end GlobalTheory.ScalW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarBlendProjectionMemStabilizerAndCommutesStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarBlend_projection_mem_stabilizer_and_commutes : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (h : X.B.I.Gf), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) → GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u → X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c → h ∈ Hfin X u ∧ ∀ h' ∈ Hfin X u, h * h' = h' * h := by
  first | exact @GlobalTheory.ScalW.hMat_mem_hfin_comm | exact GlobalTheory.ScalW.hMat_mem_hfin_comm | (intros; apply GlobalTheory.ScalW.hMat_mem_hfin_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanFixesBasisAndIdemp
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanFixesBasisAndIdemp
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ScalW

open Formalism.L2.SG.PoincareInHH.Cut

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hA_eV_eV (a b : Fin D.R.rS) : hA X.B.I (eV X a) (eV X b) = 0 := by
  rw [eV, eV, HidaSetting.eR, HidaSetting.eR, hA_crd, X.ee]
  simp

theorem hA_fV_fV (a b : Fin D.R.rS) : hA X.B.I (fV X a) (fV X b) = 0 := by
  rw [fV, fV, HidaSetting.fR, HidaSetting.fR, hA_crd, X.ff]
  simp

theorem hA_eV_fV (a b : Fin D.R.rS) : hA X.B.I (eV X a) (fV X b) = if a = b then 1 else 0 := by
  rw [eV, fV, HidaSetting.eR, HidaSetting.fR, hA_crd, X.ef]
  split_ifs <;> simp

theorem hA_fV_eV (a b : Fin D.R.rS) : hA X.B.I (fV X a) (eV X b) = if b = a then 1 else 0 :=
  hA_f_e X a b

theorem hA_zV_eV (a : Fin D.R.rS) : hA X.B.I (zV X u) (eV X a) = 0 := by
  have h := (VS D).herm.eq (X.eX a) (X.zu u)
  rw [(X.zu_orth u a).1, map_zero] at h
  rw [zV, eV, HidaSetting.zR, HidaSetting.eR, hA_crd, ← h]
  simp

theorem hA_zV_fV (a : Fin D.R.rS) : hA X.B.I (zV X u) (fV X a) = 0 := by
  have h := (VS D).herm.eq (X.fY a) (X.zu u)
  rw [(X.zu_orth u a).2, map_zero] at h
  rw [zV, fV, HidaSetting.zR, HidaSetting.fR, hA_crd, ← h]
  simp

theorem hA_eV_zV (a : Fin D.R.rS) : hA X.B.I (eV X a) (zV X u) = 0 := by
  rw [zV, eV, HidaSetting.zR, HidaSetting.eR, hA_crd, (X.zu_orth u a).1]
  simp

theorem hA_fV_zV (a : Fin D.R.rS) : hA X.B.I (fV X a) (zV X u) = 0 := adelicHermitian_hyperbolicF_anisotropic_eq_zero X u a

theorem hA_zV_zV : hA X.B.I (zV X u) (zV X u) =
    -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
  rw [zV, HidaSetting.zR, hA_crd, X.zu_norm]
  simp

theorem divN_zero' : divN X.B.I (D.mem u).A.T 0 = 0 := by
  simp [divN]

theorem prj_eV (b : Fin D.R.rS) : prj X u (eV X b) = eV X b := by
  simp only [prj, hA_fV_eV, hA_eV_eV, hA_zV_eV, divN_zero', ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, sub_zero]

theorem prj_fV (b : Fin D.R.rS) : prj X u (fV X b) = fV X b := by
  simp only [prj, hA_fV_fV, hA_eV_fV, hA_zV_fV, divN_zero', ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, zero_add, sub_zero]

theorem prj_zV : prj X u (zV X u) = zV X u := by
  have hT : ((D.mem u).A.T : ℕ) ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have h : divN X.B.I (D.mem u).A.T (-(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) = -1 := by
    rw [show -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (-1) by ring]
    exact Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul X.B.I _ hT _
  simp only [prj, hA_fV_zV, hA_eV_zV, hA_zV_zV, h, zero_smul, Finset.sum_const_zero, zero_add,
    neg_smul, one_smul, sub_neg_eq_add]

theorem prj_prj (y : VA X.B.I) : prj X u (prj X u y) = prj X u y := by
  have hL : ∀ z, prjL X u z = prj X u z := fun _ => rfl
  rw [← hL (prj X u y)]
  conv_lhs => arg 2; rw [prj]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_add (f := _), map_sum, map_smul]
  simp only [hL, prj_eV, prj_fV, prj_zV]
  rfl

theorem prj_fix_idem : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧
      GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) ∧
    GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u ∧
    ∀ y, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.prj X u y) = GlobalTheory.ScalW.prj X u y :=
  fun _ X u => ⟨fun a => ⟨prj_eV X u a, prj_fV X u a⟩, prj_zV X u, prj_prj X u⟩

end GlobalTheory.ScalW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanFixesBasisAndIdempStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthProjHyperbolicNegativeSpan_fixes_basis_and_idempotent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u ∧ ∀ y, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.prj X u y) = GlobalTheory.ScalW.prj X u y := by
  first | exact @GlobalTheory.ScalW.prj_fix_idem | exact GlobalTheory.ScalW.prj_fix_idem | (intros; apply GlobalTheory.ScalW.prj_fix_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComplementFrameDiagModConductor
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW

set_option maxHeartbeats 800000 in
theorem scalar_diag_mod_g : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (β : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)), IsLiftFrame X.B.I X.B.g (flagVec X.e0 X.f0 X.z0 X.bw X.bwd) β → ∀ c : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E, c * sigInt X.B.I c = 1 → (∀ N : ℕ, Nat.Coprime N X.B.g → ZMod' X.B.I N (1 - c.1)) → ∃ h ∈ Hfin X u, (∀ h' ∈ Hfin X u, h * h' = h' * h) ∧ ∃ x : GL (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E), frGL β x = (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∧ ∀ i j, ZMod' X.B.I X.B.g (((x : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E)) - midDiag X.B.I.n D.R.rS D.R.k 1 c) i j).1 := by
  intro D X u β hβ c hc hN
  have hg1 : 1 ≤ X.B.g := Formalism.L2.SG.PoincareInHH.Cut.one_le_g X
  obtain ⟨M6, hM6, hz6⟩ := GlobalTheory.T.exists_coprime_multiplier_one_sub_norm_congr_zero D X u
  have hTg : Nat.Coprime (D.mem u).A.T X.B.g := GlobalTheory.T.nat_coprime_of_congr_mul_one_sub_mod_level X.B.I X.B.g _ M6 hg1 hM6 hz6
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  obtain ⟨Mb, hMb, hb7⟩ := GlobalTheory.T.exists_coprime_multiplier_hyperbolic_terms_near_reference D X
  obtain ⟨Mc, hMc, hc7⟩ := GlobalTheory.T.exists_coprime_multiplier_negativeVector_term_near D X u
  have hc' : c.1 * sigA X.B.I c.1 = 1 := by
    have := congrArg Subtype.val hc
    simpa [sigInt_coe] using this
  obtain ⟨hfix, hfz, hidem⟩ := GlobalTheory.T.orthProjHyperbolicNegativeSpan_fixes_basis_and_idempotent D X u
  obtain ⟨h, hh, hhi⟩ := GlobalTheory.T.exists_unitary_scalarBlend_selfAdjoint_idempotent X.B.I (GlobalTheory.ScalW.prjM X u) c.1
    (fun y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, hidem])
    (fun x y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.T.orthProjHyperbolicNegativeSpan_selfAdjoint]) hc'
  have hh' : X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c.1 := hh
  have hhi' : X.B.I.fmat h⁻¹ = GlobalTheory.ScalW.hMat X u (sigA X.B.I c.1) := hhi
  obtain ⟨hH, hcomm⟩ := GlobalTheory.T.scalarBlend_projection_mem_stabilizer_and_commutes D X u c.1 h hfix hfz hh'
  obtain ⟨hP0, hfl⟩ := GlobalTheory.T.orthProjReferenceFrame_on_flagBasis_mod_level D X

  set P' : VA X.B.I → VA X.B.I := fun y => X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y)
    with hP'
  set M := Mb * Mc * M6 * (D.mem u).A.T with hMdef
  have hMg : Nat.Coprime M X.B.g := by
    simp only [hMdef, Nat.coprime_mul_iff_left]
    exact ⟨⟨⟨hMb, hMc⟩, hM6⟩, hTg⟩
  have smulL : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ X.B.I.Lf → s • y ∈ X.B.I.Lf := fun hs _ hy => X.B.I.Lf.smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have smulM : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ mL X.B.I X.B.g → s • y ∈ mL X.B.I X.B.g := fun hs _ hy => (mL X.B.I X.B.g).smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have hnear : ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro y hy
    rw [hP']
    beta_reduce
    rw [GlobalTheory.T.wordElement_conj_orthProjHyperbolicNegativeSpan_eq]
    simp only [GlobalTheory.ScalW.prj0]
    have hA1 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) -
        ∑ a, hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).1
    have hA2 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) -
        ∑ a, hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).2
    have hZ := hc7 y hy
    have hw0 : hA X.B.I X.z0 y • X.z0 ∈ X.B.I.Lf :=
      X.B.I.Lf.smul_mem (⟨_, GlobalTheory.St.G.FrameClose.hA_int X.vectorsInLattice.2.1 hy⟩ : IntAf X.B.I.F X.B.I.E) X.vectorsInLattice.2.1
    have hW : ((M6 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) •
        (hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := Formalism.L2.SG.PoincareInHH.Cut.GU.smul_mL X hz6 hw0
    have hTd : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
        divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) =
        hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y := Formalism.L2.SG.Pf.unitaryCongruence.gmul_divN X.B.I _ hT0 _
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) = S1 at hA1 ⊢
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) = S2 at hA2 ⊢
    generalize (∑ a, hA X.B.I (X.f0 a) y • X.e0 a) = S3 at hA1 ⊢
    generalize (∑ a, hA X.B.I (X.e0 a) y • X.f0 a) = S4 at hA2 ⊢
    generalize X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u = z' at hZ hTd ⊢
    generalize divN X.B.I (D.mem u).A.T (hA X.B.I z' y) = dd at hTd ⊢
    generalize hA X.B.I X.z0 y • X.z0 = w0 at hZ hW ⊢
    rw [← hTd] at hZ
    rw [hMdef, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, GlobalTheory.ScalW.scalW_ident]
    have hN' : ∀ m : ℕ, (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E := fun m => natCast_mem _ m
    exact sub_mem (sub_mem (add_mem (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA1)
      (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA2)) (smulM (mul_mem (hN' _) (hN' _)) hZ))
      (smulM (mul_mem (hN' _) (hN' _)) hW)
  have key : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, ZMod' X.B.I M (1 - s) → ∀ y ∈ X.B.I.Lf,
      (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro s hzs y hy
    obtain ⟨t, ht, e⟩ := hzs
    rw [e, mul_comm, mul_smul]
    exact smulM ht (hnear y hy)
  have hint : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, s ∈ IntAf X.B.I.F X.B.I.E → ZMod' X.B.I M (1 - s) →
      ∀ y ∈ X.B.I.Lf, s • y + (1 - s) • P' y ∈ X.B.I.Lf := by
    intro s hs hzs y hy
    have e : s • y + (1 - s) • P' y = s • y + (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) + (1 - s) • GlobalTheory.ScalW.prj0 X y := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (add_mem (smulL hs hy) (GlobalTheory.St.G.FrameClose.mL_le _ (key s hzs y hy)))
      (smulL (sub_mem (one_mem _) hs) (hP0 y hy))
  have hact : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (k : X.B.I.Gf), X.B.I.fmat k = GlobalTheory.ScalW.hMat X u s →
      ∀ y, X.B.I.fmat ((X.xu u)⁻¹ * k * X.xu u) *ᵥ y = s • y + (1 - s) • P' y := by
    intro s k hk y
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hk,
      GlobalTheory.ScalW.hMat_mulVec, mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec,
      Formalism.L2.SG.PoincareInHH.Cut.fmat_inv_mul, one_mulVec]
  have hcM : ZMod' X.B.I M (1 - c.1) := hN M hMg
  have hsM : ZMod' X.B.I M (1 - sigA X.B.I c.1) := by
    have := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I M hcM
    rwa [map_sub, map_one] at this
  have hinvY : ((X.xu u)⁻¹ * h * X.xu u)⁻¹ = (X.xu u)⁻¹ * h⁻¹ * X.xu u := by group
  set d : Fin X.B.I.n → Formalism.L2.Herm.intAf X.B.I.F X.B.I.E :=
    fun i => if D.R.rS ≤ i.val ∧ i.val < D.R.rS + D.R.k then c else 1 with hd
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.frame_matrix_diagonal_mod_level_of_diagonal_action X.B.I X.B.g _ β ((X.xu u)⁻¹ * h * X.xu u) d hβ
    (fun y hy => by rw [hact _ h hh']; exact hint _ c.2 hcM y hy)
    (fun y hy => by
      rw [hinvY, hact _ _ hhi']
      exact hint _ (Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem X.B.I c.2) hsM y hy)
    (fun j => by
      obtain ⟨hbL, hW, hnW⟩ := hfl j.val
      rw [hact _ h hh']
      have hk := key c.1 hcM _ hbL
      by_cases hj : D.R.rS ≤ j.val ∧ j.val < D.R.rS + D.R.k
      · have e1 : (d j).1 = c.1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          rw [smul_sub]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hW hj))
      · have e1 : (d j).1 = 1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • (GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          simp only [smul_sub, sub_smul, one_smul]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hnW hj)))
  refine ⟨h, hH, hcomm, x, hx1, fun i j => ?_⟩
  have e : midDiag X.B.I.n D.R.rS D.R.k 1 c = Matrix.diagonal d := by
    simp only [midDiag, hd]
  rw [e]
  exact hx2 i j

end GlobalTheory.ScalW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComplementFrameDiagModConductorStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_complement_frame_diag_mod_conductor : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (β : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)), IsLiftFrame X.B.I X.B.g (flagVec X.e0 X.f0 X.z0 X.bw X.bwd) β → ∀ c : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E, c * sigInt X.B.I c = 1 → (∀ N : ℕ, Nat.Coprime N X.B.g → ZMod' X.B.I N (1 - c.1)) → ∃ h ∈ Hfin X u, (∀ h' ∈ Hfin X u, h * h' = h' * h) ∧ ∃ x : GL (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E), frGL β x = (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∧ ∀ i j, ZMod' X.B.I X.B.g (((x : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E)) - midDiag X.B.I.n D.R.rS D.R.k 1 c) i j).1 := by
  first | exact @GlobalTheory.ScalW.scalar_diag_mod_g | exact GlobalTheory.ScalW.scalar_diag_mod_g | (intros; apply GlobalTheory.ScalW.scalar_diag_mod_g <;> assumption)
end
