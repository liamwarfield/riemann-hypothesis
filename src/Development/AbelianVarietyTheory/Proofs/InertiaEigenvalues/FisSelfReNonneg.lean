module

public import ReciprocityTheory.DualLattices.FischerSelfNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityShiftLatticeVariablePow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
noncomputable section

open MvPolynomial

namespace GlobalTheory.FockIsotypic

variable {σ : Type} [Fintype σ]

def flat (σ : Type) [Fintype σ] : σ ≃ Fin (Fintype.card σ) × Unit :=
  (Fintype.equivFin σ).trans (Equiv.prodPUnit _).symm

def fis (P Q : MvPolynomial σ ℂ) : ℂ :=
  ReciprocityTheory.PGsh.fischer (rename (flat σ) P) (rename (flat σ) Q)

theorem fis_conj (P Q : MvPolynomial σ ℂ) : starRingEnd ℂ (fis P Q) = fis Q P := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  set Q' := rename (flat σ) Q
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ReciprocityTheory.PGsh.fischer_eq_sum P' Q' (P'.support ∪ Q'.support) Finset.subset_union_left,
    ReciprocityTheory.PGsh.fischer_eq_sum Q' P' (P'.support ∪ Q'.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [ReciprocityTheory.PGsh.fw, map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fis_self_re_nonneg (P : MvPolynomial σ ℂ) : 0 ≤ (fis P P).re := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  rw [ReciprocityTheory.PGsh.fischer_eq_sum P' P' P'.support subset_rfl, Complex.re_sum]
  refine Finset.sum_nonneg fun A _ => ?_
  rw [Complex.mul_conj, ReciprocityTheory.PGsh.fw, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fis_self_ne_zero {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : fis P P ≠ 0 :=
  ReciprocityTheory.PGsh.fischer_self_ne_zero _ fun h =>
    hP (rename_injective _ (flat σ).injective (h.trans (map_zero _).symm))

theorem fis_add_right (P Q Q' : MvPolynomial σ ℂ) : fis P (Q + Q') = fis P Q + fis P Q' := by
  unfold fis
  rw [map_add (f := _), ReciprocityTheory.PGsh.fischer_add_right]

theorem fis_smul_right (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis P (c • Q) = starRingEnd ℂ c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_right]

theorem fis_smul_left (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis (c • P) Q = c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_left]

@[reducible] def fisCore (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := fis y.1 x.1
  conj_inner_symm x y := fis_conj _ _
  re_inner_nonneg x := fis_self_re_nonneg _
  add_left x y z := fis_add_right _ _ _
  smul_left x y r := fis_smul_right _ _ _
  definite x hx := by
    by_contra h
    exact fis_self_ne_zero (fun h' => h (Subtype.ext h')) hx

end GlobalTheory.FockIsotypic

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RhoProdFiniteAlgebraWithInvolution
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RhoProdFiniteAlgebraWithInvolution
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.RhoProd

theorem out_iff {G : Type} [Group G] (H : Subgroup G) (P : G → Prop)
    (hP : ∀ g h, h ∈ H → (P (g * h) ↔ P g)) (g : G) :
    P (Quotient.out (QuotientGroup.mk g : G ⧸ H)) ↔ P g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh]; exact hP g h h.2

theorem card_prod {G G₁ G₂ : Type} [Group G] [Group G₁] [Group G₂]
    (H : Subgroup G) (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) (e : G ≃* G₁ × G₂)
    (he : ∀ g, g ∈ H ↔ (e g).1 ∈ H₁ ∧ (e g).2 ∈ H₂)
    (P : G → Prop) (P₁ : G₁ → Prop) (P₂ : G₂ → Prop)
    (hP : ∀ g, P g ↔ P₁ (e g).1 ∧ P₂ (e g).2)
    (h₁ : ∀ g h, h ∈ H₁ → (P₁ (g * h) ↔ P₁ g)) (h₂ : ∀ g h, h ∈ H₂ → (P₂ (g * h) ↔ P₂ g)) :
    Nat.card {k : G ⧸ H // P (Quotient.out k)} =
      Nat.card {k : G₁ ⧸ H₁ // P₁ (Quotient.out k)} * Nat.card {k : G₂ ⧸ H₂ // P₂ (Quotient.out k)} := by
  let E : G ⧸ H ≃ (G₁ ⧸ H₁) × (G₂ ⧸ H₂) :=
    (Quotient.congr e.toEquiv (by
      intro a b
      show QuotientGroup.leftRel H a b ↔ (QuotientGroup.leftRel H₁).prod (QuotientGroup.leftRel H₂) (e a) (e b)
      rw [Setoid.prod_apply, QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, he]
      simp [map_mul, map_inv])).trans (Setoid.prodQuotientEquiv _ _).symm
  have hE : ∀ g : G, E (QuotientGroup.mk g) = (QuotientGroup.mk (e g).1, QuotientGroup.mk (e g).2) := by
    intro g; rfl
  have hPi : ∀ g h, h ∈ H → (P (g * h) ↔ P g) := by
    intro g h hh
    rw [hP, hP, map_mul, Prod.fst_mul, Prod.snd_mul]
    exact and_congr (h₁ _ _ ((he h).1 hh).1) (h₂ _ _ ((he h).1 hh).2)
  rw [← Nat.card_prod]
  refine Nat.card_congr ((E.subtypeEquiv ?_).trans (Equiv.subtypeProdEquivProd))
  intro k
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  rw [hE, out_iff H₁ P₁ h₁, out_iff H₂ P₂ h₂, ← hP]
  exact out_iff H P hPi g

variable {K : UQ}

def torusEquiv (B₁ B₂ : InvAlg K) : (B₁.prod B₂).T ≃* B₁.T × B₂.T where
  toFun t := (⟨Units.map (RingHom.fst B₁.A B₂.A).toMonoidHom (show (B₁.A × B₂.A)ˣ from t.1),
      congrArg Prod.fst t.2⟩,
    ⟨Units.map (RingHom.snd B₁.A B₂.A).toMonoidHom (show (B₁.A × B₂.A)ˣ from t.1),
      congrArg Prod.snd t.2⟩)
  invFun s := ⟨show (B₁.A × B₂.A)ˣ from MulEquiv.prodUnits.symm ((s.1 : B₁.Aˣ), (s.2 : B₂.Aˣ)),
      Prod.ext s.1.2 s.2.2⟩
  left_inv t := by
    apply Subtype.ext; apply Units.ext; rfl
  right_inv s := by
    ext <;> rfl
  map_mul' a b := by
    ext <;> rfl

theorem inv_mul_int (B : InvAlg K) (w : B.A) (g h : B.T)
    (hh : h ∈ (intUnits K.O B.A).subgroupOf B.T) :
    IsIntegral K.O ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) ↔
      IsIntegral K.O ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) := by
  rw [Subgroup.mem_subgroupOf] at hh
  obtain ⟨hi, hi'⟩ := hh
  have e1 : ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) =
      ((((h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w) := by
    simp [mul_inv_rev, Units.val_mul, mul_assoc]
  have e2 : ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) =
      (((h : B.T) : B.Aˣ) : B.A) * ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w) := by
    rw [e1, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  constructor
  · intro H; rw [e2]; exact hi.mul H
  · intro H; rw [e1]; exact hi'.mul H

theorem rho_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (w₁ : B₁.A) (w₂ : B₂.A),
    (B₁.prod B₂).rho ((w₁, w₂) : B₁.A × B₂.A) = B₁.rho w₁ * B₂.rho w₂ := by
  intro K B₁ B₂ w₁ w₂
  unfold InvAlg.rho
  refine card_prod ((intUnits K.O (B₁.prod B₂).A).subgroupOf (B₁.prod B₂).T) _ _ (torusEquiv B₁ B₂) ?_
    (fun g : (B₁.prod B₂).T => IsIntegral K.O ((((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) * (show (B₁.prod B₂).A from (w₁, w₂)) : (B₁.prod B₂).A)))
    (fun g : B₁.T => IsIntegral K.O ((((g : B₁.Aˣ)⁻¹ : B₁.Aˣ) * w₁ : B₁.A)))
    (fun g : B₂.T => IsIntegral K.O ((((g : B₂.Aˣ)⁻¹ : B₂.Aˣ) * w₂ : B₂.A)))
    ?_ (inv_mul_int B₁ w₁) (inv_mul_int B₂ w₂)
  · intro g
    simp only [Subgroup.mem_subgroupOf]
    show (IsIntegral K.O (show B₁.A × B₂.A from ((g : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) ∧ IsIntegral K.O (show B₁.A × B₂.A from (((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A))) ↔ _
    rw [IsIntegral.pair_iff, IsIntegral.pair_iff]
    exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨⟨a, c⟩, ⟨b, d⟩⟩, fun ⟨⟨a, c⟩, ⟨b, d⟩⟩ => ⟨⟨a, b⟩, ⟨c, d⟩⟩⟩
  · intro g
    show IsIntegral K.O (show B₁.A × B₂.A from ((((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A) * (show (B₁.prod B₂).A from (w₁, w₂)))) ↔ _
    rw [IsIntegral.pair_iff]
    exact Iff.rfl

end GlobalTheory.RhoProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RhoProdFiniteAlgebraWithInvolutionStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rho_prod_finiteAlgebraWithInvolution : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (w₁ : B₁.A) (w₂ : B₂.A), (B₁.prod B₂).rho ((w₁, w₂) : B₁.A × B₂.A) = B₁.rho w₁ * B₂.rho w₂ := by
  first | exact @GlobalTheory.RhoProd.rho_prod | exact GlobalTheory.RhoProd.rho_prod | (intros; apply GlobalTheory.RhoProd.rho_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniformizerIdempotentFrameProd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniformizerIdempotentFrameProd
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section
namespace GlobalTheory.UnitLemma.Desc

theorem norm_prod_one {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₁) :
    Algebra.norm F ((x, 1) : R₁ × R₂) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (R₁ × R₂) (x, 1) = (Algebra.lmul F R₁ x).prodMap (Algebra.lmul F R₂ 1) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₂), map_one LinearMap.det, mul_one]

theorem norm_one_prod {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₂) :
    Algebra.norm F ((1, x) : R₁ × R₂) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (R₁ × R₂) (1, x) = (Algebra.lmul F R₁ 1).prodMap (Algebra.lmul F R₂ x) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₁), map_one LinearMap.det, one_mul]

theorem coi_prod {R₁ R₂ : Type} [Ring R₁] [Ring R₂] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {e₁ : ι₁ → R₁} {e₂ : ι₂ → R₂} (h₁ : CompleteOrthogonalIdempotents e₁)
    (h₂ : CompleteOrthogonalIdempotents e₂) :
    CompleteOrthogonalIdempotents (Sum.elim (fun i => ((e₁ i, 0) : R₁ × R₂)) (fun j => ((0, e₂ j) : R₁ × R₂))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro (i | j)
    · exact Prod.ext (h₁.idem i).eq (mul_zero 0)
    · exact Prod.ext (mul_zero 0) (h₂.idem j).eq
  · rintro (i | j) (i' | j') hne
    · have hii : i ≠ i' := fun h => hne (congrArg Sum.inl h)
      exact Prod.ext (h₁.ortho hii) (mul_zero 0)
    · exact Prod.ext (mul_zero _) (zero_mul _)
    · exact Prod.ext (zero_mul _) (mul_zero _)
    · have hjj : j ≠ j' := fun h => hne (congrArg Sum.inr h)
      exact Prod.ext (mul_zero 0) (h₂.ortho hjj)
  · rw [Fintype.sum_sum_type]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, h₁.complete]
    · simp [Prod.snd_sum, h₂.complete]

theorem factor_inl {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (e : R₁) (P Q : Prop) (hPQ : P ↔ Q)
    (h : ∃ f : R₁, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (Q → e = f ∧ σ₁ f = f) ∧ (¬Q → f * σ₁ f = 0 ∧ e = f + σ₁ f)) :
    ∃ f : R₁ × R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (P → (e, 0) = f ∧ RingEquiv.prodCongr σ₁ σ₂ f = f) ∧
      (¬P → f * RingEquiv.prodCongr σ₁ σ₂ f = 0 ∧ (e, 0) = f + RingEquiv.prodCongr σ₁ σ₂ f) := by
  obtain ⟨f, hf, hf0, hfy, hQ, hnQ⟩ := h
  refine ⟨(f, 0), Prod.ext hf.eq (mul_zero 0), fun h0 => hf0 (congrArg Prod.fst h0), ?_, ?_, ?_⟩
  · rintro ⟨y₁, y₂⟩ hy
    have hy₁ : f * y₁ ≠ 0 := fun h0 => hy (Prod.ext h0 (zero_mul y₂))
    obtain ⟨z, hz⟩ := hfy y₁ hy₁
    exact ⟨(z, 0), Prod.ext hz (mul_zero _)⟩
  · intro hP
    obtain ⟨h1, h2⟩ := hQ (hPQ.1 hP)
    refine ⟨by rw [h1], ?_⟩
    show (σ₁ f, σ₂ 0) = (f, 0)
    rw [h2, map_zero]
  · intro hP
    obtain ⟨h1, h2⟩ := hnQ (fun hq => hP (hPQ.2 hq))
    show ((f, 0) * (σ₁ f, σ₂ 0) : R₁ × R₂) = 0 ∧ (e, 0) = (f, 0) + (σ₁ f, σ₂ 0)
    rw [map_zero]
    exact ⟨Prod.ext h1 (mul_zero 0), Prod.ext h2 (add_zero 0).symm⟩

theorem factor_inr {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (e : R₂) (P Q : Prop) (hPQ : P ↔ Q)
    (h : ∃ f : R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (Q → e = f ∧ σ₂ f = f) ∧ (¬Q → f * σ₂ f = 0 ∧ e = f + σ₂ f)) :
    ∃ f : R₁ × R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (P → (0, e) = f ∧ RingEquiv.prodCongr σ₁ σ₂ f = f) ∧
      (¬P → f * RingEquiv.prodCongr σ₁ σ₂ f = 0 ∧ (0, e) = f + RingEquiv.prodCongr σ₁ σ₂ f) := by
  obtain ⟨f, hf, hf0, hfy, hQ, hnQ⟩ := h
  refine ⟨(0, f), Prod.ext (mul_zero 0) hf.eq, fun h0 => hf0 (congrArg Prod.snd h0), ?_, ?_, ?_⟩
  · rintro ⟨y₁, y₂⟩ hy
    have hy₂ : f * y₂ ≠ 0 := fun h0 => hy (Prod.ext (zero_mul y₁) h0)
    obtain ⟨z, hz⟩ := hfy y₂ hy₂
    exact ⟨(0, z), Prod.ext (mul_zero _) hz⟩
  · intro hP
    obtain ⟨h1, h2⟩ := hQ (hPQ.1 hP)
    refine ⟨by rw [h1], ?_⟩
    show (σ₁ 0, σ₂ f) = (0, f)
    rw [h2, map_zero]
  · intro hP
    obtain ⟨h1, h2⟩ := hnQ (fun hq => hP (hPQ.2 hq))
    show ((0, f) * (σ₁ 0, σ₂ f) : R₁ × R₂) = 0 ∧ (0, e) = (0, f) + (σ₁ 0, σ₂ f)
    rw [map_zero]
    exact ⟨Prod.ext (mul_zero 0) h1, Prod.ext (add_zero 0).symm h2⟩

theorem unit_inl {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₁) (hu : IsUnit x) (hσ : σ₁ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((x, 1) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (x, 1) = (x, 1)) ∧
      ((x, 1) : R₁ × R₂) * (1 - (e, 0)) = 1 - (e, 0) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨hu, isUnit_one⟩, ?_⟩, ?_⟩
  · show (σ₁ x, σ₂ 1) = (x, 1)
    rw [hσ, map_one]
  · exact Prod.ext (by simpa using h1) (by simp)

theorem unit_inr {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₂) (hu : IsUnit x) (hσ : σ₂ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((1, x) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (1, x) = (1, x)) ∧
      ((1, x) : R₁ × R₂) * (1 - (0, e)) = 1 - (0, e) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨isUnit_one, hu⟩, ?_⟩, ?_⟩
  · show (σ₁ 1, σ₂ x) = (1, x)
    rw [hσ, map_one]
  · exact Prod.ext (by simp) (by simpa using h1)

theorem isFrame_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂), IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → IsFrame (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.disjSum S₂) := by
  intro K B₁ B₂ ι₁ ι₂ _ _ e₁ π₁ e₂ π₂ S₁ S₂ h₁ h₂
  obtain ⟨⟨hc₁, hf₁⟩, hπ₁⟩ := h₁
  obtain ⟨⟨hc₂, hf₂⟩, hπ₂⟩ := h₂
  refine ⟨⟨coi_prod hc₁ hc₂, ?_⟩, ?_⟩
  · rintro (i | j)
    · exact factor_inl B₁.σ B₂.σ (e₁ i) _ _ Finset.inl_mem_disjSum (hf₁ i)
    · exact factor_inr B₁.σ B₂.σ (e₂ j) _ _ Finset.inr_mem_disjSum (hf₂ j)
  · rintro (i | j) hi
    · rw [Finset.inl_mem_disjSum] at hi
      obtain ⟨⟨hu, hσ⟩, h1, hη⟩ := hπ₁ i hi
      obtain ⟨hA, hB⟩ := unit_inl B₁.σ B₂.σ (π₁ i) (e₁ i) hu hσ h1
      refine ⟨hA, hB, ?_⟩
      show K.eta (Algebra.norm K.E ((π₁ i, 1) : B₁.A × B₂.A)) = -1
      rw [norm_prod_one]
      exact hη
    · rw [Finset.inr_mem_disjSum] at hi
      obtain ⟨⟨hu, hσ⟩, h1, hη⟩ := hπ₂ j hi
      obtain ⟨hA, hB⟩ := unit_inr B₁.σ B₂.σ (π₂ j) (e₂ j) hu hσ h1
      refine ⟨hA, hB, ?_⟩
      show K.eta (Algebra.norm K.E ((1, π₂ j) : B₁.A × B₂.A)) = -1
      rw [norm_one_prod]
      exact hη

end GlobalTheory.UnitLemma.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniformizerIdempotentFrameProdStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUniformizerIdempotentFrame_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂), IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → IsFrame (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.disjSum S₂) := by
  first | exact @GlobalTheory.UnitLemma.Desc.isFrame_prod | exact GlobalTheory.UnitLemma.Desc.isFrame_prod | (intros; apply GlobalTheory.UnitLemma.Desc.isFrame_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobFixesRootOfOneModPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobFixesRootOfOneModPlace
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem frob_fixes_root_of_one_mod (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (M : ℕ) (ζ : F) (hζ : IsPrimitiveRoot ζ M) (v : HeightOneSpectrum (𝓞 F))
    (hMv : ((M : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (A : ValuationSubring Ω) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) (σ : Formalism.ConjugateSelfDual.G F Ω)
    (hσ : Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ)
    (x : 𝓞 F) (hx : x - 1 ∈ v.asIdeal) (w : Ω) (hw : w ^ M = algebraMap F Ω (x : F)) :
    σ w = w := by
  set q := Formalism.ConjugateSelfDual.normV v
  set x' := algebraMap F Ω (x : F) with hx'
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMv
    · exact h
  haveI : NeZero M := ⟨hM0.ne'⟩
  have hx1 : A.valuation (x' - 1) < 1 := by
    have := (hA (x - 1)).2 hx
    simpa [hx'] using this
  have hMk : ¬ A.valuation (M : Ω) < 1 := by
    intro h; apply hMv; apply (hA (M : 𝓞 F)).1; simpa using h
  have hpow : ∀ y : Ω, y ^ M ∈ A → y ∈ A := by
    intro y hy
    rw [← A.valuation_le_one_iff] at hy ⊢
    rwa [map_pow, pow_le_one_iff hM0.ne'] at hy
  have hx'A : x' ∈ A := by
    have h1 : x' - 1 ∈ A := (A.valuation_le_one_iff _).1 hx1.le
    simpa using add_mem h1 A.one_mem
  have hwA : w ∈ A := hpow w (hw ▸ hx'A)
  set ζ' := algebraMap F Ω ζ with hζ'
  have hζ'p : IsPrimitiveRoot ζ' M := hζ.map_of_injective (algebraMap F Ω).injective
  have hσζ : ∀ n : ℕ, σ (ζ' ^ n) = ζ' ^ n := by
    intro n; rw [map_pow, hζ', AlgEquiv.commutes]
  have hσx : σ x' = x' := AlgEquiv.commutes σ _
  have hroot : ∀ μ : Ω, μ ^ M = 1 → μ ∈ A := fun μ h => hpow μ (h ▸ A.one_mem)
  let res := IsLocalRing.residue A
  have key : ∀ a b : A, res a = res b ↔ A.valuation ((a : Ω) - b) < 1 := by
    intro a b
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simp
  have hfrob : ∀ a : A, ∃ b : A, (b : Ω) = σ a ∧ res b = res a ^ q := by
    intro a
    have h := hσ.2 a ((A.valuation_le_one_iff _).2 a.2)
    have hb : σ (a : Ω) ∈ A := by
      have h1 : σ (a:Ω) - (a:Ω) ^ q ∈ A := (A.valuation_le_one_iff _).1 h.le
      have h2 : (a : Ω) ^ q ∈ A := A.pow_mem a.2 q
      simpa using add_mem h1 h2
    refine ⟨⟨_, hb⟩, rfl, ?_⟩
    rw [← map_pow, key]; simpa using h

  obtain ⟨μ, hμM, hμ⟩ : ∃ μ : Ω, μ ^ M = 1 ∧ A.valuation (w - μ) < 1 := by
    have hprod := congrArg (Polynomial.eval w) (X_pow_sub_one_eq_prod hM0 hζ'p)
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at hprod
    by_contra hcon
    push_neg at hcon
    have h1 : A.valuation (w ^ M - 1) = 1 := by
      rw [hprod, map_prod]
      apply Finset.prod_eq_one
      intro μ hμ
      have hμM : μ ^ M = 1 := (mem_nthRootsFinset hM0 (1 : Ω)).1 hμ
      apply le_antisymm
      · exact (A.valuation_le_one_iff _).2 (A.sub_mem hwA (hroot μ hμM))
      · exact hcon μ hμM
    rw [hw] at h1
    rw [h1] at hx1
    exact lt_irrefl _ hx1
  obtain ⟨j, -, hj⟩ := hζ'p.eq_pow_of_pow_eq_one hμM

  let aw : A := ⟨w, hwA⟩
  let aμ : A := ⟨μ, hroot μ hμM⟩
  have hwμ : res aw = res aμ := (key aw aμ).2 hμ
  obtain ⟨bw, hbw, hbw'⟩ := hfrob aw
  obtain ⟨bμ, hbμ, hbμ'⟩ := hfrob aμ
  have hbμe : bμ = aμ := by
    apply Subtype.ext
    rw [hbμ]; show σ μ = μ
    rw [← hj, hσζ]
  rw [hbμe] at hbμ'
  have hB : res bw = res aw := by
    rw [hbw', hwμ, ← hbμ']

  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0.ne'] at hw
    rw [← hw] at hx1
    simp at hx1
  have hx'0 : x' ≠ 0 := by rw [← hw]; exact pow_ne_zero _ hw0
  set ξ := σ w / w with hξ
  have hξM : ξ ^ M = 1 := by
    rw [hξ, div_pow, ← map_pow, hw, hσx, div_self hx'0]
  let aξ : A := ⟨ξ, hroot ξ hξM⟩
  have hbw_eq : bw = aξ * aw := by
    apply Subtype.ext
    show (bw : Ω) = ξ * w
    rw [hbw, hξ, div_mul_cancel₀ _ hw0]
  have hresw : res aw ≠ 0 := by
    intro h0
    have h1 : res (aw ^ M) = 0 := by rw [map_pow, h0, zero_pow hM0.ne']
    have h2 : res (aw ^ M) = res 1 := by
      rw [key]
      have : ((aw ^ M : A) : Ω) = x' := by simp [aw, hw]
      rw [this]; simpa using hx1
    rw [h1, map_one] at h2
    exact zero_ne_one h2
  have hresξ : res aξ = 1 := by
    have h := hB
    rw [hbw_eq, map_mul] at h
    exact mul_right_cancel₀ hresw (h.trans (one_mul _).symm)
  by_contra hne
  have hξ1 : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ] at h
    exact (div_eq_one_iff_eq hw0).1 h
  have hsum : ∑ l ∈ Finset.range M, ξ ^ l = 0 := by
    rw [geom_sum_eq hξ1, hξM, sub_self, zero_div]
  have hsumA : ∑ l ∈ Finset.range M, aξ ^ l = 0 := by
    apply Subtype.ext
    simpa [aξ] using hsum
  have hres : res ((M : ℕ) : A) = res 0 := by
    have := congrArg res hsumA
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_pow, hresξ, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at this
    rw [map_natCast, this]
  rw [key] at hres
  apply hMk
  simpa using hres

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobFixesRootOfOneModPlaceStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrob_fixes_root_of_one_mod_place : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (M : ℕ) (ζ : F),
    IsPrimitiveRoot ζ M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
    ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G F Ω, Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ →
    ∀ x : 𝓞 F, x - 1 ∈ v.asIdeal → ∀ w : Ω, w ^ M = algebraMap F Ω (x : F) → σ w = w := by
  first | exact @GlobalTheory.frob_fixes_root_of_one_mod | exact GlobalTheory.frob_fixes_root_of_one_mod | (intros; apply GlobalTheory.frob_fixes_root_of_one_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthonormalIffUnitary
open GlobalTheory.UnitLemma Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.UnitLemma.BaseChange

variable {K : UQ} (B : InvAlg K)

theorem herm_sum_left {ι : Type} (s : Finset ι) (x : B.A) (f : ι → B.A) (z : B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right {ι : Type} (s : Finset ι) (x y : B.A) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_basis_change (x : B.A) {n : ℕ} (e e' : Module.Basis (Fin n) K.E B.A)
    (he : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (i j : Fin n) :
    B.herm x (e' i) (e' j) = ∑ k, e.toMatrix e' k i * K.c (e.toMatrix e' k j) := by
  have hi := e.sum_toMatrix_smul_self e' i
  have hj := e.sum_toMatrix_smul_self e' j
  rw [← hi, ← hj, herm_sum_left]
  simp_rw [herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, he]
  simp [mul_ite, Finset.sum_ite_eq]

theorem orthonormal_iff_unitary : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (n : ℕ) (e e' : Module.Basis (Fin n) K.E B.A),
    (∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) →
    ((∀ i j, B.herm x (e' i) (e' j) = if i = j then 1 else 0) ↔ ((e.toMatrix e').map K.c)ᵀ * e.toMatrix e' = 1) := by
  intro K B x n e e' he
  have key := herm_basis_change B x e e' he
  have hm : ∀ i j, (((e.toMatrix e').map K.c)ᵀ * e.toMatrix e') j i = B.herm x (e' i) (e' j) := by
    intro i j
    rw [key, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  constructor
  · intro h'
    ext j i
    rw [hm, h', Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · intro hu i j
    rw [← hm, hu, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

end GlobalTheory.UnitLemma.BaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityLaurentShiftEqSumSen
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityLaurentShiftEqSumSen
noncomputable section
namespace GlobalTheory.PhiGam.Range
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem finite_map_trans {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P Q S : Submodule k U}
    (hSQ : S ≤ Q) (h1 : FiniteDimensional k (P.map Q.mkQ)) (h2 : FiniteDimensional k (Q.map S.mkQ)) :
    FiniteDimensional k (P.map S.mkQ) := by
  refine Module.Finite.iff_fg.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor hSQ) ?_ ?_)
  · rw [← Submodule.map_comp, Submodule.factor_comp_mk]
    exact Module.Finite.iff_fg.mp h1
  · have hle : P.map S.mkQ ⊓ LinearMap.ker (Submodule.factor hSQ) ≤ Q.map S.mkQ := by
      rintro _ ⟨⟨p, -, rfl⟩, hp⟩
      exact ⟨p, (Submodule.Quotient.mk_eq_zero Q).mp hp, rfl⟩
    exact Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hle)

theorem finite_quot_of_map {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P S : Submodule k U}
    (h : FiniteDimensional k (P.map S.mkQ)) : FiniteDimensional k (↥P ⧸ S.submoduleOf P) := by
  have hker : LinearMap.ker (S.mkQ ∘ₗ P.subtype) = S.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hr : LinearMap.range (S.mkQ ∘ₗ P.subtype) = P.map S.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  haveI : FiniteDimensional k (LinearMap.range (S.mkQ ∘ₗ P.subtype)) := by rw [hr]; exact h
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_self {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  set P' := P ⊓ ⨆ m : ℕ, P.comap ((T - algebraMap k (Module.End k U) x) ^ m)
  have h : P.submoduleOf P' = ⊤ := eq_top_iff.mpr fun y _ => y.2.1
  haveI : Subsingleton (↥P' ⧸ P.submoduleOf P') := Submodule.Quotient.subsingleton_iff.mpr h
  exact Module.finrank_zero_of_subsingleton

theorem finite_sh {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    {N : Submodule k⟦X⟧ V} (hN : IsLat N) (a : ℤ) (m : ℕ) :
    FiniteDimensional k (((sh a N).restrictScalars k).map ((sh (a + m) N).restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Submodule.mkQ_map_self]
    infer_instance
  | succ m ih =>
    have h := Window.finite_quot (hN.shift (a + m)).1
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h
    rw [Nat.cast_succ, ← add_assoc]
    exact finite_map_trans (fun y hy => Window.sh_succ_le _ _ hy) ih h

theorem qmult_sh_range : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ) (x : k), qmult g (sh a N) (sh (a + m) N) x = ∑ j ∈ Finset.range m, sen g N (x + (a + j : ℤ)) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m x
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Finset.sum_range_zero]
    exact gmult_self _ _ _
  | succ m ih =>
    have hf := finite_quot_of_map (finite_sh hN a (m + 1))
    rw [Finset.sum_range_succ, ← ih, ← GlobalTheory.T.senMultiplicity_shift_lattice_variablePow R g hg N hN hC (a + m) x, sen, sh_sh_eq,
      add_comm (1 : ℤ)]
    rw [Nat.cast_succ, ← add_assoc] at hf ⊢
    exact GlobalTheory.T.genEigenMultiplicityQuotient_additive_chain (nab g) _ _ _ (fun y hy => Window.sh_succ_le _ _ hy)
      (fun y hy => Window.sh_add_le a m N hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy)
      (fun y hy => Window.nab_mem_sh R hg hC _ hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy) hf x

end GlobalTheory.PhiGam.Range
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityLaurentShiftEqSumSenStatement
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ) (x : k), qmult g (sh a N) (sh (a + m) N) x = ∑ j ∈ Finset.range m, sen g N (x + (a + j : ℤ)) := by
  first | exact @GlobalTheory.PhiGam.Range.qmult_sh_range | exact GlobalTheory.PhiGam.Range.qmult_sh_range | (intros; apply GlobalTheory.PhiGam.Range.qmult_sh_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftWithLastBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftWithLastBasis
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.MatchNotIm

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

theorem full_act (g : GL (Fin r) k) (Y : Gl r k) :
    full (act g Y) = embHom r k (g : Matrix (Fin r) (Fin r) k) * full Y *
      embHom r k ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  simp only [full, act, embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  congr 1
  all_goals (ext i j; simp [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct])

theorem last_eq : (Fin.last r) = finSumFinEquiv (Sum.inr (0 : Fin 1)) := by
  ext; simp

theorem embHom_last_row (g : Matrix (Fin r) (Fin r) k) (j : Fin (r + 1)) :
    embHom r k g (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim j 0]; simp [embHom, Matrix.reindex_apply]

theorem embHom_last_col (g : Matrix (Fin r) (Fin r) k) (i : Fin (r + 1)) :
    embHom r k g i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim i 0]; simp [embHom, Matrix.reindex_apply]

theorem conj_last (g g' : Matrix (Fin r) (Fin r) k) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    (embHom r k g * N * embHom r k g') (Fin.last r) (Fin.last r) = N (Fin.last r) (Fin.last r) := by
  simp [Matrix.mul_apply, embHom_last_row, embHom_last_col]

theorem eL_dot (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    eL r k ⬝ᵥ (N *ᵥ eL r k) = N (Fin.last r) (Fin.last r) := by
  simp [eL, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem full_glMap {k' : Type} [CommRing k'] (φ : k →+* k') (Y : Gl r k) :
    full (glMap φ Y) = (full Y).map φ := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [full, glMap, Matrix.reindex_apply]

end Alg

end GlobalTheory.JR.Step.MatchNotIm

namespace GlobalTheory.JR.Step.MatchNotIm

theorem conj_pow {n : Type} [Fintype n] [DecidableEq n] {k : Type} [CommRing k] (P Q N : Matrix n n k)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (i : ℕ) : (P * N * Q) ^ i = P * N ^ i * Q := by
  induction i with
  | zero => simp [hPQ]
  | succ i ih =>
    rw [pow_succ, ih, pow_succ]
    calc P * N ^ i * Q * (P * N * Q) = P * N ^ i * (Q * P) * N * Q := by simp only [Matrix.mul_assoc]
      _ = P * (N ^ i * N) * Q := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P]

theorem hasInv_liftH : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E),
    ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 →
    HasInv X (inv Z) → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) := by
  intro F E _ _ _ _ _ r Z X μ l ν hν _ _ hΔ hX
  have hΔ' : Delta (inv (glMap (algebraMap F E) Z)) ≠ 0 := by
    rw [InvMap.inv_glMap, InvMap.Delta_map]
    exact (map_ne_zero (algebraMap F E)).2 hΔ
  have hX' : inv X.toGl = inv (glMap (algebraMap F E) Z) := by
    rw [InvMap.inv_glMap]; exact hX
  obtain ⟨g, ⟨hg, -⟩, -⟩ := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E r).2.2.2.2 _ _ hΔ' hX'
  have hfull : full X.toGl = embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
    rw [← hg, full_act, full_glMap]
  have hPQ : embHom r E (g : Matrix (Fin r) (Fin r) E) * embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hQP : embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * embHom r E (g : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hs : star (ν • eL r E) = star ν • eL r E := by
    funext j
    simp only [Pi.star_apply, Pi.smul_apply, eL, Pi.single_apply, smul_eq_mul, star_mul']
    split_ifs <;> simp [mul_comm]
  replace hfull : full ((X.1.1, X.2.1, star X.2.1, algebraMap F E X.2.2) : Gl r E) =
      embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := hfull
  unfold HasInv
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift]
    rw [hfull]
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift, mom]
    rw [hs, hfull, conj_pow _ _ _ hPQ hQP, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, eL_dot, eL_dot, conj_last]
    have hp : ((full Z).map (algebraMap F E)) ^ (i : ℕ) = ((full Z) ^ (i : ℕ)).map (algebraMap F E) := by
      have := map_pow (algebraMap F E).mapMatrix (full Z) (i : ℕ)
      simpa only [RingHom.mapMatrix_apply] using this.symm
    rw [hp, Matrix.map_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, ← hν]
    ring

end GlobalTheory.JR.Step.MatchNotIm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftWithLastBasisStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianBlock_hasInvariants_of_liftWithLastBasis : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E), ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 → HasInv X (inv Z) → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) := by
  first | exact @GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH | exact GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH | (intros; apply GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH <;> assumption)
end
end
