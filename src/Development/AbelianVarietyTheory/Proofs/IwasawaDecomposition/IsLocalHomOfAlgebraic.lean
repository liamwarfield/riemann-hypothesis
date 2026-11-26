module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.CoordUniq

section Lin

variable {K : Type} [Field K] {m n : ℕ}

theorem tri_of_mul {T₁ T₂ M : Fin m → Fin m → K} (h₁ : ∀ i k, i < k → T₁ i k = 0) (h₂ : ∀ i k, i < k → T₂ i k = 0)
    (hd : ∀ i, T₂ i i ≠ 0) (h : ∀ i k, T₁ i k = ∑ j, T₂ i j * M j k) (i : Fin m) : ∀ k, i < k → M i k = 0 := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro k hk
    have e := h i k
    rw [h₁ i k hk, Finset.sum_eq_single i (fun j _ hj => by
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [ih j hj k (hj.trans hk), mul_zero]
      · rw [h₂ i j hj, zero_mul]) (by simp)] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (hd i)

theorem diag_of_mul {T₂ M : Fin m → Fin m → K} (h₂ : ∀ i k, i < k → T₂ i k = 0) (hM : ∀ i k, i < k → M i k = 0)
    (i : Fin m) : ∑ j, T₂ i j * M j i = T₂ i i * M i i :=
  Finset.sum_eq_single i (fun j _ hj => by
    rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hM j i hj, mul_zero]
    · rw [h₂ i j hj, zero_mul]) (by simp)

theorem indep_of_tri {T : Fin m → Fin m → K} (h : ∀ i k, i < k → T i k = 0) (hd : ∀ i, T i i ≠ 0)
    {e : Fin m → Fin n → K} (hg : ∀ a : Fin m → K, ∑ i, a i • ∑ j, T i j • e j = 0 → a = 0)
    {b : Fin m → K} (hb : ∑ j, b j • e j = 0) : b = 0 := by
  have hdet : IsUnit (Matrix.of T).det := by
    rw [Matrix.det_of_isLowerTriangular (Matrix.of T) (fun i k hk => h i k hk)]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have e1 : Matrix.vecMul (Matrix.vecMul b (Matrix.of T)⁻¹) (Matrix.of T) = b := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  have e2 := hg (Matrix.vecMul b (Matrix.of T)⁻¹) (by
    rw [← hb]
    conv_rhs => rw [← e1]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    rfl)
  rw [← e1, e2, Matrix.zero_vecMul]

end Lin

section Frames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_matrix {R : Type} [CommRing R] [IsLocalRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ f₂ : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ M : Fin (Dw.mult τ) → Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∃ T₁ T₂ : Fin (Dw.mult τ) → Fin (Dw.mult τ) → k,
        (∀ i, T₁ i i = t₁ τ i) ∧ (∀ i, T₂ i i = t₂ τ i) ∧ (∀ i k, i < k → T₁ i k = 0) ∧ (∀ i k, i < k → T₂ i k = 0) ∧
          ∀ i k, T₁ i k = ∑ j, T₂ i j * ψ (M j k) := by
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan τ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan τ i)
  choose M hM using fun i => (f₁.basis τ _ (f₂.tan τ i) (f₂.eig τ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v τ = fun j => vec Z.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  refine ⟨M, fun {k} _ ψ φ' x' g t₁ t₂ h₁ h₂ => ?_⟩
  obtain ⟨rfl, rfl, h₁⟩ := h₁
  obtain ⟨-, -, h₂⟩ := h₂
  choose T₁ a₁ b₁ c₁ using h₁ τ
  choose T₂ a₂ b₂ c₂ using h₂ τ
  letI : Algebra R k := ψ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  change ∀ cc, vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec Z.t x xc cc at hv
  choose G hG using fun i => vec_exists hx' _ (g.tan τ i)
  have d₁ : ∀ i, G i = ∑ j, T₁ i j • (ψ ∘ e₁ j) := fun i => by
    have := c₁ i
    simp only [he₁, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have d₂ : ∀ i, G i = ∑ j, T₂ i j • (ψ ∘ e₂ j) := fun i => by
    have := c₂ i
    simp only [he₂, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have hind : ∀ a : Fin (Dw.mult τ) → k, ∑ i, a i • G i = 0 → a = 0 := fun a ha => by
    have hb := g.basis τ _ (vec_tan hx' 0) ((vec_eig_iff hx' _ _).2 (Submodule.zero_mem _))
    rw [show g.v τ = fun j => vec Z.t _ xc' (G j) from funext hG] at hb
    exact hb.unique ((comb_iff hx' _ _ _).2 ha.symm) ((comb_iff hx' _ _ _).2 (by simp))
  refine ⟨T₁, T₂, a₁, a₂, b₁, b₂, fun i k' => ?_⟩
  have := indep_of_tri b₁ (fun i => a₁ i ▸ (t₁ τ i).ne_zero) (e := fun j => ψ ∘ e₁ j)
    (fun a ha => hind a (by simpa only [d₁] using ha))
    (b := fun k' => T₁ i k' - ∑ j, T₂ i j * ψ (M j k')) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← d₁, d₂, sub_eq_zero]
      funext q
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hM', Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul,
        Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm)
  exact sub_eq_zero.1 (congrFun this k')

theorem exists_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, (t₁ τ i : k) = t₂ τ i * ψ (u τ i) := by
  obtain rfl : φ₁ = φ₂ := RingHom.ext fun a => hι ((RingHom.congr_fun h₁.2.1 a).symm.trans (RingHom.congr_fun h₂.2.1 a))
  choose M hM using exists_matrix f₁ f₂
  have hT : ∀ τ i k, i < k → M τ i k = 0 := fun τ i k hk => by
    obtain ⟨T₁, T₂, -, a₂, b₁, b₂, h⟩ := hM τ ι f₀ t₁ t₂ h₁ h₂
    exact hι ((tri_of_mul (M := fun i k => ι (M τ i k)) b₁ b₂ (fun i => a₂ i ▸ (t₂ τ i).ne_zero) h i k hk).trans
      (map_zero ι).symm)
  refine ⟨fun τ i => M τ i i, fun {k} _ ψ φ' x' g s₁ s₂ g₁ g₂ τ i => ?_⟩
  obtain ⟨T₁, T₂, a₁, a₂, -, b₂, h⟩ := hM τ ψ g s₁ s₂ g₁ g₂
  rw [← a₁, ← a₂, h]
  exact diag_of_mul (M := fun i k => ψ (M τ i k)) b₂ (fun i k hk => by simp only [hT τ i k hk, map_zero]) i

theorem exists_unit_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Rˣ, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, t₁ τ i = t₂ τ i * Units.map (ψ : R →* k) (u τ i) := by
  obtain ⟨u, hu⟩ := exists_ratio f₁ f₂ hι h₁ h₂
  obtain ⟨v, hv⟩ := exists_ratio f₂ f₁ hι h₂ h₁
  have huv : ∀ τ i, u τ i * v τ i = 1 := fun τ i => hι (by
    have a := hu ι f₀ _ _ h₁ h₂ τ i
    have b := hv ι f₀ _ _ h₂ h₁ τ i
    rw [a, mul_assoc] at b
    rw [map_mul, map_one]
    exact (mul_left_cancel₀ (t₂ τ i).ne_zero ((mul_one _).trans b)).symm)
  exact ⟨fun τ i => Units.mkOfMulEqOne _ _ (huv τ i), fun ψ _ _ g s₁ s₂ g₁ g₂ τ i =>
    Units.ext (hu ψ g s₁ s₂ g₁ g₂ τ i)⟩

end Frames

theorem isLocalHom_of_algebraic {R F k : Type} [CommRing R] [IsLocalRing R] [Field F] [CharZero F] (φ : F →+* R)
    [Field k] [CharZero k] [Algebra.IsAlgebraic ℚ k] (ψ : R →+* k) : IsLocalHom ψ := by
  letI : Algebra ℚ R := (φ.comp (algebraMap ℚ F)).toAlgebra
  let ψ' : R →ₐ[ℚ] k := { ψ with commutes' := fun q => by simp }
  refine ⟨fun a ha => ?_⟩
  have h0 : ψ a ≠ 0 := ha.ne_zero
  have hi : IsIntegral ℚ (ψ a) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  have hc := minpoly.coeff_zero_ne_zero hi h0
  have h1 : ψ (Polynomial.aeval a (minpoly ℚ (ψ a))) = 0 :=
    (Polynomial.aeval_algHom_apply ψ' a _).symm.trans (minpoly.aeval ℚ (ψ a))
  have h2 : ¬ IsUnit (Polynomial.aeval a (minpoly ℚ (ψ a))) := fun h => (h.map ψ).ne_zero h1
  by_contra hna
  rw [← Polynomial.X_mul_divX_add (minpoly ℚ (ψ a)), map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  have h3 : algebraMap ℚ R ((minpoly ℚ (ψ a)).coeff 0) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem (IsLocalRing.maximalIdeal R) h2
      (Ideal.mul_mem_right (Polynomial.aeval a (minpoly ℚ (ψ a)).divX) _ hna)
    rwa [add_sub_cancel_left] at this
  exact h3 (hc.isUnit.map _)

theorem stalk_ext {X : Scheme.{0}} {k : Type} [Field k] {y y' : X} {ψ : X.presheaf.stalk y →+* k}
    {ψ' : X.presheaf.stalk y' →+* k} (h : IsLocalHom ψ) (h' : IsLocalHom ψ')
    (e : spMap ψ ≫ X.fromSpecStalk y = spMap ψ' ≫ X.fromSpecStalk y') : y = y' ∧ HEq ψ ψ' := by
  have := (SpecToEquivOfLocalRing X (.of k)).symm.injective (a₁ := ⟨y, CommRingCat.ofHom ψ, h⟩)
    (a₂ := ⟨y', CommRingCat.ofHom ψ', h'⟩) e
  obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 this
  exact ⟨rfl, heq_of_eq (congrArg (fun f => f.1.hom) (eq_of_heq e'))⟩

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {σ : Y.Y.Fn}

end Coord

end GlobalTheory.ShFam.CoordUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDisc
noncomputable section

namespace GlobalTheory.RelExp

section General

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology GlobalTheory.TangentOrigin GlobalTheory.RelChart

private theorem etale_chart_lemma : ∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x := by
  exact fun m g A R _ _ ψ B φ b₀ e a a_1 a_2 a_3 a_4 =>
    EtaleFamily.exists_holomorphic_sections m g A R ψ B φ b₀ e a a_1 a_2 a_3 a_4

private theorem exists_open_smoothOfRelativeDimension : ∀ (Z X : Scheme.{0}) (p : Z ⟶ X) [Smooth p] (z : Z), ∃ (g : ℕ) (W : Z.Opens), z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ p) := by
  intro Z X p _ z
  exact H1.exists_dim p z

private theorem chart_lemma_4 : ∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v' :=
  GlobalTheory.RelChart.exists_chart_with_parameters etale_chart_lemma

private theorem valAt'_presheaf_map_eqToHom {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V V' : Y.Opens} (h : V = V')
    (s : Γ(Y, V')) : valAt' x V ((Y.presheaf.map (eqToHom h).op).hom s) = valAt' x V' s := by
  subst h
  simp

private theorem evalPt_eqToHom {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) {V V' : Y.Opens} (h : V = V')
    (hV : ⊤ ≤ v ⁻¹ᵁ V) (hV' : ⊤ ≤ v ⁻¹ᵁ V') (s : Γ(Y, V')) :
    GlobalTheory.TangentOrigin.evalPt v V hV ((Y.presheaf.map (eqToHom h).op).hom s) =
      GlobalTheory.TangentOrigin.evalPt v V' hV' s := by
  subst h
  simp

private theorem app_appIso_inv_eq_presheaf_map {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) (s : Γ(W, U')) :
    (W.ι.app (W.ι ''ᵁ U')).hom ((W.ι.appIso U').inv.hom s) =
      ((W : Scheme.{0}).presheaf.map (eqToHom (W.ι.preimage_image_eq U')).op).hom s := by
  rw [← Scheme.Hom.appIso_inv_app]
  rfl

private theorem valAt'_ι_appIso_inv {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) (x : Sp ℂ ⟶ W)
    (s : Γ(W, U')) : valAt' (x ≫ W.ι) (W.ι ''ᵁ U') ((W.ι.appIso U').inv.hom s) = valAt' x U' s := by
  rw [GlobalTheory.PointUnif.valAt'_comp, app_appIso_inv_eq_presheaf_map, valAt'_presheaf_map_eqToHom]

private theorem preimage_comp_ι_image_eq_preimage {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) {R : Type}
    [CommRing R] (x : Sp R ⟶ W) : (x ≫ W.ι) ⁻¹ᵁ (W.ι ''ᵁ U') = x ⁻¹ᵁ U' := by
  show x ⁻¹ᵁ (W.ι ⁻¹ᵁ (W.ι ''ᵁ U')) = x ⁻¹ᵁ U'
  rw [Scheme.Hom.preimage_image_eq]

private theorem evalPt_ι_appIso_inv {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens)
    (v : Sp (DualNumber ℂ) ⟶ W) (h : ⊤ ≤ (v ≫ W.ι) ⁻¹ᵁ (W.ι ''ᵁ U')) (h' : ⊤ ≤ v ⁻¹ᵁ U') (s : Γ(W, U')) :
    GlobalTheory.TangentOrigin.evalPt (v ≫ W.ι) (W.ι ''ᵁ U') h ((W.ι.appIso U').inv.hom s) =
      GlobalTheory.TangentOrigin.evalPt v U' h' s := by
  rw [GlobalTheory.PointUnif.evalPt_comp, app_appIso_inv_eq_presheaf_map]
  exact evalPt_eqToHom v (W.ι.preimage_image_eq U') h h' s

private theorem exists_lift_through_opens_ι {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) {R : Type}
    [CommRing R] (x : Sp R ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ (W.ι ''ᵁ U')) : ∃ x' : Sp R ⟶ W, x' ≫ W.ι = x := by
  refine ⟨IsOpenImmersion.lift W.ι x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, -, hb⟩ := hx (show a ∈ (⊤ : (Sp R).Opens) from trivial)
  exact ⟨b, hb⟩

theorem exists_chart_of_smooth (m : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ))
    (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z) [Smooth p] (hB : IsOpen B) (hb₀ : b₀ ∈ B)
    (hy : IsHolTo B y) (hz₀ : z₀ ≫ p = y b₀) :
    ∃ (g : ℕ) (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v' := by
  obtain ⟨g, W, hzW, hWsm⟩ := exists_open_smoothOfRelativeDimension Z X p (z₀.base default)
  have hz₀W : Set.range z₀.base ⊆ Set.range W.ι.base := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default, Scheme.Opens.range_ι]
    exact hzW
  obtain ⟨z₀', rfl⟩ : ∃ z₀' : Sp ℂ ⟶ W, z₀' ≫ W.ι = z₀ := ⟨_, IsOpenImmersion.lift_fac _ _ hz₀W⟩
  obtain ⟨U', t', n, f', N, O, σ', hN, hO, hU', hO', hσ', hσN', hinv', hun'⟩ :=
    chart_lemma_4 m g W X (W.ι ≫ p) B y b₀ z₀' hWsm hB hb₀ hy (by rw [← Category.assoc]; exact hz₀)
  refine ⟨g, W.ι ''ᵁ U', fun i => (W.ι.appIso U').inv.hom (t' i), n, fun j => (W.ι.appIso U').inv.hom (f' j), N, O,
    fun q => σ' q ≫ W.ι, hN, hO, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [preimage_comp_ι_image_eq_preimage]
    exact hU'
  · simp only [valAt'_ι_appIso_inv]
    exact hO'
  · exact isHolTo_of_holAt hN fun q hq => HolAt.post ⟨N, hN, hq, hσ'⟩ W.ι
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hσN' q hq
    refine ⟨by rw [Category.assoc]; exact h1, by rw [preimage_comp_ι_image_eq_preimage]; exact h2, fun i => ?_⟩
    rw [valAt'_ι_appIso_inv]
    exact h3 i
  · intro b x hxp hxU hxO
    obtain ⟨x', rfl⟩ := exists_lift_through_opens_ι W U' x hxU
    rw [preimage_comp_ι_image_eq_preimage] at hxU
    simp only [valAt'_ι_appIso_inv] at hxO ⊢
    obtain ⟨h1, h2⟩ := hinv' b x' (by rw [← Category.assoc]; exact hxp) hxU hxO
    exact ⟨h1, by rw [h2]⟩
  · intro v v' hv hv' hp h0 he
    obtain ⟨w, rfl⟩ := exists_lift_through_opens_ι W U' v hv
    obtain ⟨w', rfl⟩ := exists_lift_through_opens_ι W U' v' hv'
    have hw : ⊤ ≤ w ⁻¹ᵁ U' := by rw [← preimage_comp_ι_image_eq_preimage W U' w]; exact hv
    have hw' : ⊤ ≤ w' ⁻¹ᵁ U' := by rw [← preimage_comp_ι_image_eq_preimage W U' w']; exact hv'
    have hp' : w ≫ W.ι ≫ p = w' ≫ W.ι ≫ p := by simpa only [Category.assoc] using hp
    have h0' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ w = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ w' :=
      (cancel_mono W.ι).mp (by simpa only [Category.assoc] using h0)
    have he' : ∀ i, GlobalTheory.TangentOrigin.evalPt w U' hw (t' i) = GlobalTheory.TangentOrigin.evalPt w' U' hw' (t' i) := by
      intro i
      rw [← evalPt_ι_appIso_inv W U' w hv hw, ← evalPt_ι_appIso_inv W U' w' hv' hw']
      exact he i
    rw [hun' w w' hw hw' hp' h0' he']

theorem exists_relative_exp_of_smooth (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (m : ℕ)
    (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (hsm : Smooth G.hom)
    (hcon : GeometricallyConnected G.hom) (hB : IsOpen B) (hb₀ : b₀ ∈ B) (hy : IsHolTo B y) :
    ∃ (g : ℕ) (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)), IsOpen B' ∧ b₀ ∈ B' ∧
      (∀ b ∈ B', (∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (b, z)) ∧
        (∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧
        IsHolTo Set.univ (fun z => pt ((e b) z)) ∧
        (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧
        (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left →
          ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧
      ∀ z₀, e b₀ z₀ = 1 → ∃ ζ : (Fin m → ℂ) → (Fin g → ℂ), ζ b₀ = z₀ ∧ AnalyticAt ℂ ζ b₀ ∧
        ∀ᶠ b in 𝓝 b₀, e b (ζ b) = 1 := by
  haveI := hsm
  have hy' : HolAt y b₀ := ⟨B, hB, hb₀, hy⟩
  obtain ⟨g, U, t, n, f, N, O, σ, hN, hO, hU, hO₀, hσ, hσN, hinv, hun⟩ :=
    exists_chart_of_smooth m G.left X G.hom B y b₀ (1 : Over.mk (y b₀) ⟶ G).left hB hb₀ hy
      (Over.w (1 : Over.mk (y b₀) ⟶ G))
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_centred_chart (G := G) (t := t) (f := f) hy' hN hU hO₀ hσ hσN hinv
  obtain ⟨B', e, r, Q, L, hB'o, hb₀', -, -, hQ, hadd, hprop, hinv'⟩ :=
    exists_global_exp (G := G) (t := t) (f := f) GlobalTheory.exists_param_exp_log_pi (hB.mem_nhds hb₀) hy' hO hU hO₀
      hs1 hs2 hs3
  refine ⟨g, B', e, hB'o, hb₀', fun b hb => ?_, fun z₀ hz₀ => ?_⟩
  · obtain ⟨hhol, hU1, hO1, hQ1, hder, -, -, -⟩ := hprop b hb
    have he0 : e b 0 = 1 := by
      have h := hadd b 0 0
      rw [add_zero] at h
      exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
    have hhol' : IsHolTo Set.univ (fun z => pt (e b z)) :=
      isHolTo_of_holAt isOpen_univ fun z _ =>
        (hhol z).comp (φ := fun v : Fin g → ℂ => (b, v)) (analyticAt_const.prod analyticAt_id)
    obtain ⟨ht1, ht2⟩ := GlobalTheory.vertical_derivative_in_coordinates X G (y b) g (e b) hhol'
    have hU0 : ⊤ ≤ (show Sp ℂ ⟶ G.left from (e b 0).left) ⁻¹ᵁ U := by
      rw [he0]
      exact hU1
    have hfd : fderiv ℂ (fun z i => valAt' (e b z).left U (t i)) 0 = ContinuousLinearMap.id ℂ (Fin g → ℂ) :=
      hder.fderiv
    have hinj : Function.Injective (fderiv ℂ (fun z i => valAt' (e b z).left U (t i)) 0) := by
      rw [hfd]
      intro a a' h
      simpa using h
    let φ : Multiplicative (Fin g → ℂ) →* (Over.mk (y b) ⟶ G) :=
      { toFun := fun z => e b (Multiplicative.toAdd z)
        map_one' := he0
        map_mul' := fun z w => hadd b _ _ }
    have hH : φ.range = ⊤ := by
      refine GlobalTheory.OpenSubgroupPts.subgroup_eq_top_of_nhds_one X G (y b) φ.range U (Fin n ⊕ Fin g) (Sum.elim f t)
        {c | (b, fun j => c (Sum.inl j)) ∈ O ∧
          (b, (fun i => c (Sum.inr i)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) ∈ Q} hsm hcon ?_ hU1 ?_ ?_
      · exact (hO.preimage (by fun_prop)).inter (hQ.preimage (by fun_prop))
      · refine ⟨hO1, ?_⟩
        show (b, crd U t (pt (1 : Over.mk (y b) ⟶ G)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) ∈ Q
        rw [sub_self]
        exact hQ1
      · intro a ha1 ha2
        exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (L (b, crd0 t a)), hinv' b a ha1 ha2.1 ha2.2⟩
    have hsurj : Function.Surjective (e b) := by
      intro a
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp (hH ▸ Subgroup.mem_top a)
      exact ⟨Multiplicative.toAdd z, hz⟩
    exact ⟨hhol, hadd b, hsurj, hhol', ht1, (ht2 U t hU0 hun).mpr hinj⟩
  · obtain ⟨hhol, hU1, hO1, hQ1, -, hL0, hL, -⟩ := hprop b₀ hb₀'
    exact exists_lift (G := G) (y := y) (U := U) (t := t) (f := f) (O := O) (e := e) (Q := Q) (L := L)
      (β := fun w => w) (x := fun w => (1 : Over.mk (y w) ⟶ G)) (w₀ := b₀) (z₀ := z₀)
      hO hQ hadd hinv' analyticAt_id (HolAt.one hy') hz₀ (hhol z₀) hU1 hO1 hQ1 hL0 hL

end General

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

theorem exists_exp_along_disc : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : ℂ → (Sp ℂ ⟶ X)) (r : ℝ), IsSemiAbelian G → 0 < r → IsHolTo (Metric.ball (0 : ℂ) r) y → ∃ (g : ℕ) (ρ : ℝ) (e : ∀ u, (Fin g → ℂ) → (Over.mk (y u) ⟶ G)), 0 < ρ ∧ ρ ≤ r ∧ IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g → ℂ) => (show Sp ℂ ⟶ G.left from (e q.1 q.2).left)) ∧ (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e u (z + w) = e u z * e u w) ∧ Function.Surjective (e u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e u z).left)) ∧ (∀ w, ∃! v : epsPt (y u) ⟶ G, IsDerivAt0 (fun z => (e u z).left) w v.left) ∧ (∀ v : epsPt (y u) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e u 0).left → ∃! w, IsDerivAt0 (fun z => (e u z).left) w v.left)) ∧ ∀ z₀, e 0 z₀ = 1 → ∃ ζ : ℂ → (Fin g → ℂ), ζ 0 = z₀ ∧ AnalyticAt ℂ ζ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), e u (ζ u) = 1 := by
  intro X G _ y r hG hr hy
  haveI := hG.comm
  let c : ℂ → (Fin 1 → ℂ) := fun u _ => u
  have hcA : ∀ u, AnalyticAt ℂ c u := fun u =>
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℂ ℂ).analyticAt u
  let y' : (Fin 1 → ℂ) → (Sp ℂ ⟶ X) := fun b => y (b 0)
  let B : Set (Fin 1 → ℂ) := (fun b : Fin 1 → ℂ => b 0) ⁻¹' Metric.ball 0 r
  have hBo : IsOpen B := Metric.isOpen_ball.preimage (continuous_apply 0)
  have hb0 : (0 : Fin 1 → ℂ) ∈ B := by
    show (0 : ℂ) ∈ Metric.ball (0 : ℂ) r
    exact Metric.mem_ball_self hr
  have hy' : IsHolTo B y' := isHolTo_of_holAt hBo fun b hb =>
    HolAt.comp (a := y) (φ := fun b : Fin 1 → ℂ => b 0) ⟨_, Metric.isOpen_ball, hb, hy⟩
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt b)
  obtain ⟨g, B', e', hB'o, hb0', hprop, hfin⟩ :=
    exists_relative_exp_of_smooth X G 1 B y' 0 hG.smooth hG.geomConnected hBo hb0 hy'
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hB'o 0 hb0'
  have hcB : ∀ u ∈ Metric.ball (0 : ℂ) (min ε r), c u ∈ B' := by
    intro u hu
    apply hεB
    rw [Metric.mem_ball, dist_zero_right]
    show ‖(fun _ : Fin 1 => u)‖ < ε
    rw [pi_norm_const]
    rw [Metric.mem_ball, dist_zero_right] at hu
    exact lt_of_lt_of_le hu (min_le_left _ _)
  refine ⟨g, min ε r, fun u => e' (c u), lt_min hε hr, min_le_right _ _, ?_, fun u hu => (hprop (c u) (hcB u hu)).2, ?_⟩
  · refine isHolTo_of_holAt (Metric.isOpen_ball.prod isOpen_univ) fun q hq => ?_
    exact ((hprop (c q.1) (hcB q.1 hq.1)).1 q.2).comp (φ := fun q : ℂ × (Fin g → ℂ) => (c q.1, q.2))
      (((ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.fst ℂ ℂ (Fin g → ℂ)).prod
        (ContinuousLinearMap.snd ℂ ℂ (Fin g → ℂ))).analyticAt q)
  · intro z₀ hz₀
    obtain ⟨ζ, h1, h2, h3⟩ := hfin z₀ hz₀
    exact ⟨fun u => ζ (c u), h1, AnalyticAt.comp (f := c) (x := (0 : ℂ)) h2 (hcA 0), (hcA 0).continuousAt.tendsto.eventually h3⟩

end GlobalTheory.RelExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDiscStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semi_abelian_exponential_along_disc : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : ℂ → (Sp ℂ ⟶ X)) (r : ℝ), IsSemiAbelian G → 0 < r → IsHolTo (Metric.ball (0 : ℂ) r) y → ∃ (g : ℕ) (ρ : ℝ) (e : ∀ u, (Fin g → ℂ) → (Over.mk (y u) ⟶ G)), 0 < ρ ∧ ρ ≤ r ∧ IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g → ℂ) => (show Sp ℂ ⟶ G.left from (e q.1 q.2).left)) ∧ (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e u (z + w) = e u z * e u w) ∧ Function.Surjective (e u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e u z).left)) ∧ (∀ w, ∃! v : epsPt (y u) ⟶ G, IsDerivAt0 (fun z => (e u z).left) w v.left) ∧ (∀ v : epsPt (y u) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e u 0).left → ∃! w, IsDerivAt0 (fun z => (e u z).left) w v.left)) ∧ ∀ z₀, e 0 z₀ = 1 → ∃ ζ : ℂ → (Fin g → ℂ), ζ 0 = z₀ ∧ AnalyticAt ℂ ζ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), e u (ζ u) = 1 := by
  first | exact @GlobalTheory.RelExp.exists_exp_along_disc | exact GlobalTheory.RelExp.exists_exp_along_disc | (intros; apply GlobalTheory.RelExp.exists_exp_along_disc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.Proof.LetterConjugation

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  exact List.mem_flatMap.2 ⟨a, List.mem_finRange a, List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩⟩

theorem nodup_letters : (letters Dw).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · exact (List.nodup_finRange _).map fun i i' h => eq_of_heq (Sigma.mk.inj h).2
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, h⟩ := List.mem_map.1 hy
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective (Sigma.mk.inj h).1).symm

theorem rt0_conj_neg_ne_zero : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h2
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h2
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, him] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem conj_ne {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h1
  exact rt0_conj_neg_ne_zero (H := H) (by simpa [conjEmb, h] using h1)

theorem conj_eq {τ : E →+* ℂ} (h : τ (H.rt : E) ≠ H.rt0) : conjEmb τ (H.rt : E) = H.rt0 := by
  have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h0, H.sqrt_neg_disc_sq]; simp
  have h2 : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_left h
  have h3 : starRingEnd ℂ H.rt0 ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq]; simp
  have h4 : starRingEnd ℂ H.rt0 = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left rt0_conj_neg_ne_zero
  simp [conjEmb, h2, h4]

theorem mult_add (τ : E →+* ℂ) : Dw.mult τ + Dw.mult (conjEmb τ) = Dw.p + Dw.q := by
  unfold Datum.mult
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h, if_neg (conj_ne h)]
  · rw [if_neg h, if_pos (conj_eq h), add_comm]

theorem two_mul_length : 2 * (letters Dw).length = Module.finrank ℚ E * (Dw.p + Dw.q) := by
  classical
  have h1 : (letters Dw).length = ∑ τ, Dw.mult τ := by
    rw [← List.toFinset_card_of_nodup (nodup_letters Dw),
      Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (mem_letters Dw x), Finset.card_univ, Fintype.card_sigma]
    simp
  have hinv : Function.Involutive (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := fun τ => by
    ext x; simp [conjEmb]
  have h2 : ∑ τ, Dw.mult (conjEmb τ) = ∑ τ, Dw.mult τ := hinv.bijective.sum_comp Dw.mult
  rw [h1, two_mul]
  nth_rewrite 2 [← h2]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => mult_add Dw τ, Finset.sum_const, Finset.card_univ,
    Embeddings.card, smul_eq_mul]

end Free

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

end GlobalTheory.Proof.LetterConjugation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapHilbertModelEqConcreteThetaMapFamilyThre
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapHilbertModelEqConcreteThetaMapFamilyThre
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.ThetaRead3

theorem lift_postOn {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (X : MMap M) :
    PiTensorProduct.lift (postOn M L X) = L ∘ₗ PiTensorProduct.lift X := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp [postOn]

theorem thF_congr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (i : Fin D.R.m) (t u : T) (hu : u = t)
    (z : (R.HV i t).H) (z' : (R.HV i u).H) (h : R.extV i u z' = R.extV i t z) : R.thF i u z' = R.thF i t z := by
  subst hu
  rw [hinj i u h]

theorem ofInjective_symm_eq {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (f : X →ₗ[ℂ] Y)
    (hf : Function.Injective f) (a : LinearMap.range f) : f ((LinearEquiv.ofInjective f hf).symm a) = a := by
  have h := LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective f hf) a
  exact congrArg Subtype.val h


set_option maxHeartbeats 4000000 in
theorem thetaP_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t x
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hP.char.base.thP hH.aux.ex
  have hM := hP.char.base.models
  have hμ : Used0 D (Y.tup t) := by
    rcases hP.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h, Y.tup0]
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  set xM := D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x) with hxM
  set zt := R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x) with hzt
  obtain ⟨w, hwM, hwK, hwW⟩ := GlobalTheory.T.thetaAdjoint_at_lift_eq_lowestKType_restriction R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hP.char.base.lev
    hP.char.base.grp hM hE R.hv0 Y.IL (Y.tup t) hμ i xM
  have hth := Y.tied.lift.theta (Y.tup t) hμ i xM w
    (GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hE.thF (Y.tup t) i) hwM hwK hwW

  set u := Y.tupT (Y.tup t) with hu
  set a := Y.IL.jMt (Y.tup t) hμ i xM with ha
  set z' : (R.HV i u).H := (LinearEquiv.ofInjective (R.extV i u) (Y.hinj i u)).symm
    (Submodule.inclusion inf_le_left a) with hz'
  have hz'1 : R.extV i u z' = R.extV i t zt := by
    rw [hz', ofInjective_symm_eq]
    exact Y.mtRead i t hμ x
  have hzz : R.thF i u z' = R.thF i t zt := thF_congr R.toRealDat Y.hinj i t u (Y.tupT_tup t) zt z' hz'1
  let w' : (⨂[ℂ] τ, (R.MW i (sg0 D A3.A)).sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap (R.MW i (sg0 D A3.A)) := PiTensorProduct.lift.symm w'
  have hU : U ∈ R.Wall i (sg0 D A3.A) :=
    GlobalTheory.HeckeParts.mult_le_triv _ ((Mult.mem_multT _ _ _ _ w').1 hwM)
  have hlow : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A3.A)) ρ, U (fun ρ => v ρ) = R.thF i u z' (fun ρ => v ρ) := by
    intro v
    have e := LinearMap.congr_fun hwK (PiTensorProduct.tprod ℂ v)
    have e2 : w' (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) =
        PiTensorProduct.lift (R.thF i u z')
          (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) := e
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod] at e2
    exact e2
  have hw0 : U - R.thF i t zt = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A3.A)) R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _ (Submodule.sub_mem _ hU (hE.thF_mem i t zt)) (fun v => by
        show U (fun ρ => v ρ) - R.thF i t zt (fun ρ => v ρ) = 0
        rw [hlow v, hzz, sub_self])
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  have h1 := (Y.mjRead i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) xM)).symm.trans hth
  change PiTensorProduct.lift _ = R.eWf i (sg0 D A3.A) ∘ₗ w' at h1
  rw [← hUw, sub_eq_zero.1 hw0, ← lift_postOn, ← hE.thG i t zt] at h1
  exact (hM.HW i (sg0 D A3.A)).1 (PiTensorProduct.lift.injective h1)

end GlobalTheory.Mem.ThetaRead3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapHilbertModelEqConcreteThetaMapFamilyThreStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) := by
  first | exact @GlobalTheory.Mem.ThetaRead3.thetaP_read | exact GlobalTheory.Mem.ThetaRead3.thetaP_read | (intros; apply GlobalTheory.Mem.ThetaRead3.thetaP_read <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRing
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigStable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

theorem basis_fixed_bc {L k : Type} [CommRing L] [CommRing k] (ψ : L →+* k) {n m : ℕ}
    (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)) (hP : ∀ c, P (P c) = P c)
    (h : ∀ c, P' (ψ ∘ c) = ψ ∘ P c) (e : Fin m → Fin n → L) (he : ∀ i, P (e i) = e i)
    (hb : ∀ c, P c = c → ∃! a : Fin m → L, c = ∑ i, a i • e i) (c' : Fin n → k) (hc : P' c' = c') :
    ∃! a : Fin m → k, c' = ∑ i, a i • (ψ ∘ e i) := by
  classical
  choose M hM using fun j : Fin n => (hb _ (hP (Pi.single j 1))).exists
  have hs : ∀ {R : Type} [CommRing R] (a : Fin n → R), ∑ j, a j • (Pi.single j 1 : Fin n → R) = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hinv : ∀ i, (fun i' => ∑ j, e i j * M j i') = Pi.single i 1 := fun i => by
    refine (hb _ (he i)).unique ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← he i, ← hs (e i), map_sum]
      simp only [map_smul, hM, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    · simp [Pi.single_apply]
  have h1 : ∀ j, P' (Pi.single j 1) = ∑ i, ψ (M j i) • (ψ ∘ e i) := fun j => by
    rw [show (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 from funext fun j' => by
      by_cases hj : j' = j <;> simp [hj, Pi.single_apply], h, hM]
    funext r
    simp [Finset.sum_apply]
  refine ⟨fun i => ∑ j, c' j * ψ (M j i), ?_, fun a ha => ?_⟩
  · show c' = _
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← hc, ← hs c', map_sum]
    simp only [map_smul, h1, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  · funext i
    have h2 : ∀ i', ∑ j, ψ (e i' j) * ψ (M j i) = if i = i' then 1 else 0 := fun i' => by
      have := congrArg ψ (congrFun (hinv i') i)
      simpa [Pi.single_apply, apply_ite ψ] using this
    have h3 : ∀ j, c' j = ∑ i', a i' * ψ (e i' j) := fun j => by
      have := congrFun ha j
      simpa [Finset.sum_apply] using this
    show a i = ∑ j, c' j * ψ (M j i)
    simp only [h3, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, h2]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {l : Level H} (c : Coeff l)

theorem exists_proj_bc {L : Type} [CommRing L] [IsLocalRing L] (φ : c.F →+* L) {x : Sp L ⟶ X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G} (hx : IsUnivChart _ n xc)
    {k : Type} [CommRing k] (ψ : L →+* k) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback (spMap ψ ≫ x)).obj t.G)
      (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, vec t (spMap ψ ≫ x) xc' (ψ ∘ cc) =
        spMap (Formalism.L2.Pj.dualMap ψ) ≫ vec t x xc cc) ∧
      ∀ τ, ∃ (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)), (∀ cc, P (P cc) = P cc) ∧
        (∀ cc, P' (ψ ∘ cc) = ψ ∘ P cc) ∧ (∀ cc, P cc = cc ↔ cc ∈ eig c φ hx τ) ∧
        ∀ cc, P' cc = cc ↔ cc ∈ eig c (ψ.comp φ) hx' τ := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have key : ∀ (τ : E →+* ℂ) {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ X}
      {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj t.G}
      (hx : IsUnivChart _ n xc), (∀ m, proj (rho hx) (embK c) α τ (proj (rho hx) (embK c) α τ m) =
          proj (rho hx) (embK c) α τ m) ∧
        ∀ m, proj (rho hx) (embK c) α τ m = m ↔ m ∈ eig c (algebraMap c.F R) hx τ :=
    fun τ {R} _ _ {x xc} hx => by
      have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) (proj (rho hx) (embK c) α τ m) := fun m =>
        eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
      have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) m → proj (rho hx) (embK c) α τ m = m := fun m hm => by
        have := proj_sum_eig (rho hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by
          by_cases h : τ' = τ
          · subst h; rwa [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
        rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
      refine ⟨fun m => e₂ _ (e₁ m), fun m => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
      exact ⟨fun h => h ▸ e₁ m, fun h => e₂ m h⟩
  letI : Algebra c.F L := φ.toAlgebra
  letI : Algebra L k := ψ.toAlgebra
  letI : Algebra c.F k := (ψ.comp φ).toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (algebraMap L k ∘ cc) = algebraMap L k ∘ rho hx a cc :=
    fun a cc => vec_inj hx' (by
      show vec t _ xc' (tmap hx' _ _) = vec t _ xc' (_ ∘ tmap hx _ _)
      rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
  have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rho hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) =
      algebraMap L k ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul (algebraMap L k) _ _).symm
  exact ⟨xc', hx', hv, fun τ => ⟨_, _, (key τ hx).1, pr _, (key τ hx).2, (key τ hx').2⟩⟩

end GlobalTheory.ShFam.EigStable


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in
theorem GlobalTheory.ShFam.EigStable.stable_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x), IsLocalRing R → GlobalTheory.ShFam.EigFrame.Stable f := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f _ R' _ _ ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  obtain ⟨xc', hx', hv, hP⟩ := GlobalTheory.ShFam.EigStable.exists_proj_bc c φ hx ψ
  choose e he using fun τ i => vec_exists hx (f.v τ i) (f.tan τ i)
  choose P P' hPP hc hP hP' using hP
  have heig : ∀ τ i, P τ (e τ i) = e τ i := fun τ i =>
    (hP τ _).2 ((vec_eig_iff hx _ _).1 (by rw [← he]; exact f.eig τ i))
  have hfv : ∀ τ, f.v τ = fun i => vec Z.t x xc (e τ i) := fun τ => funext (he τ)
  refine ⟨⟨fun τ i => vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ e τ i), fun τ i => vec_tan hx' _,
    fun τ i => (vec_eig_iff hx' _ _).2 ((hP' τ _).1 (by rw [hc, heig])), fun τ w hw hw' => ?_⟩,
    fun τ i => by rw [he]; exact hv _⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  simp only [comb_iff hx']
  refine GlobalTheory.ShFam.EigStable.basis_fixed_bc ψ (P τ) (P' τ) (hPP τ) (hc τ) (e τ) (heig τ) (fun c₀ h₀ => ?_) cc
    ((hP' τ _).2 ((vec_eig_iff hx' _ _).1 hw'))
  have := f.basis τ _ (vec_tan hx c₀) ((vec_eig_iff hx _ _).2 ((hP τ _).1 h₀))
  rw [hfv] at this
  simpa only [comb_iff hx] using this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x), IsLocalRing R → f.Stable := by
  first | exact @GlobalTheory.ShFam.EigStable.stable_of_isLocalRing | exact GlobalTheory.ShFam.EigStable.stable_of_isLocalRing | (intros; apply GlobalTheory.ShFam.EigStable.stable_of_isLocalRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem card_frame_index {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = g := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, Embeddings.card] at h1
  have h2 := GlobalTheory.PeriodCoord.card_cmType H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h5 : (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h6 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_sigma] at h6
  simp_rw [Fintype.card_fin, Datum.mult] at h6
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h5, smul_eq_mul, smul_eq_mul] at h6
  rw [h6, mul_add]

theorem exists_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  intro E _ _ _ H Dw l Xo c g e S _ _ _ y hpq
  obtain ⟨U, hU, hg⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp S), Nonempty (SABMap t Xo.univ.t y.x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull y.x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨⟨T, rfl, hTg⟩, -⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U t (hU ▸ m)
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have hgp : 1 ≤ T.g := by
    rw [hTg, hg]
    exact Nat.mul_pos hpos hpq
  obtain rfl : T.g = g := hTg.trans (hg.trans (card_frame_index Dw e))
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo S y.x T.t m
  obtain ⟨th, ht⟩ := h₁ y.s
  have hne := (h₂ th _ ht).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo S _ _ y.gen)
  have hB := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c S y.x y.u T.g e y.tan y.eig).1 y.basis
  obtain ⟨hl, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo S y.x T.t.G m.φ m.cart
  choose v hv using fun j => hl _ (y.tan (e j).1 (e j).2)
  refine ⟨⟨T, m, hgp, th, hne, v, (hb _ v).2 ?_⟩, ht, rfl, hv⟩
  rw [funext hv]
  exact hB

end GlobalTheory.KeyFourth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universalTripleFibre_at_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  first | exact @GlobalTheory.KeyFourth.exists_tied | exact GlobalTheory.KeyFourth.exists_tied | (intros; apply GlobalTheory.KeyFourth.exists_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtPtFOfEigFrame
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

theorem exists_frPt_ptF_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z L _ φ z x g hs hx
  letI := φ.toAlgebra
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (Z := Z) z hs hx g
  refine ⟨y, pullback.hom_ext ?_ ?_, fun τ i => ⟨w τ i, (hw τ i).2⟩⟩
  · exact (pullback.lift_fst _ _ _).trans hy
  · exact (pullback.lift_snd _ _ _).trans hs.symm

end GlobalTheory.ShFam
end
end
