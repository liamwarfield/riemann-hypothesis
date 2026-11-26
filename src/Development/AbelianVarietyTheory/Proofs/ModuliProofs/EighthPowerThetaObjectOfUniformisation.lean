module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OLinearMatrixOfUnifPow
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PowMatrixLinear

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

theorem comp_prod {X Y M : C} [MonObj M] [IsCommMonObj M] {J : Type*} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l :=
  map_prod (MonoidHom.mk ⟨fun x : Y ⟶ M => f ≫ x, MonObj.comp_one f⟩
    (fun a b => MonObj.comp_mul f a b)) g s

theorem prod_comp {X M N : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N] {J : Type*}
    (s : Finset J) (g : J → (X ⟶ M)) (f : M ⟶ N) [IsMonHom f] :
    (∏ l ∈ s, g l) ≫ f = ∏ l ∈ s, g l ≫ f :=
  map_prod (IsMonHom.monoidHom f X) g s

end General

local instance splitTorus_isCommMonObj (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    IsCommMonObj (splitTorus S X) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (splitTorusAff ZU X)))

end PowMatrixLinear


end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoLinCombLamOfAppellHumbert
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoLinCombLamOfAppellHumbert
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

namespace SharpBundle

def IsFrameAlong {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (L : LB X)
    (fr : L.ι → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ i, DifferentiableOn ℂ (fr i) {z | ⊤ ≤ e z ⁻¹ᵁ L.U i}) ∧ (∀ i z, ⊤ ≤ e z ⁻¹ᵁ L.U i → fr i z ≠ 0) ∧
    ∀ i j z, ⊤ ≤ e z ⁻¹ᵁ (L.U i ⊓ L.U j) → fr i z = valAt' (e z) (L.U i ⊓ L.U j) (L.g i j).val * fr j z

theorem differentiableOn_finset_prod {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (s : Finset κ) (φ : κ → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (φ k) S) :
    DifferentiableOn ℂ (fun z => ∏ k ∈ s, φ k z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem IsFrameAlong.linComb {g : ℕ} {X Y : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (L : LB Y) {K : Type}
    [Fintype K] (φ : K → (X ⟶ Y)) (ε : K → ℤ) (fr : K → L.ι → (Fin g → ℂ) → ℂ)
    (h : ∀ k, IsFrameAlong (fun z => e z ≫ φ k) L (fr k)) :
    IsFrameAlong e (LB.LinComb L φ ε) (fun (j : K → L.ι) z => ∏ k, fr k (j k) z ^ ε k) := by
  have hc : ∀ (j : K → L.ι) z, ⊤ ≤ e z ⁻¹ᵁ LB.wchart L φ j → ∀ k, ⊤ ≤ (e z ≫ φ k) ⁻¹ᵁ L.U (j k) :=
    fun j z hz => (CubeValues.le_preimage_wchart (e z) L φ j).1 hz
  refine ⟨fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_⟩
  · refine differentiableOn_finset_prod Finset.univ (fun k (z : Fin g → ℂ) => fr k (j k) z ^ ε k) fun k => ?_
    refine DifferentiableOn.zpow ?_ (Or.inl fun z hz => (h k).2.1 _ _ (hc j z hz k))
    exact ((h k).1 (j k)).mono fun z hz => hc j z hz k
  · exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ((h k).2.1 _ _ (hc j z hz k))
  · obtain ⟨h1, h2⟩ := (top_le_preimage_inf (e z) _ _).1 hz
    have e1 := CubeValues.val_linComb (e z) valAt'_rules L φ ε j j' h1 h2
    refine Eq.trans ?_ (congrArg (· * ∏ k, fr k (j' k) z ^ ε k) e1.symm)
    show _ = (∏ k, _) * _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow]
    exact congrArg (· ^ ε k) ((h k).2.2 (j k) (j' k) z
      ((top_le_preimage_inf _ _ _).2 ⟨hc j z h1 k, hc j' z h2 k⟩))

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem isFrameAlong_comp {n : ℕ} (F : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    IsFrameAlong (fun z => (u.ex (F z)).left) L (fun i z => u.fr i (F z)) :=
  ⟨fun i => (u.fr_hol i).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn fun _ hz => hz,
    fun i z hz => u.fr_ne i (F z) hz, fun i j z hz => u.fr_compat i j (F z) hz⟩

def withFrame {M : LB A.left} (fr : M.ι → (Fin g → ℂ) → ℂ) (h : IsFrameAlong (fun z => (u.ex z).left) M fr) :
    HolUnif A M g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fr
  fr_hol := h.1
  fr_ne := h.2.1
  fr_compat := h.2.2

theorem hermForm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem hermForm_swap {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = hermForm Hm z w - 2 * Complex.I * ((hermForm Hm z w).im : ℂ) := by
  have h : hermForm Hm w z = starRingEnd ℂ (hermForm Hm z w) := by
    change _ = star (hermForm Hm z w)
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, Matrix.dotProduct_mulVec]
  rw [h]
  apply Complex.ext <;> simp
  ring

variable {u} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem ah_step (h : u.IsAH Hm χ) (l : u.Λ) (i : L.ι) (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    u.fr i z = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * u.fr i (z + l) :=
  h.2.2.2 l i z hz

theorem ah_step_add (h : u.IsAH Hm χ) (l m : u.Λ) (i : L.ι) (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    u.fr i z = χ l * χ m * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l +
      (Real.pi * hermForm Hm (z + l) m + Real.pi / 2 * hermForm Hm m m)) * u.fr i (z + l + m) := by
  have h2 := ah_step h m i (z + l) (by rw [CubeValues.ex_add_period u z l l.2]; exact hz)
  rw [ah_step h l i z hz, h2, Complex.exp_add _ (_ + _)]
  ring

theorem prod_finset_fin_two' (f : Finset (Fin 2) → ℂ) :
    ∏ I : ULift.{0} (Finset (Fin 2)), f I.down = f ∅ * f {0} * f {1} * f {0, 1} := by
  rw [Fintype.prod_equiv Equiv.ulift (fun I : ULift.{0} (Finset (Fin 2)) => f I.down) f fun I => rfl]
  have : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem lam_step (h : u.IsAH Hm χ) (j : ULift.{0} (Finset (Fin 2)) → L.ι) (x x' : Fin 2 → Fin g → ℂ) (l : Fin 2 → u.Λ)
    (hx' : ∀ a, x' a = x a + l a)
    (hx : ∀ I, ⊤ ≤ (u.ex (∑ a ∈ I.down, x a)).left ⁻¹ᵁ L.U (j I)) :
    ∏ I : ULift.{0} (Finset (Fin 2)), u.fr (j I) (∑ a ∈ I.down, x a) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      Complex.exp (Real.pi * Complex.I * ((hermForm Hm (l 0) (l 1)).im : ℂ) +
        (Real.pi * (hermForm Hm (x 0) (l 1) + hermForm Hm (x 1) (l 0)) +
          Real.pi / 2 * (hermForm Hm (l 0) (l 1) + hermForm Hm (l 1) (l 0)))) *
      ∏ I : ULift.{0} (Finset (Fin 2)), u.fr (j I) (∑ a ∈ I.down, x' a) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  rw [prod_finset_fin_two' fun I => u.fr (j ⟨I⟩) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (2 - I.card)),
    prod_finset_fin_two' fun I => u.fr (j ⟨I⟩) (∑ a ∈ I, x' a) ^ ((-1 : ℤ) ^ (2 - I.card))]
  have c01 : ({0, 1} : Finset (Fin 2)).card = 2 := rfl
  have s01 : ∀ y : Fin 2 → Fin g → ℂ, ∑ a ∈ ({0, 1} : Finset (Fin 2)), y a = y 0 + y 1 := fun y =>
    Finset.sum_pair (by decide)
  have h0 := hx ⟨{0}⟩
  have h1 := hx ⟨{1}⟩
  have h01 := hx ⟨{0, 1}⟩
  simp only [Finset.sum_singleton, s01] at h0 h1 h01
  have e0 := ah_step h (l 0) _ _ h0
  have e1 := ah_step h (l 1) _ _ h1
  have e01 := ah_step_add h (l 0) (l 1) _ _ h01
  have n0 : χ (l 0) ≠ 0 := fun e => by simpa [e] using h.2.2.1 (l 0)
  have n1 : χ (l 1) ≠ 0 := fun e => by simpa [e] using h.2.2.1 (l 1)
  have hs : x 0 + l 0 + (x 1 + l 1) = x 0 + x 1 + l 0 + l 1 := by abel
  simp only [Finset.sum_singleton, s01, Finset.sum_empty, Finset.card_empty, Finset.card_singleton, c01, hx', hs]
  norm_num
  rw [e0, e1, e01]
  have key : Complex.exp (Real.pi * hermForm Hm (x 0 + x 1) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0) +
      (Real.pi * hermForm Hm (x 0 + x 1 + l 0) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1))) =
      Complex.exp (Real.pi * Complex.I * ((hermForm Hm (l 0) (l 1)).im : ℂ) +
        (Real.pi * (hermForm Hm (x 0) (l 1) + hermForm Hm (x 1) (l 0)) +
          Real.pi / 2 * (hermForm Hm (l 0) (l 1) + hermForm Hm (l 1) (l 0)))) *
      Complex.exp (Real.pi * hermForm Hm (x 0) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0)) *
      Complex.exp (Real.pi * hermForm Hm (x 1) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [hermForm_add_left]
    rw [hermForm_swap h.1 (l 0) (l 1)]
    ring
  rw [key]
  have := Complex.exp_ne_zero (Real.pi * hermForm Hm (x 0) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0))
  have := Complex.exp_ne_zero (Real.pi * hermForm Hm (x 1) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1))
  simp only [mul_inv]
  field_simp

theorem sum_symmetrise {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → Fin n → ℂ) :
    ∑ uv : Fin n × Fin n, (W uv.1 uv.2 : ℂ) * (b uv.1 uv.2 + b uv.2 uv.1) =
      ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * b i j := by
  simp only [Fintype.sum_prod_type, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add, mul_add, add_mul,
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end SharpBundle


open SharpBundle in
theorem lbIso_linComb_lam_of_appellHumbert : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (u₀ : HolUnif P₀.A P₀.L P₀.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ) (pr : Fin 8 → (P.A ⟶ P₀.A)) (R : Fin 8 → ((Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ))), u.IsAH Hm χ → u₀.IsAH H₀ χ₀ → (∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i) → (∀ z w, hermForm Hm z w = ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm H₀ (R i z) (R j w)) → (∀ l : u.Λ, χ l = Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j, (W i j : ℂ) * ((hermForm H₀ (R i l) (R j l)).im : ℂ))) → LBIso P.L (LB.LinComb (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro h1 h2 h3 h4 W P u Hm χ P₀ u₀ H₀ χ₀ pr R hu hu₀ hR hH hχ
  let r : Fin 8 × Fin 8 → Fin 2 → Fin 8 := fun uv => ![uv.1, uv.2]
  have hpt : ∀ (uv : Fin 8 × Fin 8) (I : Finset (Fin 2)) z,
      ((u.ex z).left ≫ (lift (pr uv.1) (pr uv.2)).left) ≫ (psum P₀.A (x2 P₀.A) I).left =
        (u₀.ex (∑ a ∈ I, R (r uv a) z)).left := fun uv I z => by
    rw [← Over.comp_left, ← Over.comp_left,
      CubeValues.comp_psum u₀ (u.ex z ≫ lift (pr uv.1) (pr uv.2)) (x2 P₀.A) fun a => R (r uv a) z]
    intro k
    fin_cases k <;> simp [x2, r, hR]
  have hin : ∀ uv : Fin 8 × Fin 8, IsFrameAlong (fun z => (u.ex z).left ≫ (lift (pr uv.1) (pr uv.2)).left)
      (abelian₂ P₀.A P₀.L) (fun (j : ULift.{0} (Finset (Fin 2)) → P₀.L.ι) z =>
        ∏ I : ULift.{0} (Finset (Fin 2)), u₀.fr (j I) (∑ a ∈ I.down, R (r uv a) z) ^ ((-1 : ℤ) ^ (2 - I.down.card))) :=
    fun uv => IsFrameAlong.linComb _ P₀.L (K := ULift.{0} (Finset (Fin 2))) _ _
      (fun I i z => u₀.fr i (∑ a ∈ I.down, R (r uv a) z)) fun I => by
        simp only [hpt]
        simpa only [LinearMap.sum_apply] using isFrameAlong_comp u₀ (∑ a ∈ I.down, R (r uv a))
  have hout := IsFrameAlong.linComb (fun z => (u.ex z).left) (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8)
    (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ hin
  have hΛ : ∀ i (l : u.Λ), R i l ∈ u₀.Λ := fun i l => by
    rw [← u₀.ker, hR, (u.ker _).2 l.2, ← CubeValues.ex_zero u, ← hR, map_zero, CubeValues.ex_zero]
  refine GlobalTheory.lbIso_of_same_factor h1 h2 h3 h4 P _ _ u (withFrame u _ hout) P.isLB
    (LB.isLB_linComb (LB.isLB_linComb P₀.isLB _ _) _ _) rfl fun l i j z hi hj => ?_
  have hj' := (CubeValues.le_preimage_wchart (u.ex z).left (abelian₂ P₀.A P₀.L) _ j).1 hj
  have hst := fun uv : Fin 8 × Fin 8 => lam_step hu₀ (j uv) (fun a => R (r uv a) z) (fun a => R (r uv a) (z + l))
    (fun a => ⟨R (r uv a) l, hΛ _ l⟩) (fun a => map_add _ _ _) fun I => by
      rw [← hpt]
      exact (CubeValues.le_preimage_wchart _ P₀.L _ (j uv)).1 (hj' uv) I
  dsimp only [withFrame]
  change u.fr i z * ∏ uv : Fin 8 × Fin 8, _ = u.fr i (z + l) * ∏ uv : Fin 8 × Fin 8, _
  simp only [hst, mul_zpow, Finset.prod_mul_distrib, ← Complex.exp_int_mul, ← Complex.exp_sum]
  rw [ah_step hu l i z hi, hχ, ← Complex.exp_add, hH, hH, ← sum_symmetrise W fun a b => hermForm H₀ (R a z) (R b l),
    ← sum_symmetrise W fun a b => hermForm H₀ (R a l) (R b l), ← Fintype.sum_prod_type' fun a b =>
      (W a b : ℂ) * ((hermForm H₀ (R a l) (R b l)).im : ℂ), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, mul_comm _ (u.fr i (z + l)), _root_.mul_assoc]
  congr 3
  refine Finset.sum_congr rfl fun uv _ => ?_
  simp only [r, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoLinCombLamOfAppellHumbertStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_linComb_lam_of_appellHumbert_alt : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (u₀ : HolUnif P₀.A P₀.L P₀.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ) (pr : Fin 8 → (P.A ⟶ P₀.A)) (R : Fin 8 → ((Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ))), u.IsAH Hm χ → u₀.IsAH H₀ χ₀ → (∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i) → (∀ z w, hermForm Hm z w = ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm H₀ (R i z) (R j w)) → (∀ l : u.Λ, χ l = Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j, (W i j : ℂ) * ((hermForm H₀ (R i l) (R j l)).im : ℂ))) → LBIso P.L (LB.LinComb (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.lbIso_linComb_lam_of_appellHumbert | exact GlobalTheory.lbIso_linComb_lam_of_appellHumbert | (intros; apply GlobalTheory.lbIso_linComb_lam_of_appellHumbert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfLin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpObj

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).mpr u.Λ.zero_mem

def exHom : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
  MonoidHom.mk' (fun z => u.ex z.toAdd) fun z w => u.ex_add _ _

theorem ex_zsmul (n : ℤ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  have h := map_zpow (exHom u) (Multiplicative.ofAdd z) n
  rw [← ofAdd_zsmul] at h
  simpa [exHom] using h

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_sum [IsCommMonObj A] {I : Type} [Fintype I] (z : I → Fin g → ℂ) : u.ex (∑ i, z i) = ∏ i, u.ex (z i) := by
  classical
  have key : ∀ s : Finset I, u.ex (∑ i ∈ s, z i) = ∏ i ∈ s, u.ex (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact ex_zero u
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, u.ex_add, ih]
  exact key Finset.univ

end Unif

variable (laws : Out.Laws) (laws2 : Out.Laws2)
  (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
  (hT : ThetaUnifAV)
include laws laws2 hc hT

theorem hom_ext_of_lin (P P' : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u' : HolUnif P'.A P'.L P'.g)
    (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)) (f f' : P.A ⟶ P'.A) (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f)
    (hf' : ∀ z, u'.ex (F z) = u.ex z ≫ f') (h1 : IsMonHom f) : f = f' := by
  have e : ∀ B : Over (Sp ℂ), ∀ [GrpObj B], (η[B] : 𝟙_ _ ⟶ B) = 1 := fun B _ => by rw [Hom.one_def]; simp
  have h2 : IsMonHom f' := laws.rigidity _ _ _ P.isAb P'.isAb f' (by
    rw [e, e, ← ex_zero u, ← hf', map_zero, ex_zero])
  refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P' _ _ u u' F fun z hz => ?_).unique ⟨h1, hf⟩ ⟨h2, hf'⟩
  rw [← u'.ker, hf, (u.ker z).2 hz, MonObj.one_comp]

theorem exists_proj (P P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u₀ : HolUnif P₀.A P₀.L P₀.g)
    {I : Type} [Fintype I] (σ : I × Fin P₀.g ≃ Fin P.g)
    (hΛ : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ) :
    ∃ pr : I → (P.A ⟶ P₀.A), (∀ i, IsMonHom (pr i)) ∧ (∀ i z, u₀.ex (fun j => z (σ (i, j))) = u.ex z ≫ pr i) ∧
      ∀ (T : Over (Sp ℂ)) (y : I → (T ⟶ P₀.A)), ∃! x : T ⟶ P.A, ∀ i, x ≫ pr i = y i := by
  classical
  letI := P.isAb.comm
  letI := P₀.isAb.comm
  let R : I → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  let S : I → (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := fun i =>
    LinearMap.pi fun a => if (σ.symm a).1 = i then LinearMap.proj (σ.symm a).2 else 0
  have hRS : ∀ i i' z, R i (S i' z) = if i = i' then z else 0 := fun i i' z => by
    ext j
    by_cases e : i = i' <;> simp [R, S, LinearMap.funLeft_apply, e]
  have hSR : ∀ z, ∑ i, S i (R i z) = z := fun z => by
    ext a
    obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective a
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [R, S, LinearMap.funLeft_apply]
    · intro b _ hb
      simp [S, hb.symm]
    · simp
  choose pr hpr using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P₀ _ _ u u₀ (R i) fun z hz => (hΛ z).1 hz i).exists
  choose inc hinc using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P₀ P _ _ u₀ u (S i) fun z hz => (hΛ _).2 fun i' => by
    change R i' (S i z) ∈ _
    rw [hRS]
    split_ifs
    exacts [hz, u₀.Λ.zero_mem]).exists
  haveI := fun i => (hpr i).1
  haveI := fun i => (hinc i).1
  have e1 : ∀ i, inc i ≫ pr i = 𝟙 _ := fun i =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ LinearMap.id _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i).2, hRS]; simp) (fun z => by simp) inferInstance
  have e2 : ∀ i i', i ≠ i' → inc i ≫ pr i' = 1 := fun i i' hi =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ 0 _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i').2, hRS]; simp [hi.symm])
      (fun z => by simp [ex_zero]) inferInstance
  have e3 : 𝟙 P.A = ∏ i, pr i ≫ inc i :=
    hom_ext_of_lin laws laws2 hc hT P P u u LinearMap.id _ _ (fun z => by simp) (fun z => by
      rw [PowMatrixLinear.comp_prod]
      simp only [← Category.assoc, ← (hpr _).2, ← (hinc _).2]
      rw [← ex_sum, hSR]; rfl) inferInstance
  refine ⟨pr, fun i => (hpr i).1, fun i => (hpr i).2, fun T y => ⟨∏ i, y i ≫ inc i, fun i => ?_, fun x hx => ?_⟩⟩
  · rw [PowMatrixLinear.prod_comp, Finset.prod_eq_single i]
    · rw [Category.assoc, e1, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, e2 _ _ hb, MonObj.comp_one]
    · simp
  · rw [← Category.comp_id x, e3, PowMatrixLinear.comp_prod]
    simp only [← Category.assoc, hx]

end GlobalTheory.SharpObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImInvIsHermitian
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SharpObj

variable {h : ℕ}

def per (τ : Matrix (Fin h) (Fin h) ℂ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x i => τ.mulVec (fun i' => (x (.inl i') : ℂ)) i + (x (.inr i) : ℂ)
      map_zero' := by ext i; simp [Matrix.mulVec, dotProduct]
      map_add' := fun x y => by
        ext i
        simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
        ring }

theorem per_apply (τ : Matrix (Fin h) (Fin h) ℂ) (x : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    per τ x i = τ.mulVec (fun i' => (x (.inl i') : ℂ)) i + (x (.inr i) : ℂ) := rfl

def imInv (τ : Matrix (Fin h) (Fin h) ℂ) : Matrix (Fin h) (Fin h) ℂ :=
  (τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)

theorem hermForm_real_re (M : Matrix (Fin h) (Fin h) ℝ) (z w : Fin h → ℂ) :
    (hermForm (M.map fun x : ℝ => (x : ℂ)) z w).re =
      (fun i => (z i).re) ⬝ᵥ M.mulVec (fun i => (w i).re) + (fun i => (z i).im) ⬝ᵥ M.mulVec (fun i => (w i).im) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

theorem hermForm_real_im (M : Matrix (Fin h) (Fin h) ℝ) (z w : Fin h → ℂ) :
    (hermForm (M.map fun x : ℝ => (x : ℂ)) z w).im =
      (fun i => (z i).im) ⬝ᵥ M.mulVec (fun i => (w i).re) - (fun i => (z i).re) ⬝ᵥ M.mulVec (fun i => (w i).im) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.im_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

variable {τ : Matrix (Fin h) (Fin h) ℂ}

theorem imInv_isHermitian (hp : (τ.map Complex.im).PosDef) : (imInv τ).IsHermitian := by
  unfold imInv
  exact hp.inv.isHermitian.map _ fun x => by simp

theorem imInv_pos (hp : (τ.map Complex.im).PosDef) (z : Fin h → ℂ) (hz : z ≠ 0) :
    0 < (hermForm (imInv τ) z z).re := by
  have hN := hp.inv
  rw [imInv, hermForm_real_re]
  have key : ∀ v : Fin h → ℝ, 0 ≤ v ⬝ᵥ (τ.map Complex.im)⁻¹.mulVec v := fun v => by
    simpa using hN.posSemidef.dotProduct_mulVec_nonneg v
  by_cases hr : (fun i => (z i).re) = 0
  · have hi : (fun i => (z i).im) ≠ 0 := by
      intro hi
      apply hz
      funext i
      apply Complex.ext
      · simpa using congrFun hr i
      · simpa using congrFun hi i
    have := hN.dotProduct_mulVec_pos hi
    simp only [star_trivial] at this
    linarith [key (fun i => (z i).re)]
  · have := hN.dotProduct_mulVec_pos hr
    simp only [star_trivial] at this
    linarith [key (fun i => (z i).im)]

theorem per_eq (x : Fin h ⊕ Fin h → ℤ) :
    per τ x = τ.mulVec (ReciprocityTheory.PTheta.ofRealVec fun i => (x (.inl i) : ℝ)) +
      ReciprocityTheory.PTheta.ofRealVec fun i => (x (.inr i) : ℝ) := by
  funext i
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [per_apply]

private theorem re_mulVec_ofRealVec (a : Fin h → ℝ) (i : Fin h) :
    ((τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a)) i).re = ((τ.map Complex.re).mulVec a) i := by
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]

private theorem im_mulVec_ofRealVec (a : Fin h → ℝ) (i : Fin h) :
    ((τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a)) i).im = ((τ.map Complex.im).mulVec a) i := by
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]

private theorem re_per' (x : Fin h ⊕ Fin h → ℤ) :
    (fun i => (per τ x i).re) = (τ.map Complex.re).mulVec (fun i => (x (.inl i) : ℝ)) + fun i => (x (.inr i) : ℝ) := by
  funext i
  rw [per_eq, Pi.add_apply, Complex.add_re, re_mulVec_ofRealVec]
  simp [ReciprocityTheory.PTheta.ofRealVec.eq_1]

private theorem im_per' (x : Fin h ⊕ Fin h → ℤ) :
    (fun i => (per τ x i).im) = (τ.map Complex.im).mulVec (fun i => (x (.inl i) : ℝ)) := by
  funext i
  rw [per_eq, Pi.add_apply, Complex.add_im, im_mulVec_ofRealVec]
  simp [ReciprocityTheory.PTheta.ofRealVec.eq_1]

theorem im_hermForm_per (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (x y : Fin h ⊕ Fin h → ℤ) :
    (hermForm (imInv τ) (per τ x) (per τ y)).im = omegaStd x y := by
  have hu : IsUnit (τ.map Complex.im).det := (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have hYt : Matrix.transpose (τ.map Complex.im) = τ.map Complex.im := by
    have := hp.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hXt : Matrix.transpose (τ.map Complex.re) = τ.map Complex.re := by
    rw [← Matrix.transpose_map, hs.eq]
  rw [imInv, hermForm_real_im, re_per', im_per', re_per', im_per']
  set X := τ.map Complex.re
  set Y := τ.map Complex.im
  set a : Fin h → ℝ := fun i => (x (.inl i) : ℝ)
  set b : Fin h → ℝ := fun i => (x (.inr i) : ℝ)
  set c : Fin h → ℝ := fun i => (y (.inl i) : ℝ)
  set d : Fin h → ℝ := fun i => (y (.inr i) : ℝ)
  have e1 : Y⁻¹.mulVec (Y.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have e2 : ∀ v, (Y.mulVec a) ⬝ᵥ (Y⁻¹.mulVec v) = a ⬝ᵥ v := fun v => by
    rw [← hYt, ← Matrix.vecMul_transpose, hYt, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hYt,
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have e3 : (X.mulVec a) ⬝ᵥ c = a ⬝ᵥ (X.mulVec c) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hXt, dotProduct_comm]
  rw [e1, e2, add_dotProduct, e3, dotProduct_add]
  have hω : (omegaStd x y : ℝ) = a ⬝ᵥ d - b ⬝ᵥ c := by
    simp only [omegaStd, a, b, c, d, dotProduct]
    push_cast
    rw [Finset.sum_sub_distrib]
  rw [hω]
  ring

private theorem eq_zero_of_mulVec_ofRealVec_add_eq_zero (hp : (τ.map Complex.im).PosDef) (a b : Fin h → ℝ)
    (hab : τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a) + ReciprocityTheory.PTheta.ofRealVec b = 0) : a = 0 ∧ b = 0 := by
  have hu : IsUnit (τ.map Complex.im).det := (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have him : (τ.map Complex.im).mulVec a = 0 := by
    funext i
    have := congrArg (fun v => (v i).im) hab
    simp only [Pi.add_apply, Complex.add_im, im_mulVec_ofRealVec, Pi.zero_apply, Complex.zero_im] at this
    simpa [ReciprocityTheory.PTheta.ofRealVec.eq_1] using this
  have ha : a = 0 := by
    calc a = ((τ.map Complex.im)⁻¹ * τ.map Complex.im).mulVec a := by
          rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, him, Matrix.mulVec_zero]
  refine ⟨ha, ?_⟩
  funext i
  have := congrArg (fun v => (v i).re) hab
  simp only [Pi.add_apply, Complex.add_re, re_mulVec_ofRealVec, ha, Matrix.mulVec_zero, Pi.zero_apply,
    Complex.zero_re, zero_add] at this
  simpa [ReciprocityTheory.PTheta.ofRealVec.eq_1] using this

theorem per_lattice (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    Function.Injective (per τ) ∧ DiscreteTopology (LinearMap.range (per τ)) ∧
      Submodule.span ℝ (LinearMap.range (per τ) : Set (Fin h → ℂ)) = ⊤ := by
  obtain ⟨P, hP⟩ : ∃ P : (Fin h ⊕ Fin h → ℝ) →ₗ[ℝ] (Fin h → ℂ), ∀ g, P g =
      τ.mulVec (ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inl i))) + ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inr i)) :=
    ⟨{ toFun := fun g => τ.mulVec (ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inl i))) +
          ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inr i))
       map_add' := fun g g' => by
          funext i
          unfold ReciprocityTheory.PTheta.ofRealVec
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Complex.ofReal_add,
            mul_add, Finset.sum_add_distrib]
          ring
       map_smul' := fun c g => by
          funext i
          unfold ReciprocityTheory.PTheta.ofRealVec
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul, mul_add, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun _ _ => by ring }, fun _ => rfl⟩
  have hPinj : Function.Injective P := by
    refine (injective_iff_map_eq_zero P).2 fun g hg => ?_
    rw [hP] at hg
    obtain ⟨h1, h2⟩ := eq_zero_of_mulVec_ofRealVec_add_eq_zero hp _ _ hg
    funext j
    cases j with
    | inl i => exact congrFun h1 i
    | inr i => exact congrFun h2 i
  have hper : ∀ x, per τ x = P (fun j => (x j : ℝ)) := fun x => by rw [hP, per_eq]
  have hinj : Function.Injective (per τ) := fun x y hxy => by
    rw [hper, hper] at hxy
    funext j
    exact_mod_cast congrFun (hPinj hxy) j
  have hdim : Module.finrank ℝ (Fin h ⊕ Fin h → ℝ) = Module.finrank ℝ (Fin h → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    omega
  set e := P.linearEquivOfInjective hPinj hdim with he
  set b := (Pi.basisFun ℝ (Fin h ⊕ Fin h)).map e with hb
  have hrepr : ∀ w j, b.repr w j = e.symm w j := fun w j => by
    simp [hb, Module.Basis.map_repr]
  have hrange : LinearMap.range (per τ) = Submodule.span ℤ (Set.range b) := by
    ext w
    rw [Module.Basis.mem_span_iff_repr_mem ℤ b w, LinearMap.mem_range]
    simp only [hrepr]
    constructor
    · rintro ⟨x, rfl⟩ j
      refine ⟨x j, ?_⟩
      have : e.symm (P fun j => (x j : ℝ)) = fun j => (x j : ℝ) := e.symm_apply_apply _
      rw [hper, this]
      simp
    · intro hw
      choose n hn using hw
      refine ⟨n, ?_⟩
      have : (fun j => (n j : ℝ)) = e.symm w := funext fun j => by simpa using hn j
      rw [hper, this]
      exact e.apply_symm_apply w
  refine ⟨hinj, ?_, ?_⟩
  · rw [hrange]
    infer_instance
  · rw [hrange, Submodule.span_span_of_tower, b.span_eq]

theorem exists_form (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    ∃ Ef : LinearMap.BilinForm ℤ (LinearMap.range (per τ)),
      (∀ a b : LinearMap.range (per τ), (Ef a b : ℝ) = (hermForm (imInv τ) a b).im) ∧ Function.Bijective Ef := by
  have hinj := (per_lattice hs hp).1
  set e := LinearEquiv.ofInjective (per τ) hinj with he
  have hpe : ∀ a : LinearMap.range (per τ), per τ (e.symm a) = a := fun a => by
    rw [← LinearEquiv.ofInjective_apply (per τ) (h := hinj) (e.symm a), ← he, e.apply_symm_apply]
  obtain ⟨ω, hω⟩ : ∃ ω : LinearMap.BilinForm ℤ (Fin h ⊕ Fin h → ℤ), ∀ x y, ω x y = omegaStd x y :=
    ⟨LinearMap.mk₂ ℤ omegaStd
      (fun x x' y => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring)
      (fun x y y' => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring), fun _ _ => rfl⟩
  refine ⟨ω.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, fun a b => ?_, ?_, ?_⟩
  · rw [LinearMap.compl₁₂_apply, hω, ← im_hermForm_per hs hp]
    erw [hpe, hpe]
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have hx : ∀ y, omegaStd (e.symm a) y = 0 := fun y => by
      have := LinearMap.congr_fun ha (e y)
      simpa [LinearMap.compl₁₂_apply, hω] using this
    have hz : e.symm a = 0 := by
      funext j
      cases j with
      | inl i =>
        have := hx (fun k => if Sum.inr i = k then 1 else 0)
        simpa [omegaStd] using this
      | inr i =>
        have := hx (fun k => if Sum.inl i = k then 1 else 0)
        simpa [omegaStd] using this
    simpa using congrArg e hz
  · intro φ
    set ψ := φ.comp e.toLinearMap with hψ
    refine ⟨e (Sum.elim (fun i => ψ (fun k => if Sum.inr i = k then 1 else 0))
      (fun i => -ψ (fun k => if Sum.inl i = k then 1 else 0))), ?_⟩
    ext a
    obtain ⟨y, rfl⟩ := e.surjective a
    rw [LinearMap.compl₁₂_apply, hω]
    erw [e.symm_apply_apply, e.symm_apply_apply]
    have : φ (e y) = ψ y := rfl
    rw [this, LinearMap.pi_apply_eq_sum_univ ψ y, Fintype.sum_sum_type]
    simp only [omegaStd, Sum.elim_inl, Sum.elim_inr, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem form_ext {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V) (hs : Submodule.span ℝ s = ⊤)
    (B : V → V → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w) (h2 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h3 : ∀ (c : ℂ) z w, B (c • z) w = c * B z w) (h4 : ∀ (c : ℝ) z w, B z ((c : ℂ) • w) = c * B z w)
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : V) : B z w = 0 := by
  have hB0r : ∀ z, B z 0 = 0 := fun z => by
    have := h2 z 0 0
    simpa using this
  have hB0l : ∀ w, B 0 w = 0 := fun w => by
    have := h1 0 0 w
    simpa using this
  have step1 : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := by rw [hs]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simp [hB0r]
    | add w w' _ _ ihw ihw' => rw [h2, Complex.add_im, ihw, ihw', add_zero]
    | smul c w _ ihw => rw [← Complex.coe_smul, h4, Complex.im_ofReal_mul, ihw, mul_zero]
  have step2 : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := by rw [hs]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact step1 z hz w
    | zero => simp [hB0l]
    | add z z' _ _ ihz ihz' => rw [h1, Complex.add_im, ihz, ihz', add_zero]
    | smul c z _ ihz => rw [← Complex.coe_smul, h3, Complex.im_ofReal_mul, ihz, mul_zero]
  apply Complex.ext
  · have := step2 (Complex.I • z) w
    rw [h3] at this
    simpa using this
  · simpa using step2 z w

end GlobalTheory.SharpObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerThetaObjectOfUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

namespace SharpObj

theorem omegaStd_sum_smul {h : ℕ} {I : Type} [Fintype I] (x : Fin h ⊕ Fin h → ℤ) (c : I → ℤ)
    (y : I → Fin h ⊕ Fin h → ℤ) : omegaStd x (∑ v, c v • y v) = ∑ v, c v * omegaStd x (y v) := by
  simp only [omegaStd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_act {h : ℕ} (G A : Matrix (Fin 8) (Fin 8) ℤ) (x : Fin 8 → Fin h ⊕ Fin h → ℤ) :
    ∑ u, ∑ v, G u v * omegaStd (x u) (∑ v', A v v' • x v') = ∑ u, ∑ v, (G * A) u v * omegaStd (x u) (x v) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [omegaStd_sum_smul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem exp_pi_I_int (n : ℤ) : Complex.exp (Real.pi * Complex.I * (n : ℂ)) = (-1) ^ n := by
  rw [_root_.mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem hermForm_eq_sum {g h : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (H₀ : Matrix (Fin h) (Fin h) ℂ)
    (G : Matrix (Fin 8) (Fin 8) ℤ) (R : Fin 8 → ((Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤)
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm z w).im = ∑ i, ∑ j, (G i j : ℝ) * (hermForm H₀ (R i z) (R j w)).im) (z w) :
    hermForm Hm z w = ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w) := by
  refine sub_eq_zero.1 (form_ext s hs
    (fun z w => hermForm Hm z w - ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [hermForm, map_add (f := _), add_dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  · intro z w w'
    simp only [hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, mul_add, Finset.sum_add_distrib]
    ring
  · intro c z w
    simp only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, mul_sub, Finset.mul_sum, mul_left_comm c]
  · intro c z w
    simp only [hermForm, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_sub,
      Finset.mul_sum, Complex.star_def, Complex.conj_ofReal, mul_left_comm (c : ℂ)]
  · intro z hz w hw
    simp [h0 z hz w hw, Complex.im_sum]

end SharpObj


open SharpObj in
theorem sharpClass_of_unif : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ (t : TObj g k J b (spMap em)) (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) → (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → SharpClass W a bas em t := by
  intro laws laws2 hc hT o _ g k J b em w w' h W a bas σ EF _ _ hw _ hEF t τ m Q Hm ⟨hs, hp⟩ hm hQ
    ⟨_, _, Qspan, _, _, hQim⟩ ⟨u, χ', hAH, hΛ, hχ, hpt, hact⟩
  obtain ⟨Ef₀, hEf₀, hbij⟩ := exists_form hs hp
  obtain ⟨P₀, u₀, χ₀, hg, hΛ₀, hAH₀, -, -⟩ := principalTorus_algebraic h _ (imInv τ) Ef₀ (per_lattice hs hp).2.1
    (per_lattice hs hp).2.2 (imInv_isHermitian hp) (imInv_pos hp) hEf₀ hbij
  subst hg
  let R : Fin 8 → (Fin g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  have hRQ : ∀ i x, R i (Q x) = per τ (x i) := fun i x => funext fun j => hQ x i j
  have hmem : ∀ x, per τ x ∈ u₀.Λ := fun x => hΛ₀ ▸ ⟨x, rfl⟩
  have hΛ' : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ := fun z => by
    rw [hΛ, hΛ₀]
    constructor
    · rintro ⟨x, rfl⟩ i
      exact ⟨x i, (hRQ i x).symm⟩
    · intro H
      choose x hx using H
      refine ⟨x, funext fun c => ?_⟩
      obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective c
      exact (hQ x i j).trans (congrFun (hx i) j)
  obtain ⟨pr, hpr, hpru, hprod⟩ := exists_proj laws laws2 hc hT t.pol P₀ u u₀ σ hΛ'
  change Fin 8 → (t.A ⟶ P₀.A) at pr
  change ∀ i, IsMonHom (pr i : t.A ⟶ P₀.A) at hpr
  change ∀ (T : Over (Sp ℂ)) (y : Fin 8 → (T ⟶ P₀.A)), ∃! x : T ⟶ t.A, ∀ i, x ≫ pr i = y i at hprod
  change ∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i at hpru
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun e => hk (by simp [e])
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hWeil⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm laws laws2 hc hT P₀ u₀ _ χ₀ hAH₀
  obtain ⟨c, φ, hφ, hcP, ⟨wP, hwP⟩, hlev⟩ := GlobalTheory.T.exists_siegPre_iso_of_polAV laws hc o ℂ em P₀.g k b.ζ (Units.map (em : o →* ℂ) b.ζ) P₀
    (fun x => u₀.ex ((k : ℂ)⁻¹ • per τ (m x))) rfl hk rfl
    (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em))
    (fun x y => by rw [map_add (f := _), map_add (f := _), smul_add, u₀.ex_add])
    (fun x => by
      rw [← ex_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul, u₀.ker]
      exact hmem _)
    (fun x y => hWeil k ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ _ hk0 (by
      have e : Ef ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ = omegaStd (m x) (m y) := by
        have := hEf ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩
        rw [im_hermForm_per hs hp] at this
        exact_mod_cast this
      rw [e, hm]
      simp))
  have hform : ∀ z z', hermForm Hm z z' =
      ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm (imInv τ) (R i z) (R j z') :=
    hermForm_eq_sum Hm (imInv τ) (W + W.transpose) R _ Qspan (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      simp only [hQim, hEF, hRQ, im_hermForm_per hs hp, Int.cast_sum, Int.cast_mul])
  have hchi : ∀ l : u.Λ, χ' l = Complex.exp (Real.pi * Complex.I *
      ∑ i, ∑ j, (W i j : ℂ) * ((hermForm (imInv τ) (R i l) (R j l)).im : ℂ)) := fun l => by
    obtain ⟨x, hx⟩ := (hΛ l).1 l.2
    rw [hχ x l hx.symm, hEF, form_act, hw, ← exp_pi_I_int, ← hx]
    simp [hRQ, im_hermForm_per hs hp]
  have hL := GlobalTheory.T.lbIso_linComb_lam_of_appellHumbert_alt laws laws2 hc hT W t.pol u Hm χ' P₀ u₀ _ χ₀ pr R hAH hAH₀ hpru hform hchi
  letI := P₀.isAb.comm
  haveI := hpr
  refine ⟨c, hcP, fun i => pr i ≫ φ.inv, fun i => inferInstanceAs (IsMonHom (pr i ≫ φ.inv)), fun T y => ?_, ?_, fun j i => ?_, fun i v => ?_⟩
  · simp only [← Category.assoc, Iso.comp_inv_eq]
    exact hprod T fun i => y i ≫ φ.hom
  · have hLam : (abelian₂ P₀.A P₀.L).IsLB := DVR.linComb_isLB _ P₀.isLB _ _
    refine LBIso.trans t.isLB (DVR.linComb_isLB _ hLam _ _) (DVR.linComb_isLB _ c.isLB _ _) hL (LBIso.symm ?_)
    have := iso_linComb ((isGen_iff wP).1 hwP) (K := Fin 8 × Fin 8)
      (fun uv => (lift (pr uv.1 ≫ φ.inv) (pr uv.2 ≫ φ.inv)).left) (fun uv => W uv.1 uv.2)
    simp only [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at this
    exact this
  · obtain ⟨F, hF, hFa⟩ := hact j
    haveI := t.hom j
    have hRF : ∀ z, R i (F z) = ∑ v, a j i v • R v z := fun z => by
      have : ((R i ∘ₗ F).restrictScalars ℝ) = (∑ v, a j i v • R v).restrictScalars ℝ :=
        LinearMap.ext_on_range Qspan fun x => by
          rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, LinearMap.comp_apply, hF, hRQ,
            LinearMap.sum_apply]
          simp only [LinearMap.smul_apply, hRQ]
          exact (map_sum (per τ) _ _).trans (Finset.sum_congr rfl fun v _ => map_zsmul (per τ) _ _)
      simpa using LinearMap.congr_fun this z
    have e1 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ t.act j ≫ pr i := fun z => by
      rw [hpru, hFa, Category.assoc]
    have e2 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ ∏ v, pr v ^ a j i v := fun z => by
      rw [hRF, ex_sum, PowMatrixLinear.comp_prod]
      simp only [ex_zsmul, hpru, GrpObj.comp_zpow]
    have e : t.act j ≫ pr i = ∏ v, pr v ^ a j i v :=
      hom_ext_of_lin laws laws2 hc hT t.pol P₀ u u₀ (R i ∘ₗ F) _ _ e1 e2
        (inferInstanceAs (IsMonHom (t.act j ≫ pr i)))
    rw [← Category.assoc, e, PowMatrixLinear.prod_comp]
    simp only [GrpObj.zpow_comp]
    exact (List.prod_ofFn).symm
  · rw [Over.comp_left, hpt, ← Over.comp_left, ← Category.assoc, ← hpru, map_smul, hRQ, ← hlev, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerThetaObjectOfUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_theta_object_of_uniformisation : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ (t : TObj g k J b (spMap em)) (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) → (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → SharpClass W a bas em t := by
  first | exact @GlobalTheory.sharpClass_of_unif | exact GlobalTheory.sharpClass_of_unif | (intros; apply GlobalTheory.sharpClass_of_unif <;> assumption)
end
