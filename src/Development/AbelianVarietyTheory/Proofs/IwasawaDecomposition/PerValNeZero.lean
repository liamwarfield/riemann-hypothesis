module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFramesOfHolPeriods

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam.Pad
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor

section Lin

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def horVal (K : Matrix (m ⊕ n) m ℂ) (C : Matrix n (m ⊕ n) ℂ) : ℂ :=
  (Matrix.fromRows (Classical.epsilon fun R : Matrix m (m ⊕ n) ℂ => R * K = 1) C).det

variable {K : Matrix (m ⊕ n) m ℂ} {C : Matrix n (m ⊕ n) ℂ} {R : Matrix m (m ⊕ n) ℂ} {S : Matrix (m ⊕ n) n ℂ}

theorem det_mul_det (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) :
    (Matrix.fromRows R C).det * (Matrix.fromCols K S).det = 1 := by
  rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, hR, hS, h, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, _root_.one_mul]

theorem horVal_mul (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) :
    horVal K C * (Matrix.fromCols K S).det = 1 := by

  have hR0 : Classical.epsilon (fun R : Matrix m (m ⊕ n) ℂ => R * K = 1) * K = 1 :=
    Classical.epsilon_spec (p := fun R : Matrix m (m ⊕ n) ℂ => R * K = 1) ⟨R, hR⟩
  unfold horVal
  exact det_mul_det h hR0 hS

theorem horVal_eq (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) : horVal K C = (Matrix.fromRows R C).det := by
  have h1 := horVal_mul h hR hS
  have h2 := det_mul_det h hR hS
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)

theorem horVal_ne_zero (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) : horVal K C ≠ 0 :=
  left_ne_zero_of_mul_eq_one (horVal_mul h hR hS)

end Lin

section Hol

def HolTan {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} (B : Set V)
    (v : V → (Sp (DualNumber ℂ) ⟶ X)) : Prop :=
  ∀ (U : X.Opens) (f : Γ(X, U)), DifferentiableOn ℂ
    (fun b => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (A := DualNumber ℂ) (v b) U f).snd) {b ∈ B | ⊤ ≤ v b ⁻¹ᵁ U}

def HolAlong {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (N : Set (CxPts p σ))
    (φ : CxPts p σ → ℂ) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (x : V → CxPts p σ),
    IsOpen B → IsHolTo B (fun b => (x b).1) → Set.MapsTo x B N → DifferentiableOn ℂ (fun b => φ (x b)) B

def logDom (n a : ℕ) : Set (Fin n → ℂ) := {s | ∀ k : Fin n, if (k : ℕ) < a then (s k).re < 0 else ‖s k‖ < 1}

def logExp (a : ℕ) {n : ℕ} (s : Fin n → ℂ) : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.exp (s k) else s k

end Hol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Lattice

scoped instance decEqLetter : DecidableEq (Letter Dw) := Classical.decEq _

abbrev Idx (Dw : Datum H) (τ : E →+* ℂ) : Type := Fin (Dw.mult (conjEmb τ)) ⊕ Fin (Dw.mult τ)

def IsPerBasis (Di : Datum H) {J : Type} [Fintype J] [DecidableEq J] (x : J → Di.La) (hm : Matrix J J E) : Prop :=
  LinearIndependent (𝓞 E) x ∧ (∀ v, ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x)) ∧
    (∀ (a : 𝓞 E) k k', ((Di.EF (a • x k) (x k') : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * hm k k')) ∧ hm.det ≠ 0

def IsIsom (Di : Datum H) (gm : Di.La ≃ₗ[𝓞 E] Di.La) : Prop := ∀ a b, Di.EF (gm a) (gm b) = Di.EF a b

def IsLev (l : Level H) (Di : Datum H) (gm : Di.La ≃ₗ[𝓞 E] Di.La) : Prop :=
  ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Di.La), ∃ e, gm a = a + l.M • e

variable {Di : Datum H}

def perMat {J : Type} (x : J → Di.La) (Q : Di.La →+ (Letter Dw → ℂ)) (ρ : E →+* ℂ) : Matrix (Fin (Dw.mult ρ)) J ℂ :=
  Matrix.of fun i k => Q (x k) ⟨ρ, i⟩

variable (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E)

def kerMat (Q : Di.La →+ (Letter Dw → ℂ)) : Matrix (Idx Dw τ) (Fin (Dw.mult (conjEmb τ))) ℂ :=
  ((hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ)⁻¹ * (perMat x Q (conjEmb τ))ᵀ

def perVal (Q : Di.La →+ (Letter Dw → ℂ)) : ℂ := horVal (kerMat c σ τ x hm Q) (perMat x Q τ)

def GoodPer (Q : Di.La →+ (Letter Dw → ℂ)) : Prop :=
  (∀ (a : 𝓞 E) v (z : Letter Dw), Q (a • v) z = Formalism.L2.PjFree.relab c σ z.1 (a : E) * Q v z) ∧
    perMat x Q τ * kerMat c σ τ x hm Q = 0 ∧
    (∃ R : Matrix (Fin (Dw.mult (conjEmb τ))) (Idx Dw τ) ℂ, R * kerMat c σ τ x hm Q = 1) ∧
    ∃ S : Matrix (Idx Dw τ) (Fin (Dw.mult τ)) ℂ, perMat x Q τ * S = 1

variable {c σ τ x hm}

theorem GoodPer.perVal_ne_zero {Q : Di.La →+ (Letter Dw → ℂ)} (h : GoodPer c σ τ x hm Q) : perVal c σ τ x hm Q ≠ 0 := by
  obtain ⟨-, h1, ⟨R, hR⟩, ⟨S, hS⟩⟩ := h
  exact horVal_ne_zero h1 hR hS

end Lattice

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (σ : c.F →+* ℂ)

abbrev CxFr : Type := Σ x : CxPts (genStr Z) σ, EigFrame Z σ (x.1 ≫ genι Z)

variable {Z σ}

def Inner (x : CxPts (genStr Z) σ) : Prop := x.1 (IsLocalRing.closedPoint ℂ) ∉ genBd Z

def Chg (a a' : CxFr Z σ) (ρ : E →+* ℂ) (M : Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) ℂ) : Prop :=
  a.1 = a'.1 ∧ ∀ i, IsCombAtG Z.t (a'.1.1 ≫ genι Z) (a.2.v ρ) (M i) (a'.2.v ρ i)

def HolFam {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (a : V → CxFr Z σ) : Prop :=
  IsHolTo B (fun b => (a b).1.1) ∧ ∀ ρ i, HolTan B fun b => (a b).2.v ρ i

def Dirs {g : ℕ} (a : CxFr Z σ) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)) (W : Letter Dw → Fin g → ℂ) : Prop :=
  ∀ z : Letter Dw, IsDerivAt0 e (W z) (a.2.v z.1 z.2)

abbrev Fam (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ} (e : Fin g ≃ Letter Dw) : Type 1 :=
  FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) fun j => Formalism.L2.PjFree.relab c σ (e j).1

def Per {g : ℕ} {e : Fin g ≃ Letter Dw} (Fu : Fam Xo c σ e) (a : CxFr Z σ) (i : Fin Fu.n)
    (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) : Prop :=
  ∃ (P : (Fu.Di i).La →+ (Fin g → ℂ)) (W : Letter Dw → Fin g → ℂ) (y : Sp ℂ ⟶ Xo.XF c),
    IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P ∧ y ≫ pullback.fst _ _ = Fu.u i P ∧
    y ≫ Z.jQ = a.1.1 ∧
    (∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ)) ∧
    ∀ v, P v = ∑ z, Q v z • W z


open Classical in
def horOf {g : ℕ} {e : Fin g ≃ Letter Dw} (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (x : ∀ i, Idx Dw τ → (Fu.Di i).La)
    (hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E) (a : CxFr Z σ) : ℂ :=
  if h : ∃ iQ : Σ i : Fin Fu.n, (Fu.Di i).La →+ (Letter Dw → ℂ), Per Fu a iQ.1 iQ.2 then
    perVal c σ τ (x h.choose.1) (hm h.choose.1) h.choose.2 else 0

def LogGrowth (h : CxFr Z σ → ℂ) : Prop :=
  ∀ x₀ : CxPts (genStr Z) σ, ∃ (N : Set (CxPts (genStr Z) σ)) (φ : CxPts (genStr Z) σ → ℂ), IsOpen N ∧ x₀ ∈ N ∧
    HolAlong N φ ∧ (∀ x ∈ N, φ x ≠ 0 ↔ Inner x) ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ),
      IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ N) → ∀ b₀ ∈ B, ∃ (C : ℝ) (k : ℕ), ∀ᶠ b in 𝓝 b₀, Inner (a b).1 →
        ‖h (a b)‖ ≤ C * (1 + |Real.log ‖φ (a b).1‖|) ^ k ∧ ‖(h (a b))⁻¹‖ ≤ C * (1 + |Real.log ‖φ (a b).1‖|) ^ k

def HorFn (τ : E →+* ℂ) (h : CxFr Z σ → ℂ) : Prop :=
  (∀ a, Inner a.1 → h a ≠ 0) ∧
  (∀ a a' M N, Inner a.1 → Chg a a' τ M → Chg a a' (conjEmb τ) N → h a' * M.det = h a * N.det) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ),
    IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → DifferentiableOn ℂ (fun b => h (a b)) B) ∧
  LogGrowth h

abbrev ExpMaps (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) : Type :=
  ∀ x : CxPts (genStr Z) σ, (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)

def IsExpChart {n g : ℕ} (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) : Prop :=
  e.target = Metric.ball 0 1 ∧ (∀ k, HolAlong e.source fun x => e x k) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧
  (∀ x ∈ e.source, ∀ v w, ex x (v + w) = ex x v * ex x w) ∧
  IsHolTo (e.target ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun zw => (ex (e.symm zw.1) zw.2).left) ∧
  ∀ x ∈ e.source, (∀ w, ∃! v, IsTanAtG Z.t (x.1 ≫ genι Z) v ∧ IsDerivAt0 (fun u => (ex x u).left) w v) ∧
    ∀ v, IsTanAtG Z.t (x.1 ≫ genι Z) v → ∃! w, IsDerivAt0 (fun u => (ex x u).left) w v

def IsLogChart {n g r : ℕ} (a : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g)
    (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ) : Prop :=
  IsExpChart e ex ∧ (∀ x ∈ e.source, Inner x ↔ ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0) ∧
  ContinuousOn lam (logDom n a) ∧
  (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧
    (∀ w, ex (e.symm (logExp a s)) w = 1 ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧
    ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧
  ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) →
    ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k

end GlobalTheory.ShFam.Hor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EffCartierOfProportionalSections
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EffCartierOfProportionalSections
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

namespace GlobalTheory.ProjBlowup

theorem mem_nonZeroDivisors_of_dense_compl_support {W T : Scheme.{0}} (I : W.IdealSheafData) (d : T ⟶ W)
    [IsSchemeTheoreticallyDominant d] [QuasiCompact d] (hd : ∀ t : T, d t ∉ I.support)
    (A : W.affineOpens) (s : Γ(W, A.1)) (hs : I.ideal A = Ideal.span {s}) : s ∈ nonZeroDivisors Γ(W, A.1) := by
  have hu : IsUnit (d.app A.1 s) := by
    refine T.toRingedSpace.isUnit_of_isUnit_germ _ _ fun t ht => ?_
    refine (T.mem_basicOpen _ t ht).1 ?_
    rw [← Scheme.preimage_basicOpen]
    have h := hd t
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := A) ht, hs, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton] at h
    exact not_not.1 h
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply d.app_injective A.1
  have h := congrArg (d.app A.1) hx
  rw [map_mul, map_zero] at h
  rw [map_zero]
  exact hu.mul_left_eq_zero.1 h

theorem effCartier_of_proportional (R : Type) [CommRing R] (X W T : Scheme.{0}) (I : W.IdealSheafData) (L : LB X)
    (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (d : T ⟶ W)
    (hI : GeneratesAlong I σ g) (hp : Proportional σ g ψ) (h₁ : IsSchemeTheoreticallyDominant d)
    (h₂ : QuasiCompact d) (hd : ∀ t : T, d t ∉ I.support) : FinalTheorems.EffCartier I := by
  intro w
  obtain ⟨k, hk⟩ : ∃ k, w ∈ g ⁻¹ᵁ L.U k :=
    TopologicalSpace.Opens.mem_iSup.1 (hI.1.ge (show w ∈ (⊤ : W.Opens) from trivial))
  obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart R m (ψ w)
  obtain ⟨A, hA, hw, hle⟩ := exists_isAffineOpen_mem_and_subset
    (show w ∈ g ⁻¹ᵁ L.U k ⊓ ψ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R m i from ⟨hk, hi⟩)
  have hAk : A ≤ g ⁻¹ᵁ L.U k := fun x hx => (hle hx).1
  have hAi : A ≤ ψ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R m i := fun x hx => (hle hx).2
  have hs : I.ideal ⟨A, hA⟩ = Ideal.span {(g.appLE (L.U k) A hAk).hom ((σ i).f k)} := by
    rw [hI.2 k ⟨A, hA⟩ hAk]
    refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨i, rfl⟩))
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_span_singleton'.2 ⟨_, (hp A k hAk i hAi j).symm⟩
  exact ⟨⟨A, hA⟩, _, hw, mem_nonZeroDivisors_of_dense_compl_support I d hd ⟨A, hA⟩ _ hs, hs⟩

end GlobalTheory.ProjBlowup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EffCartierOfProportionalSectionsStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effCartier_of_proportional_sections : ∀ (R : Type) [CommRing R] (X W T : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (d : T ⟶ W), GeneratesAlong I σ g → Proportional σ g ψ → IsSchemeTheoreticallyDominant d → QuasiCompact d → (∀ t : T, d t ∉ I.support) → FinalTheorems.EffCartier I := by
  first | exact @GlobalTheory.ProjBlowup.effCartier_of_proportional | exact GlobalTheory.ProjBlowup.effCartier_of_proportional | (intros; apply GlobalTheory.ProjBlowup.effCartier_of_proportional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfProportionalToGeneratingSections
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfProportionalToGeneratingSections
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

theorem Proportional.basicOpen_le_chart {R : Type} [CommRing R] {X W : Scheme.{0}} {L : LB X} {m : ℕ}
    {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (h : Proportional σ g ψ)
    (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : Fin (m + 1)) :
    W.basicOpen ((g.appLE (L.U k) A hk).hom ((σ i).f k)) ≤ ψ ⁻¹ᵁ chart R m i := by
  intro z hz
  obtain ⟨i', hi'⟩ := (isCoordFamily_pullRatio ψ).exists_mem z
  have hA : z ∈ A := W.basicOpen_le _ hz
  have e := h (A ⊓ ψ ⁻¹ᵁ chart R m i') k (inf_le_left.trans hk) i' inf_le_right i
  have e' := congrArg W.basicOpen e
  rw [Scheme.basicOpen_mul, basicOpen_pullRatio, Scheme.basicOpen_appLE] at e'
  rw [Scheme.basicOpen_appLE] at hz
  have hz' : z ∈ (A ⊓ ψ ⁻¹ᵁ chart R m i') ⊓ g ⁻¹ᵁ X.basicOpen ((σ i).f k) := ⟨⟨hA, hi'⟩, hz.2⟩
  exact (e'.le hz').1.2

theorem eq_of_proportional :
    ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ ψ' : W ⟶ PSpace R m), GeneratesAlong ⊤ σ g → ψ ≫ PSpace.str R m = ψ' ≫ PSpace.str R m → Proportional σ g ψ → Proportional σ g ψ' → ψ = ψ' := by
  intro R _ X W L m σ g ψ ψ' hG hs h h'
  refine hom_ext hs fun y => ?_
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hG.1.ge (Set.mem_univ y))
  obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAk⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open hk (g ⁻¹ᵁ L.U k).isOpen
  have hAk' : A ≤ g ⁻¹ᵁ L.U k := hAk
  have hsp := hG.2 k ⟨A, hA⟩ hAk'
  have hsp' : Ideal.span (Set.range fun j => (g.appLE (L.U k) A hAk').hom ((σ j).f k)) = ⊤ := hsp.symm
  have hcov := (IsAffineOpen.self_le_iSup_basicOpen_iff hA).2 hsp'
  obtain ⟨⟨_, i, rfl⟩, hi⟩ := Opens.mem_iSup.1 (hcov hyA)
  have hB := W.basicOpen_le ((g.appLE (L.U k) A hAk').hom ((σ i).f k))
  refine ⟨_, hi, i, h.basicOpen_le_chart A k hAk' i, h'.basicOpen_le_chart A k hAk' i, fun j => ?_⟩
  have hu : IsUnit ((g.appLE (L.U k) _ (hB.trans hAk')).hom ((σ i).f k)) := by
    rw [← resG_appLE g hAk' hB]
    exact RingedSpace.isUnit_res_basicOpen _ _
  exact hu.mul_right_cancel ((h _ k _ i _ j).symm.trans (h' _ k _ i _ j))

end GlobalTheory.ProjBlowup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfProportionalToGeneratingSectionsStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_proportional_to_generating_sections : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ ψ' : W ⟶ PSpace R m), GeneratesAlong ⊤ σ g → ψ ≫ PSpace.str R m = ψ' ≫ PSpace.str R m → Proportional σ g ψ → Proportional σ g ψ' → ψ = ψ' := by
  first | exact @GlobalTheory.ProjBlowup.eq_of_proportional | exact GlobalTheory.ProjBlowup.eq_of_proportional | (intros; apply GlobalTheory.ProjBlowup.eq_of_proportional <;> assumption)
end
end

noncomputable section

section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjBlowup

theorem eq_top_of_forall_notMem {W : Scheme.{0}} (I : W.IdealSheafData) (h : ∀ w, w ∉ I.support) : I = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, eq_bot_iff]
  exact fun w hw => (h w hw).elim

theorem effCartier_top (W : Scheme.{0}) : FinalTheorems.EffCartier (⊤ : W.IdealSheafData) := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, 1, hx, one_mem _, by simp⟩

theorem mem_support_comap {W X : Scheme.{0}} (J : X.IdealSheafData) (g : W ⟶ X) (w : W) :
    w ∈ (J.comap g).support ↔ g w ∈ J.support := by
  rw [Scheme.IdealSheafData.support_comap]; rfl

theorem exists_blowup {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) :
    ∃ (X' : Scheme.{0}) (b : X' ⟶ X), FinalTheorems.Blowup b J ∧ IsProjOver (b ≫ s) ∧
      ∀ V : X.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (b ∣_ V) := by
  obtain ⟨L, m, σ, hσ⟩ := GlobalTheory.T.exists_sections_generate_ideal_projective R X s hs J
  have : IsProper (PSpace.str R m) := isProper_str R m
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let U : X.Opens := J.support.compl
  have hU : ∀ x : U.toScheme, U.ι x ∉ J.support := fun x => x.2
  have htop : ∀ {W : Scheme.{0}} (g : W ⟶ X), (∀ w, g w ∉ J.support) → J.comap g = ⊤ := fun g hg =>
    eq_top_of_forall_notMem _ fun w hw => hg w ((mem_support_comap J g w).1 hw)
  obtain ⟨φ, hφ, hφσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X U _ L m σ U.ι (U.ι ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ U.ι hσ)
    (by rw [htop _ hU]; exact effCartier_top _)
  let b := graphClosure.fst s (PSpace.str R m) U.ι φ hφ.symm
  let c := graphClosure.snd s (PSpace.str R m) U.ι φ hφ.symm
  let j := graphClosure.incl s (PSpace.str R m) U.ι φ hφ.symm
  have hjb : j ≫ b = U.ι := graphClosure.incl_fst ..
  have hjc : j ≫ c = φ := graphClosure.incl_snd ..
  have hbc : Proportional σ b c := .of_comp j (by rwa [hjb, hjc])
  refine ⟨_, b, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance inferInstance fun t => ?_,
    fun W g hg => ?_⟩, ?_,
    fun V hV => graphClosure.isIso_fst_restrict_of_le _ _ _ _ _ V (by rw [Scheme.Opens.opensRange_ι]; exact hV)⟩
  · rw [mem_support_comap, ← Scheme.Hom.comp_apply, hjb]; exact hU t
  · obtain ⟨ψ, hψ, hψσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X W _ L m σ g (g ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ g hσ) hg
    have hd := GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier W _ hg
    let d := Scheme.Opens.ι (X := W) (J.comap g).support.compl
    have hdU : ∀ t, (d ≫ g) t ∉ J.support := fun t ht => t.2 ((mem_support_comap J g _).2 ht)
    let w := IsOpenImmersion.lift U.ι (d ≫ g) (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨_, hdU t⟩, rfl⟩)
    have hw : w ≫ U.ι = d ≫ g := IsOpenImmersion.lift_fac ..
    have hw' : d ≫ ψ = w ≫ φ := GlobalTheory.T.eq_of_proportional_to_generating_sections R X _ L m σ (d ≫ g) _ _ (htop _ hdU ▸ GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ (d ≫ g) hσ)
      (by rw [Category.assoc, hψ, Category.assoc, hφ, reassoc_of% hw]) (hψσ.comp d) (hw ▸ hφσ.comp w)
    have key : ∀ h : W ⟶ _, h ≫ b = g → d ≫ h = w ≫ j := fun h hh => by
      have H := graphClosure.isPullback_incl s (PSpace.str R m) U.ι φ hφ.symm
      have e : w ≫ U.ι = (d ≫ h) ≫ b := by rw [hw, Category.assoc, hh]
      have h1 := H.lift_fst w (d ≫ h) e
      rw [Category.comp_id] at h1
      rw [← H.lift_snd w (d ≫ h) e, h1]
    have hl := graphClosure.lift_fst s (PSpace.str R m) U.ι φ hφ.symm g ψ hψ.symm d w hw.symm hw'
    exact ⟨_, hl, fun h hh => hom_ext_of_isSchemeTheoreticallyDominant d b ((key h hh).trans (key _ hl).symm)
      (hh.trans hl.symm)⟩
  · obtain ⟨n, i, hi, e⟩ := ProjSpace.isProjOver_of_isPullback (IsPullback.of_hasPullback s (PSpace.str R m)) hs
      (ProjSpace.isProjOver_pspace_str R m)
    exact ⟨n, graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm ≫ i, inferInstance, by
      rw [Category.assoc, e, graphClosure.ι_fst_assoc]⟩

end GlobalTheory.ProjBlowup

end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.ProjBlowup

section
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isDiscreteValuationRing_coeff {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    IsDiscreteValuationRing (c.V W) := by
  have := c.fin
  have : NumberField c.F := {}
  refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

end

end GlobalTheory.ProjBlowup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp
  tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag


attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in
instance tanAddCommGroup {X : Scheme.{0}} {S : Type} [CommRing S] (x : Sp S ⟶ X) (G : Over X) [GrpObj G]
    [IsCommMonObj G] : AddCommGroup (TanM x G) := inferInstance

section Bundles

structure Charts (X : Scheme.{0}) : Type 1 where
  ι : Type
  [fin : Finite ι]
  R : ι → Type
  [ring : ∀ a, CommRing (R a)]
  χ : ∀ a, Sp (R a) ⟶ X
  opn : ∀ a, IsOpenImmersion (χ a)

attribute [instance] Charts.fin Charts.ring Charts.opn

def Charts.carrier {X : Scheme.{0}} (ch : Charts X) : Set X := ⋃ a, Set.range (ch.χ a)

structure Coc (Z : Scheme.{0}) : Type 1 where
  A : Type
  B : A → Z.Opens
  aff : ∀ α, IsAffineOpen (B α)
  cover : ∀ x : Z, ∃ α, x ∈ B α
  n : A → ℕ
  T : ∀ α β, Matrix (Fin (n α)) (Fin (n β)) Γ(Z, B α ⊓ B β)
  refl : ∀ (α : A) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ B α),
    (T α α).map (ev z _ (le_preimage_inf h h)) = 1
  coc : ∀ (α β γ : A) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hα : ⊤ ≤ z ⁻¹ᵁ B α) (hβ : ⊤ ≤ z ⁻¹ᵁ B β)
    (hγ : ⊤ ≤ z ⁻¹ᵁ B γ), (T α β).map (ev z _ (le_preimage_inf hα hβ)) * (T β γ).map (ev z _ (le_preimage_inf hβ hγ)) =
      (T α γ).map (ev z _ (le_preimage_inf hα hγ))

namespace Coc

variable {Z Z' : Scheme.{0}} (C : Coc Z) {S S' : Type} [CommRing S] [CommRing S']



end Coc

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Tan

variable {X : Scheme.{0}} {t : SAB H X} {S S' : Type} [CommRing S] [CommRing S']



variable {Z : Scheme.{0}} {π : Z ⟶ X} {U : Z.Opens} {hU : IsAffineOpen U} {κ : Type} [Finite κ]

end Tan

section Atlas

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}

structure PreAtlas (M : Model Xo c V.subtype) (X : Scheme.{0}) : Type 1 where
  ch : Charts X
  alg : ∀ a, c.F →+* ch.R a
  fr : ∀ a, Vecs Dw M.t (ch.R a)

def PreAtlas.FlagAt {M : Model Xo c V.subtype} {X : Scheme.{0}} (A : PreAtlas M X) (π : X ⟶ M.X)
    (ty : (E →+* ℂ) → Finset ℕ) {k : Type} [Field k] (w : Sp k ⟶ X) (u : Vecs Dw M.t k) : Prop :=
  ∃ (a : A.ch.ι) (φ : A.ch.R a →+* k), spMap φ ≫ A.ch.χ a = w ∧
    LocM.IsFrame M.t (φ.comp (A.alg a)) (w ≫ π) u ∧ SameFlag ty M.t (w ≫ π) ((A.fr a).bc φ) u

structure Atlas (M : Model Xo c V.subtype) {X : Scheme.{0}} (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) : Type 1
    extends PreAtlas M X where
  cover : ch.carrier = π ⁻¹' Set.range M.j
  alg_s : ∀ a, ch.χ a ≫ π ≫ M.s = spMap ((alg a).comp V.subtype)
  smooth : ∀ a, Smooth (ch.χ a ≫ π)
  frame : ∀ a, LocM.IsFrame M.t (alg a) (ch.χ a ≫ π) (fr a)
  glue : ∀ (k : Type) [Field k] (a a' : ch.ι) (φ : ch.R a →+* k) (φ' : ch.R a' →+* k),
    spMap φ ≫ ch.χ a = spMap φ' ≫ ch.χ a' → SameFlag ty M.t (spMap φ ≫ ch.χ a ≫ π) ((fr a).bc φ) ((fr a').bc φ')
  bij : ∀ (k : Type) [Field k] (f : c.F →+* k) (y : Sp k ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f →
    ∀ u, LocM.IsFrame M.t f (y ≫ M.j) u → ∃! w : Sp k ⟶ X, w ≫ π = y ≫ M.j ∧ toPreAtlas.FlagAt π ty w u

variable {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

namespace Atlas

variable (A : Atlas M π ty) {S : Type} [CommRing S] {K : Type} [Field K]

end Atlas

namespace Atlas

variable (A : Atlas M π ty) {S : Type} [CommRing S] {K : Type} [Field K]

end Atlas

variable {A : Atlas M π ty} {σ : E →+* ℂ} {k r : ℕ}

end Atlas

section Maps

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {i : Idx H p} {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ}

end Maps

end GlobalTheory.DRFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletion
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary

theorem vAlg {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

theorem v_qOf {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (hp : (qOf P).Prime)
    (h2 : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
  have e : ((qOf P : ℕ) : P.adicCompletion E) = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E)) := by
    simp
  rw [e, vAlg, HeightOneSpectrum.valuation_of_algebraMap]
  have hmem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal ^ 1 := by
    rw [pow_one]
    exact Ideal.absNorm_mem P.asIdeal
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 1).2 hmem
  have h2' : ¬ P.intValuation ((qOf P : ℕ) : 𝓞 E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
    h2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 2).1 h)
  have hne : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0 := by
    have : ((qOf P : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    exact (HeightOneSpectrum.intValuation_ne_zero P _ this)
  rw [← WithZero.exp_log hne] at h1 h2' ⊢
  rw [WithZero.exp_le_exp] at h1 h2'
  congr 1
  push_cast at h1 h2'
  omega

theorem exists_clear {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (y : FiniteAdeleRing (𝓞 E) E)
    (hP : Valued.v (y P) ≤ 1) : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * y Q) ≤ 1 := by
  have hfin : {Q : HeightOneSpectrum (𝓞 E) | ¬ y Q ∈ Q.adicCompletionIntegers E}.Finite :=
    Filter.eventually_cofinite.1 y.2
  set S := hfin.toFinset with hS
  have memS : ∀ Q, Q ∈ S ↔ 1 < Valued.v (y Q) := by
    intro Q
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, not_le]
  have hPS : P ∉ S := fun h => absurd hP (not_le.2 ((memS P).1 h))
  let m : HeightOneSpectrum (𝓞 E) → ℕ := fun Q => (WithZero.log (Valued.v (y Q))).toNat
  let J : Ideal (𝓞 E) := ∏ Q ∈ S, Q.asIdeal ^ m Q
  have hJ : ¬ J ≤ P.asIdeal := by
    intro h
    obtain ⟨Q, hQ, hle⟩ := (Ideal.IsPrime.prod_le P.isPrime).1 h
    have h1 : Q.asIdeal ≤ P.asIdeal := by
      by_cases hm : m Q = 0
      · exfalso
        have h3 := (memS Q).1 hQ
        have hne : Valued.v (y Q) ≠ 0 := ne_of_gt (lt_trans zero_lt_one h3)
        rw [← WithZero.exp_log hne] at h3
        have h4 : (0 : ℤ) < WithZero.log (Valued.v (y Q)) := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
          exact h3
        have : m Q ≠ 0 := by
          show (WithZero.log (Valued.v (y Q))).toNat ≠ 0
          omega
        exact this hm
      · exact P.isPrime.le_of_pow_le hle
    have h2 : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1)
    exact hPS (h2 ▸ hQ)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJ
  refine ⟨s, hsP, fun Q => ?_⟩
  rw [map_mul, vAlg, HeightOneSpectrum.valuation_of_algebraMap]
  by_cases hQ : Q ∈ S
  · have hsQ : s ∈ Q.asIdeal ^ m Q :=
      (Finset.inf_le (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal ^ m Q) hQ) (Ideal.prod_le_inf hsJ)
    have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem Q s (m Q)).2 hsQ
    have hne : Valued.v (y Q) ≠ 0 := ne_of_gt (lt_trans zero_lt_one ((memS Q).1 hQ))
    have h2 : Valued.v (y Q) ≤ WithZero.exp ((m Q : ℕ) : ℤ) := by
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      show WithZero.log (Valued.v (y Q)) ≤ ((WithZero.log (Valued.v (y Q))).toNat : ℤ)
      omega
    calc Q.intValuation s * Valued.v (y Q) ≤ WithZero.exp (-((m Q : ℕ) : ℤ)) * WithZero.exp ((m Q : ℕ) : ℤ) :=
          mul_le_mul' h1 h2
      _ = 1 := by rw [← WithZero.exp_add]; simp
  · have h1 : Valued.v (y Q) ≤ 1 := not_lt.1 fun h => hQ ((memS Q).2 h)
    exact mul_le_one' (HeightOneSpectrum.intValuation_le_one Q s) h1

theorem intAtA_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (x : AfE F E) :
    IntAtA (F := F) P x ↔ Valued.v (adAt F P x) ≤ 1 := by
  constructor
  · intro h
    exact GlobalTheory.TwU.IsAdIso.val_le (ι := afIso F E) ⟨afIso_tmul_one F E, mem_rInt_iff F E⟩ h
  · intro h
    obtain ⟨s, hs, hall⟩ := exists_clear P (afIso F E x) h
    refine ⟨s, hs, ?_⟩
    show _ ∈ RInt F E
    rw [mem_rInt_iff]
    intro Q
    have e : afIso F E (iA F E (algebraMap (𝓞 E) E s) * x) Q =
        algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * afIso F E x Q := by
      rw [map_mul]
      have h2 : afIso F E (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) :=
        afIso_tmul_one F E _
      rw [h2]
      rfl
    rw [e]
    exact hall Q

theorem entry_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    {n : ℕ} (N : ℕ) (z : GL (Fin n) (AfE F E)) (r s : Fin n) :
    IntAtA (F := F) P (iA F E (((qOf P : ℕ) : E) ^ N)⁻¹ * ((z : Matrix (Fin n) (Fin n) (AfE F E)) - 1) r s) ↔
      Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  rw [intAtA_iff, map_mul, adAt_inclE, Matrix.sub_apply, map_sub]
  have h1 : adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
  rw [h1, map_mul, map_inv₀, map_pow, map_natCast, map_inv₀, map_pow, hq]
  have hE : (WithZero.exp (-1 : ℤ) ^ N)⁻¹ = WithZero.exp (N : ℤ) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_neg]
    congr 1
    simp
  rw [hE]
  generalize Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) = x
  have hm : WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) = 1 := by
    rw [← WithZero.exp_add]; simp
  constructor
  · intro h
    calc x = (WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ)) * x := by rw [hm, one_mul]
      _ = WithZero.exp (-(N : ℤ)) * (WithZero.exp (N : ℤ) * x) := mul_assoc _ _ _
      _ ≤ WithZero.exp (-(N : ℤ)) * 1 := mul_le_mul' le_rfl h
      _ = WithZero.exp (-(N : ℤ)) := mul_one _
  · intro h
    calc WithZero.exp (N : ℤ) * x ≤ WithZero.exp (N : ℤ) * WithZero.exp (-(N : ℤ)) := mul_le_mul' le_rfl h
      _ = 1 := by rw [mul_comm, hm]

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n N : ℕ) (P : SBof I a) (z : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 ∧ Valued.v ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) = WithZero.exp (-1 : ℤ) ∧ (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z ↔ ∀ r s, Valued.v (adAt B.host.F P.1 (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) := by
  intro B X I hI l Z a n N P z
  have hseam : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    ext x
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 x
  have hdeg := degOne_of_ok hI a P
  have hq := v_qOf P.1 hdeg.1 hdeg.2
  refine ⟨hseam, hq, ?_⟩
  rw [hseam]
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact forall_congr' fun r => forall_congr' fun s => @entry_iff (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ P.1 hq n N z r s
end GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n N : ℕ) (P : SBof I a) (z : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 ∧ Valued.v ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) = WithZero.exp (-1 : ℤ) ∧ (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z ↔ ∀ r s, Valued.v (adAt B.host.F P.1 (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main | exact GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main | (intros; apply GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorHolo

section Hol

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X Z : Scheme.{0}}

theorem isHolTo_of_openImmersion (i : X ⟶ Z) [IsOpenImmersion i] {B : Set W} {y : W → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have hU : i ⁻¹ᵁ (i ''ᵁ U) = U := i.preimage_image_eq U
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [← ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp] at this
    exact this
  exact key U hU f

theorem isHolTo_const {B : Set W} (hB : IsOpen B) (x : Sp ℂ ⟶ X) : IsHolTo B fun _ => x := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simpa only [h, and_true, Set.ofPred_mem_eq] using hB
  · simpa only [h, and_false, Set.ofPred_false] using isOpen_empty

theorem isHolTo_of_fst {S : Scheme.{0}} (p : X ⟶ Z) (q : S ⟶ Z) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    {y : (Fin n → ℂ) → (Sp ℂ ⟶ pullback p q)} (s : Sp ℂ ⟶ S) (hs : ∀ b, y b ≫ pullback.snd _ _ = s)
    (h : IsHolTo B fun b => y b ≫ pullback.fst _ _) : IsHolTo B y := by
  have he : ∀ b, (y b ≫ pullback.fst p q) ≫ p = s ≫ q := fun b => by
    rw [← hs b, Category.assoc, Category.assoc, pullback.condition]
  refine LocLift.isHolTo_congr (holPair _ _ _ p q n B _ (fun _ => s) he hB h (isHolTo_const hB s)) fun b _ => ?_
  exact pullback.hom_ext (pullback.lift_fst _ _ _).symm ((hs b).trans (pullback.lift_snd _ _ _).symm)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem continuousOn_of_isHolTo {B : Set W} {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1) :
    ContinuousOn y B := by
  rw [continuousOn_iff_continuous_domRestrict, CxPts.continuous_iff]
  intro U
  refine ⟨?_, fun f => ?_⟩
  · convert (h U 0).1.preimage (continuous_subtype_val (p := (· ∈ B))) using 1
    ext b
    exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
  · exact (h U f).2.continuousOn.comp continuous_subtype_val.continuousOn fun b hb => ⟨b.2, hb⟩

theorem differentiableAt_chart {B : Set W} (hB : IsOpen B) {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1)
    (ch : AlgChart p σ D) {b : W} (hb : b ∈ B) (hy : y b ∈ ch.e.source) :
    DifferentiableAt ℂ (fun v => ch.e (y v)) b := by
  refine (differentiableAt_piLp 2).2 fun a => ?_
  have h1 := ((h ch.U (ch.x a)).2).differentiableAt ((h ch.U (ch.x a)).1.mem_nhds ⟨hb, ch.source_subset hy⟩)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [((continuousOn_of_isHolTo h).continuousAt (hB.mem_nhds hb)).preimage_mem_nhds
    (ch.e.open_source.mem_nhds hy)] with v hv
  exact ch.apply_eq _ hv a

theorem isHolTo_symm (ch : AlgChart p σ D) : IsHolTo ch.e.target fun v => (ch.e.symm v).1 := fun U f =>
  ⟨ChartGlue.isOpen_over ch.e (isOpen_ptsIn U), ch.holo U f⟩

end Hol

section Frames

open GlobalTheory.TorsionHolomorphic ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (X : Data E r) {B : Set W}

theorem differentiableOn_perFr {x : W → Frame X.Ψ r} (hx : ∀ b ∈ B, x b ∈ X.dom)
    (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b) τ a c) B) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    DifferentiableOn ℂ (fun b => perFr X (x b) v τ i) B := by
  unfold perFr
  split_ifs with h1 h2 h3 h4
  · simp only [mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun a _ =>
      (differentiableOn_matrix_inv _ B (hd _) (fun b hb => (hx b hb _).1) _ _).mul_const _
  · exact differentiableOn_const _
  · simp only [hermC]
    exact DifferentiableOn.fun_sum fun a _ => DifferentiableOn.fun_sum fun c _ =>
      ((hd _ _ _).mul_const _).mul_const _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

theorem differentiable_stdMat [Fintype Tau] (hj : j ≤ r) (κ : Tau ≃ X.Ψ) (τ : X.Ψ) (a c : Fin r) :
    Differentiable ℂ fun v => mat (stdMat X hj κ (unflat v)) τ a c := by
  refine differentiableOn_univ.1 (differentiableOn_matrix_mul (fun _ => mat (x0F X) τ)
    (fun v => reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) _
    (fun _ _ => differentiableOn_const _) (fun a c => ?_) a c)
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm]
  rcases idx hj a with a | a <;> rcases idx hj c with c | c
  · exact differentiableOn_const _
  · exact differentiableOn_apply (κ.symm τ, a, c) _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ} {U : Unf Xo c σ r}

end Frames

end GlobalTheory.TrueCx.TorHolo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.ModelPresentation

theorem exists_epi_twist_free {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}} (ι : X ⟶ PSpace R N)
    [IsClosedImmersion ι] (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] :
    ∃ (a m : ℕ) (φ : GlobalTheory.twist (GlobalTheory.QCoh.freeModule X (Fin m)) ((GlobalTheory.ProjSpace.On R N (-(a : ℤ))).pull ι) ⟶ F),
      Epi φ := by
  have hA := (GlobalTheory.isAmple_projective_O_one R N).pull_of_isClosedImmersion ι
  have hL := hA.isLB
  obtain ⟨a, ha⟩ := (tendsto_natCast_atTop_atTop.eventually (hA.eventually_isGloballyGenerated_twistZ F)).exists
  obtain ⟨k, s, hs⟩ := GlobalTheory.QCoh.isGloballyGenerated_iff_spanStalks.1 ha
  have h₁ := (GlobalTheory.QCoh.epi_sectionsHom_iff s).2 hs
  have h₂ := (GlobalTheory.Twist.epi_map_iff (GlobalTheory.Twist.isLB_lbZPow hL (-(a : ℤ))) (GlobalTheory.QCoh.sectionsHom s)).2 h₁
  exact ⟨a, k, (GlobalTheory.Twist.twistZPullIso ι (GlobalTheory.ProjSpace.O1_isLB R N) _ (-(a : ℤ))).inv ≫
    GlobalTheory.Twist.map _ (GlobalTheory.QCoh.sectionsHom s) ≫ (GlobalTheory.Twist.twistZAddIso F hL (add_neg_cancel (a : ℤ))).hom ≫
    (GlobalTheory.Twist.twistZZeroIso F hL).inv, inferInstance⟩

theorem nonempty_cokernel_iso {C : Type*} [Category C] [Abelian C] {A B F : C} (φ : B ⟶ F) [Epi φ]
    (ψ : A ⟶ kernel φ) [Epi ψ] : Nonempty (cokernel (ψ ≫ kernel.ι φ) ≅ F) :=
  ⟨cokernelEpiComp ψ (kernel.ι φ) ≪≫ (cokernelIsCokernel (kernel.ι φ)).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι φ) (kernel.condition φ)) (kernelIsKernel φ))⟩

theorem isNoetherianRing_place {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    IsNoetherianRing (c.V W) := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsDiscreteValuationRing (c.V W) := by
    refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  infer_instance

theorem nonempty_ofMod_toMod_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀) (F : Z.X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], Nonempty ((Z.ofMod F).toMod ≅ F) := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z F _
  have := isNoetherianRing_place Z.i.c W hp.ne_zero hW
  have : IsProper (PSpace.str (Z.i.c.V W) Z.n) := isProper_str _ _
  have : IsLocallyNoetherian Z.X :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.I.subschemeι ≫ PSpace.str (Z.i.c.V W) Z.n)
  obtain ⟨a, m, φ, hφ⟩ := exists_epi_twist_free Z.I.subschemeι F
  have := GlobalTheory.Twist.isFiniteQC_twist (F := GlobalTheory.QCoh.freeModule Z.X (Fin m))
    (LB.isLB_pull (GlobalTheory.ProjSpace.On_isLB (Z.i.c.V W) Z.n (-(a : ℤ))) Z.I.subschemeι)
  obtain ⟨a', m', ψ, hψ⟩ := exists_epi_twist_free Z.I.subschemeι (kernel φ)
  have h : ∃ S : Z.Sh, Nonempty (S.toMod ≅ F) :=
    ⟨⟨a, m, a', m', ψ ≫ kernel.ι φ⟩, nonempty_cokernel_iso φ ψ⟩
  rw [Mdl.ofMod, dite_eq_left h]
  exact h.choose_spec

end GlobalTheory.ModelPresentation
end
