module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanChangesByScalarOfTrivialAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalStabiliserScalesRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalStabiliserScalesRestriction
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SourceUnip

open GlobalTheory.MixModel GlobalTheory.UnipMean

variable {D : D7} {V V' W : HSp D} {r : ℕ}

theorem corner_alg {R a b c : Type} [CommRing R] [Fintype b] [Fintype c] {x1 : Matrix a b R} {m p q : Matrix b b R}
    {C' : Matrix b c R} {B : Matrix c b R} (hq : q = C' * B) (hp : x1 * p = 0)
    (r3 : m = p * m + m * q - p * m * q) : x1 * m = x1 * m * C' * B := by
  have a1 : x1 * (p * m) = 0 := by rw [← Matrix.mul_assoc, hp, Matrix.zero_mul]
  have a2 : x1 * (p * m * q) = 0 := by rw [← Matrix.mul_assoc, a1, Matrix.zero_mul]
  calc x1 * m = x1 * (p * m + m * q - p * m * q) := by rw [← r3]
    _ = x1 * (p * m) + x1 * (m * q) - x1 * (p * m * q) := by rw [Matrix.mul_sub, Matrix.mul_add]
    _ = x1 * m * C' * B := by rw [a1, a2, zero_add, sub_zero, hq]; simp only [Matrix.mul_assoc]

theorem hO_iso (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : WO V W) (y : Mx D W.rank r) :
    hO V W x (y ⬝ rat (Cᴴ * V.gram)) = (adj y ⬝ (gA W ⬝ (x ⬝ rat C))).trace := by
  rw [hO_eq_trace, rat_mul, rat_conjTranspose, adj_mul, adj_mul, adj_adj, ← gA, adj_gA]
  simp only [Matrix.mul_assoc, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplO_iso_of (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : WO V W} (hx : x ⬝ rat C = 0)
    (y : Mx D W.rank r) : symplO V W x (y ⬝ rat (Cᴴ * V.gram)) = 0 := by
  rw [symplO_eq, hO_iso, hx, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]

theorem mulC_eq_zero_of_symplO (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : WO V W}
    (h : ∀ y : Mx D W.rank r, symplO V W x (y ⬝ rat (Cᴴ * V.gram)) = 0) : x ⬝ rat C = 0 := by
  obtain ⟨u, hu⟩ : ∃ u : Mx D W.rank r, u = gA W ⬝ (x ⬝ rat C) := ⟨_, rfl⟩
  have hu0 : u = 0 := by
    ext i j
    have key : ∀ w : AE D, Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * u i j * w) = 0 := fun w => by
      have := h (adj (Matrix.single j i w : Mx D r W.rank))
      rw [symplO_eq, hO_iso, adj_adj, ← hu, trace_single_mul', ← mul_assoc] at this
      exact this
    have hz := eq_zero_of_trace_mul (F := D.host.F) (E := D.host.E) (R := AF D.host.F) _ key
    have hξ : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]
    have := congrArg (incA D D.host.xi0⁻¹ * ·) hz
    simpa [← mul_assoc, hξ] using this
  have e : giA W ⬝ u = giA W ⬝ (gA W ⬝ (x ⬝ rat C)) := by rw [hu]
  rw [giA_gA_cancel, hu0, Matrix.mul_zero] at e
  exact e.symm

theorem iso_mulC {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) (y : Mx D W.rank r) :
    y ⬝ rat (Cᴴ * V.gram) ⬝ rat C = 0 := by
  have h : Cᴴ * V.gram * C = 0 := hC.2.2
  rw [Matrix.mul_assoc, ← rat_mul, h, rat_zero, Matrix.mul_zero]

theorem mid_mulC {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B) (x : WO V' W) :
    x ⬝ rat (V'.gram⁻¹ * Bᴴ * V.gram) ⬝ rat C = 0 := by
  have h0 : Cᴴ * V.gram * B = 0 := hs.orth
  have h1 : Bᴴ * (V.gram * C) = 0 := by
    have := congrArg Matrix.conjTranspose h0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
      Matrix.conjTranspose_zero] at this
  rw [Matrix.mul_assoc, ← rat_mul]
  simp only [Matrix.mul_assoc, h1, Matrix.mul_zero, rat_zero]

section Gen

variable {C : Matrix (Fin V.rank) (Fin r) D.host.E} {C' : Matrix (Fin V.rank) (Fin r) D.host.E}
  {L B₀ : Matrix (Fin r) (Fin V.rank) D.host.E}

theorem gen_fix_iso (h : IsDualPair V C C' L B₀) {g : GA D V} (g2 : rat B₀ ⬝ (mt V g - 1) = 0)
    (y : Mx D W.rank r) : actO V W g 1 (y ⬝ rat (Cᴴ * V.gram)) = y ⬝ rat (Cᴴ * V.gram) := by
  have e1 : rat B₀ ⬝ mt V g = rat B₀ := by
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at g2
  have e2 : rat B₀ ⬝ mt V g⁻¹ = rat B₀ := by
    rw [← e1, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one, e1]
  rw [actO_eq, mt_one, Matrix.one_mul, ← h.hB, Matrix.mul_assoc, e2]

theorem gen_move (h : IsDualPair V C C' L B₀) {g : GA D V} (g1 : (mt V g - 1) ⬝ rat C = 0)
    (r3 : mt V g - 1 = rat (C * L) * (mt V g - 1) + (mt V g - 1) * rat (C' * B₀) -
      rat (C * L) * (mt V g - 1) * rat (C' * B₀))
    {x : WO V W} (hx : x ⬝ rat C = 0) :
    ∃ y : Mx D W.rank r, actO V W g 1 x = x + y ⬝ rat (Cᴴ * V.gram) := by
  have e1 : mt V g ⬝ rat C = rat C := by
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at g1
  have e2 : mt V g⁻¹ ⬝ rat C = rat C := by
    rw [← e1, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul, e1]
  obtain ⟨x1, hx1⟩ : ∃ x1 : WO V W, x1 = x ⬝ mt V g⁻¹ := ⟨_, rfl⟩
  have hx1C : x1 ⬝ rat C = 0 := by rw [hx1, Matrix.mul_assoc, e2, hx]
  have hx1p : x1 ⬝ rat (C * L) = 0 := by rw [rat_mul, ← Matrix.mul_assoc, hx1C, Matrix.zero_mul]
  have hx1g : x1 ⬝ mt V g = x := by rw [hx1, Matrix.mul_assoc, mt_inv_mul, Matrix.mul_one]
  have k : x1 ⬝ (mt V g - 1) = x1 ⬝ (mt V g - 1) ⬝ rat C' ⬝ rat B₀ :=
    corner_alg (rat_mul C' B₀) hx1p r3
  refine ⟨-(x1 ⬝ (mt V g - 1) ⬝ rat C'), ?_⟩
  rw [actO_eq, mt_one, Matrix.one_mul, ← h.hB, Matrix.neg_mul, ← k, Matrix.mul_sub, hx1g, Matrix.mul_one, ← hx1]
  abel

end Gen

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem weilRepresentation_source_mul (g g' : GA D V) (f : WO V W → ℂ) : ω (g * g', 1) f = ω (g, 1) (ω (g', 1) f) := by
  have : (g * g', (1 : GA D W)) = (g, 1) * (g', 1) := by simp
  rw [this, map_mul]; rfl

theorem weilRepresentation_source_one (f : WO V W → ℂ) : ω (1, 1) f = f := by
  have : ((1 : GA D V), (1 : GA D W)) = 1 := rfl
  rw [this, map_one]; rfl

theorem unit_product_rescale_disjoint_finsets {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B) (hω : IsWeilDatumO ψ V W χS χT ω)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) {g : GA D V} (hg : g ∈ NI V C) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f, IsThetaFunO ψ V W f →
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (g, 1) f) = c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  have hC := hs.frame
  obtain ⟨C', L, B₀, h⟩ := exists_dualPair hC
  have hP : (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).rank = W.rank := by
    rw [Matrix.rank_one, Fintype.card_fin]
  have hQ : (Cᴴ * V.gram).rank = r := by
    refine le_antisymm ?_ ?_
    · simpa using Matrix.rank_le_card_height (Cᴴ * V.gram)
    · have := Matrix.rank_mul_le_left (Cᴴ * V.gram) C'
      rw [← h.hB] at this ⊢
      rwa [h.BC', Matrix.rank_one, Fintype.card_fin] at this
  have eI : ∀ y : Mx D W.rank r, (HMul.hMul (HMul.hMul ((1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
      (y : Matrix (Fin W.rank) (Fin r) (AE D))) ((Cᴴ * V.gram).map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) =
      y ⬝ rat (Cᴴ * V.gram) := fun y => by
    show rat (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) ⬝ y ⬝ rat (Cᴴ * V.gram) = _
    rw [rat_one, Matrix.one_mul]
  unfold NI at hg
  refine Subgroup.closure_induction (p := fun g _ => ∃ c : ℂ, c ≠ 0 ∧ ∀ f, IsThetaFunO ψ V W f →
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (g, 1) f) = c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨g1, g2, g3⟩
    have g1' : (mt V g - 1) ⬝ rat C = 0 := g1
    obtain ⟨r1, r2, r3⟩ := gen_relations h (x := mt V g - 1) g1' (by rw [h.hB]; exact g2)
      (fun v hv => g3 v (by rw [← h.hB']; exact hv))
    have g2' : rat B₀ ⬝ (mt V g - 1) = 0 := by rw [h.hB]; exact g2
    obtain ⟨c, hc⟩ := GlobalTheory.T.isotropicMean_changes_by_scalar_of_trivial_action D V W W.rank r 1 (Cᴴ * V.gram) hP hQ
      (fun y y' => by rw [eI, eI]; exact symplO_iso_of C (iso_mulC hC y) y') ψ χS χT ω hω μ 𝓨 hcov g 1
      (fun y => by rw [eI]; exact gen_fix_iso h g2' y)
      (fun x hx => by
        obtain ⟨y, hy⟩ := gen_move h g1' r3 (mulC_eq_zero_of_symplO C fun y => by rw [← eI]; exact hx y)
        exact ⟨y, by rw [eI]; exact hy⟩)
    refine ⟨c, Circle.coe_ne_zero c, fun f hf => ?_⟩
    funext x'
    have hm := mid_mulC hs (W := W) x'
    have hh : ∀ (F : WO V W → ℂ) (y : Mx D W.rank r),
        heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') F
          (HMul.hMul (HMul.hMul ((1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
            (y : Matrix (Fin W.rank) (Fin r) (AE D))) ((Cᴴ * V.gram).map (incA D)) :
            Matrix (Fin W.rank) (Fin V.rank) (AE D)) =
          F (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') := fun F y => by
      rw [eI]
      show ψ (symplOH V W _ _) * F _ = _
      have h0 : symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') (y ⬝ rat (Cᴴ * V.gram)) = 0 := symplO_iso_of C hm y
      rw [symplOH_skew]
      unfold symplOH
      rw [h0, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
      rfl
    have := hc f hf (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') (fun y => by rw [eI]; exact symplO_iso_of C hm y)
    simp only [hh] at this
    show ∫ y in 𝓨, ω (g, 1) f _ ∂μ = (c : ℂ) • ∫ y in 𝓨, f _ ∂μ
    rw [this, smul_eq_mul]
  · exact ⟨1, one_ne_zero, fun f _ => by rw [weilRepresentation_source_one, one_smul]⟩
  · rintro a b - - ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c * d, mul_ne_zero hc hd, fun f hf => by
      rw [weilRepresentation_source_mul, ha _ (hω.om_pres _ _ hf), hb f hf, smul_smul]⟩
  · rintro a - ⟨c, hc, ha⟩
    refine ⟨c⁻¹, inv_ne_zero hc, fun f hf => ?_⟩
    have := ha _ (hω.om_pres (a⁻¹, 1) f hf)
    rw [← weilRepresentation_source_mul, mul_inv_cancel, weilRepresentation_source_one] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Main

end GlobalTheory.SourceUnip

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem GlobalTheory.SourceUnip.scal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ g : GA D V, g ∈ NI V C → ∃ c : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (g, 1) f) = c • res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcov g hg
  obtain ⟨c, -, hc⟩ := GlobalTheory.SourceUnip.unit_product_rescale_disjoint_finsets hs hω hcov hg
  exact ⟨c, hc⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalStabiliserScalesRestrictionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_stabiliser_scales_restriction : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ g : GA D V, g ∈ NI V C → ∃ c : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (g, 1) f) = c • res V V' W C B μ 𝓨 f := by
  first | exact @GlobalTheory.SourceUnip.scal | exact GlobalTheory.SourceUnip.scal | (intros; apply GlobalTheory.SourceUnip.scal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersection
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsTer
namespace GlobalTheory.TargetStatementSixOneSixtyEight

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) {y : V} (hy : y ∈ Submodule.span E (L : Set V)) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ c • y ∈ L := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨c1, hc1, h1⟩ := h1
    obtain ⟨c2, hc2, h2⟩ := h2
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add, mul_comm c1 c2, mul_smul, mul_comm c2 c1, mul_smul]
    exact L.add_mem (L.smul_mem c2 h1) (L.smul_mem c1 h2)
  | smul a x _ h =>
    obtain ⟨c0, hc0, h0⟩ := h
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    refine ⟨c0 * (s : RingOfIntegers E), mul_ne_zero hc0 (nonZeroDivisors.coe_ne_zero s), ?_⟩
    have key : (s : RingOfIntegers E) • (a • x) = b • x := by
      rw [← algebraMap_smul E (s : RingOfIntegers E), smul_smul, mul_comm, hs, algebraMap_smul]
    rw [mul_smul, key, smul_comm c0 b x]
    exact L.smul_mem b h0

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module E V] [inst_4 : Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (L : Submodule (NumberField.RingOfIntegers E) V) {y : V},
    y ∈ Submodule.span E (↑L : Set V) →
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ L :=
  fun L _ hy => main L hy

end GlobalTheory.TargetStatementSixOneSixtyEight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersection
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.Unglue

theorem ideal_eq_top {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (h : ∀ a : E, (∀ i ∈ I, a * (i : E) ∈ (algebraMap (𝓞 E) E).range) → a ∈ (algebraMap (𝓞 E) E).range) :
    I = ⊤ := by
  have h0 : (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI
  have h1 : (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ≤ 1 := by
    intro a ha
    have ha' := (FractionalIdeal.mem_inv_iff h0).1 ha
    refine (FractionalIdeal.mem_one_iff _).2 (h a fun i hi => ?_)
    exact (FractionalIdeal.mem_one_iff _).1 (ha' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hi))
  have h2 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 E)⁰ E) = I * (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact top_le_iff.1 h2

theorem star_mem {E : Type} [Field E] [NumberField E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨RingOfIntegers.mapRingEquiv starRingAut b, rfl⟩

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (L : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | (apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target ..)

theorem isLattice_capX_and_exists_glue (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V)
    (hl : IsLine Y X ι z u) (L : Submodule (𝓞 D.host.E) Y.V) (hL : IsSDIn Y (flatSp Y X ι z) L) (hp : IsPrim Y z L) :
    Submodule.IsFullLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  obtain ⟨hi, ho, hz⟩ := hl
  obtain ⟨hfg, hsp, hsd⟩ := hL
  have hT := Tu_ne_zero u
  have hinj : Function.Injective ι := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    refine X.nondeg.1 x fun y => ?_
    rw [← hi, hx, map_zero, LinearMap.zero_apply]
  have hzU : ∀ a : D.host.E, a • z ∈ flatSp Y X ι z := fun a =>
    Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))
  have hzL : z ∈ L := by simpa using (hp 1).2 (one_mem _)
  have hLU : ∀ y ∈ L, y ∈ flatSp Y X ι z := fun y hy => hsp ▸ Submodule.subset_span hy
  have hint : ∀ y ∈ L, Y.hD y z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := fun y hy =>
    (hsd z (hLU z hzL)).1 hzL y hy
  have hdec : ∀ y ∈ L, ∃ x : X.V, y = ι x + (-(Y.hD y z) * (Tu D u)⁻¹) • z := by
    intro y hy
    obtain ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 (hLU y hy)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hb
    refine ⟨x, ?_⟩
    have : Y.hD (ι x + s • z) z = -(s * Tu D u) := by
      have h1 := ho x
      simp only [HSpace.hD] at h1 hz ⊢
      rw [map_add (f := _), map_smul, h1, hz, smul_eq_mul]; ring
    rw [this]
    congr 2
    field_simp
  have hlat : Submodule.IsLattice D.host.E (capX Y X ι L) := by
    refine GlobalTheory.StdFrames.isLattice_crdLat X ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective (ι.restrictScalars (𝓞 D.host.E)) hinj (hfg.of_le ?_)
      exact Submodule.map_comap_le _ _
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  refine ⟨{ toIsLattice := hlat, span_eq_top := ?_ }, ?_⟩
  · apply Submodule.eq_top_iff'.2
    intro y
    let x := (Formalism.L2.Herm.crd X).symm y
    have hx : ι x ∈ Submodule.span D.host.E (L : Set Y.V) := by
      rw [hsp]
      exact Submodule.mem_sup_left (LinearMap.mem_range_self ι x)
    obtain ⟨c, hc, hcx⟩ := exists_smul_mem L hx
    have hcy : c • y ∈ capX Y X ι L := by
      change c • y ∈ Formalism.L2.Herm.crdLat X (L.comap (ι.restrictScalars (𝓞 D.host.E)))
      refine ⟨c • x, ?_, ?_⟩
      · change ι (c • x) ∈ L
        simpa using hcx
      · simp [x]
    have hcy' : c • y ∈ Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E)) :=
      Submodule.subset_span hcy
    rw [← algebraMap_smul D.host.E c] at hcy'
    have := (Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E))).smul_mem
      (c : D.host.E)⁻¹ hcy'
    simpa only [smul_smul, inv_mul_cancel₀ (RingOfIntegers.coe_ne_zero_iff.2 hc), one_smul] using this
  · let I : Ideal (𝓞 D.host.E) :=
      (L.map ((Y.hT z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hI : ∀ i : 𝓞 D.host.E, i ∈ I ↔ ∃ y ∈ L, Y.hD y z = (i : D.host.E) := fun i => Iff.rfl
    have hI0 : I ≠ ⊥ := by
      obtain ⟨i, hi'⟩ := hint z hzL
      intro h
      have : i ∈ I := (hI i).2 ⟨z, hzL, hi'.symm⟩
      rw [h, Ideal.mem_bot] at this
      rw [this, map_zero, hz] at hi'
      exact hT (neg_eq_zero.1 hi'.symm)
    have hItop : I = ⊤ := by
      refine ideal_eq_top I hI0 fun a ha => ?_
      have : star a • z ∈ L := by
        refine (hsd _ (hzU _)).2 fun x hx => ?_
        obtain ⟨i, hi'⟩ := hint x hx
        have := ha i ((hI i).2 ⟨x, hx, hi'.symm⟩)
        have e : Y.hD x (star a • z) = a * Y.hD x z := by
          simp only [HSpace.hD]
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
          congr 1
          exact star_star a
        rw [e, ← hi']
        exact this
      simpa using star_mem ((hp _).1 this)
    obtain ⟨l, hlL, hl1⟩ := (hI (-1)).1 (hItop ▸ Submodule.mem_top)
    obtain ⟨x₀, hx₀⟩ := hdec l hlL
    have hl2 : l = (Tu D u)⁻¹ • z + ι x₀ := by
      rw [hx₀, hl1, add_comm]
      simp
    have hc : (capX Y X ι L).comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
        L.comap (ι.restrictScalars (𝓞 D.host.E)) :=
      Submodule.comap_map_eq_of_injective (f := (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E))
        (Formalism.L2.Herm.crd X).injective _
    refine ⟨x₀, ?_⟩
    rw [glueLat, hc, ← hl2]
    refine le_antisymm (fun y hy => ?_)
      (sup_le (Submodule.map_comap_le _ _) ((Submodule.span_singleton_le_iff_mem _ _).2 hlL))
    obtain ⟨x, hx⟩ := hdec y hy
    obtain ⟨b, hb⟩ := hint y hy
    have e : y + b • l = ι (x + b • x₀) := by
      rw [← algebraMap_smul D.host.E b, ← algebraMap_smul D.host.E b x₀, hb, map_add (f := _), map_smul, hl2]
      generalize Y.hD y z = t at hx ⊢
      rw [hx]
      module
    have hm : y + b • l ∈ L := L.add_mem hy (L.smul_mem _ hlL)
    have e2 : y = ι (x + b • x₀) - b • l := by rw [← e, add_sub_cancel_right]
    rw [e2]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x + b • x₀, ?_, rfl⟩)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l)))
    change ι (x + b • x₀) ∈ L
    rw [← e]
    exact hm

end GlobalTheory.AdIsom.Unglue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersectionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_lattice_glued_from_intersection : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ L, IsSDIn Y (flatSp Y X ι z) L → IsPrim Y z L → Submodule.IsFullLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  intro D u Y X ι z hl L hL hp
  obtain ⟨hlat, hglue⟩ := GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue D u Y X ι z hl L hL hp
  refine ⟨{ toIsLattice := by first | exact hlat | exact hlat.toIsLattice, span_eq_top := ?_ }, hglue⟩
  apply Submodule.eq_top_iff'.2
  intro y
  let x := (Formalism.L2.Herm.crd X).symm y
  have hx : ι x ∈ Submodule.span D.host.E (L : Set Y.V) := by
    rw [hL.2.1]
    exact Submodule.mem_sup_left (LinearMap.mem_range_self ι x)
  obtain ⟨c, hc, hcx⟩ := GlobalTheory.AdIsom.Unglue.exists_smul_mem L hx
  have hcy : c • y ∈ capX Y X ι L := by
    change c • y ∈ Formalism.L2.Herm.crdLat X (L.comap (ι.restrictScalars (𝓞 D.host.E)))
    refine ⟨c • x, ?_, ?_⟩
    · change ι (c • x) ∈ L
      simpa using hcx
    · simp [x]
  have hcy' : c • y ∈ Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E)) :=
    Submodule.subset_span hcy
  rw [← algebraMap_smul D.host.E c] at hcy'
  have h := (Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E))).smul_mem
    (c : D.host.E)⁻¹ hcy'
  simpa only [smul_smul, inv_mul_cancel₀ (RingOfIntegers.coe_ne_zero_iff.2 hc), one_smul] using h
end
end
