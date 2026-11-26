module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsClopenSpecializationsGenPt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

def IsPullWedge {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V]
    (i : Ω₀ →+* Ω) (j : V₀ →+ V) {n : ℕ} (a : ⋀[Ω₀]^n V₀) (a' : ⋀[Ω]^n V) : Prop :=
  ∀ (b : Fin n → V₀) (α : Ω₀), a = α • exteriorPower.ιMulti Ω₀ n b →
    a' = i α • exteriorPower.ιMulti Ω n fun k => j (b k)

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : Set (Xo.XF c)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

def IsTie (Z : CptOver Y U) (𝔐 : HodgeCpt Y S y) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) : Prop :=
  Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f i ∧ i.comp Z.inc = 𝔐.cst ∧ IsExtOver i j ∧
    ∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (Z.M.pt e).left

end Comparison₂

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open Algebra GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ratioField_eq_blockFnField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ratioField y c = blockFnField y := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    have hp : y p / y ⟨p.1, c p.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨q.1, c q.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    have key : y p / y q = (y p / y ⟨p.1, c p.1⟩) / (y q / y ⟨q.1, c q.1⟩) := by
      rw [← hpq]
      have h0 := hc p.1
      by_cases hq0 : y q = 0
      · simp [hq0]
      · field_simp
    rw [key]
    exact div_mem hp hq

theorem ringKrullDim_coord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (blockFnField y) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  haveI hP : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime (mConeMap y)
  have hdim := GroundTheory.Heights₂.Heights.IntDomainDim.full (MRing ι ⧸ mCoordIdeal y)
    (algebraMap_injective _ (horizontal y))
  have hne : ∀ k, ∃ i, ratioPtL y c ⟨k, i⟩ ≠ 0 := by
    intro k
    refine ⟨c k, fun h0 => ?_⟩
    have h1 := congrArg Subtype.val h0
    change ratioPt y c ⟨k, c k⟩ = 0 at h1
    simp [ratioPt, hc k] at h1
  have htr := GroundTheory.Heights₂.Heights.ConeTrdeg.full K ι (ratioField y c) (ratioPtL y c)
    (birational y c hc) hne (horizontal _)
  rw [mCoordIdeal_ratioPtL y c hc] at htr
  rw [hdim, htr, ratioField_eq_blockFnField y c hc]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem trdeg_eq_of_le_of_isAlgebraic {L₁ L₂ : IntermediateField ℚ Ω} (h : L₁ ≤ L₂)
    (halg : ∀ t ∈ L₂, IsAlgebraic L₁ t) : Algebra.trdeg ℤ L₂ = Algebra.trdeg ℤ L₁ := by
  letI : Algebra L₁ L₂ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : FaithfulSMul L₁ L₂ :=
    (faithfulSMul_iff_algebraMap_injective L₁ L₂).2 (RingHom.injective _)
  let f : L₂ →ₐ[L₁] Ω :=
    { toRingHom := L₂.val.toRingHom
      commutes' := fun _ => rfl }
  haveI : Algebra.IsAlgebraic L₁ L₂ :=
    ⟨fun x => (isAlgebraic_algHom_iff f Subtype.val_injective).mp (halg x x.2)⟩
  have h0 : trdeg L₁ L₂ = 0 := trdeg_eq_zero
  rw [← trdeg_add_eq (R := ℤ) (S := L₁) (A := L₂), h0, add_zero]

end Dim

theorem isArithVar_of_isAlgebraic_image (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type)
    [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type)
    [Field Ω] [CharZero Ω] (y : (Σ k, ι' k) → Ω) (d : ℕ) (hv : IsBlockMap κ v)
    (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (hz : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (y ∘ v)) d)
    (halg : ∀ t ∈ blockFnField y, IsAlgebraic (blockFnField (y ∘ v)) t) : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d := by
  classical
  obtain ⟨hK, -, -, hdz⟩ := hz
  obtain ⟨hκ, -, hfst, hsurj⟩ := hv
  choose c' hc' using hy
  have hcv : ∀ k : K, ∃ i : ι k, (y ∘ v) ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨⟨k', i⟩, hp⟩ := hsurj ⟨κ k, c' (κ k)⟩ ⟨k, rfl⟩
    have h2 : k' = k := by
      apply hκ
      have h3 := hfst ⟨k', i⟩
      rw [hp] at h3
      exact h3.symm
    subst h2
    exact ⟨i, fun h0 => hc' _ (by rw [← hp]; exact h0)⟩
  choose c hc using hcv
  have e1 := hdz.symm.trans (ringKrullDim_coord (y ∘ v) c hc)
  have hle : blockFnField (y ∘ v) ≤ blockFnField y := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨v p, v q, by rw [hfst, hfst, hpq], rfl⟩
  have htr := trdeg_eq_of_le_of_isAlgebraic hle halg
  unfold ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar IsMultiProjPrime
  refine ⟨⟨κ hK.some⟩, ⟨RingHom.ker_isPrime (mConeMap y), isMultiHomogIdeal y, relevant y c' hc'⟩,
    horizontal y, ?_⟩
  rw [ringKrullDim_coord y c' hc', htr]
  generalize Algebra.trdeg ℤ ↥(blockFnField (y ∘ v)) = T at e1 ⊢
  simp only [map_add (f := _), map_natCast] at e1 ⊢
  generalize Cardinal.toENat T = e at e1 ⊢
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    have h5 : ((d + Fintype.card K : ℕ) : ℕ∞) = ⊤ := by exact_mod_cast e1
    exact ENat.natCast_ne_top _ h5
  | coe m =>
    norm_cast at e1 ⊢
    omega

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraicStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArithVar_of_block_algebraic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι' k) → Ω) (d : ℕ), IsBlockMap κ v → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsArithVar (mCoordIdeal (y ∘ v)) d → (∀ t ∈ blockFnField y, IsAlgebraic (blockFnField (y ∘ v)) t) → IsArithVar (mCoordIdeal y) d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image | exact GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

abbrev XQ (X : Scheme.{0}) : Scheme.{0} := pullback (toZ X) (toZ (Sp ℚ))

abbrev XQ.fst (X : Scheme.{0}) : XQ X ⟶ X := pullback.fst _ _

abbrev XQ.snd (X : Scheme.{0}) : XQ X ⟶ Sp ℚ := pullback.snd _ _

def toXQ {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) : Sp F ⟶ XQ X :=
  pullback.lift x (spMap (algebraMap ℚ F)) (specULiftZIsTerminal.hom_ext _ _)

@[simp] theorem toXQ_fst {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) :
    toXQ x ≫ XQ.fst X = x := pullback.lift_fst _ _ _

def evalAt {S : Scheme.{0}} (U : S.Opens) (f : Γ(S, U)) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) : ℂ :=
  (Scheme.stalkClosedPointTo z).hom (S.presheaf.germ U (centre z) hz f)

def anTop (S : Scheme.{0}) : TopologicalSpace (Sp ℂ ⟶ S) :=
  TopologicalSpace.generateFrom
    {A | ∃ (U : S.Opens) (f : Γ(S, U)) (V : Set ℂ), IsOpen V ∧ A = {z | ∃ hz : centre z ∈ U, evalAt U f z hz ∈ V}}

section Good

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  {M : LieModel G ξ Li}

def GoodAt (h : LieMetric M y) (C : ℝ) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) {GK : Over (Sp L)}
    [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) : Prop :=
  letI := τ.addCommGroup
  ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)),
    ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT →
    ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier),
      IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier,
      (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (ε a)).left)) →
      ∀ (σ : L →+* ℂ) (w : Fin r → ℂ),
        C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧
        sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2

end Good

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalScheme
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalScheme
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem component_whole_isIntegral_and_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) :=
  PositivityTheory.HtPt.Mf.xr_normal

end GlobalTheory.CompanionTheory.Ar.XR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_cpt_iff_normal_scheme : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ IsNormalScheme X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal | exact GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

section Alg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

abbrev chartQ {κ : Type} (x : κ → Ω) (c : κ) : Subalgebra ℚ Ω :=
  Algebra.adjoin ℚ (Set.range fun j => x j / x c)

abbrev invAdj (A : Subalgebra ℚ Ω) (h : Ω) : Subalgebra ℚ Ω :=
  Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω))

theorem le_invAdj (A : Subalgebra ℚ Ω) (h : Ω) : A ≤ invAdj A h := fun _ ha =>
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha)

theorem inv_mem_invAdj (A : Subalgebra ℚ Ω) (h : Ω) : h⁻¹ ∈ invAdj A h :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem exists_mul_pow_mem {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) {s : Ω}
    (hs : s ∈ invAdj A g) : ∃ k : ℕ, s * g ^ k ∈ A := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with rfl | ha
    · exact ⟨1, by rw [pow_one, inv_mul_cancel₀ h0]; exact A.one_mem⟩
    · exact ⟨0, by simpa using ha⟩
  | algebraMap r => exact ⟨0, by simpa using A.algebraMap_mem r⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, hk⟩ := ha
    obtain ⟨l, hl⟩ := hb
    refine ⟨k + l, ?_⟩
    have : (a + b) * g ^ (k + l) = a * g ^ k * g ^ l + b * g ^ l * g ^ k := by ring
    rw [this]
    exact A.add_mem (A.mul_mem hk (A.pow_mem hg _)) (A.mul_mem hl (A.pow_mem hg _))
  | mul a b _ _ ha hb =>
    obtain ⟨k, hk⟩ := ha
    obtain ⟨l, hl⟩ := hb
    refine ⟨k + l, ?_⟩
    have : a * b * g ^ (k + l) = a * g ^ k * (b * g ^ l) := by ring
    rw [this]
    exact A.mul_mem hk hl

abbrev primeUnder (A : Subalgebra ℚ Ω) (g : Ω) (q : Ideal (invAdj A g)) : Ideal A :=
  q.comap (Subalgebra.inclusion (le_invAdj A g)).toRingHom

theorem mem_primeUnder {A : Subalgebra ℚ Ω} {g : Ω} {q : Ideal (invAdj A g)} {a : A} :
    a ∈ primeUnder A g q ↔ (⟨a, le_invAdj A g a.2⟩ : invAdj A g) ∈ q := Iff.rfl

theorem not_mem_of_isPrime {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) {q : Ideal (invAdj A g)}
    (hq : q.IsPrime) : (⟨g, le_invAdj A g hg⟩ : invAdj A g) ∉ q := by
  intro h
  apply hq.ne_top
  rw [Ideal.eq_top_iff_one]
  have : (⟨g⁻¹, inv_mem_invAdj A g⟩ : invAdj A g) * ⟨g, le_invAdj A g hg⟩ = 1 :=
    Subtype.ext (by simp [h0])
  rw [← this]
  exact q.mul_mem_left _ h

theorem mem_iff_mul_pow {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) {q : Ideal (invAdj A g)}
    (hq : q.IsPrime) (s : invAdj A g) (k : ℕ) (t : A) (ht : (s : Ω) * g ^ k = t) :
    s ∈ q ↔ t ∈ primeUnder A g q := by
  have e : (⟨t, le_invAdj A g t.2⟩ : invAdj A g) = s * (⟨g, le_invAdj A g hg⟩ : invAdj A g) ^ k :=
    Subtype.ext (by simp [ht])
  rw [mem_primeUnder, e]
  constructor
  · exact fun h => q.mul_mem_right _ h
  · intro h
    rcases hq.mem_or_mem h with h | h
    · exact h
    · exact absurd (hq.mem_of_pow_mem _ h) (not_mem_of_isPrime hg h0 hq)

theorem isLocAt_invAdj {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) {q : Ideal (invAdj A g)}
    (hq : q.IsPrime) {R : Subring Ω} (hR : IsLocAt A (primeUnder A g q) R) : IsLocAt (invAdj A g) q R := by
  intro a
  rw [hR a]
  constructor
  · rintro ⟨s, hs, hsa⟩
    exact ⟨⟨s, le_invAdj A g s.2⟩, hs, le_invAdj A g hsa⟩
  · rintro ⟨s, hs, hsa⟩
    obtain ⟨k, hk⟩ := exists_mul_pow_mem hg h0 s.2
    obtain ⟨l, hl⟩ := exists_mul_pow_mem hg h0 hsa
    have hsk : (⟨(s : Ω) * g ^ k, hk⟩ : A) ∉ primeUnder A g q := fun h =>
      hs ((mem_iff_mul_pow hg h0 hq s k ⟨_, hk⟩ rfl).2 h)
    have hgl : (⟨g, hg⟩ : A) ∉ primeUnder A g q := not_mem_of_isPrime hg h0 hq
    have hprime : (primeUnder A g q).IsPrime := Ideal.comap_isPrime _ _
    refine ⟨⟨(s : Ω) * g ^ k, hk⟩ * ⟨g, hg⟩ ^ l, ?_, ?_⟩
    · intro h
      rcases hprime.mem_or_mem h with h | h
      · exact hsk h
      · exact hgl (hprime.mem_of_pow_mem _ h)
    · have e : (((⟨(s : Ω) * g ^ k, hk⟩ * ⟨g, hg⟩ ^ l : A) : Ω)) * a =
          ((s : Ω) * a * g ^ l) * g ^ k := by
        simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
        ring
      rw [e]
      exact A.mul_mem hl (A.pow_mem hg _)

end Alg

section Pts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

theorem unitAt_one (p : Cpt ξ) : unitAt ξ p 1 :=
  ⟨one_ne_zero, (regAt ξ p).one_mem, by simpa using (regAt ξ p).one_mem⟩

variable {ξ}

theorem unitAt_mul {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, (regAt ξ p).mul_mem ha.2.1 hb.2.1, by
    rw [mul_inv]; exact (regAt ξ p).mul_mem ha.2.2 hb.2.2⟩

theorem unitAt_pow {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) (k : ℕ) : unitAt ξ p (a ^ k) := by
  induction k with
  | zero => simpa using unitAt_one ξ p
  | succ k ih => rw [pow_succ]; exact unitAt_mul ih ha

theorem unitAt_of_mul_left {p : Cpt ξ} {a b : Ω} (h : unitAt ξ p (a * b)) (ha : a ∈ regAt ξ p)
    (hb : b ∈ regAt ξ p) : unitAt ξ p a := by
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h.1
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [this]
  exact (regAt ξ p).mul_mem hb h.2.2

theorem unitAt_of_mul_right {p : Cpt ξ} {a b : Ω} (h : unitAt ξ p (a * b)) (ha : a ∈ regAt ξ p)
    (hb : b ∈ regAt ξ p) : unitAt ξ p b :=
  unitAt_of_mul_left (by rwa [mul_comm]) hb ha

theorem not_unitAt_add (hξ : IsCptGen ξ) {p : Cpt ξ} {a b : Ω} (ha : a ∈ regAt ξ p) (hb : b ∈ regAt ξ p)
    (hna : ¬ unitAt ξ p a) (hnb : ¬ unitAt ξ p b) : ¬ unitAt ξ p (a + b) := by
  haveI : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hξ p).1
  have key : ∀ {c : Ω} (hc : c ∈ regAt ξ p), IsUnit (⟨c, hc⟩ : regAt ξ p) ↔ unitAt ξ p c := by
    intro c hc
    constructor
    · rintro ⟨u, hu⟩
      have hu1 : ((u : regAt ξ p) : Ω) = c := congrArg Subtype.val hu
      have h1 : ((u : regAt ξ p) : Ω) * (((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p) : Ω) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
      have hc0 : c ≠ 0 := by
        intro h0
        rw [hu1, h0, zero_mul] at h1
        exact zero_ne_one h1
      refine ⟨hc0, hc, ?_⟩
      have : c⁻¹ = (((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p) : Ω) := by
        rw [hu1] at h1
        exact (eq_inv_of_mul_eq_one_right h1).symm
      rw [this]
      exact Subtype.property _
    · rintro ⟨h0, -, hi⟩
      exact IsUnit.of_mul_eq_one ⟨c⁻¹, hi⟩ (Subtype.ext (by simp [h0]))
  intro hab
  have hsum : IsUnit ((⟨a, ha⟩ : regAt ξ p) + ⟨b, hb⟩) := (key ((regAt ξ p).add_mem ha hb)).2 hab
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
  · exact hna ((key ha).1 h)
  · exact hnb ((key hb).1 h)

variable [CharZero Ω]

theorem Char0.unitAt_natCast {p : Cpt ξ} (hp : Char0 ξ p) {m : ℕ} (hm : m ≠ 0) : unitAt ξ p (m : Ω) := by
  induction m using Nat.recOnMul with
  | zero => exact absurd rfl hm
  | one => simpa using unitAt_one ξ p
  | prime r hr =>
    have := hp r hr
    simpa [InFibre] using this
  | mul a b ha hb =>
    rw [Nat.cast_mul]
    exact unitAt_mul (ha (left_ne_zero_of_mul hm)) (hb (right_ne_zero_of_mul hm))

theorem Char0.algebraMap_mem {p : Cpt ξ} (hp : Char0 ξ p) (r : ℚ) : algebraMap ℚ Ω r ∈ regAt ξ p := by
  have e : algebraMap ℚ Ω r = (r.num : Ω) * ((r.den : Ω))⁻¹ := by
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
  rw [e]
  exact (regAt ξ p).mul_mem (intCast_mem _ _) (Char0.unitAt_natCast hp r.den_nz).2.2

theorem chartQ_le {κ : Type} {x : κ → Ω} {c : κ} {p : Cpt ξ} (hp : Char0 ξ p) (hc : InChart ξ x c p)
    {s : Ω} (hs : s ∈ chartQ x c) : s ∈ regAt ξ p := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hc.2 j
  | algebraMap r => exact Char0.algebraMap_mem hp r
  | add a b _ _ ha hb => exact (regAt ξ p).add_mem ha hb
  | mul a b _ _ ha hb => exact (regAt ξ p).mul_mem ha hb

theorem invAdj_le {p : Cpt ξ} (hp : Char0 ξ p) {A : Subalgebra ℚ Ω} {h : Ω} (hA : ∀ s ∈ A, s ∈ regAt ξ p)
    (hh : unitAt ξ p h) {s : Ω} (hs : s ∈ invAdj A h) : s ∈ regAt ξ p := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with rfl | ha
    · exact hh.2.2
    · exact hA _ ha
  | algebraMap r => exact Char0.algebraMap_mem hp r
  | add a b _ _ ha hb => exact (regAt ξ p).add_mem ha hb
  | mul a b _ _ ha hb => exact (regAt ξ p).mul_mem ha hb

end Pts

section Gens

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {N : ℕ}

abbrev ratEval (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (G : MRing (fun _ : Unit => Fin (N + 1))) : Ω :=
  MvPolynomial.aeval (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2 / x c) G

def bdGens (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : Fin (N + 1) → Ω) (B : Set (Cpt ξ)) :
    Set (MRing (fun _ : Unit => Fin (N + 1))) :=
  {G | ∃ d : ℕ, G.IsHomogeneous d ∧ ∀ c', ∀ q ∈ B, InChart ξ x c' q → ¬ unitAt ξ q (ratEval x c' G)}

end Gens

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishing
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NonvanishingPointsDense
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.nonvanishing_points_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof)
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishing
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem nonvanishing_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  exact @PositivityTheory.Xgn.nonvanishing_points_dense

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishingStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_dense_nonvanishing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | exact GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroCentreOfComplex
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroCentreOfComplex
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem char_zero_centre_complex_point : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z), IsCptGen ξ → Char0 ξ ⟨centre z, h⟩ := by
  intro Ω _ X ξ z h _
  unfold Char0 InFibre unitAt regAt
  intro r hr hfib
  apply hfib
  have h1 := map_natCast (Scheme.stalkClosedPointTo z).hom r
  have h2 : IsUnit ((r : ℕ) : ℂ) := (Nat.cast_ne_zero.2 hr.ne_zero).isUnit
  rw [← h1] at h2
  obtain ⟨u, hu'⟩ := isUnit_of_map_unit _ _ h2
  have hv : genMap ξ ⟨centre z, h⟩ u.val = (r : Ω) :=
    (congrArg (genMap ξ ⟨centre z, h⟩) hu').trans (map_natCast _ r)
  refine ⟨?_, ⟨_, hv⟩, ⟨(u⁻¹).val, ?_⟩⟩
  · rw [← hv]
    exact (u.isUnit.map (genMap ξ ⟨centre z, h⟩)).ne_zero
  · exact (map_units_inv (genMap ξ ⟨centre z, h⟩) u).trans (congrArg Inv.inv hv)

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroCentreOfComplexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_zero_centre_of_complex : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z), IsCptGen ξ → Char0 ξ ⟨centre z, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.char_zero_centre_complex_point | exact GlobalTheory.CompanionTheory.Ar.SncBase.char_zero_centre_complex_point | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.char_zero_centre_complex_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponent
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem eq_of_regAt_eq_of_coordTie :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω),
      CoordTie o ξ x → ∀ p q : Cpt ξ, regAt ξ p = regAt ξ q → p = q := by
  intro X Ω _ ξ o _ _ κ x h p q e
  obtain ⟨c, hc⟩ := h.cover p
  have hq : InChart ξ x c q := ⟨hc.1, fun c' => e ▸ hc.2 c'⟩
  haveI hloc : IsLocalRing (regAt ξ p) :=
    (regAt_isLocalRing_isFractionRing_stalk X Ω ξ h.gen p).1
  have hmem : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c), (s : Ω) ∈ regAt ξ p :=
    fun s => (h.ring c hc.1 s).1 s.2 p hc
  let f : Algebra.adjoin o (Set.range fun j => x j / x c) →+* regAt ξ p :=
    ((Algebra.adjoin o (Set.range fun j => x j / x c)).val :
      Algebra.adjoin o (Set.range fun j => x j / x c) →+* Ω).codRestrict (regAt ξ p) hmem
  have hI : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hp' : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hq' : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ q (s : Ω) := by
    intro s
    rw [hp' s]
    simp only [unitAt, e]
  exact (GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ o κ x h c hc.1 _ hI).unique ⟨hc, hp'⟩ ⟨hq, hq'⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_ring_determines_component : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ p q : Cpt ξ, regAt ξ p = regAt ξ q → p = q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointGenericFibre
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenFibre

variable {Y P : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isIso_stalkMap_of_lift (f : Y ⟶ P) [Mono f] (y : Y)
    (t : Spec (P.presheaf.stalk (f y)) ⟶ Y) (ht : t ≫ f = P.fromSpecStalk (f y)) :
    IsIso (f.stalkMap y) := by
  have h0 : Spec.map (f.stalkMap y) ≫ P.fromSpecStalk (f y) = Y.fromSpecStalk y ≫ f :=
    Scheme.SpecMap_stalkMap_fromSpecStalk f
  have h1 : Spec.map (f.stalkMap y) ≫ t = Y.fromSpecStalk y := by
    rw [← cancel_mono f, Category.assoc, ht, h0]
  have hc : t (IsLocalRing.closedPoint (P.presheaf.stalk (f y))) = y := by
    have e1 : Spec.map (f.stalkMap y) (IsLocalRing.closedPoint (Y.presheaf.stalk y)) =
        IsLocalRing.closedPoint (P.presheaf.stalk (f y)) := Spec_closedPoint
    have e2 : (Spec.map (f.stalkMap y) ≫ t) (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y := by
      rw [h1]
      exact Scheme.fromSpecStalk_closedPoint
    rw [← e1]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e2
  have hs : t (IsLocalRing.closedPoint (P.presheaf.stalk (f y))) ⤳ y := by rw [hc]
  have h2 : Spec.map (Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo t) ≫ Y.fromSpecStalk y = t := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  generalize Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo t = τ at h2
  refine ⟨τ, ?_, ?_⟩
  · apply Spec.map_injective
    rw [← cancel_mono (P.fromSpecStalk (f y)), Spec.map_comp, Category.assoc, h0, ← Category.assoc, h2, ht,
      Spec.map_id, Category.id_comp]
  · apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk y), Spec.map_comp, Category.assoc, h2, h1, Spec.map_id, Category.id_comp]

theorem genMap_bijective {ζ : Spec (CommRingCat.of Ω) ⟶ P} (h : IsCptGen ζ) (p : Cpt ζ) (e : p.1 = genPt ζ) :
    Function.Bijective (genMap ζ p) := by
  obtain ⟨p, hp⟩ := p
  obtain rfl : p = genPt ζ := e
  have : P.presheaf.stalkSpecializes hp = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap, this]
  exact h.bij

theorem isCptGen_of_isIso_stalkMap (f : Y ⟶ P) (hf : ∀ y, IsIso (f.stalkMap y))
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y) (h : IsCptGen (ξ ≫ f)) : IsCptGen ξ := by
  have hd : Dominates ξ (ξ ≫ f) f (RingHom.id Ω) := by
    show ξ ≫ f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ ≫ f
    rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]
  have hb : ∀ q, Function.Bijective (f.stalkMap q).hom := fun q =>
    have := hf q
    ConcreteCategory.bijective_of_isIso (f.stalkMap q)
  have hcl : ∀ (q : Cpt ξ), genPt (ξ ≫ f) ⤳ f q.1 := fun q =>
    RegAtDom.map_genPt hd ▸ q.2.map f.continuous
  have hcomp : ∀ (q : Cpt ξ), genMap ξ q ∘ (f.stalkMap q.1).hom = genMap (ξ ≫ f) ⟨f q.1, hcl q⟩ := fun q =>
    funext fun t => RegAtDom.genMap_stalkMap hd q.1 q.2 (hcl q) t
  have hself : genMap ξ ⟨genPt ξ, specializes_rfl⟩ = (Scheme.stalkClosedPointTo ξ).hom := by
    have : Y.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    have e : Y.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫ Scheme.stalkClosedPointTo ξ =
        Scheme.stalkClosedPointTo ξ := by
      rw [this]
      exact Category.id_comp _
    exact congrArg (fun g => g.hom) e
  refine ⟨?_, fun q => ?_⟩
  · have e := hcomp ⟨genPt ξ, specializes_rfl⟩
    have hB := genMap_bijective h ⟨f (genPt ξ), hcl ⟨genPt ξ, specializes_rfl⟩⟩ (RegAtDom.map_genPt hd)
    rw [← e] at hB
    rw [← hself]
    exact ⟨hB.1.of_comp_right (hb _).2, hB.2.of_comp⟩
  · have hi := h.inj ⟨f q.1, hcl q⟩
    rw [← hcomp q] at hi
    exact hi.of_comp_right (hb _).2

variable {F : Type} [Field F] [NumberField F]


omit [NumberField F] in
theorem injective_of_charZero [CharZero Ω] (φ : 𝓞 F →+* Ω) : Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  ext n
  simp [Ideal.mem_comap, RingHom.mem_ker]

theorem exists_lift_field {R : CommRingCat.{0}} [IsLocalRing R] (g : Spec R ⟶ Sp (𝓞 F)) (z : Sp F)
    (hz : g (IsLocalRing.closedPoint R) = spMap (algebraMap (𝓞 F) F) z) :
    ∃ v : Spec R ⟶ Sp F, v ≫ spMap (algebraMap (𝓞 F) F) = g := by
  have hg : Spec.map (Spec.preimage g) = g := Spec.map_preimage g
  generalize Spec.preimage g = c at hg
  subst hg
  have hu : ∀ a : nonZeroDivisors (𝓞 F), IsUnit (c.hom a) := by
    intro a
    by_contra hn
    have h1 : (a : 𝓞 F) ∈ (Spec.map c (IsLocalRing.closedPoint R)).asIdeal :=
      (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [hz] at h1
    have h2 : algebraMap (𝓞 F) F a ∈ PrimeSpectrum.asIdeal z := h1
    have hp : (PrimeSpectrum.asIdeal z).IsPrime := PrimeSpectrum.isPrime _
    rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal z), Ideal.mem_bot] at h2
    have h3 : (a : 𝓞 F) = 0 := IsFractionRing.injective (𝓞 F) F (h2.trans (map_zero _).symm)
    exact nonZeroDivisors.ne_zero a.2 h3
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors (𝓞 F)) (S := F) hu)), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

theorem isIso_stalkMap_fst (s : P ⟶ Sp (𝓞 F)) (y : ↑(pullback s (spMap (algebraMap (𝓞 F) F)))) :
    IsIso ((pullback.fst s (spMap (algebraMap (𝓞 F) F))).stalkMap y) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 F) F)) := IsLocalization.epi (nonZeroDivisors (𝓞 F)) F
  have : Mono (spMap (algebraMap (𝓞 F) F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  have hz : (P.fromSpecStalk (pullback.fst s (spMap (algebraMap (𝓞 F) F)) y) ≫ s) (IsLocalRing.closedPoint _) =
      spMap (algebraMap (𝓞 F) F) (pullback.snd s (spMap (algebraMap (𝓞 F) F)) y) := by
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    rw [Scheme.fromSpecStalk_closedPoint]
    have e : (pullback.fst s (spMap (algebraMap (𝓞 F) F)) ≫ s) y =
        (pullback.snd s (spMap (algebraMap (𝓞 F) F)) ≫ spMap (algebraMap (𝓞 F) F)) y := by
      rw [pullback.condition]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans (e.trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨v, hv⟩ := exists_lift_field _ _ hz
  exact isIso_stalkMap_of_lift _ y (pullback.lift _ v hv.symm) (pullback.lift_fst _ _ _)

theorem exists_point : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P), IsCptGen ξ₀ → ∃ (b : F →+* Ω) (ξF : Sp Ω ⟶ pullback s (spMap (algebraMap (𝓞 F) F))), ξF ≫ pullback.fst _ _ = ξ₀ ∧ ξF ≫ pullback.snd _ _ = spMap b ∧ IsCptGen ξF := by
  intro F _ _ P s Ω _ _ ξ₀ h
  have hφ : Spec.map (Spec.preimage (ξ₀ ≫ s)) = ξ₀ ≫ s := Spec.map_preimage _
  generalize Spec.preimage (ξ₀ ≫ s) = φ at hφ
  have hinj : Function.Injective φ.hom := injective_of_charZero φ.hom
  have hb : (CommRingCat.ofHom (algebraMap (𝓞 F) F)) ≫ CommRingCat.ofHom (IsFractionRing.lift hinj) = φ := by
    ext a
    simp
  have hw : ξ₀ ≫ s = spMap (IsFractionRing.lift hinj) ≫ spMap (algebraMap (𝓞 F) F) :=
    hφ.symm.trans ((congrArg Spec.map hb.symm).trans (Spec.map_comp _ _))
  refine ⟨IsFractionRing.lift hinj, pullback.lift ξ₀ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  apply isCptGen_of_isIso_stalkMap (pullback.fst _ _) (isIso_stalkMap_fst s)
  rwa [pullback.lift_fst]

end GlobalTheory.CompanionTheory.Ar.GenFibre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_generic_fibre : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P), IsCptGen ξ₀ → ∃ (b : F →+* Ω) (ξF : Sp Ω ⟶ pullback s (spMap (algebraMap (𝓞 F) F))), ξF ≫ pullback.fst _ _ = ξ₀ ∧ ξF ≫ pullback.snd _ _ = spMap b ∧ IsCptGen ξF := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point | exact GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point | (intros; apply GlobalTheory.CompanionTheory.Ar.GenFibre.exists_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch

def TorusOver {L L' : Type} [Field L] [Field L'] (e : L →+* L') {G : Over (Sp L)} {G' : Over (Sp L')} [GrpObj G]
    [GrpObj G'] (τ : TorusExtension G) (τ' : TorusExtension G') (φ : G'.left ⟶ G.left) : Prop :=
  letI := τ.addCommGroup
  letI := τ'.addCommGroup
  ∃ κ : τ.X ≃+ τ'.X, ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Sp L') (t' : Over.mk a ⟶ splitTorus (Sp L') τ'.X)
    (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) τ.X), (∀ χ, charVal t χ = charVal t' (κ χ)) →
      (t' ≫ τ'.i).left ≫ φ = (t ≫ τ.i).left

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointMemDenseOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointMemDenseOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem genPt_mem_of_dense_open : ∀ (W : Scheme.{0}) [IsLocallyNoetherian W] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W) (U : W.Opens), IsCptGen ξ → Dense (U : Set W) → genPt ξ ∈ U := by
  intro W _ Ω _ ξ U hξ hU
  have hcl := GlobalTheory.T.isClopen_specializations_genPt W Ω ξ hξ
  obtain ⟨q, hq, hqU⟩ := hU.inter_open_nonempty _ hcl.isOpen ⟨genPt ξ, specializes_rfl⟩
  exact hq.mem_open U.isOpen hqU

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointMemDenseOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_mem_dense_open : ∀ (W : Scheme.{0}) [IsLocallyNoetherian W] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W) (U : W.Opens), IsCptGen ξ → Dense (U : Set W) → genPt ξ ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.genPt_mem_of_dense_open | exact GlobalTheory.CompanionTheory.Ar.SncBase.genPt_mem_of_dense_open | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.genPt_mem_of_dense_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EveryComponentInSomeChart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EveryComponentInSomeChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_inChart_of_comp_eq :
    ∀ (W P : Scheme.{0}) (Ω : Type) [Field Ω] (ξ' : Sp Ω ⟶ W) (ξ₀ : Sp Ω ⟶ P) (g : W ⟶ P) (o : Type) [CommRing o]
      [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → ξ' ≫ g = ξ₀ → ∀ p' : Cpt ξ', ∃ c, InChart ξ' u c p' := by
  intro W P Ω _ ξ' ξ₀ g o _ _ κ u h he p'
  have hd : Dominates ξ' ξ₀ g (RingHom.id Ω) := by
    have e : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 (Spec (CommRingCat.of Ω)) := by
      exact Spec.map_id _
    show ξ' ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ₀
    rw [e, Category.id_comp]
    exact he
  obtain ⟨hs, hreg, -⟩ := RegAtDom.regAt_dominates P Ω ξ₀ W Ω ξ' g (RingHom.id Ω) hd p'
  obtain ⟨c, hc, hr⟩ := h.cover ⟨g p'.1, hs⟩
  exact ⟨c, hc, fun c' => hreg _ (hr c')⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EveryComponentInSomeChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_component_in_some_chart : ∀ (W P : Scheme.{0}) (Ω : Type) [Field Ω] (ξ' : Sp Ω ⟶ W) (ξ₀ : Sp Ω ⟶ P) (g : W ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → ξ' ≫ g = ξ₀ → ∀ p' : Cpt ξ', ∃ c, InChart ξ' u c p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothSchemeStalksDomains
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothSchemeStalksDomains
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem isDomain_and_isIntegrallyClosed_stalk_sp_field (K : Type) [Field K] (y : Sp K) :
    IsDomain ((Sp K).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp K).presheaf.stalk y) := by
  let p : PrimeSpectrum K := y
  have hle : p.asIdeal.primeCompl ≤ IsUnit.submonoid K := fun x hx =>
    isUnit_iff_ne_zero.2 fun h0 => hx (h0 ▸ p.asIdeal.zero_mem)
  let e₁ : K ≃+* Localization.AtPrime p.asIdeal :=
    (IsLocalization.atUnits K p.asIdeal.primeCompl hle).toRingEquiv
  let e₂ : (Sp K).presheaf.stalk y ≃+* Localization.AtPrime p.asIdeal :=
    (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of K) p).commRingCatIsoToRingEquiv
  let e : K ≃+* (Sp K).presheaf.stalk y := e₁.trans e₂.symm
  haveI := Field.instIsIntegrallyClosed K
  exact ⟨(MulEquiv.isField (Field.toIsField K) e.symm.toMulEquiv).isDomain, IsIntegrallyClosed.of_equiv e⟩

theorem isDomain_stalk_of_smoothOfRelativeDimension_field (K : Type) [Field K] (e : ℕ)
    (X : Scheme.{0}) (g : X ⟶ Sp K) (hg : SmoothOfRelativeDimension e g) (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  haveI : Smooth g := SmoothOfRelativeDimension.smooth e g
  exact (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g
    (isDomain_and_isIntegrallyClosed_stalk_sp_field K) x).1

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothSchemeStalksDomainsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_scheme_stalks_domains : ∀ (K : Type) [Field K] (e : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp K), SmoothOfRelativeDimension e g → ∀ x : X, IsDomain (X.presheaf.stalk x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | exact GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field <;> assumption)
end
end
