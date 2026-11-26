module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGenerators
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeRegular
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuation
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameGenericRank
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelRight
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBaseChangeCompatible
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDivisorFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameHeightFormula

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetT
namespace YgbHelp

private lemma detT {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) :
    M.det = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : R) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

end YgbHelp

theorem UpperTheory.Reformulated.B.Ygb2.main :
    ∀ {R : Type} [inst : CommRing R] {r n : ℕ} (B : Matrix (Fin r) (Fin n) R) (C : Matrix (Fin n) (Fin r) R),
      (B * C).det = ∑ f : Fin r → Fin n, (∏ i : Fin r, B i (f i)) * (C.submatrix f id).det := by
  intro R inst r n B C
  rw [YgbHelp.detT]
  simp_rw [YgbHelp.detT, Matrix.mul_apply, Fintype.prod_sum, Finset.mul_sum, Matrix.submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiag
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiag
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem blkF_eq_none_iff (Ψ : Type) (p q : ℕ) (K₀ : Type) (r : Ψ × Fin (p + q)) :
    blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2 := by
  unfold blkF
  split_ifs with h <;> simp [h]

theorem stepOf_injective (Ψ : Type) (p q : ℕ) : Function.Injective (stepOf Ψ p q) := by
  rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
  have hi := i.2
  have hi' := i'.2
  by_cases h₁ : (i : ℕ) < p <;> by_cases h₂ : (i' : ℕ) < p
  · simp only [stepOf, dite_eq_left h₁, dite_eq_left h₂] at h
    have e₁ : τ = τ' := Sum.inl.inj (congrArg Sigma.fst h)
    have e₂ := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
    exact Prod.ext e₁ (Fin.ext e₂)
  · simp only [stepOf, dite_eq_left h₁, dite_eq_right h₂] at h
    exact absurd (congrArg Sigma.fst h) (by simp)
  · simp only [stepOf, dite_eq_right h₁, dite_eq_left h₂] at h
    exact absurd (congrArg Sigma.fst h) (by simp)
  · simp only [stepOf, dite_eq_right h₁, dite_eq_right h₂] at h
    have e₁ : τ = τ' := Sum.inr.inj (congrArg Sigma.fst h)
    have e₂ : (i : ℕ) - p = (i' : ℕ) - p := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
    exact Prod.ext e₁ (Fin.ext (by show (i : ℕ) = (i' : ℕ); omega))

theorem blkF_inj (Ψ : Type) (p q : ℕ) (K₀ : Type) (r r' : Ψ × Fin (p + q)) (k : K₀ ⊕ StepIx Ψ p q)
    (h : blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k)
    (h' : blkF (Ψ := Ψ) (p := p) (q := q) K₀ r' = some k) : r = r' := by
  unfold blkF at h h'
  split_ifs at h h'
  apply stepOf_injective Ψ p q
  have e := (Option.some.inj h).trans (Option.some.inj h').symm
  exact Sum.inr.inj e

theorem fromBlocks_isBlockDiag {R : Type} [CommRing R] (p q : ℕ) (A : Matrix (Fin q) (Fin q) R)
    (B : Matrix (Fin p) (Fin p) R) :
    IsBlockDiag p ((Matrix.fromBlocks A 0 0 B).submatrix (blockEquiv p q).symm (blockEquiv p q).symm) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with x | x <;> rcases y with y | y
  · exfalso
    apply hab
    have hx := x.2
    have hy := y.2
    show ((x : ℕ) < _ ↔ (y : ℕ) < _)
    omega
  · rfl
  · rfl
  · exfalso
    apply hab
    show (q + (x : ℕ) < _ ↔ q + (y : ℕ) < _)
    omega

theorem gMat_isBlockDiag (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) :
    IsBlockDiag p (gMat p q Ω τ) :=
  fromBlocks_isBlockDiag p q (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))

theorem blocks_main : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type),
    (∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
    (∀ r r' k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k →
      blkF (Ψ := Ψ) (p := p) (q := q) K₀ r' = some k → r = r') ∧
    ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) :=
  fun Ψ _ p q Ω _ K₀ => ⟨blkF_eq_none_iff Ψ p q K₀, blkF_inj Ψ p q K₀, gMat_isBlockDiag Ψ p q Ω⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiagStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blkF_properStep_injective_blockDiag :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type),
      (∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
      (∀ r r' k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k →
        blkF (Ψ := Ψ) (p := p) (q := q) K₀ r' = some k → r = r') ∧
      ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) := by
  intro Ψ _ p q Ω _ K₀
  have stepOf_injective : Function.Injective (stepOf (Ψ := Ψ) (p := p) (q := q)) := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    have hi := i.2
    have hi' := i'.2
    by_cases h₁ : (i : ℕ) < p <;> by_cases h₂ : (i' : ℕ) < p
    · simp only [stepOf, dite_eq_left h₁, dite_eq_left h₂] at h
      have e₁ : τ = τ' := Sum.inl.inj (congrArg Sigma.fst h)
      have e₂ := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
      exact Prod.ext e₁ (Fin.ext e₂)
    · simp only [stepOf, dite_eq_left h₁, dite_eq_right h₂] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · simp only [stepOf, dite_eq_right h₁, dite_eq_left h₂] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · simp only [stepOf, dite_eq_right h₁, dite_eq_right h₂] at h
      have e₁ : τ = τ' := Sum.inr.inj (congrArg Sigma.fst h)
      have e₂ : (i : ℕ) - p = (i' : ℕ) - p :=
        congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
      exact Prod.ext e₁ (Fin.ext (by show (i : ℕ) = (i' : ℕ); omega))
  have fromBlocks_isBlockDiag {R : Type} [CommRing R] (A : Matrix (Fin q) (Fin q) R)
      (B : Matrix (Fin p) (Fin p) R) :
      IsBlockDiag p ((Matrix.fromBlocks A 0 0 B).submatrix
        (blockEquiv p q).symm (blockEquiv p q).symm) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases x with x | x <;> rcases y with y | y
    · exfalso
      apply hab
      have hx := x.2
      have hy := y.2
      show ((x : ℕ) < _ ↔ (y : ℕ) < _)
      omega
    · rfl
    · rfl
    · exfalso
      apply hab
      show (q + (x : ℕ) < _ ↔ q + (y : ℕ) < _)
      omega
  refine ⟨?_, ?_, ?_⟩
  · intro r
    unfold blkF
    split_ifs with h <;> simp [h]
  · intro r r' k h h'
    unfold blkF at h h'
    split_ifs at h h'
    apply stepOf_injective
    have e := (Option.some.inj h).trans (Option.some.inj h').symm
    exact Sum.inr.inj e
  · intro τ
    exact fromBlocks_isBlockDiag
      (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormula
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem flag_total_normal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → (∀ q : Z, genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) → Smooth f → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ _ Z ξ' f _ _ _ hf
  exact GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f (fun x => ⟨𝔐.normal.1 x, 𝔐.normal.2 x⟩)

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormulaStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_degree_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → (∀ q : Z, genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) → Smooth f → IsNormalScheme Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameOrderBound
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameOrderBound
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar GlobalTheory.CompanionTheory.Ar.TieArith ReciprocityTheory.ChartRestriction.G.AI.I4

section Comparison₂

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {K : Type} [Fintype K] {J : K → Type}

theorem exists_chart (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) :
    ∃ c : ∀ k, J k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  obtain ⟨c, hchart⟩ := h.cover (genCpt ξ)
  exact ⟨c, fun k ↦ (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)⟩

theorem ratioField_eq_top [CharZero Ω] (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : ratioField y c = ⊤ := by
  have hne : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, u, hu, -, rfl⟩ := FracChart.exists_eq_div_adjoin X Ω ξ _ (seg y) c h hne a
  exact div_mem (adjoin_le_ratioField y c hg) (adjoin_le_ratioField y c hu)

theorem trdeg_eq_of_ringKrullDim [∀ k, Fintype (J k)] [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) (d : ℕ)
    (hdim : ringKrullDim (MRing J ⧸ mCoordIdeal y) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    Algebra.trdeg ℤ Ω = d := by
  have hb : blockFnField y = ⊤ := by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]
  have htr : Algebra.trdeg ℤ (blockFnField y) = Algebra.trdeg ℤ Ω := by
    rw [hb]
    exact (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq
  rw [Cmp.ringKrullDim_coord y c hc, htr] at hdim
  have h1 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  have h2 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat =
      ((d + Fintype.card K : ℕ) : ℕ∞) := by
    generalize (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat = e at h1
    cases e using ENat.recTopCoe with
    | top => exact absurd h1 (by rw [top_add]; exact (ENat.natCast_ne_top _).symm)
    | coe e =>
      have h3 : e + 1 = d + 1 + Fintype.card K := by exact_mod_cast h1
      have h4 : e = d + Fintype.card K := by omega
      rw [h4]
  have h5 : Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal) = ((d + Fintype.card K : ℕ) : Cardinal) :=
    Cardinal.toENat_eq_natCast.mp h2
  rw [Nat.cast_add] at h5
  exact (Cardinal.add_nat_inj _).mp h5

end Comparison₂

theorem isArithVar_xb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x₀) (d + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d _ hT hA
  obtain ⟨c₀, hc₀⟩ := exists_chart 𝔐.ξ x₀ 𝔐.tie
  obtain ⟨cb, hcb⟩ := exists_chart 𝔐.ξ _ hT
  have hd : Algebra.trdeg ℤ Ω = d :=
    trdeg_eq_of_ringKrullDim x₀ c₀ hc₀ (ratioField_eq_top 𝔐.ξ x₀ 𝔐.tie c₀ hc₀) d hA.2.2.2
  obtain ⟨k₀⟩ := hA.1
  have hK : Nonempty (NonPluckerBlocks (blkF (CMType H) D.p D.q K₀)) := by
    refine ⟨⟨.inl k₀, fun r ↦ ?_⟩⟩
    unfold blkF
    split <;> simp
  exact isArithVar_of_ratioField_eq_top _ cb hcb (ratioField_eq_top 𝔐.ξ _ hT cb hcb) d hd

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameOrderBoundStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_order_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptIsVectorBundleRank
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptIsVectorBundleRank
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.FlagBun

section Map

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem isFrameAt_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {b : Fin r → E} {p : Cpt ξ} (h : L.IsFrameAt b p) : (L.map f).IsFrameAt (fun a => f (b a)) p := by
  refine ⟨h.1.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  show (L p).map (f.restrictScalars (regAt ξ p)) = _
  rw [h.2, Submodule.map_span, ← Set.range_comp]
  rfl

theorem isVB_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {V : Submodule Ω E} (h : L.IsVB r V) : (L.map f).IsVB r (V.map f) := by
  intro p hp
  obtain ⟨U, hU, b, hb, hq⟩ := h p hp
  refine ⟨U, hU, fun a => f (b a), ?_, fun q hqT hqU => isFrameAt_map_of_injective hf (hq q hqT hqU)⟩
  rw [← hb, Submodule.map_span, ← Set.range_comp]
  rfl

end Map

section Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}

theorem inW_injective (A : HodgeCpt Y S x) : Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective (A : HodgeCpt Y S x) (τ : CMType H) : Function.Injective (inO A τ) := by
  intro a b h
  have e := congrFun (congrArg Prod.snd h) τ
  simpa [inO] using e

end Bundles

theorem LL_isVB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)
    (𝔐 : HodgeCpt Y S x₀), ∀ s, (LL 𝔐 s).IsVB (rk (CMType H) D.p D.q s) (VV 𝔐 s) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 s
  rcases s with τ | τ
  · exact isVB_map_of_injective (inW_injective 𝔐) (𝔐.vb (.inl τ))
  · exact isVB_map_of_injective (inO_injective 𝔐 τ) (omBundle_isVB 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptIsVectorBundleRankStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_isVectorBundle_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀), ∀ s, (LL 𝔐 s).IsVB (rk (CMType H) D.p D.q s) (VV 𝔐 s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminant
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminant
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph

theorem det_mul_expand {R : Type} [CommRing R] {r n : ℕ} (B : Matrix (Fin r) (Fin n) R)
    (C : Matrix (Fin n) (Fin r) R) :
    (B * C).det = ∑ f : Fin r → Fin n, (∏ i, B i (f i)) * (C.submatrix f id).det :=
  _root_.UpperTheory.Reformulated.B.Ygb2.main B C

section Point

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_unitAt_of_sum (hg : IsCptGen ξ) (p : Cpt ξ) {ι : Type} (s : Finset ι) (f : ι → Ω)
    (hf : ∀ i ∈ s, f i ∈ regAt ξ p) (h1 : ∑ i ∈ s, f i = 1) : ∃ i ∈ s, unitAt ξ p (f i) := by
  classical
  have hf' : ∀ i, ∃ g : X.presheaf.stalk p.1, i ∈ s → genMap ξ p g = f i := fun i => by
    by_cases hi : i ∈ s
    · obtain ⟨g, hg⟩ := hf i hi
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose g hgf using hf'
  have hs : ∑ i ∈ s, g i = 1 := hg.inj p (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one, Finset.sum_congr rfl (fun i hi => hgf i hi), h1])
  by_contra hcon
  push_neg at hcon
  have hnu : ∀ i ∈ s, g i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p.1) := by
    intro i hi
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine hcon i hi ?_
    have e := hgf i hi
    have hu' : IsUnit (f i) := e ▸ hu.map (genMap ξ p)
    refine ⟨hu'.ne_zero, hf i hi, ⟨((hu.unit⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
    have h2 : genMap ξ p ((hu.unit⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1) * f i = 1 := by
      rw [← e, ← map_mul, ← map_one (genMap ξ p)]
      congr 1
      exact hu.val_inv_mul
    exact eq_inv_of_mul_eq_one_left h2
  have h1m : (1 : X.presheaf.stalk p.1) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p.1) :=
    hs ▸ Ideal.sum_mem _ hnu
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1m

theorem det_mem_subring {R : Subring Ω} {r : ℕ} (M : Matrix (Fin r) (Fin r) Ω) (h : ∀ i j, M i j ∈ R) :
    M.det ∈ R := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem R _) (prod_mem fun i _ => h _ _)

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_inChart_minors (hg : IsCptGen ξ) {κ : Type} (x : κ → Ω) (L : Lat ξ E) {m n r : ℕ}
    (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (hv : L.IsVB r V)
    (hT : IsTwistGen ξ x L m φ) (hs : Submodule.span Ω (Set.range b) = V) (p : Cpt ξ) (c : κ)
    (hc : InChart ξ x c p) :
    ∃ J : Fin r → Fin n, InChart ξ
      (fun J : Fin r → Fin n => ((Matrix.of fun j l => φ j (b l) : Matrix (Fin n) (Fin r) Ω).submatrix J id).det)
      J p := by
  classical
  obtain ⟨U, hpU, β, hβs, hfr⟩ := hv p (Set.mem_univ _)
  have hfrp := hfr p (Set.mem_univ _) hpU
  obtain ⟨B, hBr, hCr, hBC⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse X Ω ξ E κ x L m n r φ hT p c hc β hfrp
  set C : Matrix (Fin n) (Fin r) Ω := Matrix.of (fun j a => φ j (β a) / x c ^ m) with hC
  set A : Matrix (Fin n) (Fin r) Ω := Matrix.of fun j l => φ j (b l) with hA
  have hxm : x c ^ m ≠ 0 := pow_ne_zero _ hc.1

  have hβ : ∀ a, ∃ t : Fin r → Ω, ∑ l, t l • b l = β a := fun a => by
    have : β a ∈ Submodule.span Ω (Set.range b) := by
      rw [hs, ← hβs]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  choose T hTb using hβ
  set T' : Matrix (Fin r) (Fin r) Ω := Matrix.of T with hT'
  have hAC : ∀ J : Fin r → Fin n, (A.submatrix J id).det * T'.det = (x c ^ m) ^ r * (C.submatrix J id).det := by
    intro J
    have e : A.submatrix J id * T'ᵀ = (x c ^ m) • C.submatrix J id := by
      ext i a
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id, Matrix.smul_apply,
        smul_eq_mul, hA, hC, hT', Matrix.of_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [mul_div_cancel₀ _ hxm, ← hTb a, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul, mul_comm]
    have := congrArg Matrix.det e
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at this
  have hdreg : ∀ J : Fin r → Fin n, (C.submatrix J id).det ∈ regAt ξ p := fun J =>
    det_mem_subring _ fun i a => hCr _ _
  have hsum := det_mul_expand B C
  rw [hBC, Matrix.det_one] at hsum
  obtain ⟨J, -, hu⟩ := exists_unitAt_of_sum hg p Finset.univ
    (fun f : Fin r → Fin n => (∏ i, B i (f i)) * (C.submatrix f id).det)
    (fun f _ => mul_mem (prod_mem fun i _ => hBr _ _) (hdreg f)) hsum.symm
  have hd0 : (C.submatrix J id).det ≠ 0 := right_ne_zero_of_mul hu.1
  have hPr : (∏ i, B i (J i)) ∈ regAt ξ p := prod_mem fun i _ => hBr _ _
  have hdinv : (C.submatrix J id).det⁻¹ ∈ regAt ξ p := by
    have e : (C.submatrix J id).det⁻¹ =
        (∏ i, B i (J i)) * ((∏ i, B i (J i)) * (C.submatrix J id).det)⁻¹ := by
      have := left_ne_zero_of_mul hu.1
      field_simp
    rw [e]
    exact mul_mem hPr hu.2.2
  have h0 : (A.submatrix J id).det * T'.det ≠ 0 := by
    rw [hAC J]
    exact mul_ne_zero (pow_ne_zero _ hxm) hd0
  have hz0 : (A.submatrix J id).det ≠ 0 := left_ne_zero_of_mul h0
  have ht0 : T'.det ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨J, hz0, fun J' => ?_⟩
  have e : (A.submatrix J' id).det / (A.submatrix J id).det =
      (C.submatrix J' id).det * (C.submatrix J id).det⁻¹ := by
    have e1 := hAC J
    have e2 := hAC J'
    have hw : (x c ^ m) ^ r ≠ 0 := pow_ne_zero _ hxm
    rw [← eq_div_iff ht0] at e1 e2
    rw [e1, e2]
    field_simp
  show (A.submatrix J' id).det / (A.submatrix J id).det ∈ regAt ξ p
  rw [e]
  exact mul_mem (hdreg J') hdinv

theorem coordTie_seg_equiv {K₀ K' K : Type} [Fintype K₀] [Fintype K'] [Fintype K] {J₀ : K₀ → Type} {J' : K' → Type}
    {J : K → Type} [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J' k)] (e : K₀ ⊕ K' ≃ K)
    (F : ∀ a, Sum.elim J₀ J' a ≃ J (e a)) (x₀ : (Σ k, J₀ k) → Ω) (w : (Σ k, J' k) → Ω) (y : (Σ k, J k) → Ω)
    (h₁ : ∀ k i, y ⟨e (.inl k), F (.inl k) i⟩ = x₀ ⟨k, i⟩)
    (h₂ : ∀ k i, y ⟨e (.inr k), F (.inr k) i⟩ = w ⟨k, i⟩)
    (h : CoordTie ℤ ξ (seg x₀)) (hw : ∀ (k : K') (p : Cpt ξ), ∃ i, InChart ξ (fun i' : J' k => w ⟨k, i'⟩) i p) :
    CoordTie ℤ ξ (seg y) := by
  have h2 := GlobalTheory.T.coords_join_blocks X Ω ξ K₀ J₀ x₀ K' J' w h hw
  have h3 := GlobalTheory.CompanionTheory.Ar.FlagBun.coordTie_comp_equiv h2 (Equiv.piCongr e F).symm
  convert h3 using 1
  funext c'
  obtain ⟨c, rfl⟩ := (Equiv.piCongr e F).surjective c'
  simp only [Function.comp, Equiv.symm_apply_apply]
  show ∏ k, y ⟨k, Equiv.piCongr e F c k⟩ = _
  rw [← Equiv.prod_comp e, Fintype.prod_sum_type]
  simp only [Equiv.piCongr_apply_apply, h₁, h₂]

end Point

section Blocks

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ}

abbrev FullStep (Ψ : Type) (p q : ℕ) : Type := {t : StepIx Ψ p q // (t.2 : ℕ) + 1 = rk Ψ p q t.1}

theorem blkF_ne_full (K₀ : Type) (t : FullStep Ψ p q) (r : Ψ × Fin (p + q)) :
    blkF Ψ p q K₀ r ≠ some (.inr t.1) := by
  classical
  obtain ⟨⟨s, j⟩, ht⟩ := t
  obtain ⟨τ, i⟩ := r
  unfold blkF
  split_ifs with hp
  · intro h
    have h' : stepOf Ψ p q (τ, i) = ⟨s, j⟩ := by simpa using h
    unfold stepOf at h'
    obtain ⟨hp1, hp2⟩ := hp
    split_ifs at h' with hi
    · cases h'
      exact hp1 ht
    · cases h'
      have := i.2
      apply hp2
      simp only [Sum.elim_inr] at ht hi ⊢
      omega
  · simp

theorem exists_blkF_of_not_full (K₀ : Type) (t : StepIx Ψ p q) (ht : (t.2 : ℕ) + 1 ≠ rk Ψ p q t.1) :
    ∃ r, blkF Ψ p q K₀ r = some (.inr t) := by
  classical
  obtain ⟨s, j⟩ := t
  have hj := j.2
  rcases s with τ | τ
  · simp only [Sum.elim_inl] at ht hj
    refine ⟨(τ, ⟨j, by omega⟩), ?_⟩
    have hP : IsProperStep (p + q) p (⟨j, by omega⟩ : Fin (p + q)) := ⟨ht, by simp only; omega⟩
    unfold blkF
    rw [if_pos hP]
    unfold stepOf
    simp only [dif_pos hj]
  · simp only [Sum.elim_inr] at ht hj
    refine ⟨(τ, ⟨p + j, by omega⟩), ?_⟩
    have hP : IsProperStep (p + q) p (⟨p + j, by omega⟩ : Fin (p + q)) :=
      ⟨by simp only; omega, by simp only; omega⟩
    unfold blkF
    rw [if_pos hP]
    unfold stepOf
    have hn : ¬ (p + (j : ℕ) < p) := by omega
    simp only [dif_neg hn]
    congr 2
    exact congrArg (fun z => (⟨.inr τ, z⟩ : StepIx Ψ p q)) (Fin.ext (by simp))


variable (Ψ p q) in
def baseFun (K₀ : Type) : K₀ ⊕ FullStep Ψ p q → NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀)
  | .inl k => ⟨.inl k, fun r => by
      classical
      unfold blkF
      split_ifs <;> simp⟩
  | .inr t => ⟨.inr t.1, fun r => blkF_ne_full K₀ t r⟩

theorem baseFun_bijective (K₀ : Type) : Function.Bijective (baseFun Ψ p q K₀) := by
  constructor
  · rintro (k | t) (k' | t') h
    · simpa [baseFun] using h
    · simp [baseFun] at h
    · simp [baseFun] at h
    · have : t.1 = t'.1 := by simpa [baseFun] using h
      exact congrArg _ (Subtype.ext this)
  · rintro ⟨k | t, hk⟩
    · exact ⟨.inl k, rfl⟩
    · by_cases ht : (t.2 : ℕ) + 1 = rk Ψ p q t.1
      · exact ⟨.inr ⟨t, ht⟩, rfl⟩
      · obtain ⟨r, hr⟩ := exists_blkF_of_not_full K₀ t ht
        exact absurd hr (hk r)


variable (Ψ p q) in
def baseEquiv (K₀ : Type) : K₀ ⊕ FullStep Ψ p q ≃ NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀) :=
  Equiv.ofBijective _ (baseFun_bijective K₀)

variable {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

abbrev fullIx (n : Ψ ⊕ Ψ → ℕ) (t : FullStep Ψ p q) : Type := Fin ((t.1.2 : ℕ) + 1) → Fin (n t.1.1)

def fullMinor (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) : (Σ t : FullStep Ψ p q, fullIx n t) → Ω :=
  fun r => ((A r.1.1.1).submatrix r.2 (Fin.castLE r.1.1.2.2)).det

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]

def baseIxEquiv (n : Ψ ⊕ Ψ → ℕ) : ∀ a : K₀ ⊕ FullStep Ψ p q, Sum.elim J₀ (fullIx n) a ≃
    baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) (baseEquiv Ψ p q K₀ a)
  | .inl _ => Equiv.refl _
  | .inr _ => Equiv.refl _

theorem coordTie_seg_xb {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (x₀ : (Σ k, J₀ k) → Ω)
    (h : CoordTie ℤ ξ (seg x₀))
    (hw : ∀ (t : FullStep Ψ p q) (P : Cpt ξ), ∃ J, InChart ξ
      (fun J : fullIx n t => ((A t.1.1).submatrix J (Fin.castLE t.1.2.2)).det) J P) :
    CoordTie ℤ ξ (seg (xb (p := p) (q := q) A x₀)) := by
  classical
  haveI : Fintype (FullStep Ψ p q) := Fintype.ofFinite _
  exact coordTie_seg_equiv (baseEquiv Ψ p q K₀) (baseIxEquiv n) x₀ (fullMinor A) _
    (fun _ _ => rfl) (fun _ _ => rfl) h hw

end Blocks

theorem exists_inChart_minors_cast {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] (hg : IsCptGen ξ) {κ : Type} (x : κ → Ω) (L : Lat ξ E) {m n r r' : ℕ}
    (hle : r' ≤ r) (hr : r' = r)
    (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (hv : L.IsVB r V)
    (hT : IsTwistGen ξ x L m φ) (hs : Submodule.span Ω (Set.range b) = V) (p : Cpt ξ) (c : κ)
    (hc : InChart ξ x c p) :
    ∃ J : Fin r' → Fin n, InChart ξ
      (fun J : Fin r' → Fin n =>
        ((Matrix.of fun j l => φ j (b l) : Matrix (Fin n) (Fin r) Ω).submatrix J (Fin.castLE hle)).det) J p := by
  subst hr
  exact exists_inChart_minors hg x L V φ b hv hT hs p c hc

theorem coordTie_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF
  obtain ⟨hvb, hbas, htw, -⟩ := hF
  refine coordTie_seg_xb 𝔐.ξ _ x₀ 𝔐.tie fun t P => ?_
  obtain ⟨c', hc'⟩ := 𝔐.tie.cover P
  exact exists_inChart_minors_cast 𝔐.tie.gen _ (LL 𝔐 t.1.1) t.1.2.2 t.2 (VV 𝔐 t.1.1) (φ t.1.1)
    (cc 𝔐 bW bO t.1.1) (hvb _) (htw _) (hbas _).2 P c' hc'

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminantStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_change_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXb
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXb
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase

theorem det_genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) : (genU Ω r s).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [genU]
  · intro l k hlk
    have hlk' : l < k := hlk
    have h1 : ¬ k < l := not_lt.2 hlk'.le
    have h2 : l ≠ k := hlk'.ne
    simp [genU, h1, h2]

theorem det_map_mul_submatrix {Ω L : Type} [Field Ω] [Field L] (f : Ω →+* L) {n m r : ℕ} (hm : m = r) (h : m ≤ r)
    (A : Matrix (Fin n) (Fin r) Ω) (U : Matrix (Fin r) (Fin r) L) (hU : U.det = 1) (J : Fin m → Fin n) :
    ((A.map f * U).submatrix J (Fin.castLE h)).det = f ((A.submatrix J (Fin.castLE h)).det) := by
  subst hm
  have hc : (Fin.castLE h : Fin m → Fin m) = id := by
    funext i
    rfl
  rw [hc, RingHom.map_det]
  have : (A.map f * U).submatrix J id = (f.mapMatrix (A.submatrix J id)) * U := by
    ext a b
    simp [Matrix.mul_apply]
  rw [this, Matrix.det_mul, hU, mul_one]

variable {Ψ : Type} {p q : ℕ}

theorem full_of_noBlock (K₀ : Type) (t : StepIx Ψ p q)
    (h : ∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r ≠ some (.inr t)) : (t.2 : ℕ) + 1 = rk Ψ p q t.1 := by
  obtain ⟨s, i⟩ := t
  rcases s with τ | τ
  · have hi : (i : ℕ) < p := i.2
    by_contra hne
    have hne' : (i : ℕ) + 1 ≠ p := hne
    refine h (τ, ⟨i, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨i, by omega⟩ : Fin (p + q)) := ⟨hne', by
      show (i : ℕ) + 1 ≠ p + q
      omega⟩
    simp only [blkF, if_pos hp, stepOf]
    simp [hi]
    rfl
  · have hi : (i : ℕ) < q := i.2
    by_contra hne
    have hne' : (i : ℕ) + 1 ≠ q := hne
    refine h (τ, ⟨p + i, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨p + i, by omega⟩ : Fin (p + q)) := ⟨by
      show p + (i : ℕ) + 1 ≠ p
      omega, by
      show p + (i : ℕ) + 1 ≠ p + q
      omega⟩
    simp only [blkF, if_pos hp, stepOf]
    simp
    rfl

theorem basePart_yv : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type)
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r,
    basePart (blkF (Ψ := Ψ) (p := p) (q := q) K₀) (yv A x₀) r =
      algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r
  obtain ⟨⟨k, hk⟩, i⟩ := r
  rcases k with k | t
  · rfl
  · exact det_map_mul_submatrix (algebraMap Ω (GenField Ω (rk Ψ p q))) (full_of_noBlock K₀ t hk) t.2.2 (A t.1)
      (genU Ω (rk Ψ p q) t.1) (det_genU Ω _ _) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXbStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basePart_yv_eq_algebraMap_xb : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r, basePart (blkF Ψ p q K₀) (yv A x₀) r = algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTerm
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTerm
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]

def segIxEquiv : ((k : K₀ ⊕ StepIx Ψ p q) → idx (p := p) (q := q) J₀ n k) ≃
    FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q) :=
  Equiv.sumPiEquivProdPi (idx (p := p) (q := q) J₀ n)

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∃ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) ∧ (∀ q : Z, genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ∧ Smooth f := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF
  classical
  obtain ⟨hL, hc, hφ, hB⟩ := hF
  set r := rk (CMType H) D.p D.q with hr
  set x : ((k : K₀) → J₀ k) → Ω := seg x₀ with hxdef
  set cF := cc 𝔐 bW bO with hcF
  have hx : CoordTie ℤ 𝔐.ξ x := 𝔐.tie
  obtain ⟨c₀, hc₀⟩ := hx.cover ⟨genPt 𝔐.ξ, specializes_refl _⟩
  have hB' : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (cF s l)) = 1 := hB
  obtain ⟨J₁, hJ₁, hfrac⟩ := GlobalTheory.T.frame_matrix_chart_ratios Ω (EE 𝔐) (CMType H ⊕ CMType H) r n ((k : K₀) → J₀ k) x φ cF c₀ hc₀.1
    (GlobalTheory.T.function_field_ratio_generators 𝔐.X Ω 𝔐.ξ _ x c₀ hx hc₀.1) hB'
  have : Finite (FlagIx ((k : K₀) → J₀ k) n r) := by unfold FlagIx; infer_instance
  obtain ⟨X', ξ', s', hx', hirr', -, hprop, -⟩ :=
    GlobalTheory.T.exists_proper_integral_model (GenField Ω r) ℤ (FlagIx ((k : K₀) → J₀ k) n r) (flagCoord _ x φ cF) J₁ hJ₁ hfrac
  obtain ⟨f, hdom, hch⟩ := GlobalTheory.T.dominates_of_coords_regular 𝔐.X Ω 𝔐.ξ ℤ _ x X' (GenField Ω r) ξ' (algebraMap Ω (GenField Ω r)) hx hx'.gen
    hirr' (fun z p' => by simp [intCast_mem (regAt ξ' p') z]) (fun p' => by
      obtain ⟨⟨c1, J⟩, hne, hrat⟩ := hx'.cover p'
      have e1 : ∀ k, flagCoord _ x φ cF (k, J) = algebraMap Ω (GenField Ω r) (x k) *
          ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (J q) (Fin.castLE q.2.2)).det := fun k => rfl
      rw [e1] at hne
      refine ⟨c1, left_ne_zero_of_mul hne, fun k => ?_⟩
      have := hrat (k, J)
      rwa [e1, e1, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)] at this)
  have hsm := GlobalTheory.T.flag_frames_generic_model_right 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ x (CMType H ⊕ CMType H) r (VV 𝔐) (LL 𝔐) m n φ cF X' ξ' f hx 𝔐.all hL hφ hc
    hx' hirr' hdom hch
  have hseg : seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) =
      flagCoord ((k : K₀) → J₀ k) x φ cF ∘ segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀) := by
    funext c'
    show ∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, c' k⟩ =
      algebraMap Ω (GenField Ω r) (∏ k, x₀ ⟨k, c' (.inl k)⟩) *
        ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (c' (.inr q)) (Fin.castLE q.2.2)).det
    rw [Fintype.prod_sum_type, map_prod]
    rfl
  refine ⟨X', ξ', f, ?_, hirr', hdom, hsm⟩
  rw [hseg]
  convert coordTie_comp_equiv hx' (segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀)) using 1 <;> exact Subsingleton.elim _ _
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTermStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_leading_term : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∃ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) ∧ (∀ q : Z, genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ∧ Smooth f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGiven
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists : GlobalTheory.CompanionTheory.Ar.Top.Given → PB.FlagModelExists := by
  intro _ E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 nd d bW bO hv hd
  classical
  have hVB := GlobalTheory.T.hodgeCpt_isVectorBundle_rank E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐
  have hcc := GlobalTheory.T.hodgeCpt_bases_linearIndependent_span E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO
  have hg : ∀ s, ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω (EE 𝔐)), IsTwistGen 𝔐.ξ (seg x₀) (LL 𝔐 s) m φ := fun s =>
    GlobalTheory.T.exists_twisted_generators 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) 𝔐.tie 𝔐.all (hVB s)
  choose m n φ hφ using hg
  have hB : ∀ s, ∃ B : Matrix (Fin (rk (CMType H) D.p D.q s)) (Fin (n s)) Ω, B * aOf 𝔐 bW bO φ s = 1 := fun s =>
    GlobalTheory.T.frame_via_twisted_generators 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) (m s) (n s) (φ s) (cc 𝔐 bW bO s) 𝔐.tie (hVB s)
      (hφ s) (hcc s).1 (hcc s).2
  have hF : FormsOK 𝔐 bW bO m φ := ⟨hVB, hcc, hφ, hB⟩
  have hx₀ : ∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0 := by
    obtain ⟨c₀, hc₀⟩ := exists_inBlockChart 𝔐.tie ⟨genPt 𝔐.ξ, specializes_refl _⟩
    exact fun k => ⟨c₀ k, (hc₀ k).1⟩
  have ht := GlobalTheory.T.hodgeCpt_frame_change_determinant E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hP := GlobalTheory.T.blkF_properStep_injective_blockDiag (CMType H) D.p D.q Ω K₀
  have hmod : ModelOK (aOf 𝔐 bW bO φ) x₀ m :=
    ⟨hP.1, hP.2.1, GlobalTheory.T.exists_nonzero_xb_of_left_inverse _ _ _ Ω _ _ K₀ J₀ x₀ hx₀ hB,
      GlobalTheory.T.basePart_yv_eq_algebraMap_xb _ _ _ Ω _ _ K₀ J₀ x₀, hP.2.2, GlobalTheory.T.isGenericFlag_gMat _ _ _ Ω, GlobalTheory.T.yv_eq_sum_minors_gMat _ _ _ Ω _ _ K₀ J₀ x₀,
      GlobalTheory.T.hodgeCpt_frame_change_regular E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht⟩
  have hT := GlobalTheory.T.hodgeCpt_frame_minor_valuation E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod
  obtain ⟨Z, ξ', f, htie, hall, hdom, hsm⟩ := GlobalTheory.T.hodgeCpt_frame_leading_term E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hnorm := GlobalTheory.T.hodgeCpt_frame_degree_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF Z ξ' f htie hall hdom hsm
  obtain ⟨𝔐', e, j, -, hov, hR, hsp, hV⟩ := GlobalTheory.T.hodgeCpt_base_change_compatible E H D l Xo c Y S Ω _ (algebraMap Ω _) K₀ _ J₀ _ x₀ _ 𝔐 Z ξ' f hall htie hnorm hdom hsm
  obtain ⟨Fl, hdeg, hfl⟩ := GlobalTheory.T.hodgeCpt_frame_divisor_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ d hF hd 𝔐' _ j hov hsp hV
  obtain ⟨xdeg, hroot, hdy⟩ := GlobalTheory.T.hodgeCpt_frame_height_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod 𝔐' _ j Fl hov hsp hV hfl
  let M := model (aOf 𝔐 bW bO φ) x₀ m hmod
  let 𝔐₁ : HodgeCpt Y S M.x := reTie 𝔐 (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) ht
  let tie : FlagTie M 𝔐₁ :=
    { eW := bW, eO := bO, frameW := fun q F h h' τ => (hT q F h h' τ).1, frameO := fun q F h h' τ => (hT q F h h' τ).2 }
  have hκ : ∀ k : K₀, ∀ r, M.blk r ≠ some (.inl k) := fun k r h => by
    change blkF (CMType H) D.p D.q K₀ r = _ at h
    unfold blkF at h
    split_ifs at h
    simpa using h
  let κ : K₀ → NonPluckerBlocks M.blk := fun k => ⟨.inl k, hκ k⟩
  let v : (Σ k, J₀ k) → Σ k, baseIdx (idx (p := D.p) (q := D.q) J₀ n) M.blk k := fun r => ⟨κ r.1, r.2⟩
  refine ⟨K₀ ⊕ StepIx (CMType H) D.p D.q, inferInstance, idx J₀ n, inferInstance, GenField Ω (rk (CMType H) D.p D.q),
    inferInstance, yv (aOf 𝔐 bW bO φ) x₀, M, 𝔐₁, tie, κ, v, RingHom.id Ω, 𝟙 𝔐.X, AddMonoidHom.id 𝔐.Li, 𝔐', Fl, xdeg,
    fun _ => 1, ⟨?_, fun _ => rfl, Function.bijective_id, inferInstanceAs (IsIso (𝟙 𝔐.X)), ?_, rfl, ?_⟩,
    ⟨hd, GlobalTheory.T.hodgeCpt_frame_order_bound E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF ht hv, GlobalTheory.T.hodgeCpt_frame_generic_rank E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ ht⟩,
    GlobalTheory.T.hodgeCpt_frame_unit_criterion E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF hv, ?_, hdeg⟩
  · refine ⟨fun a b h => Sum.inl_injective (congrArg (fun k => k.1) h), ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      have h1 : k = k' := Sum.inl_injective (congrArg (fun r => r.1.1) h)
      subst h1
      have h2 : HEq i i' := (Sigma.mk.inj_iff.1 h).2
      rw [eq_of_heq h2]
    · rintro ⟨_, i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
  · exact HodgeOver.refl 𝔐
  · exact BasesOver.refl bW bO
  · refine ⟨⟨e.hom ≫ f, j, hov, hR, hV, hfl.1, hfl.2⟩, hroot, hdy, fun τ i => ?_⟩
    have h1 : detFac D.p i (M.g τ) = 1 := GlobalTheory.T.detFac_gMat_eq_one (CMType H) D.p D.q Ω τ i
    have h2 : M.lam (τ, i) = 1 := rfl
    rw [h1, h2]
    rcases M.blk (τ, i) with _ | b <;> simp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGivenStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_exists_of_given : Given → PB.FlagModelExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists <;> assumption)
end
