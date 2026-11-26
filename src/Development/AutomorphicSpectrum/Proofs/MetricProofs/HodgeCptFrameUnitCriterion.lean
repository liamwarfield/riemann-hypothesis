module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatios
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUnique
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterion
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Fields

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]


omit [∀ k, Fintype (ι k)] in
theorem prod_div_mem (y : (Σ k, ι k) → G) (u v : ∀ k, ι k) :
    (∏ k, y ⟨k, u k⟩) / (∏ k, y ⟨k, v k⟩) ∈ blockFnField y := by
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, u k⟩, ⟨k, v k⟩, rfl, rfl⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem blockFnField_eq_top [Algebra ℤ G] (y : (Σ k, ι k) → G) {κ : Type} (f : κ → G) (c₀ : κ)
    (hsub : ∀ j, f j / f c₀ ∈ blockFnField y)
    (hgen : ∀ a : G, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), h ≠ 0 ∧ a = g / h) :
    blockFnField y = ⊤ := by
  have hle : ∀ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), g ∈ blockFnField y := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hsub j
    | algebraMap r => rw [eq_intCast]; exact intCast_mem (blockFnField y) r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, h, hh, -, rfl⟩ := hgen a
  exact div_mem (hle g hg) (hle h hh)

theorem trdeg_top : Algebra.trdeg ℤ (⊤ : IntermediateField ℚ G) = Algebra.trdeg ℤ G := by
  have e : (⊤ : IntermediateField ℚ G) ≃ₐ[ℤ] G := (IntermediateField.topEquiv (F := ℚ) (E := G)).restrictScalars ℤ
  exact e.trdeg_eq

end Fields

section Gen

variable (Ω : Type) [Field Ω] [CharZero Ω] {S : Type} (r : S → ℕ)

theorem trdeg_genField [inst : Algebra ℤ (GenField Ω r)] :
    Algebra.trdeg ℤ (GenField Ω r) = Algebra.trdeg ℤ Ω + Cardinal.mk (GenIx r) := by
  obtain rfl : inst = OreLocalization.instAlgebra := Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic (MvPolynomial (GenIx r) Ω) (GenField Ω r) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (GenIx r) Ω))
  haveI : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr
    (by simpa using (Int.cast_injective (α := Ω)))
  have h1 := trdeg_add_eq ℤ Ω (A := GenField Ω r)
  have h2 := trdeg_add_eq Ω (MvPolynomial (GenIx r) Ω) (A := GenField Ω r)
  rw [trdeg_eq_zero (R := MvPolynomial (GenIx r) Ω) (A := GenField Ω r), add_zero, MvPolynomial.trdeg_of_isDomain] at h2
  rw [← h1, ← h2, Cardinal.lift_id]

end Gen

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]

theorem isArithVar_of_trdeg [Nonempty K] (y : (Σ k, ι k) → G) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : ℕ)
    (htr : Algebra.trdeg ℤ (blockFnField y) = e) : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 1) := by
  refine ⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord y c hc, htr, map_add (f := _), Cardinal.toENat_nat, Cardinal.toENat_nat]
  have h4 : (e : ℕ∞) + (Fintype.card K : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [h4]
  rfl

theorem trdeg_of_isArithVar (x : (Σ k, ι k) → G) (d : ℕ) (hx : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (d + 1)) :
    ∃ c : ∀ k, ι k, (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ Algebra.trdeg ℤ (blockFnField x) = d := by
  obtain ⟨-, ⟨-, -, hrel⟩, -, hdim⟩ := hx
  have hne : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X, h0, map_zero, zero_mul]
  choose c hc using hne
  refine ⟨c, hc, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord x c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField x) + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  rw [map_add (f := _), Cardinal.toENat_nat] at h1
  have h3 : (Algebra.trdeg ℤ (blockFnField x)).toENat + ((Fintype.card K + 1 : ℕ) : ℕ∞) =
      (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
    push_cast at h1 ⊢
    rw [← add_assoc, h1]
    ring
  have h2 : (Algebra.trdeg ℤ (blockFnField x)).toENat = (d : ℕ∞) :=
    WithTop.add_right_cancel (ENat.coe_ne_top _) h3
  exact Cardinal.toENat_eq_natCast.mp h2

end Dim

section Main

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ}

theorem mk_genIx : Cardinal.mk (GenIx (rk Ψ p q)) = ((Fintype.card Ψ * (p.choose 2 + q.choose 2) : ℕ) : Cardinal) := by
  show Cardinal.mk (Σ s : Ψ ⊕ Ψ, {lk : Fin (rk Ψ p q s) × Fin (rk Ψ p q s) // lk.2 < lk.1}) = _
  rw [Cardinal.mk_fintype, Fintype.card_sigma]
  simp only [FlagTrdeg.card_below_diagonal]
  rw [Fintype.sum_sum_type]
  simp [rk, Nat.choose_two_right]
  ring

variable {Ω : Type} [Field Ω] [CharZero Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {n : Ψ ⊕ Ψ → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (rk Ψ p q s) → E)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)

abbrev vals (s : Ψ ⊕ Ψ) : Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω := Matrix.of fun j l => φ s j (c s l)

def chartOf (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) : ∀ k, idx (p := p) (q := q) J₀ n k
  | .inl k => j.1 k
  | .inr t => j.2 t

theorem flagCoord_eq_prod (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) :
    flagCoord _ (seg x₀) φ c j = ∏ k, yv (vals φ c) x₀ ⟨k, chartOf j k⟩ := by
  rw [Fintype.prod_sum_type]
  simp only [flagCoord, yv, chartOf, seg, map_prod]
  rfl

theorem isArithVar_yv (hB : ∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * vals φ c s = 1)
    (hgen : ∀ c₀, seg x₀ c₀ ≠ 0 → ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀), h ≠ 0 ∧ a = g / h)
    (d : ℕ) (hx : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x₀) (d + 1)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (yv (vals φ c) x₀)) (d + Fintype.card Ψ * (p.choose 2 + q.choose 2) + 1) := by
  classical
  obtain ⟨c₀, hc₀, htr⟩ := trdeg_of_isArithVar x₀ d hx
  have hs : seg x₀ c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc₀ k
  obtain ⟨J, hJ, hfrac⟩ := CoordGen.flagCoord_generate Ω E (Ψ ⊕ Ψ) (rk Ψ p q) n _ (seg x₀) φ c c₀ hs (hgen c₀ hs) hB
  haveI : CharZero (GenField Ω (rk Ψ p q)) :=
    charZero_of_injective_algebraMap (algebraMap Ω (GenField Ω (rk Ψ p q))).injective
  have hy : ∀ k, yv (vals φ c) x₀ ⟨k, chartOf J k⟩ ≠ 0 := by
    rw [flagCoord_eq_prod] at hJ
    exact fun k => Finset.prod_ne_zero_iff.1 hJ k (Finset.mem_univ k)
  have htop := blockFnField_eq_top (yv (vals φ c) x₀) (flagCoord _ (seg x₀) φ c) J
    (fun j => by rw [flagCoord_eq_prod, flagCoord_eq_prod]; exact prod_div_mem _ _ _) hfrac
  have htop0 := blockFnField_eq_top x₀ (seg x₀) c₀ (fun j => prod_div_mem x₀ _ _) (hgen c₀ hs)
  haveI : Nonempty (K₀ ⊕ StepIx Ψ p q) := ⟨.inl hx.1.some⟩
  refine isArithVar_of_trdeg _ (chartOf J) hy _ ?_
  rw [htop, trdeg_top, trdeg_genField, ← trdeg_top (G := Ω), ← htop0, htr, mk_genIx]
  push_cast
  rfl

end Main

theorem isArithVar_flagModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x₀) (d + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d hF hx
  exact isArithVar_yv φ (cc 𝔐 bW bO) x₀ hF.2.2.2
    (fun c₀ hc₀ => FracChart.exists_eq_div_adjoin 𝔐.X Ω 𝔐.ξ _ (seg x₀) c₀ 𝔐.tie hc₀) d hx

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterionStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_unit_criterion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x₀) (d + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMat
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMat
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings

theorem det_mul_cols {R : Type} [CommRing R] {N d : ℕ} (M : Matrix (Fin d) (Fin N) R)
    (B : Matrix (Fin N) (Fin N) R) (C : Finset (Fin N)) (hC : C.card = d) :
    (M * B.submatrix id (C.orderEmbOfFin hC)).det =
      ∑ I : Finset (Fin N), (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) *
        minorIJ B I C := by
  rw [GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  have h1 : ∑ I : Finset (Fin N), (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) *
        minorIJ B I C =
      ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin N) => I.card = d),
        (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) * minorIJ B I C := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_
    have hc : s.card ≠ d := fun hc => hs (by simp [hc])
    rw [dif_neg hc, zero_mul]
  rw [h1, Finset.sum_subtype (Finset.univ.filter fun I : Finset (Fin N) => I.card = d)
    (p := fun s : Finset (Fin N) => s.card = d) (fun s => by simp)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dif_pos s.2, MinorCalc.minorIJ_eq_det B s.1 C d s.2 hC]
  rfl

variable {Ψ : Type} {p q : ℕ}

theorem blockEquiv_symm_omEmb (a : Fin q) : (blockEquiv p q).symm (omEmb p q a) = Sum.inl a := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [blockEquiv, omEmb]

theorem blockEquiv_symm_wEmb (a : Fin p) : (blockEquiv p q).symm (wEmb p q a) = Sum.inr a := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [blockEquiv, wEmb]
  omega

theorem blocks_wEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R) (a b : Fin p) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (wEmb p q a) (wEmb p q b) =
      Y a b := by
  rw [Matrix.submatrix_apply, blockEquiv_symm_wEmb, blockEquiv_symm_wEmb, Matrix.fromBlocks_apply₂₂]

theorem blocks_omEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R) (a b : Fin q) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (omEmb p q a) (omEmb p q b) =
      X a b := by
  rw [Matrix.submatrix_apply, blockEquiv_symm_omEmb, blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₁₁]

theorem gMat_posOf (Ω : Type) [Field Ω] (τ : Ψ) (s : Ψ ⊕ Ψ) (hs : s = .inl τ ∨ s = .inr τ)
    (l l' : Fin (rk Ψ p q s)) :
    gMat p q Ω τ (posOf p q s l) (posOf p q s l') = genU Ω (rk Ψ p q) s l l' := by
  rcases hs with rfl | rfl
  · exact blocks_wEmb _ _ l l'
  · exact blocks_omEmb _ _ l l'

theorem posOf_strictMono (s : Ψ ⊕ Ψ) : StrictMono (posOf p q s) := by
  rcases s with τ | τ
  · exact wEmb_strictMono p q
  · exact omEmb_strictMono p q

theorem sum_aExt_mul {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    {L : Type} [Field L] (f : Ω →+* L) (s : Ψ ⊕ Ψ) (j : Fin (n s)) (G : Fin (p + q) → L) :
    ∑ a, f (aExt A s j a) * G a = ∑ l, f (A s j l) * G (posOf p q s l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [aExt, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (posOf p q s l)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem stepOf_fst (r : Ψ × Fin (p + q)) :
    (stepOf Ψ p q r).1 = .inl r.1 ∨ (stepOf Ψ p q r).1 = .inr r.1 := by
  unfold stepOf
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem mem_stepCols_iff (r : Ψ × Fin (p + q)) (a : Fin (p + q)) :
    a ∈ stepCols (p + q) p r.2 ↔
      ∃ y : Fin (((stepOf Ψ p q r).2 : ℕ) + 1),
        posOf p q (stepOf Ψ p q r).1 (Fin.castLE (stepOf Ψ p q r).2.2 y) = a := by
  have hr := r.2.2
  by_cases h : (r.2 : ℕ) < p
  · have e : stepOf Ψ p q r = ⟨.inl r.1, ⟨r.2, h⟩⟩ := dif_pos h
    rw [e]
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨a - q, ?_⟩, Fin.ext ?_⟩
      · show (a : ℕ) - q < (r.2 : ℕ) + 1
        omega
      · show q + ((a : ℕ) - q) = a
        omega
    · rintro ⟨y, rfl⟩
      have hy : (y : ℕ) < (r.2 : ℕ) + 1 := y.2
      show p + q - p ≤ q + (y : ℕ) ∧ q + (y : ℕ) < p + q - p + ((r.2 : ℕ) + 1)
      omega
  · have e : stepOf Ψ p q r = ⟨.inr r.1, ⟨r.2 - p, by show _ < q; omega⟩⟩ := dif_neg h
    rw [e]
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_neg (by omega)]
    constructor
    · intro h1
      refine ⟨⟨a, ?_⟩, Fin.ext rfl⟩
      show (a : ℕ) < (r.2 : ℕ) - p + 1
      omega
    · rintro ⟨y, rfl⟩
      have hy : (y : ℕ) < (r.2 : ℕ) - p + 1 := y.2
      show (y : ℕ) < (r.2 : ℕ) + 1 - p
      omega

theorem det_fMat_eq {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    {K₀ : Type} {J₀ : K₀ → Type} (τ : Ψ) (t : StepIx Ψ p q) (hs : t.1 = .inl τ ∨ t.1 = .inr τ)
    (C : Finset (Fin (p + q)))
    (hC : ∀ a, a ∈ C ↔ ∃ y : Fin ((t.2 : ℕ) + 1), posOf p q t.1 (Fin.castLE t.2.2 y) = a)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) :
    ((fMat A t.1).submatrix J (Fin.castLE t.2.2)).det =
      ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q))
        (coefF (K₀ := K₀) (J₀ := J₀) A ⟨.inr t, J⟩ I) * minorIJ (gMat p q Ω τ) I C := by
  have hf : StrictMono fun y : Fin ((t.2 : ℕ) + 1) => posOf p q t.1 (Fin.castLE t.2.2 y) :=
    (posOf_strictMono t.1).comp (Fin.strictMono_castLE _)
  have hCe : C = Finset.univ.image fun y : Fin ((t.2 : ℕ) + 1) => posOf p q t.1 (Fin.castLE t.2.2 y) := by
    ext a
    simp [hC]
  have hcard : C.card = (t.2 : ℕ) + 1 := by
    rw [hCe, Finset.card_image_of_injective _ hf.injective]
    simp
  have henum : ∀ y, C.orderEmbOfFin hcard y = posOf p q t.1 (Fin.castLE t.2.2 y) := fun y =>
    congrFun (Finset.orderEmbOfFin_unique hcard (fun x => (hC _).2 ⟨x, rfl⟩) hf).symm y
  have hmat : (fMat A t.1).submatrix J (Fin.castLE t.2.2) =
      ((aExt A t.1).map (algebraMap Ω (GenField Ω (rk Ψ p q)))).submatrix J id *
        (gMat p q Ω τ).submatrix id (C.orderEmbOfFin hcard) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.map_apply, id, fMat]
    rw [sum_aExt_mul A _ t.1 (J x) fun a => gMat p q Ω τ a (C.orderEmbOfFin hcard y)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [henum, gMat_posOf Ω τ t.1 hs]
  rw [hmat, det_mul_cols _ _ C hcard]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  by_cases e : I.card = (t.2 : ℕ) + 1
  · rw [dif_pos e]
    simp only [coefF]
    rw [dif_pos e, RingHom.map_det]
    rfl
  · rw [dif_neg e]
    simp [coefF, e]

theorem yv_step :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
      (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀]
      (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω),
    ∀ r k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k → ∀ i : idx J₀ n k,
      yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) *
        minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r k hk i
  unfold blkF at hk
  split_ifs at hk with hp
  obtain rfl := Option.some.inj hk
  exact det_fMat_eq A r.1 (stepOf Ψ p q r) (stepOf_fst r) _ (mem_stepCols_iff r) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMatStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.yv_eq_sum_minors_gMat :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
      (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀]
      (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω),
    ∀ r k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k → ∀ i : idx J₀ n k,
      yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) *
        minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r k hk i
  unfold blkF at hk
  split_ifs at hk
  obtain rfl := Option.some.inj hk
  exact BlockEmbeddings.det_fMat_eq A r.1 (stepOf Ψ p q r)
    (BlockEmbeddings.stepOf_fst r) _ (BlockEmbeddings.mem_stepCols_iff r) i
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartSectionNotMemComponents
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartSectionNotMemComponents
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights (chartLift chartLift_segre_apply)

namespace SecNotIn

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartMono (i : (k : K) → ι k) : MRingOver ℂ ι := ∏ k, X ⟨k, i k⟩

theorem eval_chartMono (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : eval x (chartMono i) = segre x i := by
  simp [chartMono, segre]

theorem eval_scale_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    (c : K → ℂ) {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) :
    ∀ f ∈ Q, eval (fun q => c q.1 * x q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hQ
  have hle : Ideal.span S ≤ RingHom.ker (eval (fun q : Σ k, ι k => c q.1 * x q)) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha c x
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h' : eval (fun q : Σ k, ι k => c q.1 * x q) f = (∏ k, c k ^ a k) * eval x f := h
    rw [h', hx f (Ideal.subset_span hf), mul_zero]
  exact fun f hf => hle hf

theorem mem_of_eval_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) {i : (k : K) → ι k}
    (hw : chartMono i ∉ Q) {g : MRingOver ℂ ι}
    (h : ∀ x : (Σ k, ι k) → ℂ, (∀ f ∈ Q, eval x f = 0) → segre x i ≠ 0 → eval x g = 0) : g ∈ Q := by
  have hrad : g * chartMono i ∈ Q.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p := fun _ => rfl
    rw [hae, map_mul, eval_chartMono]
    by_cases h0 : segre x i = 0
    · rw [h0, mul_zero]
    · rw [h x (fun f hf => by have := hx f hf; rwa [hae] at this) h0, zero_mul]
  rw [hQp.radical] at hrad
  exact (hQp.mem_or_mem hrad).resolve_right hw

def normAt (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => (x ⟨q.1, i q.1⟩)⁻¹ * x q

theorem entry_ne_zero {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (h : segre x i ≠ 0) (k : K) :
    x ⟨k, i k⟩ ≠ 0 := fun h0 => h (Finset.prod_eq_zero (Finset.mem_univ k) h0)

theorem segre_normAt (i i' : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) :
    segre (normAt i x) i' = segre x i' / segre x i := by
  simp only [segre, normAt, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [div_eq_mul_inv, mul_comm]

theorem normAt_mem {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    normAt i x ∈ conePts Q :=
  ⟨fun k => ⟨i k, mul_ne_zero (inv_ne_zero (entry_ne_zero h k)) (entry_ne_zero h k)⟩,
    eval_scale_eq_zero hQ (fun k => (x ⟨k, i k⟩)⁻¹) hx⟩

theorem normAt_mem_chartSet {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ}
    (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    (fun a => segre x (σ a) / segre x i) ∈ chartSet (conePts Q) σ i :=
  ⟨normAt i x, normAt_mem hQ hx h, by rw [segre_normAt, div_self h],
    funext fun a => (segre_normAt i (σ a) x).symm⟩

theorem exists_homogenise {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Fin m) ℂ) :
    ∃ (F : MRingOver ℂ ι) (D : ℕ), ∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
      eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f := by
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, fun x _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨F, D, hF⟩ := hf
    obtain ⟨G, E, hG⟩ := hg
    refine ⟨F * chartMono i ^ E + G * chartMono i ^ D, D + E, fun x hx => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, eval_chartMono, hF x hx, hG x hx]
    ring
  | mul_X f a hf =>
    obtain ⟨F, D, hF⟩ := hf
    refine ⟨F * chartMono (σ a), D + 1, fun x hx => ?_⟩
    simp only [map_mul, eval_chartMono, hF x hx, eval_X]
    field_simp
    ring

theorem chartIdeal_isPrime {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime)
    (hQh : IsMultiHomogIdeal Q) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    {i : (k : K) → ι k} (hw : chartMono i ∉ Q) (hne : chartIdeal (conePts Q) σ i ≠ ⊤) :
    (chartIdeal (conePts Q) σ i).IsPrime := by
  have back : ∀ (f : MvPolynomial (Fin m) ℂ) (F : MRingOver ℂ ι) (D : ℕ),
      (∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
        eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f) →
      F ∈ Q → f ∈ chartIdeal (conePts Q) σ i := by
    intro f F D hF hFQ
    rw [chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 : segre z i ≠ 0 := by rw [hz1]; exact one_ne_zero
    have h := hF z h0
    rw [hz.2 F hFQ, hz1] at h
    simpa using h.symm
  refine ⟨hne, fun {f g} hfg => ?_⟩
  obtain ⟨F, D, hF⟩ := exists_homogenise σ i f
  obtain ⟨G, E, hG⟩ := exists_homogenise σ i g
  have hFG : F * G ∈ Q := mem_of_eval_eq_zero hQp hw fun x hx h0 => by
    have h1 : eval (fun a => segre x (σ a) / segre x i) (f * g) = 0 :=
      (mem_vanishingIdeal_iff.1 hfg) _ (normAt_mem_chartSet hQh σ hx h0)
    rw [map_mul] at h1
    rw [map_mul, hF x h0, hG x h0]
    linear_combination (segre x i ^ D * segre x i ^ E) * h1
  rcases hQp.mem_or_mem hFG with h | h
  · exact Or.inl (back f F D hF h)
  · exact Or.inr (back g G E hG h)

theorem eval_chartSection [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (s : MRingOver ℂ ι) : eval x (chartSection σ i s) = eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add f g hf hg =>
    simp only [chartSection, map_add (f := _)] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [chartSection, map_mul, aeval_X, eval_X] at hf ⊢
    rw [hf]
    rfl

end SecNotIn


open SecNotIn in
theorem chartSection_notMem_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by
  intro K _ _ ι _ Q e m σ i s a hQ hs hsQ J hJ hmem
  obtain ⟨-, ⟨hQp, hQh, -⟩, -⟩ := hQ
  have hJmin := mem_chartComponents.1 hJ
  have hprimeJ : J.IsPrime := hJmin.1.1
  have hne : chartIdeal (conePts Q) σ i ≠ ⊤ := fun h =>
    hprimeJ.ne_top (top_le_iff.1 (h ▸ hJmin.1.2))
  have hw : chartMono i ∉ Q := by
    intro hwQ
    apply hne
    rw [Ideal.eq_top_iff_one, chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 := hz.2 _ hwQ
    rw [eval_chartMono, hz1] at h0
    exact absurd h0 one_ne_zero
  have hprime := chartIdeal_isPrime hQp hQh σ hw hne
  have hJI : J ≤ chartIdeal (conePts Q) σ i := hJmin.2 ⟨hprime, le_rfl⟩ hJmin.1.2
  have hI := hJI hmem
  apply hsQ
  refine mem_of_eval_eq_zero hQp hw fun x hx h0 => ?_
  have hz1 : segre (normAt i x) i = 1 := by rw [segre_normAt, div_self h0]
  have hpt : (fun a => segre (normAt i x) (σ a)) ∈ chartSet (conePts Q) σ i :=
    ⟨normAt i x, normAt_mem hQh hx h0, hz1, rfl⟩
  have h1 : eval (fun a => segre (normAt i x) (σ a)) (chartSection σ i s) = 0 :=
    (mem_vanishingIdeal_iff.1 hI) _ hpt
  have hlift : chartLift σ i (fun a => segre (normAt i x) (σ a)) = normAt i x := by
    funext ⟨k, j⟩
    rw [chartLift_segre_apply σ i _ hz1]
    have : normAt i x ⟨k, i k⟩ = 1 := inv_mul_cancel₀ (entry_ne_zero h0 k)
    rw [this, inv_one, mul_one]
  rw [eval_chartSection, hlift] at h1
  have hsc : eval (normAt i x) s = (∏ k, ((x ⟨k, i k⟩)⁻¹) ^ a k) * eval x s :=
    ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog (fun d hd k => hs d hd k)
      (fun k => (x ⟨k, i k⟩)⁻¹) x
  rw [hsc] at h1
  refine (mul_eq_zero.1 h1).resolve_left ?_
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (entry_ne_zero h0 k))

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartSectionNotMemComponentsStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartSection_not_mem_components : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component <;> assumption)
end
end
