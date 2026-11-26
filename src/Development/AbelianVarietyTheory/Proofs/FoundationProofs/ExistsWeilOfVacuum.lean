module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicWeilRepresentationModel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpTwoAddSmulSinhcAdjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobianActionUpperRightBlockExpCoords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil


set_option maxHeartbeats 1000000 in
theorem exists_weil_of_vacuum (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ)
    (e0 : VC D N N' → ℂ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (h0 : e0 ≠ 0) (χ : HeckeU D N) (χ' : HeckeU D N') :
    ∃ W : WeilO D cc δ N N' e0, W.chV = χ ∧ W.chV' = χ' ∧ W.ep = 1 ∧ W.ep' = 1 := by
  have hg : admG1 D := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨w, γ, WA, hM⟩ := GlobalTheory.T.exists_adelicWeilRepresentationModel D hg cc δ hc N N'
  obtain ⟨hT, hfix, hspan⟩ := GlobalTheory.T.adelicWeil_vacuum_fixed_and_translates_span D hg cc δ hc N N' w γ WA hM e0 he h0
  obtain ⟨lam, hlam, hsq⟩ := GlobalTheory.T.exists_goodIndexNormalization_negative_inert D
  obtain ⟨c', hc1', hc2'⟩ := GlobalTheory.T.exists_split_character_unitary_group D N χ N'
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_split_character_unitary_group D N' χ' N
  have hidx := GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hg cc δ hc N N'
  have hM' := hM
  obtain ⟨hH, hSD, hinv, hrat, hcont⟩ := hM'
  obtain ⟨Om, hOm1, hOm2⟩ := GlobalTheory.T.exists_weil_representation_heisenberg hH lam hlam _ hSD ⟨e0, hT⟩ (fun h => h0 (congrArg Subtype.val h)) hfix hspan
    (actA D N N') hinv (fun u => (hidx u.1 u.2).1)
  let O : GA D N → GA D N' → (VC D N N' → ℂ) → (VC D N N' → ℂ) := fun g g' F =>
    if h : F ∈ TTs D (tor0 D cc δ) N N' then
      ((((c' g' * c g : ℂˣ) : ℂ) • Om (g, g') ⟨F, h⟩ : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) else 0
  have hO : ∀ g g' (F : TTs D (tor0 D cc δ) N N'), O g g' F =
      ((((c' g' * c g : ℂˣ) : ℂ) • Om (g, g') F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := fun g g' F => dif_pos F.2
  refine ⟨{ nz := h0, chV := χ, chV' := χ', ep := 1, ep' := 1, ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩, Om := O,
            maps := ?_, add := ?_, smul := ?_, one := ?_, mul := ?_, lift := ?_, inert := ?_, split := ?_ }, rfl, rfl, rfl, rfl⟩
  · intro g g' F hF
    rw [hO g g' ⟨F, hF⟩]
    exact Subtype.property _
  · intro g g' F hF F' hF'
    have := hO g g' (⟨F, hF⟩ + ⟨F', hF'⟩)
    rw [map_add (f := _), smul_add, Submodule.coe_add, Submodule.coe_add, ← hO, ← hO] at this
    exact this
  · intro g g' a F hF
    have := hO g g' (a • ⟨F, hF⟩)
    rw [map_smul, smul_comm, Submodule.coe_smul, Submodule.coe_smul a, ← hO] at this
    exact this
  · intro F hF
    rw [hO 1 1 ⟨F, hF⟩, map_one, map_one, mul_one, Units.val_one, one_smul, Prod.mk_one_one, map_one]
    rfl
  · intro g₁ g₂ g₁' g₂' F hF
    rw [hO _ _ ⟨F, hF⟩, hO g₂ g₂' ⟨F, hF⟩, hO, map_smul, smul_smul, ← Prod.mk_mul_mk, map_mul Om, map_mul, map_mul,
      ← Units.val_mul, mul_mul_mul_comm]
    rfl
  · intro g g' z F hF
    obtain ⟨m, hm, h⟩ := hcont (actA D N N' (g, g') (z.map (inc D))) (Om (g, g') ⟨F, hF⟩)
    refine ⟨m, hm, fun z' hz' => ?_⟩
    choose a ha1 ha2 using hz'
    have h1 : z'.map (inc D) = actA D N N' (g, g') (z.map (inc D)) + m • (Matrix.of a : XA D N N') := by
      rw [← sub_eq_iff_eq_add']
      ext i j
      rw [actA_apply, ha2 i j, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    have h2 := hrat z ⟨F, hF⟩
    rw [← h2, hO, hO g g' ⟨F, hF⟩, ← hrat, map_smul, hOm1, h1, h (Matrix.of a) ha1]
  · intro k k' hk hk' hs hs'
    have h3 := (GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ (hOm2 (k, k')).1).2.2 ((hidx k k').2.2 hk hk')
    rw [hO k k' ⟨e0, hT⟩, hc1 k hs, hc1' k' hs', mul_one, Units.val_one, one_smul, (hOm2 (k, k')).2, normOp, h3.1,
      h3.2 _ hfix, map_one, inv_one, one_smul]
  · intro g g' x x' L₁ L₁' hs hs' hx h1 h1' hL hL'
    have h3 := GlobalTheory.T.thetaIntertwiner_eq_normalisedAdelicSum D hg cc δ hc N N' w γ WA hM g g' L₁ L₁' hL hL' (hOm2 (g, g')).1 ⟨e0, hT⟩ hfix
    have h4 := hsq _ (hidx g g').1 fun q hq hi => (hidx g g').2.1 q hq (hs q hq hi) (hs' q hq hi)
    rw [hO g g' ⟨e0, hT⟩, hc2 g x (fun q hq hi => (hx q hq hi).1) h1, hc2' g' x' (fun q hq hi => (hx q hq hi).2) h1',
      (hOm2 (g, g')).2, normOp, h4, Submodule.coe_smul, Submodule.coe_smul, ← h3, zpow_one, zpow_one]
    rfl

theorem exists_weil : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even N → Even N' → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ (χ : HeckeU D N) (χ' : HeckeU D N'), ∃ W : WeilO D cc δ N N' e0, W.chV = χ ∧ W.chV' = χ' ∧ W.ep = 1 ∧ W.ep' = 1 :=
  fun D cc δ hc N N' _ _ e0 he h0 χ χ' => exists_weil_of_vacuum D cc δ hc N N' e0 he h0 χ χ'

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelLawsCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

instance finite_levelMod : Finite (LevelMod Dw l) := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ (LevelMod Dw l) := Module.Finite.trans (𝓞 E) _
  have hM : (l.M : ℤ) ≠ 0 := by have := l.three_le; omega
  apply Module.finite_of_fg_torsion
  intro q
  refine ⟨⟨(l.M : ℤ), mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
  change (l.M : ℤ) • (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a = 0
  rw [natCast_zsmul, ← map_nsmul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Moduli.LevelAction.mem_of_modN l ⟨a, rfl⟩)

instance finite_levelAut : Finite (LevelAut Dw l) :=
  Finite.of_injective (fun g : LevelAut Dw l => (g : LevelMod Dw l → LevelMod Dw l)) DFunLike.coe_injective

theorem frMap_id_iff {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y' ↔ y = y' := by
  obtain ⟨hu, hr, -⟩ := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y
  exact ⟨fun h => hu _ _ hr h, fun h => h ▸ hr⟩

section Laws

variable {G : Type} [Group G] (R : RelFam Xo c G)

variable {R}

end Laws

end General

section Record

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

end Record

end GlobalTheory.LevelLawsCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHermitianLogUnitaryBlockDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHermitianLogUnitaryBlockDiagonal
noncomputable section
namespace GlobalTheory.CartanInt.UnitLog
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

theorem norm_entry_le {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (a b : n) :
    ‖A a b‖ ≤ ‖A‖ := by
  have h := A.l2_opNorm_mulVec (EuclideanSpace.single b (1 : ℂ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ (EuclideanSpace.single b (1 : ℂ)))) a
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ (h2.trans h)
  simp

theorem exists_log {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n ℂ)
    (hu : u ∈ unitary (Matrix n n ℂ)) :
    ∃ H : Matrix n n ℂ, Hᴴ = H ∧ ‖H‖ ≤ Real.pi ∧ u = NormedSpace.exp (Complex.I • H) ∧
      ∀ J, Commute u J → Commute (star u) J → Commute H J := by
  have hn : IsStarNormal u := isStarNormal_of_mem_unitary hu
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  refine ⟨cfc (fun z : ℂ => (Complex.arg z : ℂ)) u, ?_, ?_, ?_, fun J h1 h2 => h1.cfc h2 _⟩
  · rw [← Matrix.star_eq_conjTranspose, ← cfc_star]
    refine cfc_congr fun z _ => ?_
    simp
  · refine norm_cfc_le Real.pi_pos.le fun z _ => ?_
    simpa using Complex.abs_arg_le_pi z
  · rw [← cfc_const_mul Complex.I _ u (hf := hfin.continuousOn _),
      ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp' Complex.exp _ u (hf := hfin.continuousOn _)]
    conv_lhs => rw [← cfc_id' ℂ u]
    refine cfc_congr fun z hz => ?_
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hsph z hz, mul_comm _ Complex.I] at this
    simpa using this.symm

theorem isKC_iff_commute {p q : ℕ} (X : Mat p q) : IsKC X ↔ Commute X (Formalism.UG.Jpq p q) := by
  constructor
  · intro h
    ext a b
    have h1 := h a b
    rcases a with i | i <;> rcases b with j | j <;>
      simp_all [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · intro h a b hab
    have h1 := congrFun (congrFun h.eq a) b
    rcases a with i | i <;> rcases b with j | j <;>
      simp [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at h1 hab ⊢
    · linear_combination (-1 / 2 : ℂ) * h1
    · linear_combination (1 / 2 : ℂ) * h1

theorem exists_unitlog : ∀ (p q : ℕ) (k : UpqT p q), k ∈ Kc p q → ∃ H : Mat p q, Hᴴ = H ∧ IsKC H ∧
    (∀ a b, ‖H a b‖ ≤ Real.pi) ∧ UpqT.mat k = NormedSpace.exp (Complex.I • H) := by
  intro p q k hk
  have hu : (UpqT.mat k : Mat p q) ∈ unitary (Mat p q) :=
    Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hk)
  obtain ⟨H, h1, h2, h3, h4⟩ := exists_log _ hu
  refine ⟨H, h1, (isKC_iff_commute H).2 (h4 _ ((isKC_iff_commute _).1 hk) ?_),
    fun a b => (norm_entry_le H a b).trans h2, h3⟩
  rw [Matrix.star_eq_conjTranspose, ← mat_inv_of_mem_Kc hk]
  exact (isKC_iff_commute _).1 ((Ksg p q).inv_mem hk)

end GlobalTheory.CartanInt.UnitLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHermitianLogUnitaryBlockDiagonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_log_unitaryBlockDiagonal : ∀ (p q : ℕ) (k : UpqT p q), k ∈ Kc p q → ∃ H : Mat p q, Hᴴ = H ∧ IsKC H ∧ (∀ a b, ‖H a b‖ ≤ Real.pi) ∧ UpqT.mat k = NormedSpace.exp (Complex.I • H) := by
  first | exact @GlobalTheory.CartanInt.UnitLog.exists_unitlog | exact GlobalTheory.CartanInt.UnitLog.exists_unitlog | (intros; apply GlobalTheory.CartanInt.UnitLog.exists_unitlog <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar

variable {p : ℕ} [Fact p.Prime]

def yAt (g : GL3Theta.G1 p) (v : ℂ) : ℂ_[p] :=
  ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 *
    (lamC g.lam (wpD g.abelian₂ v) / 2 - g.C.s * (lamC g.lam (wpF g.abelian₂ v) - g.C.r) - g.C.t)

theorem norm_natCast_le (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n

theorem sm_add {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

theorem sm_sub {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]; exact sm_add ha (by rwa [norm_neg])

theorem it_add {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)

theorem it_mul {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem sm_mul {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact hb

theorem sm_mul' {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ < 1 := by
  rw [mul_comm]; exact sm_mul hb ha

theorem disc_small (W : WeierstrassCurve ℂ_[p]) (x y : ℂ_[p]) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (hx : ‖x‖ ≤ 1) (he : W.toAffine.Equation x y) (hy : ‖2 * y + W.a₁ * x + W.a₃‖ < 1)
    (hx' : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ < 1) : ‖W.Δ‖ < 1 := by
  let C : WeierstrassCurve.VariableChange ℂ_[p] := ⟨1, x, 0, y⟩
  have hΔ : (C • W).Δ = W.Δ := by
    rw [WeierstrassCurve.variableChange_Δ]; simp [C]
  rw [WeierstrassCurve.Affine.equation_iff] at he
  have e1 : (C • W).a₁ = W.a₁ := by simp [C, WeierstrassCurve.variableChange_a₁]
  have e2 : (C • W).a₂ = W.a₂ + 3 * x := by simp [C, WeierstrassCurve.variableChange_a₂]
  have e3 : (C • W).a₃ = 2 * y + W.a₁ * x + W.a₃ := by
    simp [C, WeierstrassCurve.variableChange_a₃]; ring
  have e4 : (C • W).a₄ = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    simp [C, WeierstrassCurve.variableChange_a₄]; ring
  have e6 : (C • W).a₆ = 0 := by
    simp [C, WeierstrassCurve.variableChange_a₆]; linear_combination -he
  rw [← hΔ]
  have A1 : ‖(C • W).a₁‖ ≤ 1 := e1 ▸ h1
  have A2 : ‖(C • W).a₂‖ ≤ 1 := by
    rw [e2]; exact it_add h2 (it_mul (by simpa using norm_natCast_le (p := p) 3) hx)
  have A3 : ‖(C • W).a₃‖ < 1 := e3 ▸ hy
  have A4 : ‖(C • W).a₄‖ < 1 := e4 ▸ hx'
  set V := C • W
  have n4 : ‖(4 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 4
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2
  have n8 : ‖(8 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 8
  have n27 : ‖(27 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 27
  have n9 : ‖(9 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 9
  have B2 : ‖V.b₂‖ ≤ 1 := by
    rw [WeierstrassCurve.b₂]; exact it_add (by rw [sq]; exact it_mul A1 A1) (it_mul n4 A2)
  have B4 : ‖V.b₄‖ < 1 := by
    rw [WeierstrassCurve.b₄]; exact sm_add (sm_mul n2 A4) (sm_mul A1 A3)
  have B6 : ‖V.b₆‖ < 1 := by
    rw [WeierstrassCurve.b₆, e6, mul_zero, add_zero, sq]; exact sm_mul A3.le A3
  have BetaSesquilinearity : ‖V.b₈‖ < 1 := by
    rw [WeierstrassCurve.b₈, e6]
    simp only [mul_zero, add_zero]
    refine sm_sub (sm_add (sm_sub (by norm_num) (sm_mul (it_mul A1 A3.le) A4))
      (sm_mul A2 (by rw [sq]; exact sm_mul A3.le A3))) (by rw [sq]; exact sm_mul A4.le A4)
  rw [WeierstrassCurve.Δ]
  refine sm_add (sm_sub (sm_sub ?_ (sm_mul n8 (by rw [show V.b₄ ^ 3 = V.b₄ * V.b₄ * V.b₄ by ring]; exact sm_mul (it_mul B4.le B4.le) B4)))
    (sm_mul n27 (by rw [sq]; exact sm_mul B6.le B6))) (sm_mul (it_mul (it_mul n9 B2) B4.le) B6)
  rw [neg_mul]
  rw [norm_neg]; exact sm_mul (by rw [sq]; exact it_mul B2 B2) BetaSesquilinearity

end GlobalTheory.ThetaPar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormThetaTranslateValueAtZeroPadicPeriodic
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormThetaTranslateValueAtZeroPadicPeriodic
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl

variable {p : ℕ} [Fact p.Prime]

theorem norm_lamC_root_mul (lam : Qbar →+* ℂ_[p]) {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1)
    (x : ℂ) : ‖lamC lam (ζ * x)‖ = ‖lamC lam x‖ := by
  have hq : ζ ∈ Qbar := by
    refine mem_algebraicClosure_iff.2 ⟨Polynomial.X ^ n - Polynomial.C 1,
      Polynomial.X_pow_sub_C_ne_zero hn 1, ?_⟩
    simp [hζ]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hζ
    exact zero_ne_one hζ
  have h1 : ‖lam ⟨ζ, hq⟩‖ = 1 := by
    have e : (⟨ζ, hq⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using hζ)
    have : ‖lam ⟨ζ, hq⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, e, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  by_cases hx : x ∈ Qbar
  · have hzx : ζ * x ∈ Qbar := mul_mem hq hx
    simp only [lamC, dif_pos hx, dif_pos hzx]
    have : (⟨ζ * x, hzx⟩ : Qbar) = ⟨ζ, hq⟩ * ⟨x, hx⟩ := rfl
    rw [this, map_mul, norm_mul, h1, one_mul]
  · have hzx : ζ * x ∉ Qbar := by
      intro h
      apply hx
      have : x = ζ⁻¹ * (ζ * x) := by field_simp
      rw [this]
      exact mul_mem (inv_mem hq) h
    simp only [lamC, dif_neg hx, dif_neg hzx]

theorem cval_norm_periodic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t ω : ℂ, InRationalLattice g.abelian₂ t → ω ∈ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g (t + ω)‖ = ‖GlobalTheory.ThetaTransl.cval g t‖ := by
  intro D p _ cc δ g hg t ω ht hω
  obtain ⟨hcc, -, hδ, hΛ, -⟩ := hg
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hcc, hδ⟩).1
  rw [← hΛ] at hlat
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair g.abelian₂ hlat
  have hlaw := (GlobalTheory.OddTheta.sgStar_laws g.abelian₂ hlat).1.2.2.2 ω hω t
  obtain ⟨m, hm, hmt⟩ := ht
  set s := sgStar g.abelian₂ with hs
  set A : ℂ := (area g.abelian₂ : ℂ) with hAdef
  have hA : area g.abelian₂ = GlobalTheory.latticeArea L := GlobalTheory.OddTheta.area_eq L g.abelian₂ hL
  have hA0 : A ≠ 0 := by
    rw [hAdef, hA]; exact_mod_cast (GlobalTheory.latticeArea_pos L).ne'
  set ψ : ℂ := if ω / 2 ∈ g.abelian₂ then 1 else -1 with hψ
  set E : ℂ := Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A)) with hE
  have key : U1 g.abelian₂ (t + ω) s 0 = (ψ * E) * U1 g.abelian₂ t s 0 := by
    have h2 : s (t + ω) = ψ * s t * Complex.exp (-(-(Real.pi : ℂ) * t * (starRingEnd ℂ) ω / A -
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * A))) := by
      have hlaw' := hlaw
      simp only [U1] at hlaw'
      rw [← hlaw', mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    simp only [U1]
    rw [zero_add, zero_add, h2, show ψ * E * (s t * Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) t / A -
        (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * A))) = ψ * s t * (E * Complex.exp (-(Real.pi : ℂ) * 0 *
        (starRingEnd ℂ) t / A - (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * A))) by ring,
      hE, ← Complex.exp_add, mul_assoc (ψ * s t), ← Complex.exp_add]
    congr 1
    congr 1
    simp only [map_add (f := _)]
    ring
  have hroot : (ψ * E) ^ (2 * m) = 1 := by
    have hψ2 : ψ ^ 2 = 1 := by rw [hψ]; split_ifs <;> norm_num
    have ha' : (m : ℂ) * t ∈ L.lattice := (hL _).1 hmt
    have hω' : ω ∈ L.lattice := (hL _).1 hω
    obtain ⟨k, hk⟩ := GlobalTheory.exists_int_im_latticeForm L ha' hω'
    have hL0 : (GlobalTheory.latticeArea L : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.latticeArea_pos L).ne'
    have him : ((m : ℂ) * t * (starRingEnd ℂ) ω).im = k * GlobalTheory.latticeArea L := by
      rw [GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff (GlobalTheory.latticeArea_pos L).ne'] at hk
      exact hk
    have hc : (starRingEnd ℂ) ((m : ℂ) * t * (starRingEnd ℂ) ω) = (m : ℂ) * (starRingEnd ℂ) t * ω := by
      simp [map_mul]
    have hsub := Complex.sub_conj ((m : ℂ) * t * (starRingEnd ℂ) ω)
    rw [hc, him] at hsub
    have hexp : ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A)) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      calc ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A))
          = (Real.pi : ℂ) * ((m : ℂ) * t * (starRingEnd ℂ) ω - (m : ℂ) * (starRingEnd ℂ) t * ω) / A := by
            push_cast; field_simp
        _ = (Real.pi : ℂ) * (((2 * (k * GlobalTheory.latticeArea L) : ℝ) : ℂ) * Complex.I) / A := by rw [hsub]
        _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
            rw [hAdef, hA]; push_cast; field_simp
    rw [mul_pow, pow_mul, hψ2, one_pow, one_mul, hE, ← Complex.exp_nat_mul, hexp,
      Complex.exp_int_mul_two_pi_mul_I]
  unfold cval
  rw [key]
  exact norm_lamC_root_mul g.lam (by omega) hroot _

end GlobalTheory.ThetaTransl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormThetaTranslateValueAtZeroPadicPeriodicStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_thetaTranslateValueAtZeroPadic_periodic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t ω : ℂ, InRationalLattice g.abelian₂ t → ω ∈ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g (t + ω)‖ = ‖GlobalTheory.ThetaTransl.cval g t‖ := by
  first | exact @GlobalTheory.ThetaTransl.cval_norm_periodic | exact GlobalTheory.ThetaTransl.cval_norm_periodic | (intros; apply GlobalTheory.ThetaTransl.cval_norm_periodic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationThetaMovedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationThetaMovedLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.WeilTheta

theorem sd_of_moves (D : D7) {N : ℕ} (g : GA D N) (L : Lat D N) (h : Moves D (g : GL (Fin N) (AE D)) L) :
    SD D L := by
  obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x
    rw [h x, (hLt g).1 x]
  rw [this]
  exact (hLt g).2

theorem om_mem_Th_moved : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h : GA D N) (g' h' : GA D N') (L₁ L₂ : Lat D N) (L₁' L₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' F ∈ Th D (tor0 D cc δ) L₂ L₂' := by
  intro D cc δ hC N N' e0 W g h g' h' L₁ L₂ L₁' L₂' h1 h1' h2 h2' F hF
  have hD := (GlobalTheory.InducedType.induced_type D).1
  have s1 := sd_of_moves D h L₁ h1
  have s1' := sd_of_moves D h' L₁' h1'
  have s2 := sd_of_moves D _ L₂ h2
  have s2' := sd_of_moves D _ L₂' h2'
  obtain ⟨hnice, -⟩ := GlobalTheory.ThetaTriple.klat_triples D cc δ hC N N'
  have n1 := hnice _ (Or.inr ⟨L₁, L₁', s1, s1', rfl⟩)
  have n2 := hnice _ (Or.inr ⟨L₂, L₂', s2, s2', rfl⟩)
  obtain ⟨hT, hW, -⟩ := GlobalTheory.T.thetaFunctions_all_levels_closure D cc δ hC N N'
  have hFT := hT L₁ L₁' s1 s1' F hF
  have hGT := W.maps g g' F hFT
  have hfix := ((n1.mem_ThSp F).1 hF).2
  refine (n2.mem_ThSp _).2 ⟨hGT.1, fun y hy => ?_⟩
  obtain ⟨z, hz, -⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hD cc δ hC.1.1 N N' _ _ L₂ L₂' h2 h2' y hy
  have hWT : Wd D (tor0 D cc δ) y (W.Om g g' F) ∈ TT D (tor0 D cc δ) N N' := by
    rw [hz]; exact hW z _ hGT
  obtain ⟨x, hx, he⟩ := GlobalTheory.WeilEquiv.om_wd_moved D hD cc δ hC.1.1 N N' e0 W g⁻¹ (g * h) g'⁻¹ (g' * h')
    L₂ L₁ L₂' L₁' h2 h2' (by rwa [inv_mul_cancel_left]) (by rwa [inv_mul_cancel_left]) y hy _ hGT
  rw [← W.mul _ _ _ _ F hFT, inv_mul_cancel, inv_mul_cancel, W.one F hFT, hfix x hx] at he
  have h3 := congrArg (W.Om g g') he
  rwa [← W.mul _ _ _ _ _ hWT, mul_inv_cancel, mul_inv_cancel, W.one _ hWT] at h3

end GlobalTheory.WeilTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationThetaMovedLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_theta_moved_lattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h : GA D N) (g' h' : GA D N') (L₁ L₂ : Lat D N) (L₁' L₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' F ∈ Th D (tor0 D cc δ) L₂ L₂' := by
  first | exact @GlobalTheory.WeilTheta.om_mem_Th_moved | exact GlobalTheory.WeilTheta.om_mem_Th_moved | (intros; apply GlobalTheory.WeilTheta.om_mem_Th_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpLogNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpLogNearOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open Filter Topology

namespace GlobalTheory.CartanInt.ExpLocal

attribute [local instance] GlobalTheory.CompactDualExists.sumNormedAddCommGroup
  GlobalTheory.CompactDualExists.sumNormedSpace

theorem l1_eq_norm {n : Type} [Fintype n] (A : Matrix n n ℂ) : l1 A = ‖A‖ :=
  (GlobalTheory.CompactDualExists.sum_norm_def A).symm

theorem exists_exp_approx (n : Type) [Fintype n] [DecidableEq n] :
    ∃ r : ℝ, 0 < r ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < r →
      ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 21 * ‖Y‖ := by
  have h := (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt
  have h2 := h.isLittleO.def (c := 1 / 21) (by norm_num)
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff_ball.1 h2
  refine ⟨r, hr, fun Y hY => ?_⟩
  have h3 := H Y (mem_ball_zero_iff.2 hY)
  rw [NormedSpace.exp_zero, sub_zero] at h3
  exact h3

theorem exp_log_near_one : ∀ (p q : ℕ), ∃ ρ : ℝ, 0 < ρ ∧ (∀ Y : Mat p q, l1 Y < ρ → l1 (NormedSpace.exp Y - 1) ≤ 21 / 20 * l1 Y) ∧ ∀ g : UpqT p q, l1 (UpqT.mat g - 1) < ρ → ∃ X : lieU p q, UpqT.mat g = NormedSpace.exp (X : Mat p q) ∧ l1 (X : Mat p q) ≤ 21 / 20 * l1 (UpqT.mat g - 1) := by
  intro p q
  obtain ⟨r, hr, H⟩ := exists_exp_approx (Fin p ⊕ Fin q)
  have hN := GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds p q r hr
  rw [GlobalTheory.UpqTopology.isInducing_mat.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨T, hT, hsub⟩ := hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hT
  refine ⟨min r ε, lt_min hr hε, fun Y hY => ?_, fun g hg => ?_⟩
  · rw [l1_eq_norm] at hY
    rw [l1_eq_norm, l1_eq_norm]
    have h1 := H Y (hY.trans_le (min_le_left _ _))
    have h2 := norm_le_norm_add_norm_sub' (NormedSpace.exp Y - 1) Y
    have h3 := norm_nonneg Y
    linarith
  · rw [l1_eq_norm] at hg
    have hg' : UpqT.mat g ∈ Metric.ball (UpqT.mat (1 : UpqT p q)) ε := by
      rw [mem_ball_iff_norm, mat_one]
      exact hg.trans_le (min_le_right _ _)
    obtain ⟨X, hX, hgX⟩ := hsub (show g ∈ UpqT.mat ⁻¹' T from hball hg')
    refine ⟨X, hgX, ?_⟩
    have hX' : l1 (X : Mat p q) < r := hX
    rw [l1_eq_norm] at hX'
    rw [l1_eq_norm, l1_eq_norm, hgX]
    have h1 := H X hX'
    have h2 := norm_le_norm_add_norm_sub (NormedSpace.exp (X : Mat p q) - 1) (X : Mat p q)
    linarith

end GlobalTheory.CartanInt.ExpLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpLogNearOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_radius_exp_sub_one_le_and_exists_log : ∀ (p q : ℕ), ∃ ρ : ℝ, 0 < ρ ∧ (∀ Y : Mat p q, l1 Y < ρ → l1 (NormedSpace.exp Y - 1) ≤ 21 / 20 * l1 Y) ∧ ∀ g : UpqT p q, l1 (UpqT.mat g - 1) < ρ → ∃ X : lieU p q, UpqT.mat g = NormedSpace.exp (X : Mat p q) ∧ l1 (X : Mat p q) ≤ 21 / 20 * l1 (UpqT.mat g - 1) := by
  first | exact @GlobalTheory.CartanInt.ExpLocal.exp_log_near_one | exact GlobalTheory.CartanInt.ExpLocal.exp_log_near_one | (intros; apply GlobalTheory.CartanInt.ExpLocal.exp_log_near_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorCombinationParameterSeriesAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorCombinationParameterSeriesAlgebra
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

namespace GlobalTheory.TranslLin

open PowerSeries

theorem taylorCoeffAtZero_const_mul (F : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coef1 (fun z => c * F z) n = c * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]

theorem taylorCoeffAtZero_linearCombination {ι : Type} (s : Finset ι) (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (hφ : ∀ k, Differentiable ℂ (φ k)) (n : ℕ) :
    coef1 (fun z => ∑ k ∈ s, c k * φ k z) n = ∑ k ∈ s, c k * coef1 (φ k) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coef1]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hd : Differentiable ℂ (fun z => ∑ k ∈ s, c k * φ k z) := by
      fun_prop
    rw [GlobalTheory.SerTransport.taylorCoeff_add_entire ((hφ a).const_mul (c a)) hd, taylorCoeffAtZero_const_mul, ih]

theorem exists_retraction : ∃ π : ℂ →ₗ[Qbar] Qbar, ∀ q : Qbar, π (q : ℂ) = q := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ)
    (LinearMap.ker_eq_bot.2 (fun x y h => Subtype.val_injective h))
  exact ⟨π, fun q => LinearMap.congr_fun hπ q⟩

theorem lamC_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {y : ℂ} (h : y ∈ Qbar) :
    lamC lam y = lam ⟨y, h⟩ := dif_pos h

theorem transl_lin : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  intro p _ g ι _ φ c E hE hφ hEq
  obtain ⟨π, hπ⟩ := exists_retraction
  refine ⟨fun k => ((π (c k) : Qbar) : ℂ), fun k => (π (c k)).2, ?_⟩
  have hE' : E = fun z => ∑ k, c k * φ k z := funext hEq
  have key : ∀ n, (⟨coef1 E n, hE.2 n⟩ : Qbar) =
      ∑ k, π (c k) * (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) := by
    intro n
    have h1 : coef1 E n = ∑ k, c k * coef1 (φ k) n := by
      rw [hE']; exact taylorCoeffAtZero_linearCombination Finset.univ φ c (fun k => (hφ k).1) n
    have h2 : π ((⟨coef1 E n, hE.2 n⟩ : Qbar) : ℂ) = π (∑ k, c k * coef1 (φ k) n) :=
      congrArg π h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hπ, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : c k * coef1 (φ k) n = (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) • c k := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [e, map_smul, smul_eq_mul, mul_comm]
  have hser : GL3Theta.ser1 g.lam E =
      ∑ k, C (lamC g.lam ((π (c k) : Qbar) : ℂ)) * GL3Theta.ser1 g.lam (φ k) := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam (hE.2 n), key n, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, coeff_C_mul, GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam ((hφ k).2 n),
      GlobalTheory.SerTransport.lamC_coe]
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  simp only [GlobalTheory.SerTransport.atU_eq, hser]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← coe_substAlgHom hs, map_sum, map_mul]
  simp only [coe_substAlgHom, subst_C]
  rfl

end GlobalTheory.TranslLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorCombinationParameterSeriesAlgebraStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTaylorCombination_parameterSeries_algebraic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  first | exact @GlobalTheory.TranslLin.transl_lin | exact GlobalTheory.TranslLin.transl_lin | (intros; apply GlobalTheory.TranslLin.transl_lin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsInvInvariantOfRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.CartanInt

variable {p q : ℕ}

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem isUnit_mat (g : UpqT p q) : IsUnit (UpqT.mat g) := Units.isUnit _

theorem isCompact_Kc : IsCompact (Kc p q) := by
  have h : Kc p q = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : UpqT p q | UpqT.mat x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  have hcl : IsClosed (Kc p q) := by
    rw [h]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
    exact isClosed_eq (GlobalTheory.UpqTopology.continuous_mat.matrix_elem a b) continuous_const
  have hc : IsCompact (Set.univ.pi fun _ : Ix p q => Set.univ.pi fun _ : Ix p q => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine (GlobalTheory.UpqTopology.isClosedEmbedding_mat.isCompact_preimage (K := _) hc).of_isClosed_subset hcl ?_
  intro x hx a _ b _
  simpa using entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hx)) a b

theorem exists_action (L : Mat p q → (Fin p → Fin q → ℂ)) (hL : ContinuousOn L {g | IsUnit g})
    (hLk : ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B)
    (g : UpqT p q) : ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧
      ∀ B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  let ψ : UpqT p q → (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ) := fun g B => L (UpqT.mat (eP B * g))
  have key : ∀ (x κ : UpqT p q) (B' : Fin p → Fin q → ℂ), κ ∈ Kc p q → x = κ * eP B' →
      L (UpqT.mat x) = B' := by
    intro x κ B' hκ hx
    rw [hx, mat_mul, mat_eP]
    exact hLk _ _ (star_mul_of_mem_Kc hκ)
  have dec : ∀ g B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ g B) := by
    intro g B
    obtain ⟨κ, hκ, B', h⟩ := exists_cartan (eP B * g)
    have : ψ g B = B' := key _ κ B' hκ h
    exact ⟨κ, hκ, by rw [this]; exact h⟩
  have inv : ∀ g B, ψ g⁻¹ (ψ g B) = B := by
    intro g B
    obtain ⟨κ, hκ, h⟩ := dec g B
    refine key _ κ⁻¹ B ((Ksg p q).inv_mem hκ) ?_
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h, mul_inv_cancel_right]
  refine ⟨ψ g, ?_, ?_, dec g⟩
  · exact hL.comp_continuous
      (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_eP.mul continuous_const)) fun B => isUnit_mat _
  · refine Function.bijective_iff_has_inverse.2 ⟨ψ g⁻¹, inv g, fun B => ?_⟩
    have := inv g⁻¹ B
    rwa [inv_inv] at this

theorem haar_polar : ∀ (p q : ℕ) (m : Measure (UpqT p q)), m.IsHaarMeasure → ∃ (c : ℝ) (mK : Measure (UpqT p q)), 0 < c ∧ IsProbabilityMeasure mK ∧ mK (Kc p q)ᶜ = 0 ∧ (∀ k ∈ Kc p q, Measure.map (fun x => k * x) mK = mK) ∧ ∀ f : UpqT p q → ENNReal, Measurable f → ∫⁻ g, f g ∂m = ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ, (∫⁻ k, f (k * eP B) ∂mK) * ENNReal.ofReal (polJ (pY B)) := by
  intro p q m hm
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure p q m hm
  haveI := isInvInvariant_of_right m
  obtain ⟨mK, hprob, hK0, hleft, hright⟩ :=
    GlobalTheory.exists_biinvariant_probability_on_compact_subgroup (UpqT p q) (Ksg p q) isCompact_Kc
  obtain ⟨L, hLc, hL⟩ := GlobalTheory.PolarLogCont.exists_continuousOn_polar_log p q
  have hpos : ∀ B : Fin p → Fin q → ℂ, 0 < polJ (pY B) := fun B => one_pos.trans_le (one_le_polJ _)
  have hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B) := (continuous_polJ p q).comp continuous_pY
  have hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B) :=
    fun B => det_sinhc_eq_polarJacobian p q _ (SinhcPres.sAd_pY p q B)
  have hem : Measurable (eP : (Fin p → Fin q → ℂ) → UpqT p q) := continuous_eP.measurable
  haveI : IsLocallyFiniteMeasure
      ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hJc
  obtain ⟨c, hc, hf⟩ := GlobalTheory.Twist.lintegral_haar_eq_transversal (UpqT p q) (Fin p → Fin q → ℂ) m mK
    (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) (Kc p q) eP hem hK0 hright
    (by
      intro h0
      rw [withDensity_eq_zero_iff hJm.aemeasurable] at h0
      haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot :=
        ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ))
          Set.univ_nonempty) (by rw [h]; rfl)
      obtain ⟨B, hB⟩ := h0.exists
      exact absurd hB (by simpa using hpos B))
    (by
      intro C hC
      have hcomp : IsCompact (L '' (UpqT.mat '' C)) :=
        (hC.image GlobalTheory.UpqTopology.continuous_mat).image_of_continuousOn (hLc.mono (by
          rintro _ ⟨x, -, rfl⟩; exact isUnit_mat x))
      refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
      rintro B ⟨k, hk, hB⟩
      refine ⟨_, ⟨_, hB, rfl⟩, ?_⟩
      rw [mat_mul, mat_eP]
      exact hL _ B (star_mul_of_mem_Kc hk))
    (by
      intro g
      obtain ⟨ψ, hψc, hψb, hψ⟩ := exists_action L hLc hL g
      refine ⟨ψ, hψc.measurable, GlobalTheory.map_withDensity_of_jacobian p q _ ψ hJc hψc hψb ?_, hψ⟩
      have := jacobian_action_p p q (UpqT.mat g) ψ hψc (fun B => by
          obtain ⟨κ, hκ, h⟩ := hψ B
          obtain ⟨U, hU, V, hV, hm⟩ := (mem_Kc_iff κ).1 hκ
          refine ⟨U, hU, V, hV, ?_⟩
          have := congrArg UpqT.mat h
          rwa [mat_mul, mat_mul, mat_eP, mat_eP, hm] at this)
        (fun B => by rw [hdet]; exact hpos B) (SinhcPres.sAd_pY p q)
        (fun B => hasStrictFDerivAt_exp_two_pY p q B (hasDerivAt_exp_two_add_smul p q (pY B)))
      simpa only [hdet] using this)
  refine ⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩
  rw [hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]
  · congr 1
    refine lintegral_congr fun B => ?_
    simp only [Pi.mul_apply, mul_comm]
  · exact Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × UpqT p q => f (z.2 * eP z.1))
      (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))

end GlobalTheory.CartanInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpTwoOfCoshDecayUnitaryPQCover
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpTwoOfCoshDecayUnitaryPQCover
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod pOf)
open GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix

namespace GlobalTheory.CoshSqInt

variable {p q : ℕ}

theorem pOf_mem_pR (B : Matrix (Fin p) (Fin q) ℂ) : pOf B ∈ pR p q := by
  refine ⟨?_, ?_⟩
  · change (pOf B)ᴴ * Jm p q + Jm p q * pOf B = 0
    rw [(pOf_herm B).eq]
    simp [pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp [pOf]

theorem exists_cartan (T : GrpData p q) (g : T.G) :
    ∃ k ∈ T.Kset, g = k * T.expt (pOf (cartanB (T.covU g))) := by
  set B := cartanB (T.covU g) with hB
  refine ⟨g * (T.expt (pOf B))⁻¹, ?_, by simp⟩
  obtain ⟨k₁, -, k₂, -, h⟩ := isCartan_cartanB (T.covU g)
  have h1 : ((T.cov g : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.fromBlocks k₁ 0 0 k₂ * ((T.cov (T.expt (pOf B)) : GL (Ix p q) ℂ) : Mat p q) := by
    rw [T.expt_cov _ (pOf_mem_pR B).1]; exact h
  have h2 : ((T.cov (g * (T.expt (pOf B))⁻¹) : GL (Ix p q) ℂ) : Mat p q) = Matrix.fromBlocks k₁ 0 0 k₂ := by
    rw [map_mul, map_inv, Units.val_mul, h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  change IsKC _
  rw [h2]
  rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp

theorem decay_sq (n : ℕ) (g : Formalism.BasicNotions.UpqT p q) :
    decay n (pOf (cartanB g)) ^ 2 = coshPow (2 * (n : ℝ)) g := by
  unfold decay coshPow singVal
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (pOf (cartanB g)).toBlocks₁₂ = cartanB g := by simp [pOf]
  rw [this, Real.rpow_neg (Real.cosh_pos _).le, inv_pow, ← pow_mul, mul_comm n 2]
  congr 1
  rw [← Real.rpow_natCast]; push_cast; rfl

theorem memLp_two_of_decay : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n →
    ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f →
    (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  intro hI p q n hn T f C hf hd
  obtain ⟨m, hm⟩ := GlobalTheory.MinfMeasure.exists_isMinf p q
  have hc : 2 * (((p + q : ℕ) : ℝ) - 1) < 2 * (n : ℝ) := by
    have : ((p + q : ℕ) : ℝ) < n := by exact_mod_cast hn
    linarith
  have h1 := hI.1 p q m hm _ hc
  haveI := hm.1
  haveI := GlobalTheory.DetSqrtCover.isHaarMeasure_map_covU T
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.CompactDualUnique.exists_eq_smul (T.haar.map T.covU) m
  have h2 : Integrable (coshPow (2 * (n : ℝ))) (T.haar.map T.covU) := by
    rw [ht]; exact h1.smul_measure_nnreal
  have h3 : Integrable (coshPow (2 * (n : ℝ)) ∘ T.covU) T.haar :=
    h2.comp_measurable (GlobalTheory.DetSqrtCover.continuous_covU T).measurable
  have hfm : AEStronglyMeasurable f T.haar := hf.measurable.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hfm]
  refine (h3.const_mul (C ^ 2)).mono' (hfm.norm.pow 2) (Filter.Eventually.of_forall fun g => ?_)
  obtain ⟨k, hk, hg⟩ := exists_cartan T g
  have h4 := hd k hk _ (pOf_mem_pR (cartanB (T.covU g)))
  rw [← hg] at h4
  rw [Real.norm_of_nonneg (by positivity), Function.comp_apply, ← decay_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h4 2

end GlobalTheory.CoshSqInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpTwoOfCoshDecayUnitaryPQCoverStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memLp_two_of_cosh_decay_unitaryPQCover : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n → ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f → (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  first | exact @GlobalTheory.CoshSqInt.memLp_two_of_decay | exact GlobalTheory.CoshSqInt.memLp_two_of_decay | (intros; apply GlobalTheory.CoshSqInt.memLp_two_of_decay <;> assumption)
end
end
