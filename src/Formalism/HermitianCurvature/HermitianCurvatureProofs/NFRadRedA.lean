module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakToStrongSmoothnessReal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCellsOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Plain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Classical

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem uwb_glev {g : Q.Mx k r} (hg : g ∈ B2.UWb k r) : g ∈ Glev k r (Fin.last r) := ⟨hg.1, fun a _ => hg.2 a⟩

theorem glev_uwb {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) : g ∈ B2.UWb k r := ⟨hg.1, fun a => hg.2 a a.isLt⟩

theorem muZ_uwb (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    muZ k r μsec ζ ∈ B2.UWb k r := TwoByOneBlock.emb_mem_UWb (hsec.2 ζ hζ).1

theorem zeta_eq (g : Q.Mx k r) : zetaL k r z z' (Fin.last r) g = herm (Hpk k r) (g *ᵥ z') z := by
  simp [Q.zetaL, Formalism.QuantumDeterminants.fvec]

private theorem one_mem_uwset (w : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r w := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp [UH]

theorem zeta_muZ (hz : inWb k r z) (hz' : inWb k r z') (hsec : IsSection k r z z' μsec) {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) : zetaL k r z z' (Fin.last r) (muZ k r μsec ζ) = ζ := by
  have h1 := one_mem_uwset (k := k) (r := r) z
  have h1' := one_mem_uwset (k := k) (r := r) z'
  have h2 := (TwoByOneBlock.rankOneMem k r z z' μsec hz hz' hsec ζ hζ 1 h1 1 h1').2
  rw [zeta_eq]
  simpa [NF.muZ] using h2

theorem qr_open : IsOpen (QR k r z z') := by
  have hO : IsOpen (OmX r) := by
    have he : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
    rw [he]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  exact (hO.preimage continuous_fst).inter
    (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))

theorem mem_domR (hz : inWb k r z) (hz' : inWb k r z') (hsec : IsSection k r z z' μsec)
    {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QR k r z z') : (q.1, muZ k r μsec q.2) ∈ DomR k r z z' := by
  refine ⟨hq.1, uwb_glev (muZ_uwb hsec hq.2), ?_⟩
  show 0 < GGl k r z z' (muZ k r μsec q.2)
  unfold GGl
  rw [zeta_muZ hz hz' hsec hq.2]
  exact sub_pos.2 hq.2

theorem muZ_contDiffOn (hsec : IsSection k r z z' μsec) :
    ContDiffOn ℝ ∞ (fun ζ => muZ k r μsec ζ) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  simp only [NF.muZ, B2.embWb]
  by_cases h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · simp only [dif_pos h]
    exact hsec.1 _ _
  · simp only [dif_neg h]
    exact contDiffOn_const

theorem decomp (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r z z' g) :
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z', g = h * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * h' := by
  have hU : g ∈ B2.UWb k r := glev_uwb hg
  have hζ : Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) (g *ᵥ z') z) := by
    have h2 := hG
    unfold GGl at h2
    rw [zeta_eq] at h2
    linarith
  obtain ⟨h, hh, h', hh', he⟩ := TwoByOneBlock.rankOneCoord k r z z' μsec hk hz hz' hT hT' hsec g hU hζ
  refine ⟨h⁻¹, BigCellInversePair.uw_inv hh, h', hh', ?_⟩
  rw [zeta_eq]
  exact he

theorem radRedMem : NF.RadRedMem := by
  intro Wp Wq _ _ _ _ k r z z' μsec π π' hB Φ hΦ
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨?_, fun q hq => ?_, fun q hq => Set.indicator_of_notMem hq _⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro q0 hq0
    obtain ⟨V, F, hV, hxV, hF, hΦF⟩ := hs _ (mem_domR hz hz' hsec hq0)
    have hψ : ContDiffOn ℝ ∞ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) (QR k r z z') :=
      contDiffOn_fst.prodMk ((muZ_contDiffOn hsec).comp contDiffOn_snd (fun q hq => hq.2))
    refine ⟨QR k r z z' ∩ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) ⁻¹' V,
      hψ.continuousOn.isOpen_inter_preimage qr_open hV, ⟨hq0, hxV⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (F ∘ fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2))
        (QR k r z z' ∩ (QR k r z z' ∩ (fun q : (Fin r → ℂ) × ℂ => (q.1, muZ k r μsec q.2)) ⁻¹' V)) :=
      hF.comp (hψ.mono fun q hq => hq.1) fun q hq => hq.2.2
    refine hc.congr fun q hq => ?_
    simp only [radR, Set.indicator_of_mem hq.1, Function.comp_apply]
    exact hΦF _ hq.2.2 (uwb_glev (muZ_uwb hsec hq.1.2))
  · simp only [radR, Set.indicator_of_mem hq, Fib, Set.mem_setOf_eq]
    intro p hp
    obtain ⟨hp1, hp2, hpe⟩ := hp
    have h3 := he _ (mem_domR hz hz' hsec hq) p.1 hp1 p.2 hp2
    simp only at h3
    rw [hpe] at h3
    exact h3.symm

theorem radRedInj : NF.RadRedInj := by
  intro Wp Wq _ _ _ _ k r z z' μsec π π' hB Φ hΦ Ψ hΨ hR
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, -, he⟩ := hΦ
  obtain ⟨h0', -, he'⟩ := hΨ
  funext x g
  by_cases hx : (x, g) ∈ DomR k r z z'
  · obtain ⟨hxO, hg, hG⟩ := hx
    obtain ⟨h, hh, h', hh', hd⟩ := decomp hk hz hz' hT hT' hsec hg hG
    have hq : (x, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z' := by
      refine ⟨hxO, ?_⟩
      have h2 := hG
      unfold GGl at h2
      linarith
    have hD := mem_domR hz hz' hsec hq
    have e1 := he _ hD h hh h' hh'
    have e2 := he' _ hD h hh h' hh'
    have hr := congrFun hR (x, zetaL k r z z' (Fin.last r) g)
    simp only [radR, Set.indicator_of_mem hq] at hr
    simp only at e1 e2 hd
    rw [hd, e1, e2, hr]
  · exact (h0 (x, g) hx).trans (h0' (x, g) hx).symm

end Formalism.FourierDecayAlt.P.NFRadRedA

namespace Formalism.FourierDecayAlt.P

theorem radical_reduction_mem : Formalism.FourierDecayAlt.NF.RadRedMem := NFRadRedA.radRedMem

theorem radical_reduction_injective : Formalism.FourierDecayAlt.NF.RadRedInj := NFRadRedA.radRedInj

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
namespace Formalism.FourierDecayAlt.P

theorem integration_formula_constant : Formalism.FourierDecayAlt.B2.IntConst :=
  integration_formula_of_parts iterated_integration_formula rank_one_integration_formula b2_conjInvRaw_proof opposite_weyl_haar_exists
    bruhat_big_cell_factorization unipotent_weyl_properties weight_factorization

theorem integration_formula_normalisation_unique : Formalism.FourierDecayAlt.B2.IntNorm :=
  integral_normalisation_from_constant integration_formula_constant

theorem normalisation_unique_every_setting : Formalism.FourierDecayAlt.B2.IntNormB :=
  normalisation_every_setting integration_formula_normalisation_unique

theorem norm_power_integrable_sharp : Formalism.FourierDecayAlt.B2.GNIntSharp :=
  norm_power_integrable_sharp_of_volume spherical_shell_integral matrix_norm_ge_one norm_ball_volume_sharp

theorem matrix_coefficient_integrable_all : Formalism.FourierDecayAlt.B2.CCIntAll :=
  matrix_coefficient_integrable_of_parts matrix_coefficient_bound_by_norm norm_power_integrable_sharp

namespace IntegrationFormulaNormalisation

theorem exists_both : Formalism.FourierDecayAlt.B2.RealPlaceDataExists ∧ Formalism.FourierDecayAlt.B2.RealPlaceDataNonempty :=
  Formalism.FourierDecayAlt.P.SettingConstruction.setting_exists_of_haar_normalisation Formalism.FourierDecayAlt.P.unitary_group_haar_exists Formalism.FourierDecayAlt.P.weyl_haar_exists
    Formalism.FourierDecayAlt.P.unipotent_haar_exists Formalism.FourierDecayAlt.P.integration_formula_normalisation_unique

end IntegrationFormulaNormalisation

theorem setting_with_prescribed_data_exists : Formalism.FourierDecayAlt.B2.RealPlaceDataExists :=
  Formalism.FourierDecayAlt.P.IntegrationFormulaNormalisation.exists_both.1

theorem lemma_b_from_xi : Formalism.FourierDecayAlt.B2.LemmaBFromXi :=
  Formalism.FourierDecayAlt.P.BesselScaling.lemmaBFromXi_of conjugation_invariance_every_setting dilation_jacobian_every_setting matrix_coefficient_integrable_all normalisation_unique_every_setting

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section local_

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_local {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) {X : Mat k r} (hX : inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → RdV X f₁ x = RdV X f₂ x := by
  intro x hx hxG
  have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt x X 0
  have hγ0 : x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = x := by simp
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp ((t : ℂ) • X) ∈ V :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hV.mem_nhds hx)
  show deriv (fun t : ℝ => f₁ (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f₂ (x * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hmem] with t ht
  exact h _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)

theorem rw_local {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) (w : List (Mat k r)) (hw : ∀ X ∈ w, inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → Rw w f₁ x = Rw w f₂ x := by
  induction w with
  | nil => exact h
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local hV (ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY))) (hw X (by simp)) x hx hxG

theorem rw_smul (w : List (Mat k r)) (c : ℂ) (f : Mat k r → E) : Rw w (c • f) = c • Rw w f := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show RdV X (Rw w (c • f)) = c • RdV X (Rw w f)
    rw [ih]
    funext g
    simp only [RdV, Pi.smul_apply]
    exact deriv_const_smul_field (f := fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) c

end local_

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wq] in
theorem zhat_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => Zhat k r z z' g) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold Zhat herm
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))

omit [FiniteDimensional ℂ Wq] in
theorem dmin_cont (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    Continuous (fun g : Mat k r => Dmin k r z z' g l) := by
  unfold Dmin
  exact ((zhat_cont z z').matrix_submatrix _ _).matrix_det

omit [FiniteDimensional ℂ Wq] in
theorem gf_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => Gf k r z z' g) := by
  unfold Gf
  exact (Complex.continuous_normSq.comp (dmin_cont z z' _)).sub
    (continuous_const.mul (Complex.continuous_normSq.comp (dmin_cont z z' _)))

omit [FiniteDimensional ℂ Wq] in
theorem omPlus_open (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Q.OmPlus k r z z') := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have h1 : ∀ᶠ x in 𝓝 g, ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' x l ≠ 0 := by
    refine Filter.eventually_all.2 fun l => ?_
    by_cases hl : l.val ≤ r
    · filter_upwards [(dmin_cont z z' l).continuousAt.eventually_ne (hg.1 l hl)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hl
  have h2 : ∀ᶠ x in 𝓝 g, 0 < Gf k r z z' x := continuousAt_const.eventually_lt (gf_cont z z').continuousAt hg.2
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

omit [FiniteDimensional ℂ Wq] in
theorem sgs_S (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ ∈ Sset k r D.z ∧
      (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ Sset k r D.z' := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_inv_rev]
    exact ⟨_, BigCellInversePair.uw_inv h1, _, WeylGroupFacts.mem_n_inv h2, rfl⟩
  · exact (sGroup k r D.z' D.z'_mem).2.1 _ ⟨1, BigCellZetaMinors.one_uw _, _, h4, (Matrix.one_mul _).symm⟩ _
      ⟨_, h3, 1, WeylGroupFacts.mem_n_one, (Matrix.mul_one _).symm⟩

omit [FiniteDimensional ℂ Wq] in
theorem sgs_GV (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ GV k r) :
    sgs p y ∈ GV k r := by
  rw [B5.sgs_eq]
  exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B5.inSS_left D hp)) hy) (B5.inSS_right D hp)

omit [FiniteDimensional ℂ Wq] in
theorem sgs_Om (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ Om k r D.z D.z') :
    sgs p y ∈ Om k r D.z D.z' := by
  refine ⟨sgs_GV D hp hy.1, fun l hl => ?_, ?_⟩
  · rw [BigCellZetaMinors.dmin_sgs D hp]; exact hy.2.1 l hl
  · obtain ⟨hs, hs'⟩ := sgs_S D hp
    show 0 < Gf k r D.z D.z' (sgs p y)
    rw [B5.sgs_eq, gInv k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' y]
    exact hy.2.2


end Formalism.FourierDecayAlt.P.PositiveOrbitOpen

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def OmB {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Set (B.Mat k r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g ∧
    ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def IsFrameB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ

def rawJ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) : MA.Qp P.r P.TT → ℂ :=
  fun q => ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq Bs q.1)))

def trJB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawJ P Bs e J ρ)

def wR (k : ℕ) (TT : ℝ) (ζ : ℂ) : ℝ := Real.sqrt ((Complex.normSq ζ - TT) ^ (k - 1))

def rawR (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) : MA.Qp P.r P.TT → ℂ :=
  fun q => ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
    inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (Φ q.1.1 (NF.muZ P.k P.r μsec q.1.2)))

def FamR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r))
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) : Prop :=
  IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r ∧ x.2 ∈ Dc x.1} ∧
  (∀ c ∈ OmX P.r, Q.IsDom P.k P.r Bs.z Bs.z' (Fin.last P.r) (Dc c)) ∧
  (∀ q : MA.Qp P.r P.TT, NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Dc q.1.1) ∧
  Q.FamFF P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) Dc Φ

end defs

def GTrChain : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs),
      FamR P Bs (fun c => {g | Q.wCell P.k P.r (Fin.last P.r) c * g ∈ OmB Bs}) (Q.resG P.k P.r (Fin.last P.r) J) ∧
      (∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P),
        rawJ P Bs e J ρ = rawR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) ρ) ∧
      ∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (Y : ℝ),
        rawJ P Bs e (Q.CV P.k P.r (Y : ℂ) J) ρ =
          ∑ a : Fin 2, ∑ b : Fin 2, rawR P Bs.μsec e
            (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
              (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
                (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) (Q.resG P.k P.r (Fin.last P.r) J)))) ρ

def GRawSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ ρ, rawR P Bs.μsec e Φ ρ ∈ MA.smSub P.r P.TT

def GQLFam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2), FamR P Bs Dc (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ)

def GVTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (b : Fin 2),
        FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ∧
        ∀ ρ, MA.toSm P (rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ρ) =
          MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def GVsTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a : Fin 2),
        FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a) Φ) ∧
        ∀ ρ, MA.toSm P (rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a) Φ) ρ) =
          MA.actA P (star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a)) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def GCore : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
      ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

section act

variable (P : M.Par)

theorem fst_zero : (0 : (MA.DQ P).Pr).1 = 0 := rfl

theorem fst_add (x y : (MA.DQ P).Pr) : (x + y).1 = x.1 + y.1 := rfl

theorem fst_mul (x y : (MA.DQ P).Pr) : (x * y).1 = x.1 * y.1 := rfl

def fstHom : (MA.DQ P).Pr →+ (MA.DQ P).Op where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

theorem fst_sum {ι : Type} (s : Finset ι) (x : ι → (MA.DQ P).Pr) : (∑ i ∈ s, x i).1 = ∑ i ∈ s, (x i).1 :=
  map_sum (fstHom P) x s

theorem op_zero_apply (g : (MA.DQ P).R) : (0 : (MA.DQ P).Op) g = 0 := rfl

theorem op_add_apply (X Z : (MA.DQ P).Op) (g : (MA.DQ P).R) : (X + Z) g = X g + Z g := rfl

def evalHom (g : (MA.DQ P).R) : (MA.DQ P).Op →+ (MA.DQ P).R where
  toFun X := X g
  map_zero' := rfl
  map_add' _ _ := rfl

theorem op_sum_apply {ι : Type} (s : Finset ι) (X : ι → (MA.DQ P).Op) (g : (MA.DQ P).R) :
    (∑ i ∈ s, X i) g = ∑ i ∈ s, X i g :=
  map_sum (evalHom P g) X s

theorem actA_zero (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 0 f = 0 := by
  funext π
  simp only [MA.actA, Matrix.zero_apply, fst_zero, Pi.zero_apply]
  exact Finset.sum_eq_zero fun π' _ => op_zero_apply P (f π')

theorem actA_add (x y : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (x + y) f = MA.actA P x f + MA.actA P y f := by
  funext π
  simp only [MA.actA, Matrix.add_apply, fst_add, Pi.add_apply]
  exact (Finset.sum_congr rfl fun π' _ => op_add_apply P _ _ (f π')).trans Finset.sum_add_distrib

theorem actA_sum {ι : Type} (s : Finset ι) (x : ι → MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (∑ i ∈ s, x i) f = ∑ i ∈ s, MA.actA P (x i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, actA_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, actA_add, ih]

theorem actA_mul (x y : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (x * y) f = MA.actA P x (MA.actA P y f) := by
  funext π
  simp only [MA.actA, Matrix.mul_apply, fst_sum, fst_mul]
  have h1 : ∀ π'' : M.Ty P, (∑ j, (x π j).1 * (y j π'').1) (f π'') =
      ∑ j, (x π j).1 ((y j π'').1 (f π'')) := fun π'' =>
    op_sum_apply P Finset.univ (fun j => (x π j).1 * (y j π'').1) (f π'')
  have h2 : ∀ π' : M.Ty P, (x π π').1 (∑ π'', (y π' π'').1 (f π'')) =
      ∑ π'', (x π π').1 ((y π' π'').1 (f π'')) := fun π' => map_sum (x π π').1 _ _
  exact (Finset.sum_congr rfl fun π'' _ => h1 π'').trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun π' _ => (h2 π').symm))

theorem toSm_of_mem {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) : MA.toSm P u = ⟨u, h⟩ := by
  simp [MA.toSm, h]

theorem toSm_add {u v : MA.Qp P.r P.TT → ℂ} (hu : u ∈ MA.smSub P.r P.TT) (hv : v ∈ MA.smSub P.r P.TT) :
    MA.toSm P (u + v) = MA.toSm P u + MA.toSm P v := by
  rw [toSm_of_mem P hu, toSm_of_mem P hv, toSm_of_mem P (add_mem hu hv)]
  rfl

end act

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
namespace Formalism.FourierDecayAlt.P

theorem coordinate_sizes_in_norm : Formalism.FourierDecayAlt.U.SliceCoordinateSizes :=
  coordinate_sizes_of_parts slice_membership block3_apply_embedding aux_statement_17 hat_z_on_slice level_determinant_z

theorem norm_decay_in_coordinates : Formalism.FourierDecayAlt.U.CoordinateDecay :=
  norm_decay_of_coordinate_sizes coordinate_sizes_in_norm

theorem phi_pointwise_bound : Formalism.FourierDecayAlt.U.PointwiseIntegralBound :=
  phi_bound_of_parts slice_membership derivative_cost_bound norm_decay_in_coordinates weight_integrability

theorem theorem_u : Formalism.FourierDecayAlt.U.TheoremU :=
  theorem_u_of_parts phi_pointwise_bound phi_support_determinant weak_to_strong_smoothness

theorem phi_support_level_function : Formalism.FourierDecayAlt.U.PhiSuppG :=
  phi_support_level_of_parts level_function_slice level_determinant_z hat_z_on_slice

theorem corollary_u2_germ_hypothesis : Formalism.FourierDecayAlt.U.GermExpansionHypothesis :=
  corollary_u2_of_parts theorem_u corollary_u1_truncated_alt star_projection budget_second_corollary
    thresholds_second_corollary phi_support_level_function

theorem germ_expansion_applies : Formalism.FourierDecayAlt.U.UseGerm :=
  germ_expansion_of_parts germ_rate det_weyl_matrix corollary_u2_germ_hypothesis derivative_bound_of_decay
    power_matching scale_matching

theorem germ_expansion_top_level : Formalism.FourierDecayAlt.U.UseGermTop :=
  germ_top_level_of_parts germ_rate det_weyl_matrix top_cells derivative_bound_of_decay

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def GlobCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d : ℝ) : Prop :=
  ∀ Tm ∈ Θ, B.CkOn ⊤ (B.GV k r) Tm.coef ∧ B.CkOn ⊤ (B.GV k r) Tm.coefAdj ∧
    ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r,
        ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ d ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ d

def nDim (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

def bddHat (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  {x | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ X ∈ MA.hatSet P L, x = b * X}

def JDHatBdd : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 ≤ P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L)

def JDHatOp : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ X ∈ MA.hatSet (D.parOf S v) L,
        ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
          (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ B.SmoothCoef (B.GPos (T v).base) t.2 ∧
            B.Commutes (T v).base (B.GPos (T v).base) t.2 ∧
            GlobCoef t.2 (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder t.2 : ℝ) ≤ Cc * nDim S.G.k S.G.r) ∧
          ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
            MA.actA (D.parOf S v) X (trJ S T v e J) =
              (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

def JDJComm : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (d A : ℝ), 0 ≤ d →
      B.SmoothCoef (B.GPos (T v).base) Θ → B.Commutes (T v).base (B.GPos (T v).base) Θ → GlobCoef Θ d →
      Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        B.JF (T v).base (B.opApply Θ F) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧
          ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            B.opApply Θ (B.JF (T v).base F) (B.gq (T v).base x) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base x)

def JDCCLower : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ),
    0 ≤ d → GlobCoef Θ d → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC A m F) →
      B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧ ∀ m : ℕ, B.InCC (A - d) m (B.opApply Θ F)

def TransferSquareIntegrable : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ A : ℝ, Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        ∀ π, MeasureTheory.Integrable
          (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF (T v).base F) π) q‖ ^ 2) (MA.mu0 (D.parOf S v).r (D.parOf S v).TT)

def BoundedOperatorsSquareIntegrable : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∀ u : M.Ty P → MA.SmQ P.r P.TT,
      (∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (u π) q‖ ^ 2) (MA.mu0 P.r P.TT)) →
      ∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (MA.actA P b u π) q‖ ^ 2) (MA.mu0 P.r P.TT)

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

noncomputable section

def foldCV (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (a : List C.Letter)
    (H : B.Mat k r → E) : B.Mat k r → E :=
  a.foldr (fun x J => s • Q.CV k r (x.2 : ℂ) J) H

def CVLocal : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (U : Set (B.Mat k r)) (f₁ f₂ : B.Mat k r → E)
    (Y : ℂ), IsOpen U → B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (U ∩ B.GV k r) f₁ →
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (U ∩ B.GV k r) f₂ → (∀ g ∈ U ∩ B.GV k r, f₁ g = f₂ g) →
    ∀ g ∈ U ∩ B.GV k r, Q.CV k r Y f₁ g = Q.CV k r Y f₂ g

def FoldRev : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Dm : Set (Q.Mx k r)), IsOpen Dm →
    (∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm) →
    ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (s : ℂ) (a : List C.Letter), ∀ g ∈ Q.Glev k r 0 ∩ Dm,
      foldCV k r s a.reverse J g = foldCV k r s a J g

def AdmLen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f)
    (a : List C.Letter), D.AdmAt S v a → a.length ≤ S.Ntop

def CVInCC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (F : B.Mat k r → E) (Y s : ℂ),
    B.InCC A (m + (2 * r + k + 1)) F → B.InCC A m (s • Q.CV k r Y F)

def BesselFoldBuilt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW 100 S T f χ ν' m₀ top A₀ →
    ∀ v, (∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) →
      ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      ∀ a : List C.Letter, a.length ≤ S.Ntop → ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z',
        B.JF (T v).base (foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)) g =
          foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) g

def L2BoundAtTowerPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW 100 S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ ε : ℝ, 0 < ε → ∀ a : List C.Letter, a.length ≤ S.Ntop →
      B.normSq (T v).base (foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)) ≠ ⊤

def FibMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
        J (B.gq (T v).base q) ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' q.2

def TrSmooth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ ρ,
      (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1)))) ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT

def BetaFrame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
    ∀ J₁ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
    ∀ J₂ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z')
          (fun q => B.hsVec (J₁ (B.gq (T v).base q))) ≠ ⊤ →
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z')
          (fun q => B.hsVec (J₂ (B.gq (T v).base q))) ≠ ⊤ →
      betaBig S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z') (T v).base.μsec
          (fun g => B.hsVec (J₁ g)) (fun g => B.hsVec (J₂ g)) =
        MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e J₂)

end

end Formalism.FourierDecayAlt.P.CutMP.En
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedFrameProperty
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x7

theorem fixed_frame_property : C2.FixFrame := by
  intro k r z hz
  ext g
  constructor
  · rintro ⟨hgV, hfix⟩
    have hS : g ∈ Sset k r z := by
      rw [← standard_flag_property k r z hz]
      exact ⟨hgV, fun a => by simp [hfix a]⟩
    refine ⟨hS, uMap_eq hz g 1 fun b => ?_⟩
    simp [Matrix.one_apply, hfix b]
  · rintro ⟨hS, hU⟩
    have hS' := hS
    rw [← standard_flag_property k r z hz] at hS'
    refine ⟨hS'.1, fun a => ?_⟩
    rw [((unipotent_map_frame k r z hz).1 g hS).1 a, hU]
    simp [Matrix.one_apply]

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DiscreteSeriesFormOneReduction
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

end Formalism.FourierDecayAlt.P.DDSmoothness

namespace Formalism.FourierDecayAlt.P

theorem discrete_series_form_one_reduction : Formalism.FourierDecayAlt.ThreeDimData.DDFormOneOfSteps := DDSmoothness.discrete_form_one_side

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCVPresFF
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem isDom_omP {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') :
    Q.IsDom k r z z' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  refine ⟨?_, ?_⟩
  · have e : {g : Q.Mx k r | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
        ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} =
        {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g} ∩
          ⋂ a : Fin r, {g | Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
      ext g; simp
    rw [e]
    exact (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z')).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' _) continuous_const)
  · rintro g ⟨-, hg⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Sset k r z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Sset k r z' := ⟨h', hh', m', hm'.1, rfl⟩
    have hD : ∀ l, Dmin k r z z' (h * m * g * (h' * m')) l = Dmin k r z z' g l :=
      fun l => dInv k r z z' hz hz' _ hs _ hs' g l
    refine ⟨?_, fun a => by rw [hD]; exact hg.2 a⟩
    have e : Gf k r z z' (h * m * g * (h' * m')) = Gf k r z z' g := by
      unfold Gf
      rw [hD, hD]
    rw [e]
    exact hg.1

theorem coefficient_vector_preserves_form : CVPresFF := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _ v J hJ Y s
  have hz := (T v).base.z_mem
  have hz' := (T v).base.z'_mem
  have hD : Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := isDom_omP hz hz'
  have hC : Q.CV S.G.k S.G.r (Y : ℂ) J ∈
      Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) :=
    Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms _ _ S.G.k S.G.r _ _ _ _ 0 _ (Y : ℂ) 0 0 hz hz' hD J hJ
  exact Formalism.FourierDecayAlt.P.Qx8.FFl_smul hC s

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialMapProper
theorem Formalism.FourierDecayAlt.P.polynomial_map_proper : Formalism.FourierDecayAlt.C2.PolyProper :=
  PI.PolynomialProperness.polyProper_of_mx PI.PolynomialProperness.mxFacts
end
