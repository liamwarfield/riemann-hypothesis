module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
public import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DixmierMalliavinFactorisationHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open ValuativeRel GroundTheory.Automorphic.GLnLocal
open scoped Pointwise

noncomputable section
namespace GlobalTheory.StabInt

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem mem_O_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ w.adicCompletionIntegers E := by
  show _ ↔ Valued.v x ≤ 1
  simp only [Valuation.mem_integer_iff]
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 := (Valuation.Compatible.vle_iff_le (v := Valued.v) x 1)
  rw [map_one] at h1
  rw [← h1]
  exact Iff.symm (Valuation.vle_one_iff (valuation (w.adicCompletion E)))

theorem mem_integralGL_of_mem_KGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) :
    g ∈ integralGL (w.adicCompletion E) n := by
  obtain ⟨u, rfl⟩ := hg
  rw [mem_integralGL_iff]
  refine ⟨fun i j => (mem_O_iff _).2 (u i j).2, fun i j => (mem_O_iff _).2 ?_⟩
  rw [← map_inv]
  exact ((u⁻¹ : GL (Fin n) (Ov E w)) i j).2

theorem mem_KGL_of_mem_integralGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ integralGL (w.adicCompletion E) n) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  rw [mem_integralGL_iff] at hg
  have h1 : ∀ i j, g.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.1 i j)
  have h2 : ∀ i j, g⁻¹.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.2 i j)
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem mem_integralGL_of_conj (N t g : GL (Fin n) (w.adicCompletion E))
    (hN : N ∈ integralGL (w.adicCompletion E) n)
    (hsep : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1)
    (htN : t * N = N * t) (ht' : g⁻¹ * t * g ∈ integralGL (w.adicCompletion E) n)
    (hN' : g⁻¹ * N * g ∈ integralGL (w.adicCompletion E) n) : t ∈ integralGL (w.adicCompletion E) n := by
  set F := w.adicCompletion E
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField _ _
  haveI : IsUltrametricDist F :=
    inferInstanceAs (@IsUltrametricDist F (Valued.toNormedField F (WithZero (Multiplicative ℤ))).toDist)
  have hO : ∀ x : F, ‖x‖ ≤ 1 ↔ x ∈ 𝒪[F] := fun x =>
    (Valued.toNormedField.norm_le_one_iff).trans (mem_O_iff x).symm
  have hs : N.val.charpoly.Separable := by
    obtain ⟨u, v, -, -, h⟩ := hsep
    exact ⟨u, v, h⟩
  have hsep' : ∃ u v : Polynomial F, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.val.charpoly + v * Polynomial.derivative N.val.charpoly = 1 := by
    obtain ⟨u, v, hu, hv, h⟩ := hsep
    exact ⟨u, v, fun i => (hO _).2 ((mem_O_iff _).2 (hu i)), fun i => (hO _).2 ((mem_O_iff _).2 (hv i)), h⟩
  have hNi : ∀ i j, ‖N.val i j‖ ≤ 1 := fun i j => (hO _).2 ((mem_integralGL_iff F n).1 hN |>.1 i j)
  have hN'i : ∀ i j, ‖((g.val)⁻¹ * N.val * g.val) i j‖ ≤ 1 := by
    intro i j
    have := ((mem_integralGL_iff F n).1 hN').1 i j
    rw [← Matrix.coe_units_inv]
    exact (hO _).2 this
  obtain ⟨c, hcu, hcN, hy, hdet⟩ := GlobalTheory.IntConj.exists_commuting_mul_integral F n N.val g.val hNi hsep' g.isUnit hN'i
  set cU := hcu.unit with hcU
  have hcUv : (cU : Matrix (Fin n) (Fin n) F) = c := rfl
  have hcadj : c ∈ Algebra.adjoin F {N.val} := GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N.val c hs hcN
  have htNv : Commute t.val N.val := by
    show t.val * N.val = N.val * t.val
    have := congrArg Units.val htN
    simpa [Units.val_mul] using this
  have htc : Commute t.val c := Algebra.commute_of_mem_adjoin_singleton_of_commute hcadj htNv
  have htcU : t * cU = cU * t := Units.ext (by simpa [Units.val_mul, hcUv] using htc.eq)
  set yU := cU⁻¹ * g with hyU
  have hyv : (yU : Matrix (Fin n) (Fin n) F) = c⁻¹ * g.val := by
    rw [hyU, Units.val_mul, Matrix.coe_units_inv, hcUv]
  have hyO : yU ∈ integralGL F n := by
    rw [mem_integralGL_iff]
    have h1 : ∀ i j, (yU : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := fun i j => by
      rw [hyv]; exact (hO _).1 (hy i j)
    refine ⟨h1, fun i j => ?_⟩
    let y₀ : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, h1 i j⟩
    have hy₀ : (RingHom.mapMatrix (𝒪[F]).subtype) y₀ = (yU : Matrix (Fin n) (Fin n) F) := rfl
    have hadj : ∀ i j, (yU : Matrix (Fin n) (Fin n) F).adjugate i j ∈ 𝒪[F] := fun i j => by
      rw [← hy₀, ← RingHom.map_adjugate]
      exact (y₀.adjugate i j).2
    have hd : ‖Ring.inverse (yU : Matrix (Fin n) (Fin n) F).det‖ ≤ 1 := by
      rw [Ring.inverse_eq_inv', norm_inv, hyv, hdet, inv_one]
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ((hO _).1 hd) (hadj i j)
  have e : t = yU * (g⁻¹ * t * g) * yU⁻¹ := by
    have e1 : cU⁻¹ * t * cU = t := by
      rw [mul_assoc, htcU, ← mul_assoc, inv_mul_cancel, one_mul]
    calc t = cU⁻¹ * t * cU := e1.symm
      _ = (cU⁻¹ * g) * (g⁻¹ * t * g) * (cU⁻¹ * g)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyO ht') (Subgroup.inv_mem _ hyO)

def pairGrp {G : Type} [Group G] (t N : G) (h : Commute t N) : Subgroup G where
  carrier := {x | ∃ a b : ℤ, x = t ^ a * N ^ b}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    rw [_root_.zpow_add, _root_.zpow_add, mul_assoc, mul_assoc, ← mul_assoc (N ^ b), (h.zpow_zpow c b).eq.symm, mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    rw [_root_.mul_inv_rev, _root_.zpow_neg, _root_.zpow_neg]
    exact (h.zpow_zpow a b).inv_inv.eq.symm

theorem mem_KGL_of_commute : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N t : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    t * N = N * t → IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) (w.adicCompletion E)))) →
    t ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ n w N t hN hsep htN htc
  set F := w.adicCompletion E
  have hNO : N ∈ integralGL F n := mem_integralGL_of_mem_KGL hN
  let H0 := pairGrp t N htN
  have hC : IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F))) :=
    htc.mul (isCompact_integralGL F n)
  have hsub : (H0 : Set (GL (Fin n) F)) ⊆
      closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F)) := by
    rintro _ ⟨a, b, rfl⟩
    exact Set.mul_mem_mul (subset_closure (Subgroup.zpow_mem_zpowers t a)) (Subgroup.zpow_mem _ hNO b)
  have hH : IsCompact (H0.topologicalClosure : Set (GL (Fin n) F)) := by
    rw [Subgroup.topologicalClosure_coe]
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  obtain ⟨g, hg⟩ := exists_conj_le_integralGL F n hH
  have ht' := hg t (H0.le_topologicalClosure ⟨1, 0, by simp⟩)
  have hN' := hg N (H0.le_topologicalClosure ⟨0, 1, by simp⟩)
  exact mem_KGL_of_mem_integralGL (mem_integralGL_of_conj N t g hNO hsep htN ht' hN')

end GlobalTheory.StabInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBoundedStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N t : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    t * N = N * t → IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) (w.adicCompletion E)))) →
    t ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.StabInt.mem_KGL_of_commute | exact GlobalTheory.StabInt.mem_KGL_of_commute | (intros; apply GlobalTheory.StabInt.mem_KGL_of_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartNearOne

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sum_succ_sub_castSucc {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ f
  have h2 := Fin.sum_univ_castSucc f
  linarith

theorem nmat_entry_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    ‖nmat X z τ a b - (if a = b then 1 else 0)‖ ≤ ‖z‖ := by
  unfold nmat
  by_cases h : b < a
  · have hab : a ≠ b := fun e => lt_irrefl b (e ▸ h)
    rw [dite_eq_left h, if_neg hab, sub_zero]
    exact PiLp.norm_apply_le z _
  · rw [dite_eq_right h]
    split_ifs <;> simp

theorem det_nmat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (mat (nmat X z) τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [mat, nmat]
  · intro a b hab
    have h1 : ¬ b < a := fun h => lt_asymm h hab
    have h2 : a ≠ b := ne_of_lt hab
    simp [mat, nmat, h1, h2]

theorem norm_dmin_zero (X : Data E r) (y : Frame X.Ψ r) (τ : X.Ψ) : ‖dmin X.Gm y τ 0‖ = 1 := by
  haveI : IsEmpty (Fin ((0 : Fin (r + 1)) : ℕ)) := ⟨fun i => absurd i.2 (by simp)⟩
  rw [dmin, lminor, Matrix.det_isEmpty, norm_one]

theorem norm_dmin_last (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) :
    ‖dmin X.Gm (cpt X x z) τ (Fin.last r)‖ = 1 := by
  rw [PoinPf.dmin_cpt_orth X hx]
  have e : lminor (PoinPf.Gw X z τ) (Fin.last r) = (PoinPf.Gw X z τ).det := rfl
  rw [e, PoinPf.Gw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_nmat,
    show (mat (nmat X z) τ).map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (mat (nmat X z) τ) from rfl,
    ← RingHom.map_det, det_nmat, PoinPf.Jd, Matrix.det_diagonal]
  simp only [one_mul, map_one, mul_one, norm_prod, Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]
  simp

theorem abs_sub_mid_le (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    |(la τ i : ℝ) - ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2| ≤ X.spread la τ / 2 := by
  have h1 := le_ciSup (Finite.bddAbove_range fun k => (la τ k : ℝ)) i
  have h2 := ciInf_le (Finite.bddBelow_range fun k => (la τ k : ℝ)) i
  unfold Data.spread
  rw [abs_le]
  constructor <;> linarith

theorem weighted_diff_le (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) (L : Fin (r + 1) → ℝ) {t : ℝ}
    (hL : ∀ i, |L i| ≤ t) (h0 : L 0 = 0) (hr : L (Fin.last r) = 0) :
    ∑ i : Fin r, (la τ i : ℝ) * (L i.succ - L i.castSucc) ≤ r * t * X.spread la τ := by
  set c := ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2
  have hs : 0 ≤ X.spread la τ := by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp [Data.spread]
    · have := abs_sub_mid_le X la τ ⟨0, hr0⟩
      linarith [abs_nonneg ((la τ ⟨0, hr0⟩ : ℝ) - c)]
  have e : ∑ i : Fin r, (la τ i : ℝ) * (L i.succ - L i.castSucc) =
      ∑ i : Fin r, ((la τ i : ℝ) - c) * (L i.succ - L i.castSucc) +
        c * ∑ i : Fin r, (L i.succ - L i.castSucc) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, sum_succ_sub_castSucc, h0, hr, sub_zero, mul_zero, add_zero]
  calc ∑ i : Fin r, ((la τ i : ℝ) - c) * (L i.succ - L i.castSucc)
      ≤ ∑ i : Fin r, X.spread la τ / 2 * (2 * t) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        have h1 := abs_sub (L i.succ) (L i.castSucc)
        have h2 : |L i.succ - L i.castSucc| ≤ 2 * t := by linarith [hL i.succ, hL i.castSucc]
        exact mul_le_mul (abs_sub_mid_le X la τ i) h2 (abs_nonneg _) (by linarith)
    _ = r * t * X.spread la τ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end

theorem chart_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w →
    ∀ z : V (nd X), ‖z‖ ≤ chartRad E r w → cpt X x z ∈ X.dom ∧
      Real.exp (-(1/20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1/10)) ≤ densF X x z := by
  intro E _ _ _ r X la w x hr hx hw z hz
  have hf : (1 : ℝ) ≤ fdeg E := one_le_field_half_degree
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsp : ∀ τ, 0 ≤ X.spread la τ := fun τ => by
    have := abs_sub_mid_le X la τ ⟨0, hr⟩
    linarith [abs_nonneg ((la τ ⟨0, hr⟩ : ℝ) - ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2)]
  have hw0 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => hsp τ) hw
  set δ := chartRad E r w with hδdef
  have hwf : 0 < w + fdeg E := by linarith
  have hδ0 : 0 < δ := by rw [hδdef, chartRad]; positivity
  have key : (r : ℝ) ^ 3 * δ * (w + fdeg E) * 200 = 1 := by
    rw [hδdef, chartRad]
    have : (r : ℝ) ≠ 0 := by positivity
    field_simp
  have hA0 : 0 ≤ (r : ℝ) ^ 3 * δ := by positivity
  have hA : (r : ℝ) ^ 3 * δ ≤ 1 / 200 := by
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ w + fdeg E by linarith) hA0]
  have hr2 : (r : ℝ) ^ 2 * δ ≤ (r : ℝ) ^ 3 * δ := by
    have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this hδ0.le
  obtain ⟨hdom, hd⟩ := GlobalTheory.dmin_rmul_near_one X x hx (nmat X z) hδ0.le (by linarith)
    (fun τ a b => (nmat_entry_le X z τ a b).trans hz)
  change cpt X x z ∈ X.dom at hdom
  change ∀ τ i, dmin X.Gm (cpt X x z) τ i ≠ 0 ∧ |Real.log ‖dmin X.Gm (cpt X x z) τ i‖| ≤ 9 * ((r : ℝ) ^ 2 * δ) at hd
  set t := 9 * ((r : ℝ) ^ 2 * δ) with ht
  have ht0 : 0 ≤ t := by positivity
  refine ⟨hdom, ?_, ?_⟩
  ·
    have hne : ∀ τ i, dmin X.Gm (cpt X x z) τ i ≠ 0 := fun τ i => (hd τ i).1
    have hN := CurvPf.neg2log_nfac X la (cpt X x z) hne
    have hbound : -2 * Real.log (X.nfac la (cpt X x z)) ≤ r * t * w := by
      rw [hN]
      calc ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Real.log ‖dmin X.Gm (cpt X x z) τ i.succ‖ -
            Real.log ‖dmin X.Gm (cpt X x z) τ i.castSucc‖)
          ≤ ∑ τ, (r : ℝ) * t * X.spread la τ :=
            Finset.sum_le_sum fun τ _ => weighted_diff_le X la τ
              (fun i => Real.log ‖dmin X.Gm (cpt X x z) τ i‖) (fun i => (hd τ i).2)
              (by simp only [norm_dmin_zero, Real.log_one])
              (by simp only [norm_dmin_last X hx, Real.log_one])
        _ = (r : ℝ) * t * ∑ τ, X.spread la τ := (Finset.mul_sum _ _ _).symm
        _ ≤ (r : ℝ) * t * w := mul_le_mul_of_nonneg_left hw (by positivity)
    have hsmall : (r : ℝ) * t * w ≤ 1 / 20 := by
      have e1 : (r : ℝ) * t * w = 9 * ((r : ℝ) ^ 3 * δ * w) := by rw [ht]; ring
      have e2 : 0 ≤ (r : ℝ) ^ 3 * δ * fdeg E := by positivity
      rw [e1]
      nlinarith
    have hpos : 0 < X.nfac la (cpt X x z) := by
      unfold Data.nfac
      exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
        Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hne _ _) (hne _ _))) _
    have e : X.nfac la (cpt X x z) ^ 2 = Real.exp (-(-2 * Real.log (X.nfac la (cpt X x z)))) := by
      rw [show -(-2 * Real.log (X.nfac la (cpt X x z))) =
        Real.log (X.nfac la (cpt X x z)) + Real.log (X.nfac la (cpt X x z)) by ring,
        Real.exp_add, Real.exp_log hpos, sq]
    rw [e]
    exact Real.exp_le_exp.2 (by linarith)
  ·
    have hfac : ∀ τ (i : Fin r), Real.exp (-(2 * t)) ≤ ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ ^ (-2 : ℤ) := by
      intro τ i
      obtain ⟨h0, h1⟩ := hd τ i.castSucc
      have hu : 0 < ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ := norm_pos_iff.2 h0
      have hu' : ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ ≤ Real.exp t := by
        calc ‖dmin X.Gm (cpt X x z) τ i.castSucc‖
            = Real.exp (Real.log ‖dmin X.Gm (cpt X x z) τ i.castSucc‖) := (Real.exp_log hu).symm
          _ ≤ Real.exp t := Real.exp_le_exp.2 (abs_le.1 h1).2
      rw [zpow_neg, zpow_two, Real.exp_neg, two_mul, Real.exp_add]
      exact inv_anti₀ (by positivity) (mul_le_mul hu' hu' hu.le (Real.exp_pos _).le)
    have hprod : Real.exp (-(2 * t)) ^ (Fintype.card X.Ψ * r) ≤ densF X x z := by
      unfold densF
      calc Real.exp (-(2 * t)) ^ (Fintype.card X.Ψ * r)
          = ∏ τ : X.Ψ, ∏ i : Fin r, Real.exp (-(2 * t)) := by
            rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
              Fintype.card_fin, ← pow_mul, Nat.mul_comm (Fintype.card X.Ψ)]
        _ ≤ _ := Finset.prod_le_prod₀ (fun τ _ => by positivity) (fun τ _ =>
            Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hfac τ i))
    refine le_trans ?_ hprod
    rw [← Real.exp_nat_mul, QuadraticCoefficientForms.card_Psi X]
    refine Real.exp_le_exp.2 ?_
    push_cast
    have e1 : (fdeg E : ℝ) * r * -(2 * t) = -(18 * ((r : ℝ) ^ 3 * δ * fdeg E)) := by rw [ht]; ring
    have e2 : 0 ≤ (r : ℝ) ^ 3 * δ * w := by positivity
    rw [e1]
    nlinarith

end GlobalTheory.ChartNearOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChartStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normFactor_and_density_near_one_in_flagChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → ∀ z : V (nd X), ‖z‖ ≤ chartRad E r w → cpt X x z ∈ X.dom ∧ Real.exp (-(1/20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1/10)) ≤ densF X x z := by
  first | exact @GlobalTheory.ChartNearOne.chart_near_one | exact GlobalTheory.ChartNearOne.chart_near_one | (intros; apply GlobalTheory.ChartNearOne.chart_near_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MuExist

def nsUnits (E : Type) [Field E] [NumberField E] [IsCMField E] : Subgroup (Neutral.B1.Ideles E) :=
  Subgroup.closure {x | ∃ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ GlobalTheory.UnitaryBC.IsSplitAt w ∧
    Valued.v (u : w.adicCompletion E) = 1 ∧ x = Neutral.B1.localIdele E w u}

theorem localIdele_mem_nsUnits {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (u : (w.adicCompletion E)ˣ) (hw : ¬ GlobalTheory.UnitaryBC.IsSplitAt w) (hu : Valued.v (u : w.adicCompletion E) = 1) :
    Neutral.B1.localIdele E w u ∈ nsUnits E :=
  Subgroup.subset_closure ⟨w, u, hw, hu, rfl⟩

end GlobalTheory.MuExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma

def intVec (K : UQ) (n : ℕ) : Submodule K.O (Fin n → K.E) where
  carrier := {v | ∀ i, v i ∈ (algebraMap K.O K.E).range}
  add_mem' := fun ha hb i => Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun _ => Subring.zero_mem _
  smul_mem' := fun c v hv i => by
    simp only [Pi.smul_apply, Algebra.smul_def]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hv i)

def modelLat {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))
    (P : Matrix (Fin n) (Fin n) K.E) : Submodule K.O B.A :=
  (intVec K n).comap ((Matrix.toLin' P).restrictScalars K.O ∘ₗ ψ.toLinearMap.restrictScalars K.O)

def unitLat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} {K : UQ}
    (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (q : UL n w) :
    Submodule K.O B.A :=
  modelLat B ψ ((((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm)

end GlobalTheory.InertUnitOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSec_sum_smul_bc {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {m : ℕ} (a : Fin m → ℂ)
    (P : Fin m → Frame X.Ψ r → ℂ) (hP : ∀ i, X.IsSec la (P i)) :
    X.IsSec la (fun x => ∑ i, a i * P i x) := by
  refine ⟨DifferentiableOn.fun_sum fun i _ => (hP i).1.const_mul _, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.1 x hx b hb]; ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.2 γ hγ x hx]; ring

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

open Classical in
theorem rdU_unfExt_of_isBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hBC : IsBC hle f' as fs) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) f' k x = ∑ i, σ' (as i) * rdU U (fs i) k x := by
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c' f' ((unfExt hle σ' hσ U).un k ⟨x, h⟩)) else 0) =
    ∑ i, σ' (as i) * (if h : x ∈ (U.X k).dom then toC (evR Xo c (fs i) (U.un k ⟨x, h⟩)) else 0)
  by_cases hx : x ∈ (U.X k).dom
  · simp only [dif_pos hx]
    exact @hBC (CAt σ') _ σ.toAlgebra σ'.toAlgebra hσ _
  · simp only [dif_neg hx, mul_zero, Finset.sum_const_zero]

theorem isUnf_unfExt (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) {U : Unf Xo c σ r} (hU : IsUnf U) : IsUnf (unfExt hle σ' hσ U) := by
  obtain rfl : σ = σ'.comp (incF c c' hle) := RingHom.ext fun a => (hσ a).symm
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hU
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  refine ⟨h1, h2, fun y => ?_, h4, fun a n hd f' hf' k => ?_, h6⟩
  · exact h3 (FrPt.res hle (S := CAt σ') hσ y)
  · obtain ⟨m, as, fs, hfs, hBC⟩ := (secBC_and_cuspBC E H Dw l Xo c c' hle).1 a n f' hf'
    have e : rdU (unfExt hle σ' hσ U) f' k = fun x => ∑ i, σ' (as i) * rdU U (fs i) k x :=
      funext fun x => rdU_unfExt_of_isBC hle σ' hσ U hBC k x
    rw [e]
    exact isSec_sum_smul_bc (U.X k) (laU U a n k) _ _ fun i => h5 a n hd _ (hfs i) k

theorem rdU_unfExt_smul_rulBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) (u : c'.F) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) (u • rulBC hle f) k x = σ' u * rdU U f k x := by
  rw [map_smulₛₗ]
  have e := rdU_unfExt_of_isBC hle σ' hσ U (GlobalTheory.FieldBCModel.isBC_rulBC hle hf.1) k x
  simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_fin_one, map_one, one_mul] at e
  rw [← e]
  rfl

end Gen

theorem cXiAt_covBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (n r : ℕ) (c c' : Coeff l) (hle : c.F ≤ c'.F) (V : HSp D) (hr : V.rank = r) (d : DeltaDat Xo c n) (u : c'.F)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ)
    (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (h : CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0) :
    CXiAt V hr c'.F.val.toRingHom (covBC hle d u) (covUnf hle d u U₂) dict₂ io x₀ xi ((u : ℂ) * c0) := by
  obtain ⟨h1, h2, g, e, F, ik, φ, th, h3, h4, h5⟩ := h
  refine ⟨isUnf_unfExt (le_covCoeff hle d) _ (fun _ => rfl) h1, h2, g, e, F, ik, φ, th, h3, h4, fun h γ hm => ?_⟩
  have e1 := rdU_unfExt_smul_rulBC (le_covCoeff hle d)
    (c'.F.val.toRingHom.comp ((covBC hle d u).eF.symm : (covBC hle d u).c₂.F →+* c'.F)) (fun _ => rfl) U₂
    (show (covCoeff hle d).F from u) hs (dict₂ h).1 (dict₂ h).2
  refine e1.trans ?_
  rw [h5 h γ hm, ← mul_assoc]
  rfl

end GlobalTheory.OneMapAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}


variable (σ) in
def conjHalf (e : AEF F E) (nS nT : ℕ) : AddSubgroup (WOF F E nS nT) where
  carrier := {u | ∀ i j, cAF σ e * u i j = u i j}
  add_mem' := fun {a b} ha hb i j => by
    simp only [Set.mem_setOf_eq] at ha hb
    rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  zero_mem' := fun i j => by simp
  neg_mem' := fun {a} ha i j => by
    simp only [Set.mem_setOf_eq] at ha
    rw [Matrix.neg_apply, mul_neg, ha i j]


variable (σ JS JT xi0 ψ) in
def heisL (w : WOF F E nS nT) : (WOF F E nS nT → ℂ) →ₗ[ℂ] (WOF F E nS nT → ℂ) where
  toFun := heisOF σ JS JT xi0 ψ w
  map_add' := GlobalTheory.WeilPartsF.heisOF_add w
  map_smul' := fun c f => GlobalTheory.WeilPartsF.heisOF_smul c w f


variable (σ JS JT xi0 ψ) in
def commF (u y : WOF F E nS nT) : ℂ :=
  ψ (symplOHF σ JS JT xi0 u y - symplOHF σ JS JT xi0 y u)

theorem heisOF_heisOF (u y : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ u (heisOF σ JS JT xi0 ψ y f) =
      ψ (symplOHF σ JS JT xi0 u y) • heisOF σ JS JT xi0 ψ (u + y) f := by
  funext w
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.HeisThetaF.symplOHF_add_left w u y, GlobalTheory.HeisThetaF.symplOHF_add_right w u y,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heisOF_comm (u y : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ u (heisOF σ JS JT xi0 ψ y f) =
      commF σ JS JT xi0 ψ u y • heisOF σ JS JT xi0 ψ y (heisOF σ JS JT xi0 ψ u f) := by
  rw [heisOF_heisOF, heisOF_heisOF, smul_smul, add_comm y u, commF, ← AddChar.map_add_eq_mul, sub_add_cancel]

theorem heisOF_zero (f : WOF F E nS nT → ℂ) : heisOF σ JS JT xi0 ψ 0 f = f := by
  funext w
  simp only [heisOF, add_zero, GlobalTheory.HeisThetaF.symplOHF_zero_right, AddChar.map_zero_eq_one, one_mul]

theorem cAF_cAF {e : AEF F E} (he : IsSplitIdemF σ e) : cAF σ (cAF σ e) = e := by
  obtain ⟨-, -, v, ε, -, h⟩ := he
  have h2 := congrArg (cAF σ) h
  rw [map_add (f := _), GlobalTheory.HeisThetaF.cAF_algebraMap] at h2
  linear_combination h2 - h

theorem hOF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : hOF σ JS JT x y = 0 := by
  have hcc := cAF_cAF he
  have h2 : e * cAF σ e = 0 := he.2.1
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have e1 : cAF σ (y c b) = e * cAF σ (y c b) := by
    conv_lhs => rw [← hy c b]
    rw [map_mul, hcc]
  rw [e1, ← hx d a]
  linear_combination (incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) * x d a) * h2

theorem symplOHF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : symplOHF σ JS JT xi0 x y = 0 := by
  simp only [symplOHF, symplOF, hOF_half he hx hy, mul_zero, map_zero]

theorem exists_nsmul_fix {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT)
    {g : WOF F E nS nT → ℂ} (hg : IsThetaFunOF σ JS JT xi0 ψ g) :
    ∃ k : ℕ, 0 < k ∧ heisOF σ JS JT xi0 ψ (k • u) g = g := by
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := he
  obtain ⟨α, rfl, hα1, hα0⟩ := id hpl
  obtain ⟨U, hU, hUf⟩ := hg.level
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : ContinuousSMul (AF F) (AEF F E) := IsModuleTopology.toContinuousSMul (AF F) (AEF F E)
  set ε' := algebraMap (AF F) (AEF F E) (pairA F 0 α) with hε'
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  have hce : cAF σ e * ε' = cAF σ e := by
    rw [← hsum]
    linear_combination he2 + hcc
  have hu' : ∀ i j, ε' * u i j = u i j := fun i j => by
    have := hu i j
    calc ε' * u i j = ε' * (cAF σ e * u i j) := by rw [this]
      _ = (cAF σ e * ε') * u i j := by ring
      _ = u i j := by rw [hce, this]
  let φ : Af F → WOF F E nS nT := fun t i j => algebraMap (AF F) (AEF F E) (pairA F 0 t) * u i j
  have hφ : Continuous φ := by
    have h1 : Continuous fun t : Af F => algebraMap (AF F) (AEF F E) (pairA F 0 t) := by
      have : Continuous fun t : Af F => pairA F 0 t := continuous_const.prodMk continuous_id
      have h2 : Continuous fun c : AF F => algebraMap (AF F) (AEF F E) c := by
        simp only [Algebra.algebraMap_eq_smul_one]
        exact continuous_smul.comp (continuous_id.prodMk continuous_const)
      exact h2.comp this
    exact continuous_pi fun i => continuous_pi fun j => h1.mul continuous_const
  have h0 : φ 0 = 0 := by
    funext i j
    show algebraMap (AF F) (AEF F E) (pairA F 0 0) * u i j = 0
    rw [show pairA F 0 0 = (0 : AF F) from rfl, map_zero, zero_mul]
  have hV : φ ⁻¹' (U : Set (WOF F E nS nT)) ∈ nhds (0 : Af F) :=
    (hU.preimage hφ).mem_nhds (by rw [Set.mem_preimage, h0]; exact U.zero_mem)
  obtain ⟨N, hN, hNα⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  have hint : ∀ w, α w ∈ w.adicCompletionIntegers F := fun w => by
    by_cases hw : w = v
    · subst hw
      rw [show α w = 1 from hα1]
      exact one_mem _
    · rw [show α w = 0 from hα0 w hw]
      exact zero_mem _
  have hmem := hNα α hint
  have heq : φ (N • α) = N • u := by
    funext i j
    show algebraMap (AF F) (AEF F E) (pairA F 0 (N • α)) * u i j = (N • u) i j
    rw [show pairA F 0 (N • α) = N • pairA F 0 α by
      show ((0 : Ainf F), N • α) = N • ((0 : Ainf F), α)
      rw [Prod.smul_mk, smul_zero], map_nsmul, smul_mul_assoc, hu' i j, Matrix.smul_apply]
  rw [Set.mem_preimage, heq] at hmem
  refine ⟨N, hN, hUf _ hmem ?_⟩
  ext i j
  show infPartF F E ((N • u) i j) = 0
  rw [Matrix.smul_apply, map_nsmul, ← hu' i j, map_mul, GlobalTheory.WeilPartsF.infPartF_placeIdem hpl, zero_mul, smul_zero]

end GlobalTheory.SplitInvFormF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGeneric

theorem exists_th_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] [CharZero K] (yK : S.R →+* K), ∃ a : S.Gam, yK ⟨S.th a, S.th_mem a⟩ ≠ 0 := by
  intro hL hL₂ o Ω _ _ _ S ρ K _ _ yK
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem hL hL₂ ρ ⟨RingHom.ker yK, RingHom.ker_isPrime yK⟩ 0
  exact ⟨0 + c, fun e => h (RingHom.mem_ker.2 e)⟩

end GlobalTheory.ThetaGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def kernSum (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) :
        ℂ))⁻¹ *
      ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * chW lam γ.1.val.charpoly

def clsSum (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (γ : UE E n) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ) : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n)))
        (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ)) ⊓
          (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) : ℂ))⁻¹ *
        globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q)

end GlobalTheory.BCT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eq_of_toSub_eq {G : Type} [Group G] {H : Subgroup G} {g h : G} (hg : g ∈ H) (hh : h ∈ H)
    (e : toSub H g = toSub H h) : g = h := by
  unfold toSub at e
  rw [dite_eq_left hg, dite_eq_left hh] at e
  exact congrArg Subtype.val e

theorem under_conjSrc (w : Pl E) :
    (conjSrc (GlobalTheory.SplitPts.conjE E) w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
    (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))

theorem conjSrc_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  by_contra h
  exact hw ⟨_, h, under_conjSrc w⟩

theorem ext_cj (w : Pl E) (a : Af E) : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
    Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      f (pLoc E v a) = cj w (pLoc E w a) := by
  rintro v rfl f hf h
  have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
  have hcj : cj v = hex.choose := by unfold cj; rw [dite_eq_left hex]
  rw [hcj]
  exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
    (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _

theorem cLoc_mem_UL {w : Pl E} (hw : ¬ IsSplitAt w) (x : UA E n) : cLoc w x ∈ UL n w := by
  have hUL : UL n w = UJ (cj w) 1 := by unfold UL; rw [if_neg hw]
  rw [hUL]
  show cT (cj w) (cLoc w x).val * 1 * (cLoc w x).val = 1
  have hc := GlobalTheory.SplitPts.comp_eq x w
  have e : (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) =
      (cLoc w x).val.map (cj w) := by
    refine Matrix.ext fun i j => ?_
    exact ext_cj w (pFin E (x.1.val i j)) _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec _ w).1
      (conjLoc_spec _ w).2.1
  rw [e] at hc
  rw [Matrix.mul_one]
  exact hc

theorem cLoc_conj_eq (w : Pl E) (x y : UA E n) (h : cLoc w x = cLoc w y) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y := by
  have hx := GlobalTheory.SplitPts.comp_eq x w
  have hy := GlobalTheory.SplitPts.comp_eq y w
  rw [h] at hx
  have e : ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ =
      ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ := by
    have h1 := mul_eq_one_comm.1 hx
    have h2 := mul_eq_one_comm.1 hy
    calc _ = ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ *
            ((cLoc w y).val * ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map
              (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ) := by rw [← Matrix.mul_assoc, hy, Matrix.one_mul]
      _ = _ := by rw [h1, Matrix.mul_one]
  refine Units.ext (Matrix.ext fun i j => (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective ?_)
  have := congrFun (congrFun e j) i
  simpa using this

end GlobalTheory.LocInj

open GlobalTheory.LocInj in
theorem GlobalTheory.BCT.finU_eq_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ S : Set (Pl E), IsSection S → ∀ x y : finU (E := E) (n := n),
      (∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = toSub (UL n w) (cLoc w (y : UA E n))) → x = y := by
  intro E _ _ _ _ n S hS x y hxy

  have hS' : ∀ w ∈ S, cLoc w (x : UA E n) = cLoc w (y : UA E n) := by
    intro w hw
    by_cases hsp : IsSplitAt w
    · have hUL : ∀ g, g ∈ UL n w := fun g => by unfold UL; rw [if_pos hsp]; trivial
      exact eq_of_toSub_eq (hUL _) (hUL _) (hxy w hw)
    · exact eq_of_toSub_eq (cLoc_mem_UL hsp _) (cLoc_mem_UL hsp _) (hxy w hw)

  have hall : ∀ u : Pl E, cLoc u (x : UA E n) = cLoc u (y : UA E n) := by
    intro u
    obtain ⟨s, ⟨hsS, hsu⟩, -⟩ := hS u
    by_cases hus : u = s
    · subst hus; exact hS' u hsS
    · have hsp : IsSplitAt s := ⟨u, hus, hsu.symm⟩
      obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
      rcases hover u hsu.symm with h | h
      · exact absurd h hus
      · subst h; exact cLoc_conj_eq s _ _ (hS' s hsS)
  have hxi : cInf (x : UA E n) = 1 := MonoidHom.mem_ker.1 x.2
  have hyi : cInf (y : UA E n) = 1 := MonoidHom.mem_ker.1 y.2
  refine Subtype.ext (Subtype.ext (ga_ext (hxi.trans hyi.symm) ?_))
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
  exact congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryPoint_eq_of_section_components_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ x y : finU (E := E) (n := n), (∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = toSub (UL n w) (cLoc w (y : UA E n))) → x = y := by
  first | exact @GlobalTheory.BCT.finU_eq_of_loc | exact GlobalTheory.BCT.finU_eq_of_loc | (intros; apply GlobalTheory.BCT.finU_eq_of_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsCompactIsOpen
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ParabLevel

open GlobalTheory.SmGL

section General

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  {n : Type} [Fintype n] [DecidableEq n]

theorem isClosed_parab_two {a b : Type} (e : a ⊕ b ≃ n) :
    IsClosed (parab R (two e) : Set (GL n R)) := by
  have h : (parab R (two e) : Set (GL n R)) =
      ⋂ (j : b) (i : a), {g : GL n R | (g : Matrix n n R) (e (.inr j)) (e (.inl i)) = 0} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_parab_two R
  rw [h]
  exact isClosed_iInter fun j => isClosed_iInter fun i =>
    isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const

theorem continuous_leviProj {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ x, Fintype (m x)]
    [∀ x, DecidableEq (m x)] (e : (Σ x, m x) ≃ n) : Continuous (leviProj R e) := by
  refine continuous_pi fun x => Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun p : parab R e => ((p : GL n R) : Matrix n n R) (e ⟨x, i⟩) (e ⟨x, j⟩)
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
  · have hc : Continuous fun p : parab R e => ((leviProj R e p⁻¹ x : GL (m x) R) : Matrix (m x) (m x) R) := by
      refine continuous_matrix fun i j => ?_
      show Continuous fun p : parab R e => (((p⁻¹ : parab R e) : GL n R) : Matrix n n R) (e ⟨x, i⟩) (e ⟨x, j⟩)
      exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_elem _ _
    refine hc.congr fun p => ?_
    rw [map_inv]
    rfl

theorem continuous_leviTwo_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    Continuous (leviTwo R a b).symm :=
  (continuous_apply false).prodMk (continuous_apply true)

end General

end GlobalTheory.ParabLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierMalliavinFactorisationFromLibrary
namespace GlobalTheory

theorem dixmierMalliavinFactorisation_fromLibrary : GlobalTheory.Published.DixmierMalliavinFactorisation :=
  CompanionTheory.DM.dixmierMalliavinFactorisation_holds

end GlobalTheory
end
