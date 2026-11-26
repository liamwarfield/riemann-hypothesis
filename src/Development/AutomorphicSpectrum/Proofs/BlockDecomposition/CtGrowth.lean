module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.Growth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem exists_unip_bound {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (x : BlockIx a r → Ad E) (y : GL (Fin a) (Cinf E)),
      ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  let Cm : Set (BlockIx a r → Ad E) := Set.univ.pi fun _ => K
  have hCm : IsCompact Cm := isCompact_univ_pi fun _ => hK
  have hT : IsCompact ((fun x => JointCont.finPart g x) '' Cm) :=
    hCm.image (JointCont.continuous_finPart g)
  obtain ⟨C₀, N, hC₀, hgrow⟩ := GlobalTheory.CompanionTheory.BoxBound.exists_growth_uniform hφ hT
  have hI : Continuous (fun x : BlockIx a r → Ad E => JointCont.infPart g x) := by
    have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p)) :=
      continuous_pi fun p => JointCont.continuous_pInf.comp (continuous_apply p)
    exact (JointCont.continuous_unip.comp h1).mul continuous_const
  obtain ⟨B, hB⟩ := (hCm.image (GlobalTheory.CompanionTheory.BoxBound.continuous_height.comp hI)).bddAbove
  have hc : (0 : ℝ) ≤ 1 + 2 * a := by positivity
  refine ⟨C₀ * ((1 + 2 * a) * max B 1) ^ N, N, by positivity, fun x y => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Cm, x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  have e1 : unip ((fun p => algebraMap E (Ad E) (q p)) + x') * (g * infGL E a y) =
      ratGL E a (unip q) * (finGL E a (JointCont.finPart g x') * infGL E a (JointCont.infPart g x' * y)) := by
    rw [unip_add, unip_algebraMap, mul_assoc, ← mul_assoc (unip x'), JointCont.unip_mul_eq, map_mul, mul_assoc]
  rw [e1, hφ.left]
  refine (hgrow _ ⟨x', hx'm, rfl⟩ _).trans ?_
  have hb : height (JointCont.infPart g x') ≤ max B 1 := le_trans (hB ⟨x', hx'm, rfl⟩) (le_max_left _ _)
  have hy := one_le_height y
  have hH : height (JointCont.infPart g x' * y) ≤ (1 + 2 * a) * max B 1 * height y := by
    refine (GlobalTheory.CompanionTheory.BoxBound.height_mul_le' _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by linarith)) hc
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [one_le_height (JointCont.infPart g x' * y)]) hH N) hC₀

theorem ct_growth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), IsAutForm φ → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r φ hφ _ _ μ 𝓕 hμ hF g
  have := hμ
  obtain ⟨C, N, -, h⟩ := exists_unip_bound (r := r) hφ g
  refine ⟨C * μ.real 𝓕, N, fun y => ?_⟩
  refine (norm_setIntegral_le_of_norm_le_const (covol_lt_top μ 𝓕 hF) fun x _ => h x y).trans_eq ?_
  ring

end GlobalTheory.CompanionTheory.CTFin.Growth

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowthStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_moderate_growth_alt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), IsAutForm φ → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth | exact GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth | (intros; apply GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylCharEqGtChar
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.RmCharacter

open ReciprocityTheory.ChartRestriction.TR.Weyl PositivityTheory.RgBcC

theorem gtChar_zero : ∀ (n : ℕ) (t : Fin n → ℂ), gtChar n (0 : Fin n → ℤ) t = 1
  | 0, _ => by simp [gtChar]
  | n + 1, t => by
    have h : interl (0 : Fin (n + 1) → ℤ) = {(0 : Fin n → ℤ)} := by
      ext mu
      simp only [interl, Fintype.mem_piFinset, Pi.zero_apply, Finset.Icc_self, Finset.mem_singleton]
      exact ⟨fun h => funext h, fun h i => congrFun h i⟩
    rw [gtChar, h, Finset.sum_singleton, gtChar_zero n]
    simp [wsum]

theorem wden_ne_zero {n : ℕ} {t : Fin n → ℂ} (ht : Function.Injective t) : wden n t ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  split_ifs with h
  · exact sub_ne_zero.2 fun e => h.ne (ht e)
  · exact one_ne_zero

theorem alt_num {n : ℕ} (lam : Fin n → ℤ) (t : Fin n → ℂ) :
    alt n (lam + delta n) t = (Matrix.of fun i j : Fin n => t i ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det := by
  unfold alt
  congr 1
  refine Matrix.ext fun i j => ?_
  have hj := j.2
  simp only [Matrix.of_apply, Pi.add_apply, delta]
  congr 2
  omega

theorem alt_den {n : ℕ} (t : Fin n → ℂ) :
    alt n ((0 : Fin n → ℤ) + delta n) t = (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))).det := by
  unfold alt
  congr 1
  refine Matrix.ext fun i j => ?_
  have hj := j.2
  simp only [Matrix.of_apply, Pi.add_apply, Pi.zero_apply, delta, zero_add]
  rw [← zpow_natCast]
  congr 1
  omega

theorem weylChar_eq_gtChar {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) (t : Fin n → ℂ) (h0 : ∀ a, t a ≠ 0)
    (ht : Function.Injective t) : weylChar lam t = gtChar n lam t := by
  have hnum := weylGT ℂ n lam hlam t h0
  have hden := weylGT ℂ n (0 : Fin n → ℤ) (fun _ _ _ => le_rfl) t h0
  rw [gtChar_zero, mul_one, alt_den] at hden
  rw [alt_num] at hnum
  rw [weylChar, ← hnum, ← hden, mul_div_cancel_left₀ _ (wden_ne_zero ht)]

theorem rmChar : RmChar := by
  intro n lam hlam t h0 ht
  have hu : IsUnit (diagonal t : Matrix (Fin n) (Fin n) ℂ).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => h0 a)
  have hw : (dw lam).w = lam := by
    simp only [dw, dif_pos hlam]
  rw [Rm, dif_pos hu, ← LinearMap.trace_eq_matrix_trace, weylChar_eq_gtChar lam hlam t h0 ht,
    GlobalTheory.ContraChar.trace_sqRep_diag (dw lam) _ t rfl, hw]

end GlobalTheory.CompanionTheory.RmCharacter
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentOfProjectionZero
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem hecke_pow_kills_of_proj_eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J),
    PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ v : fixed π D.J, D.proj π (v : V) = 0 →
    ∃ j : ℕ, (U ^ j) v = 0 := by
  intro G _ _ _ D V _ _ π hπ t ht U hU v hv

  have hdom : ∀ r : ℕ, D.IsDom (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1
    | succ r ih =>
      rw [pow_succ]
      exact (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ U]
      exact GlobalTheory.T.casselman_first_property G D V π hπ (t ^ r) t (hdom r) ht.1 _ _ ih hU

  have key : ∀ u ∈ twKer π D.N 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ D.J, l ∘ₗ π x = l) → l (π ((t : G) ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := ht.2.1 (n : G) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : (t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹ ∈ D.J ⊓ D.N := by
        have := (hdom j).1 _ hR
        convert this using 1
        simp only [Subgroup.coe_pow]
        rw [add_comm R j, pow_add]
        group
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π ((t : G) ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π ((t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹) (π ((t : G) ^ (R + j)) w)
          = π ((t : G) ^ (R + j)) (π (n : G) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add (f := _), map_add (f := _), hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((U ^ R) v : fixed π D.J) : V) = 0 := by
    refine GlobalTheory.T.fixed_vector_zero_of_dual G D.J D.isCompact_J V π hπ _ ((U ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, Subgroup.coe_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Cass
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupport
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.ConvHecke

theorem conv_isHecke : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (K L : Subgroup H) (f₁ f₂ : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → IsHecke L f₁ → IsHecke L f₂ →
    IsHecke L (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ∧
      ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
  intro H _ _ _ _ K L f₁ f₂ hLK hfin h₁ h₂
  have hu : ∀ y, L ≤ rStab (fun z => f₁ z * f₂ (z⁻¹ * y)) := by
    intro y l hl x
    show f₁ (x * l) * f₂ ((x * l)⁻¹ * y) = f₁ x * f₂ (x⁻¹ * y)
    have e : (x * l)⁻¹ * y = l⁻¹ * (x⁻¹ * y) := by group
    rw [e, (h₁.2 l hl x).2, (h₂.2 l⁻¹ (L.inv_mem hl) _).1]
  have hlev := fun y =>
    GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L (fun z => f₁ z * f₂ (z⁻¹ * y)) hLK (hu y) hfin
  have hnz : ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 →
      ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    apply hy
    rw [hlev y]
    have hz : ∀ p : H ⧸ L, f₁ p.out * f₂ ((p.out)⁻¹ * y) = 0 := by
      intro p
      by_cases h : f₁ p.out = 0
      · simp [h]
      · simp [hcon _ h]
    simp [hz]
  refine ⟨⟨?_, ?_⟩, hnz⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (h₁.1.isCompact.mul h₂.1.isCompact) ?_
    intro y hy
    obtain ⟨z, hz1, hz2⟩ := hnz y hy
    exact Set.mem_mul.2 ⟨z, subset_tsupport _ hz1, z⁻¹ * y, subset_tsupport _ hz2, by group⟩
  · intro l hl x
    constructor
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (l * x))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      rw [hlev (l * x), hlev x]
      congr 1
      refine (finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (H ⧸ L))).symm.trans
        (finsum_congr fun p => ?_)
      set w : H := ((MulAction.toPerm l : Equiv.Perm (H ⧸ L)) p).out with hw
      have hcl : ((l * p.out : H) : H ⧸ L) = (w : H ⧸ L) := by
        rw [hw, QuotientGroup.out_eq']
        show ((l * p.out : H) : H ⧸ L) = l • p
        conv_rhs => rw [← QuotientGroup.out_eq' p]
        rfl
      have hm : (l * p.out)⁻¹ * w ∈ L := QuotientGroup.eq.1 hcl
      have hinv := hu (l * x) hm (l * p.out)
      have hmul : l * p.out * ((l * p.out)⁻¹ * w) = w := by group
      simp only [hmul] at hinv
      refine hinv.trans ?_
      have e : (l * p.out)⁻¹ * (l * x) = (p.out)⁻¹ * x := by group
      rw [e, (h₁.2 l hl _).1]
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      have e : (fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = fun z => f₁ z * f₂ (z⁻¹ * x) := by
        funext z
        rw [← mul_assoc, (h₂.2 l hl _).2]
      rw [e]

end GlobalTheory.CompanionTheory.ConvHecke

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupportStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_convolution_support : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (f₁ f₂ : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → IsHecke L f₁ → IsHecke L f₂ →
  IsHecke L (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ∧ ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke | exact GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke | (intros; apply GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusArchimedeanFrameAction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusArchimedeanFrameAction
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem mul_frameLine {n r : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {P : Matrix (Fin n) (Fin r) ℂ}
    (Q : Matrix (Fin r) (Fin n) ℂ) {d : Fin r → ℂ} (hA : A * P = P * diagonal d) (i : Fin r) :
    A * (P * single i i (1 : ℂ) * Q) = d i • (P * single i i (1 : ℂ) * Q) := by
  have e : diagonal d * single i i (1 : ℂ) = d i • single i i (1 : ℂ) := by
    ext a b
    by_cases h : i = a
    · subst h
      simp [Matrix.diagonal_mul, Matrix.single_apply]
    · simp [Matrix.diagonal_mul, Matrix.single_apply, h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.mul_assoc P, e, Matrix.mul_smul, Matrix.smul_mul]

theorem map_frameLine {E : Type} [Field E] {n r : ℕ} (f : E →+* ℂ) (P : Matrix (Fin n) (Fin r) E)
    (Q : Matrix (Fin r) (Fin n) E) (i : Fin r) :
    (P * single i i (1 : E) * Q).map f = P.map f * single i i (1 : ℂ) * Q.map f := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext a b
  by_cases h : a = i ∧ b = i
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [Matrix.single_apply, show ¬(i = a ∧ i = b) from fun q => h ⟨q.1.symm, q.2.symm⟩]

theorem torus_mul_frameIdem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → (∀ i, 0 < t i) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (β : FrameIx r), archMat σ J τ (projArch σ J w a) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = ((frameWt t β : ℝ) : ℂ) • (frameIdem (σ : E →+* E) J X Y β).map τ.1 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW t a ha _ w τ β
  obtain ⟨h1, h2, h3⟩ := ha.2 w τ
  have yx : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, show cT (σ : E →+* E) (cT (σ : E →+* E) X) = X from
      Matrix.ext fun i j => sigma_sigma h _, GlobalTheory.UAut.cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  rcases β with _ | i | i
  · have hV : (cT (σ : E →+* E) X * J) * frameIdem (σ : E →+* E) J X Y none = 0 := by
      simp only [frameIdem, Matrix.mul_sub, Matrix.mul_one]
      rw [← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy]
      simp
    have hU : (cT (σ : E →+* E) Y * J) * frameIdem (σ : E →+* E) J X Y none = 0 := by
      simp only [frameIdem, Matrix.mul_sub, Matrix.mul_one]
      rw [← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.yy, yx]
      simp
    have col : ∀ (M : Matrix (Fin r) (Fin n) E), M * frameIdem (σ : E →+* E) J X Y none = 0 → ∀ j,
        M *ᵥ (fun k => frameIdem (σ : E →+* E) J X Y none k j) = 0 := fun M hM j => by
      funext i
      exact congrFun (congrFun hM i) j
    have key : archMat σ J τ (projArch σ J w a) * (frameIdem (σ : E →+* E) J X Y none).map τ.1 =
        (frameIdem (σ : E →+* E) J X Y none).map τ.1 := by
      ext i j
      exact congrFun (h3 _ (col _ hV j) (col _ hU j)) i
    simpa [frameWt] using key
  · simp only [frameIdem, frameWt]
    rw [map_frameLine]
    exact mul_frameLine _ h1 i
  · simp only [frameIdem, frameWt]
    rw [map_frameLine, Complex.ofReal_inv]
    exact mul_frameLine _ h2 i

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusArchimedeanFrameActionStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_archimedean_frame_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → (∀ i, 0 < t i) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (β : FrameIx r), archMat σ J τ (projArch σ J w a) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = ((frameWt t β : ℝ) : ℂ) • (frameIdem (σ : E →+* E) J X Y β).map τ.1 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.torus_mul_frameIdem | exact GlobalTheory.CompanionTheory.RapidDecay.torus_mul_frameIdem | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.torus_mul_frameIdem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGLMulVecAndNabsDet
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem det_one_add_eLast {k : Type} [Field k] {n : ℕ} (b : Fin (n + 1) → k) :
    (1 + vecMulVec (eLast k n) b).det = 1 + b (Fin.last n) := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    GlobalTheory.BZMir.eLast, dotProduct_single, mul_one]

theorem shearGL_mulVec_and_nabs_det : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (b : Fin (n + 1) → k), valuation k (b (Fin.last n)) < 1 → (∀ x : Fin (n + 1) → k, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x = x + (b ⬝ᵥ x) • eLast k n) ∧ nabs k (Matrix.GeneralLinearGroup.det (shearGL n b)) = 1 := by
  intro k _ _ _ _ n b hb
  have hv : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hb
  have hdet := GlobalTheory.CompanionTheory.MirPair.det_one_add_eLast b
  have hunit : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero]
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    simp only [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hunit, IsUnit.unit_spec]
  refine ⟨fun x => ?_, ?_⟩
  · rw [hcoe, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [Matrix.GeneralLinearGroup.val_det_apply, hcoe, hdet, hv]

end GlobalTheory.CompanionTheory.MirPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthVanishing
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem twist_integral_eq_JJ_shear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (b : Fin (n + 1) → k) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V'), valuation k (b (Fin.last n)) < 1 → T (levi k (n + 1) (shearGL n b)) v = v → (∀ x, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M) → ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = JJ ν ψ T B M v (T' (levi k (n + 1) (shearGL n b)) v') := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T T' B s _ _ hB b M v v' hb hfix hM
  obtain ⟨hg, hdet⟩ := GlobalTheory.CompanionTheory.MirPair.shearGL_mulVec_and_nabs_det b hb
  obtain ⟨-, -, hlevi⟩ := GlobalTheory.CompanionTheory.MirPair.coef_rules T T' B s hB
  have hcoef : ∀ x, GlobalTheory.CompanionTheory.MirPair.coef T B v
      (T' (GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) v') x =
      GlobalTheory.CompanionTheory.MirPair.coef T B v v'
        ((((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) := by
    intro x
    have h := hlevi (GlobalTheory.CompanionTheory.MirPair.shearGL n b) x v v'
    rw [hfix] at h
    rw [h, GlobalTheory.SmGL.detChar_apply, GlobalTheory.SmGL.val_absPow, hdet]
    simp
  have hgg : ∀ x : Fin (n + 1) → k,
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
        ((((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hset : {y : Fin (n + 1) → k | ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y ∈ M} = M := Set.ext fun y => hM y
  have key := GlobalTheory.CompanionTheory.MirPair.setIntegral_inv_mulVec ν (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b) M
    (fun y => GlobalTheory.CompanionTheory.MirPair.wt ψ n
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) *
      GlobalTheory.CompanionTheory.MirPair.coef T B v v' y)
  rw [hdet, hset] at key
  simp only [hgg, Complex.ofReal_one, NNReal.coe_one, one_mul] at key
  rw [GlobalTheory.CompanionTheory.MirPair.JJ]
  simp_rw [hcoef]
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hlast : (x + (b ⬝ᵥ x) • GlobalTheory.BZMir.eLast k n) (Fin.last n) = x (Fin.last n) + b ⬝ᵥ x := by
    simp [GlobalTheory.BZMir.eLast]
  simp only [GlobalTheory.CompanionTheory.MirPair.wt]
  rw [hg x, hlast, show -(x (Fin.last n) + b ⬝ᵥ x) = -(b ⬝ᵥ x) + -x (Fin.last n) by ring,
    AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

end GlobalTheory.CompanionTheory.MirPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthVanishingStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_depth_vanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (b : Fin (n + 1) → k) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V'), valuation k (b (Fin.last n)) < 1 → T (levi k (n + 1) (shearGL n b)) v = v → (∀ x, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M) → ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = JJ ν ψ T B M v (T' (levi k (n + 1) (shearGL n b)) v') := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear | exact GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear | (intros; apply GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantLeviElement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantLeviElement
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaInvLevi

theorem theta_levi_invariant : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
    PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
    ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) →
    ∀ Φ : schwartzA θ V.rank n,
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g a hg Φ
  obtain ⟨-, -, -, hχ, -, -, -, hW⟩ := hS
  obtain ⟨-, hχ⟩ := hχ
  let a' : GL (Fin n) (Formalism.L2.Theta.AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hg' : GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 (a' : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)) 0 0
      (GlobalTheory.MixModel.adj ((a'⁻¹ : GL (Fin n) (Formalism.L2.Theta.AE D)) : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))) :=
    hg
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D : D.host.E →* Formalism.L2.Theta.AE D) (Matrix.GeneralLinearGroup.det a) :=
    Units.ext (by exact (RingHom.map_det (incA D) a.1).symm)
  have hχ1 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact hχ _
  have habs : GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact GlobalTheory.Doubling.absE_inclR _
  have hc : ∀ x, ((ω g Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n) : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) x =
      (Φ : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) (x * (a' : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))) := by
    intro x
    rw [hW.levi g a' hg' Φ x, hχ1, habs]
    simp [GlobalTheory.Doubling.npow]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * (a : Matrix (Fin n) (Fin n) D.host.E)).map (incA D)) := by
    intro ξ
    rw [hc, Matrix.map_mul]
    rfl
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * (a : Matrix (Fin n) (Fin n) D.host.E)
      invFun := fun ξ => ξ * ((a⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      left_inv := fun ξ => by simp [Matrix.mul_assoc]
      right_inv := fun ξ => by simp [Matrix.mul_assoc] }
  rw [tsum_congr hterm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))

end GlobalTheory.CompanionTheory.ThetaInvLevi
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantLeviElementStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_invariant_levi_element : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
  PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
  ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g a hg Φ
  obtain ⟨-, -, -, ⟨-, hχ⟩, -, -, -, hW⟩ := hS
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hg' : mat g = blk4 (a' : Matrix (Fin n) (Fin n) (AE D)) 0 0
      (adj ((a'⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D))) := hg
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D : D.host.E →* AE D) (Matrix.GeneralLinearGroup.det a) :=
    Units.ext (by exact (RingHom.map_det (incA D) a.1).symm)
  have hχ1 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact hχ _
  have habs : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact absE_inclR _
  have hc : ∀ x, (ω g Φ).1 x = Φ.1 (x * (a' : Matrix (Fin n) (Fin n) (AE D))) := by
    intro x
    rw [hW.levi g a' hg' Φ x, hχ1, habs]
    simp [npow]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * (a : Matrix (Fin n) (Fin n) D.host.E)).map (incA D)) := by
    intro ξ
    rw [hc, Matrix.map_mul]
    rfl
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * (a : Matrix (Fin n) (Fin n) D.host.E)
      invFun := fun ξ => ξ * ((a⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      left_inv := fun ξ => by simp [Matrix.mul_assoc]
      right_inv := fun ξ => by simp [Matrix.mul_assoc] }
  rw [tsum_congr hterm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateRationalEntriesBounded
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateRationalEntriesBounded
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthEntries

open GlobalTheory.CompanionTheory.BoxBound

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_entry_le_toL (A : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) (w : InfinitePlace E) :
    ‖A i j w‖ ≤ ‖toL A‖ :=
  (norm_le_pi_norm (A i j) w).trans
    ((norm_le_pi_norm (toL A i) j).trans (norm_le_pi_norm (toL A) i))

theorem norm_toL_le_height (y : GL (Fin a) (Cinf E)) : ‖toL y.val‖ ≤ height y := by
  have := norm_nonneg (toL (y⁻¹).val)
  unfold height
  linarith

theorem norm_toL_inv_le_height (y : GL (Fin a) (Cinf E)) : ‖toL (y⁻¹).val‖ ≤ height y := by
  have := norm_nonneg (toL y.val)
  unfold height
  linarith

theorem norm_toL_mul_le_of_le {u v : GL (Fin a) (Cinf E)} {p r : ℝ} (hu : ‖toL u.val‖ ≤ p)
    (hv : ‖toL v.val‖ ≤ r) : ‖toL (u * v).val‖ ≤ a * (p * r) :=
  (norm_toL_mul_le u.val v.val).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hu hv (norm_nonneg _) ((norm_nonneg _).trans hu)) (Nat.cast_nonneg a))

theorem gFin_mul (g h : GA E a) : gFin (g * h) = gFin g * gFin h := map_mul _ g h

theorem gFin_inv (g : GA E a) : gFin g⁻¹ = (gFin g)⁻¹ := map_inv _ g

theorem gFin_zpow (g : GA E a) (n : ℤ) : gFin (g ^ n) = gFin g ^ n := map_zpow _ g n

theorem gInf_mul (g h : GA E a) : gInf (g * h) = gInf g * gInf h := map_mul _ g h

theorem gInf_inv (g : GA E a) : gInf g⁻¹ = (gInf g)⁻¹ := map_inv _ g

theorem gFin_splitCentre (t : ℝ) : gFin (splitCentre E a t) = 1 := pFin_infGL _

theorem exists_bound_splitCentre (n₀ : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℤ, |m| ≤ n₀ →
    ‖toL (gInf (splitCentre E a 1 ^ m)).val‖ ≤ B := by
  refine ⟨∑ m ∈ Finset.Icc (-(n₀ : ℤ)) n₀, ‖toL (gInf (splitCentre E a 1 ^ m)).val‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun m hm => ?_⟩
  exact Finset.single_le_sum (f := fun m : ℤ => ‖toL (gInf (splitCentre E a 1 ^ m)).val‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_Icc.2 (abs_le.1 hm))

theorem place_eq_norm_pInf (x : E) (w : InfinitePlace E) :
    w x = ‖pInf E (algebraMap E (Ad E) x) w‖ := by
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq]

theorem entries_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g₀ : GA E a)
    (Q : Set (GA E a)), IsCompact Q → ∀ n₀ : ℕ, ∃ (Qf : Set (Af E)) (C : ℝ), IsCompact Qf ∧ 0 ≤ C ∧
      ∀ (y : GL (Fin a) (Cinf E)) (γ : GL (Fin a) E) (n : ℤ), |n| ≤ n₀ →
        (g₀ * infGL E a y)⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * (g₀ * infGL E a y) ∈ Q →
        ∀ i j, algebraMap E (Af E) (γ.val i j) ∈ Qf ∧ ∀ w : InfinitePlace E, w (γ.val i j) ≤ C * height y ^ 2 := by
  intro E _ _ _ a g₀ Q hQ n₀
  have hK : IsCompact ((fun q : GA E a => gFin g₀ * gFin q * (gFin g₀)⁻¹) '' Q) :=
    hQ.image ((continuous_const.mul continuous_gFin).mul continuous_const)
  have hent : ∀ i j : Fin a, Continuous fun g : GL (Fin a) (Af E) => g.val i j := fun i j =>
    (Units.continuous_val : Continuous fun g : GL (Fin a) (Af E) => (g.val : Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨B, hB0, hB⟩ := exists_height_bound (E := E) (a := a) hQ
  obtain ⟨Z, hZ0, hZ⟩ := exists_bound_splitCentre (E := E) (a := a) n₀
  set g1 : ℝ := ‖toL (gInf g₀).val‖ with hg1
  set g2 : ℝ := ‖toL ((gInf g₀)⁻¹).val‖ with hg2
  have hg10 : 0 ≤ g1 := norm_nonneg _
  have hg20 : 0 ≤ g2 := norm_nonneg _
  refine ⟨⋃ i, ⋃ j, (fun g : GL (Fin a) (Af E) => g.val i j) '' ((fun q : GA E a => gFin g₀ * gFin q * (gFin g₀)⁻¹) '' Q),
    (a : ℝ) ^ 5 * (g1 * g2 * B * Z),
    isCompact_iUnion fun i => isCompact_iUnion fun j => hK.image (hent i j),
    mul_nonneg (pow_nonneg (Nat.cast_nonneg a) 5) (mul_nonneg (mul_nonneg (mul_nonneg hg10 hg20) hB0) hZ0), ?_⟩
  intro y γ n hn hq i j
  set X : GA E a := g₀ * infGL E a y with hX
  set q : GA E a := X⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * X with hqdef
  have h1 : ratGL E a γ * splitCentre E a 1 ^ n = X * q * X⁻¹ := by
    rw [hqdef]; group
  have hfin : gFin (ratGL E a γ) = gFin g₀ * gFin q * (gFin g₀)⁻¹ := by
    have e1 : gFin X = gFin g₀ := by
      rw [hX, gFin_mul, show gFin (infGL E a y) = 1 from pFin_infGL y, mul_one]
    have e2 : gFin (splitCentre E a 1 ^ n) = 1 := by
      rw [gFin_zpow, gFin_splitCentre, _root_.one_zpow]
    have h := congrArg gFin h1
    rw [gFin_mul, e2, mul_one, gFin_mul, gFin_mul, gFin_inv, e1] at h
    exact h
  have hinf : gInf (ratGL E a γ) =
      gInf g₀ * y * gInf q * y⁻¹ * (gInf g₀)⁻¹ * gInf (splitCentre E a 1 ^ (-n)) := by
    have h2 : ratGL E a γ = X * q * X⁻¹ * splitCentre E a 1 ^ (-n) := by
      rw [← h1, _root_.zpow_neg, mul_inv_cancel_right]
    have e1 : gInf X = gInf g₀ * y := by
      rw [hX, gInf_mul, show gInf (infGL E a y) = y from pInf_infGL y]
    have h := congrArg gInf h2
    rw [gInf_mul, gInf_mul, gInf_mul, gInf_inv, e1] at h
    rw [h]
    group
  refine ⟨?_, fun w => ?_⟩
  · refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    exact ⟨gFin (ratGL E a γ), ⟨q, hq, hfin.symm⟩, rfl⟩
  · have hy := norm_toL_le_height y
    have hy' := norm_toL_inv_le_height y
    have hR : ‖toL (gInf q).val‖ ≤ B := (norm_toL_le_height _).trans (hB q hq)
    have hZn : ‖toL (gInf (splitCentre E a 1 ^ (-n))).val‖ ≤ Z := hZ (-n) (by rwa [abs_neg])
    have hM := norm_toL_mul_le_of_le (norm_toL_mul_le_of_le (norm_toL_mul_le_of_le
      (norm_toL_mul_le_of_le (norm_toL_mul_le_of_le (le_refl g1) hy) hR) hy') (le_refl g2)) hZn
    rw [← hinf] at hM
    rw [place_eq_norm_pInf]
    have he : ‖pInf E (algebraMap E (Ad E) (γ.val i j)) w‖ ≤ ‖toL (gInf (ratGL E a γ)).val‖ :=
      norm_entry_le_toL (gInf (ratGL E a γ)).val i j w
    refine he.trans (hM.trans_eq ?_)
    ring

end GlobalTheory.CompanionTheory.GrowthEntries

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateRationalEntriesBoundedStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_conjugate_rational_entries_bounded : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g₀ : GA E a)
    (Q : Set (GA E a)), IsCompact Q → ∀ n₀ : ℕ, ∃ (Qf : Set (Af E)) (C : ℝ), IsCompact Qf ∧ 0 ≤ C ∧
      ∀ (y : GL (Fin a) (Cinf E)) (γ : GL (Fin a) E) (n : ℤ), |n| ≤ n₀ →
        (g₀ * infGL E a y)⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * (g₀ * infGL E a y) ∈ Q →
        ∀ i j, algebraMap E (Af E) (γ.val i j) ∈ Qf ∧ ∀ w : InfinitePlace E, w (γ.val i j) ≤ C * height y ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GrowthEntries.entries_bound | exact GlobalTheory.CompanionTheory.GrowthEntries.entries_bound | (intros; apply GlobalTheory.CompanionTheory.GrowthEntries.entries_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValuePermInvariantStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValuePermInvariant
theorem GlobalTheory.CompanionTheory.ModelS.gelfVal_perm :
    ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ),
      GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k :=
  fun _ χ σ k => GlobalTheory.CompanionTheory.WaveMult.gelfVal_comp_perm χ σ k
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_value_perm_invariant : ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ), GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.gelfVal_perm | exact GlobalTheory.CompanionTheory.ModelS.gelfVal_perm | (intros; apply GlobalTheory.CompanionTheory.ModelS.gelfVal_perm <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnitaryGroupStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnitaryGroup
open MeasureTheory

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_rightInvariant_measure_unitaryGroup
    (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] :
    ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ),
      IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
    GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  let μ : Measure (Matrix.unitaryGroup (Fin n) ℂ) := Measure.haarMeasure ⊤
  refine ⟨μ.inv, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.ModelS
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_unitary_group : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)], ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ), IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup | exact GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup | (intros; apply GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteGeneratorStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteGenerator
open Matrix Finset
open PositivityTheory.RgBcC.RealD (epow gelA)

namespace GlobalTheory.CompanionTheory.ModelS

theorem epow_eq_pow_of {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero =>
      change (if a = b then 1 else 0) = _
      simp only [pow_zero, Matrix.one_apply]
  | succ m ih =>
      change (∑ c, E a c * epow E m c b) = _
      simp only [pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem gelA_central : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E →
    ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  intro n V _ _ E hE m a b
  rw [eq_comm, ← sub_eq_zero]
  delta gelA
  simp only [epow_eq_pow_of]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [GlobalTheory.SmoothForms.comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]

end GlobalTheory.CompanionTheory.ModelS
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_invariant_commute_generator : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.gelA_central | exact GlobalTheory.CompanionTheory.ModelS.gelA_central | (intros; apply GlobalTheory.CompanionTheory.ModelS.gelA_central <;> assumption)
end
