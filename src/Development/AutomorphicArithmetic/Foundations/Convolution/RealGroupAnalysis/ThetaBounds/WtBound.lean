module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_mono' {F : Type} [Field F] [NumberField F]
    {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : K ⊆ K') (N : ℕ) (v : V4 F) :
    wt K N v ≤ wt K' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private theorem majorant {F : Type} [Field F] [NumberField F] {G : V4 F → ℂ}
    (hG : G ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    ∃ K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ N, ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ‖G v‖ ≤ B * wt K N v := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have hgc : Continuous g := ((mem_finiteSchwartzBruhatPi F).mp hg).1.continuous
    have hgs : HasCompactSupport g := ((mem_finiteSchwartzBruhatPi F).mp hg).2
    obtain ⟨C₂, h₂⟩ := hgc.bounded_above_of_compact_support hgs
    refine ⟨tsupport g, hgs.isCompact, fun N => ?_⟩
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_le_inv_one_add_pow φ N
    refine ⟨C₁ * max C₂ 0, mul_nonneg hC₁ (le_max_right _ _), fun v => ?_⟩
    simp only [schwartzBruhatTensorPi, norm_mul]
    by_cases hx : finPartPi v ∈ tsupport g
    · rw [wt, if_pos hx]
      calc ‖φ (infPartPi v)‖ * ‖g (finPartPi v)‖
          ≤ (C₁ * ((1 + ‖infPartPi v‖) ^ N)⁻¹) * max C₂ 0 :=
            mul_le_mul (h₁ _) ((h₂ _).trans (le_max_left _ _)) (norm_nonneg _)
              (mul_nonneg hC₁ (inv_nonneg.2 (by positivity)))
        _ = C₁ * max C₂ 0 * ((1 + ‖infPartPi v‖) ^ N)⁻¹ := by ring
    · rw [wt, if_neg hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  | zero =>
    exact ⟨∅, isCompact_empty, fun N => ⟨0, le_rfl, fun v => by simp⟩⟩
  | add G H _ _ hG hH =>
    obtain ⟨K₁, hK₁, h₁⟩ := hG
    obtain ⟨K₂, hK₂, h₂⟩ := hH
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun N => ?_⟩
    obtain ⟨B₁, hB₁, b₁⟩ := h₁ N
    obtain ⟨B₂, hB₂, b₂⟩ := h₂ N
    refine ⟨B₁ + B₂, add_nonneg hB₁ hB₂, fun v => ?_⟩
    calc ‖(G + H) v‖ ≤ ‖G v‖ + ‖H v‖ := norm_add_le _ _
      _ ≤ B₁ * wt K₁ N v + B₂ * wt K₂ N v := add_le_add (b₁ v) (b₂ v)
      _ ≤ B₁ * wt (K₁ ∪ K₂) N v + B₂ * wt (K₁ ∪ K₂) N v :=
          add_le_add (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_left N v) hB₁)
            (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_right N v) hB₂)
      _ = (B₁ + B₂) * wt (K₁ ∪ K₂) N v := by ring
  | smul c G _ hG =>
    obtain ⟨K, hK, h⟩ := hG
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB, b⟩ := h N
    refine ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b v) (norm_nonneg c)

theorem UpperTheory.ConvolutionTheory.R2.Ff.wtBound :
    ∀ (F : Type) [Field F] [NumberField F], WtBound F := by
  intro F _ _ φ
  refine ⟨continuous_of_mem_schwartzBruhatPi φ.2, ?_⟩
  obtain ⟨K, hK, h⟩ := majorant φ.2
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨B, _, b⟩ := h N
  exact ⟨B, fun _ _ v => b v⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem cont_inf (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem cont_fin (E : Type) [Field E] [NumberField E] (a : ℕ) :
    Continuous (finGL E a) := by
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem cont_unherm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) : Continuous D.unherm := by
  have hco : ∀ i, Continuous fun z => D.co z i := fun i => (continuous_apply i).comp D.continuous_co
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (hco 0).comp (continuous_id.matrix_elem 1 1)
  · exact (hco 0).comp (continuous_id.matrix_elem 0 0)
  · exact (hco 0).comp (continuous_id.matrix_elem 0 1)
  · exact (hco 1).comp (continuous_id.matrix_elem 0 1)

private theorem cont_act {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (v : V4 F) : Continuous fun h : GL (Fin 2) (A E) => D.act h v := by
  have hv : Continuous fun h : GL (Fin 2) (A E) => h.val := Units.continuous_val
  exact (cont_unherm D).comp ((hv.matrix_mul continuous_const).matrix_mul
    (hv.matrix_map D.continuous_bar).matrix_transpose)

theorem UpperTheory.ConvolutionTheory.R2.Ff.actCont :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), ActCont D := by
  intro F E _ _ _ _ _ _ _ D
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hval : Continuous fun h => (ρ h).val := continuous_matrix fun i j => by
    have e : ∀ h, (ρ h).val i j = D.act h (Pi.single j 1) i := fun h => by rw [hρ]; simp
    simp only [e]
    exact (continuous_apply i).comp (cont_act D _)
  refine ⟨ρ, Units.continuous_iff.2 ⟨hval, ?_⟩, hρ, continuous_nu, cont_inf E 2, cont_fin E 2⟩
  have e : (fun h => (((ρ h)⁻¹ : GL (Fin 4) (A F)) : Matrix (Fin 4) (Fin 4) (A F))) = fun h => (ρ h⁻¹).val := by
    funext h; rw [map_inv]
  exact e ▸ hval.comp continuous_inv
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

open scoped nonZeroDivisors
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private noncomputable def lw (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (ξ : Fin 4 → F) : ℝ :=
  if ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F) then ((1 + ‖embPi F ξ‖) ^ N)⁻¹ else 0

private theorem lw_nonneg (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (ξ : Fin 4 → F) : 0 ≤ lw J N ξ := by
  unfold lw
  split_ifs
  · positivity
  · exact le_rfl

private theorem wt_nonneg (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem summable_lat (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {N : ℕ}
    (hN : Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) < N) :
    Summable fun z : idealLatticePi (K := F) (fun _ : Fin 4 => J) =>
      ((1 + ‖(z : Fin 4 → mixedEmbedding.mixedSpace F)‖) ^ N)⁻¹ := by
  have hrank : Module.finrank ℤ (idealLatticePi (K := F) (fun _ : Fin 4 => J)) < N := by
    rw [ZLattice.rank ℝ (idealLatticePi (K := F) (fun _ : Fin 4 => J))]; exact hN
  have hs := ZLattice.summable_norm_pow_inv (idealLatticePi (K := F) (fun _ : Fin 4 => J)) N hrank
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(Set.finite_singleton (0 : idealLatticePi (K := F) (fun _ : Fin 4 => J))).compl_mem_cofinite] with z hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz' : ‖z‖ = ‖(z : Fin 4 → mixedEmbedding.mixedSpace F)‖ := rfl
  rw [Real.norm_of_nonneg (inv_nonneg.2 (by positivity)), inv_pow, ← hz']
  gcongr
  linarith

private theorem mem_lat (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (ξ : Fin 4 → F)
    (h : ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)) :
    embPi F ξ ∈ idealLatticePi (K := F) (fun _ : Fin 4 => J) := by
  rw [mem_idealLatticePi]
  intro i
  exact (mixedEmbedding.mem_idealLattice F J).2 ⟨_, h i, rfl⟩

private theorem embPi_injective : Function.Injective (embPi F : (Fin 4 → F) → _) := fun _ _ h =>
  funext fun i => (mixedEmbedding F).injective (congrFun h i)

private theorem summable_lw (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {N : ℕ}
    (hN : Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) < N) : Summable (lw J N) := by
  have hsT : Summable fun ξ : {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} =>
      ((1 + ‖embPi F (ξ : Fin 4 → F)‖) ^ N)⁻¹ := by
    have hinj : Function.Injective fun ξ : {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} =>
        (⟨embPi F ξ.1, mem_lat J ξ.1 ξ.2⟩ : idealLatticePi (K := F) (fun _ : Fin 4 => J)) := fun x y h =>
      Subtype.ext (embPi_injective (congrArg Subtype.val h))
    have h := (summable_lat J hN).comp_injective hinj
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply]
  have heq : lw (F := F) J N = Set.indicator {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)}
      (fun ξ => ((1 + ‖embPi F ξ‖) ^ N)⁻¹) := by
    funext ξ
    unfold lw
    by_cases h : ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)
    · rw [if_pos h, Set.indicator_of_mem (show ξ ∈ {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show ξ ∉ {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} from h)]
  rw [heq, ← summable_subtype_iff_indicator]
  exact hsT

private theorem mixed_le {S : Set (IdeleGroup F)} (hS : IsCompact S) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (s : ℝ) (hs : 0 < s), 1 ≤ s → ∀ u ∈ S, ∀ η : F,
      ‖mixedEmbedding F η‖ ≤ B * ‖homeomorphMixedSpace F
        ((((posIdele s hs * u : IdeleGroup F) : A F) * rt η).1)‖ := by
  have hc : Continuous fun u : IdeleGroup F => ∑ w : InfinitePlace F, ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖ :=
    continuous_finsetSum _ fun w _ => continuous_norm.comp
      ((continuous_apply w).comp (continuous_fst.comp Units.continuous_coe_inv))
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  set b := max M 1
  have hb1 : 1 ≤ b := le_max_right _ _
  set n : ℝ := (Fintype.card (InfinitePlace F) : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨n * b + 1, by nlinarith, fun s hs hs1 u hu η => ?_⟩
  set y := (((posIdele s hs * u : IdeleGroup F) : A F) * rt η).1
  have hub : ∀ w, ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖ ≤ b := fun w => by
    refine le_trans ?_ ((le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM u hu).trans (le_max_left _ _)))
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have hw : ∀ w, ‖(rt η : A F).1 w‖ ≤ b * ‖homeomorphMixedSpace F y‖ := fun w => by
    have e1 : y w = ((posIdele s hs : IdeleGroup F) : A F).1 w * (((u : IdeleGroup F) : A F) * rt η).1 w := by
      simp only [y, Units.val_mul, mul_assoc]
      rfl
    have e2 : (rt η : A F).1 w = (((u⁻¹ : IdeleGroup F) : A F)).1 w * (((u : IdeleGroup F) : A F) * rt η).1 w := by
      have : (rt η : A F) = ((u⁻¹ : IdeleGroup F) : A F) * (((u : IdeleGroup F) : A F) * rt η) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      exact congrArg (fun z : A F => z.1 w) this
    have e3 : ‖(((u : IdeleGroup F) : A F) * rt η).1 w‖ ≤ ‖y w‖ := by
      rw [e1, norm_mul, norm_posIdele_infinite]
      nlinarith [norm_nonneg ((((u : IdeleGroup F) : A F) * rt η).1 w)]
    rw [e2, norm_mul]
    exact mul_le_mul (hub w) (e3.trans (GJGlobal.norm_apply_le_norm_homeomorphMixedSpace y w)) (norm_nonneg _)
      (by linarith)
  have h1 : ‖mixedEmbedding F η‖ ≤ ∑ w : InfinitePlace F, ‖(rt η : A F).1 w‖ := by
    have := GJGlobal.norm_homeomorphMixedSpace_le_sum (algebraMap F (InfiniteAdeleRing F) η)
    rw [homeomorphMixedSpace_algebraMap] at this
    exact this
  have h2 : ∑ w : InfinitePlace F, ‖(rt η : A F).1 w‖ ≤ n * (b * ‖homeomorphMixedSpace F y‖) := by
    refine (Finset.sum_le_sum fun w _ => hw w).trans_eq ?_
    simp [n, Finset.card_univ]
  nlinarith [norm_nonneg (homeomorphMixedSpace F y)]

private theorem fin_mem {K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K)
    {S : Set (IdeleGroup F)} (hS : IsCompact S) :
    ∃ J : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∀ (s : ℝ) (hs : 0 < s), ∀ u ∈ S, ∀ η : Fin 4 → F,
      finPartPi (sc (posIdele s hs * u) η) ∈ K → ∀ i, η i ∈ (J : FractionalIdeal (𝓞 F)⁰ F) := by
  set Kf : Set (FiniteAdeleRing (𝓞 F) F) := ⋃ i : Fin 4, (fun k : Fin 4 → FiniteAdeleRing (𝓞 F) F => k i) '' K
  have hKf : IsCompact Kf := isCompact_iUnion fun i => hK.image (continuous_apply i)
  set Q : Set (FiniteAdeleRing (𝓞 F) F) :=
    (fun p : IdeleGroup F × FiniteAdeleRing (𝓞 F) F => (((p.1⁻¹ : IdeleGroup F) : A F)).2 * p.2) '' (S ×ˢ Kf)
  have hi : Continuous fun u : IdeleGroup F => (((u⁻¹ : IdeleGroup F) : A F)).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hQ : IsCompact Q := (hS.prod hKf).image ((hi.comp continuous_fst).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hQ
  set dK := algebraMap (𝓞 F) F d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)), fun s hs u hu η hη i => ?_⟩
  have hp : (((posIdele s hs : IdeleGroup F) : A F)).2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact posIdele_finite s hs v
  have hmem : algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i) ∈ Q := by
    refine ⟨(u, finPartPi (sc (posIdele s hs * u) η) i),
      ⟨hu, Set.mem_iUnion.2 ⟨i, _, hη, rfl⟩⟩, ?_⟩
    have e1 : finPartPi (sc (posIdele s hs * u) η) i =
        (((u : IdeleGroup F) : A F)).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i) := by
      change ((((posIdele s hs * u : IdeleGroup F) : A F)) * rt (η i)).2 = _
      rw [Units.val_mul, mul_assoc]
      change (((posIdele s hs : IdeleGroup F) : A F)).2 * _ = _
      rw [hp, one_mul]
      rfl
    have e2 : (((u⁻¹ : IdeleGroup F) : A F)).2 * (((u : IdeleGroup F) : A F)).2 = 1 :=
      congrArg Prod.snd (Units.inv_mul u)
    change (((u⁻¹ : IdeleGroup F) : A F)).2 * finPartPi (sc (posIdele s hs * u) η) i = _
    rw [e1, ← mul_assoc, e2, one_mul]
  have h1 := hd _ hmem
  rw [← map_mul] at h1
  have h2 : dK * η i ∈ ((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
  rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

private theorem wt_le {K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} {J : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
    {B : ℝ} (hB : 1 ≤ B) {a : (A F)ˣ}
    (hfin : ∀ η : Fin 4 → F, finPartPi (sc a η) ∈ K → ∀ i, η i ∈ (J : FractionalIdeal (𝓞 F)⁰ F))
    (hinf : ∀ η : F, ‖mixedEmbedding F η‖ ≤ B * ‖homeomorphMixedSpace F (((a : A F) * rt η).1)‖)
    (N : ℕ) (η : Fin 4 → F) : wt K N (sc a η) ≤ B ^ N * lw J N η := by
  have hB0 : 0 < B := one_pos.trans_le hB
  by_cases h : finPartPi (sc a η) ∈ K
  · unfold wt lw
    rw [if_pos h, if_pos (hfin η h)]
    have h1 : ‖embPi F η‖ ≤ B * ‖infPartPi (sc a η)‖ :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (hinf (η i)).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm (infPartPi (sc a η)) i) hB0.le)
    have h2 : 1 + ‖embPi F η‖ ≤ B * (1 + ‖infPartPi (sc a η)‖) := by linarith
    calc ((1 + ‖infPartPi (sc a η)‖) ^ N)⁻¹ = B ^ N * ((B * (1 + ‖infPartPi (sc a η)‖)) ^ N)⁻¹ := by
          rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ B ^ N * ((1 + ‖embPi F η‖) ^ N)⁻¹ := by gcongr
  · unfold wt
    rw [if_neg h]
    exact mul_nonneg (by positivity) (lw_nonneg _ _ _)

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ConvolutionTheory.R2.Ff.wtSum :
    ∀ (F : Type) [Field F] [NumberField F], WtSum F := by
  intro F _ _
  refine ⟨Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1, fun K hK c hc => ?_⟩
  set N := Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1 with hNdef
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) hc c
  obtain ⟨J, hJ⟩ := fin_mem hK hS
  obtain ⟨B, hB1, hB⟩ := mixed_le hS
  have hsum : Summable (lw J N) := summable_lw J (Nat.lt_succ_self _)
  have hB0 : 0 ≤ B ^ N := pow_nonneg (zero_le_one.trans hB1) _
  refine ⟨B ^ N * ∑' ξ, lw J N ξ, fun a ha => ?_⟩
  set d := Module.finrank ℚ F
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  set s := (ab a / c) ^ (d : ℝ)⁻¹
  have hs1 : 1 ≤ s := Real.one_le_rpow hx (by positivity)
  have hs0 : 0 < s := one_pos.trans_le hs1
  have hsd : s ^ d = ab a / c := Real.rpow_inv_natCast_pow (zero_le_one.trans hx) hd
  set p : IdeleGroup F := posIdele s hs0 with hp
  have hm : (IdeleGroup.ideleModule F (p⁻¹ * a) : ℝ) = c := by
    have h1 : (IdeleGroup.ideleModule F (p⁻¹ * a) : ℝ) =
        ((IdeleGroup.ideleModule F p : ℝ))⁻¹ * (IdeleGroup.ideleModule F a : ℝ) := by
      simp [map_mul, map_inv]
    have h2 : (0 : ℝ) < ab a := hc.trans_le ha
    rw [h1, hp, ideleModule_posIdele, hsd]
    change (ab a / c)⁻¹ * ab a = c
    field_simp
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set u := IdeleGroup.diagonal F t * (p⁻¹ * a) with hu
  have hau : IdeleGroup.diagonal F t * a = p * u := by
    rw [hu, mul_left_comm, mul_inv_cancel_left]
  let e : (Fin 4 → F) ≃ (Fin 4 → F) := Equiv.piCongrRight fun _ => Units.mulLeft t
  have hsc : ∀ ξ, sc a (e ξ) = sc (p * u) ξ := fun ξ => by
    funext i
    have h1 : ((IdeleGroup.diagonal F t : IdeleGroup F) : A F) = rt (t : F) := IdeleGroup.coe_diagonal _ _
    have h2 : ((p * u : IdeleGroup F) : A F) = (a : A F) * rt (t : F) := by
      rw [← hau, Units.val_mul, h1, mul_comm]
    change (a : A F) * rt ((t : F) * ξ i) = ((p * u : IdeleGroup F) : A F) * rt (ξ i)
    rw [h2, show rt ((t : F) * ξ i) = rt (t : F) * rt (ξ i) from map_mul _ _ _, mul_assoc]
  have hle : ∀ ξ, wt K N (sc a (e ξ)) ≤ B ^ N * lw J N ξ := fun ξ => by
    rw [hsc]
    exact wt_le hB1 (hJ s hs0 u ht) (hB s hs0 hs1 u ht) N ξ
  have hs' : Summable fun ξ => wt K N (sc a (e ξ)) :=
    Summable.of_nonneg_of_le (fun _ => wt_nonneg _ _ _) hle (hsum.mul_left _)
  refine ⟨e.summable_iff.1 hs', ?_⟩
  rw [← e.tsum_eq, ← tsum_mul_left]
  exact hs'.tsum_le_tsum hle (hsum.mul_left _)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

open scoped Matrix.Norms.Operator

private theorem ex_val (X : Lie E 2) (t : ℝ) : (ex X t).val = NormedSpace.exp (t • Matrix.of X) := rfl

private theorem ex_add (X : Lie E 2) (s t : ℝ) : ex X (s + t) = ex X s * ex X t := by
  refine Units.ext ?_
  rw [Units.val_mul, ex_val, ex_val, ex_val, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl (Matrix.of X)).smul_left s).smul_right t)

private theorem ex_zero (X : Lie E 2) : ex X 0 = 1 := by
  refine Units.ext ?_
  rw [ex_val, zero_smul, NormedSpace.exp_zero]
  rfl

private theorem ex_inv (X : Lie E 2) (t : ℝ) : (ex X t)⁻¹ = ex X (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← ex_add, add_neg_cancel, ex_zero])

private theorem ex_val_cont (X : Lie E 2) : Continuous fun t : ℝ => (ex X t).val :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) t).continuousAt

private theorem ex_cont (X : Lie E 2) : Continuous (ex X) := by
  refine Units.continuous_iff.2 ⟨ex_val_cont X, ?_⟩
  simp only [ex_inv]
  exact (ex_val_cont X).comp continuous_neg

private theorem ex_der (X : Lie E 2) : HasDerivAt (fun t => toL (ex X t).val) X 0 := by
  let L : Matrix (Fin 2) (Fin 2) (Cinf E) →L[ℝ] Lie E 2 :=
    { toLinearMap := (Matrix.ofLinearEquiv ℝ).symm.toLinearMap, cont := continuous_id }
  have h : HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • Matrix.of X)))
      (L (NormedSpace.exp ((0 : ℝ) • Matrix.of X) * Matrix.of X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) (0 : ℝ))
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

private theorem ex_ent (X : Lie E 2) (i j : Fin 2) :
    HasDerivAt (fun t => (ex X t).val i j) (X i j) 0 :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 (ex_der X) i) j

private theorem ex_det_der (X : Lie E 2) :
    HasDerivAt (fun t => (ex X t).val.det) ((Matrix.of X).trace) 0 := by
  have h := ((ex_ent X 0 0).mul (ex_ent X 1 1)).sub ((ex_ent X 0 1).mul (ex_ent X 1 0))
  have e0 : (ex X 0).val = 1 := by rw [ex_zero]; rfl
  simp only [e0, Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
    Matrix.one_apply_ne, mul_one, one_mul, zero_mul, mul_zero, add_zero, sub_zero] at h
  rw [Matrix.trace_fin_two]
  simp only [Matrix.det_fin_two]
  exact h

private theorem ex_det (X : Lie E 2) (hX : (Matrix.of X).trace = 0) (t : ℝ) : (ex X t).val.det = 1 := by
  have hm : ∀ s t, (ex X (s + t)).val.det = (ex X s).val.det * (ex X t).val.det := fun s t => by
    rw [ex_add, Units.val_mul, Matrix.det_mul]
  have hd : ∀ t, HasDerivAt (fun s => (ex X s).val.det) (0 : Cinf E) t := fun t => by
    have h0 := ex_det_der X
    rw [hX] at h0
    have h1 : HasDerivAt (fun s => (ex X (s - t)).val.det) (0 : Cinf E) t :=
      HasDerivAt.comp_sub_const t t (by simpa using h0)
    have h2 := h1.const_mul (ex X t).val.det
    rw [mul_zero] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show (ex X s).val.det = (ex X t).val.det * (ex X (s - t)).val.det
    rw [← hm, add_sub_cancel]
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have e0 : (ex X 0).val = 1 := by rw [ex_zero]; rfl
  simpa [e0] using hc

private theorem ex_cen (X : Lie E 2) (s : Cinf E) (t : ℝ) : ex (X + zE s) t = ex (zE s) t * ex X t := by
  refine Units.ext ?_
  rw [Units.val_mul, ex_val, ex_val, ex_val]
  have e : Matrix.of (X + zE s) = Matrix.of (zE s) + Matrix.of X := by
    rw [add_comm]; rfl
  have c : Commute (Matrix.of (zE s)) (Matrix.of X) :=
    Matrix.scalar_commute s (fun r => Commute.all _ _) (Matrix.of X)
  rw [e, smul_add]
  exact NormedSpace.exp_add_of_commute ((c.smul_left t).smul_right t)

end

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.exPar :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ExPar E := by
  intro E _ _ _ X
  exact ⟨ex_add X, ex_cont X, ex_der X, ex_det X, fun s t => ex_cen X s t⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Transl
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.transl :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F), Transl W M := by
  intro F E _ _ _ _ _ _ _ D W M f φ h h₀
  have hnu : nu F (h * h₀) = nu F h * nu F h₀ := by
    simp only [nu, map_mul]
  unfold lift
  refine congrArg (fun u : G1 F → ℂ => ∫ g in M.D, u g ∂M.μ) (funext fun g => ?_)
  simp only [hnu, dM_mul, map_mul, Module.End.mul_apply, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieSplit
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieSplit {E : Type} [Field E] [NumberField E] (X : Lie E 2) :
    ∃ (Y : Lie E 2) (s : Cinf E), (Matrix.of Y).trace = 0 ∧ X = Y + zE s ∧ X 0 0 + X 1 1 = s + s := by
  have h : X 0 0 + X 1 1 = (2⁻¹ : ℝ) • (X 0 0 + X 1 1) + (2⁻¹ : ℝ) • (X 0 0 + X 1 1) := by
    rw [← add_smul]; norm_num
  refine ⟨X - zE ((2⁻¹ : ℝ) • (X 0 0 + X 1 1)), _, ?_, (sub_add_cancel _ _).symm, h⟩
  rw [Matrix.trace_fin_two]
  change (X 0 0 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) + (X 1 1 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) = 0
  linear_combination h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ParCont
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem parCont_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Continuous (TR.infGL F 2) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((TR.continuous_infEq F).prodMk continuous_const :
    Continuous fun x : TR.Rinf F => ((TR.infEq F x, 0) : InfiniteAdeleRing F × Af F))))

private theorem parCont_val {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {c : ℝ → GL (Fin 2) (TR.Rinf F)} {Y : TR.Lie F 2} (h : Par c Y) :
    Continuous fun t => (c t).val := by
  have h0 : ContinuousAt (fun t => (c t).val) 0 := h.2.continuousAt
  refine continuous_iff_continuousAt.2 fun t => ?_
  have e : (fun s => (c s).val) = fun s => (c t).val * (c (s - t)).val := by
    funext s
    rw [← Units.val_mul, ← h.1, add_sub_cancel]
  rw [e]
  have hs : ContinuousAt (fun s : ℝ => s - t) t := (continuous_id.sub continuous_const).continuousAt
  have h0' : ContinuousAt (fun t => (c t).val) ((fun s : ℝ => s - t) t) := by
    simpa using h0
  exact continuousAt_const.mul (ContinuousAt.comp (f := fun s : ℝ => s - t) h0' hs)

theorem UpperTheory.ConvolutionTheory.R2.Ff.parCont :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ParCont (F := F) := by
  intro F _ _ _
  refine ⟨parCont_infGL F, fun c Y h => ?_⟩
  have h1 : c 0 = 1 := by
    have := h.1 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← h.1, add_neg_cancel, h1])
  have hv := parCont_val h
  refine ⟨h1, Units.continuous_iff.2 ⟨hv, ?_⟩, ?_, ?_⟩
  · have : (fun t => ((c t)⁻¹ : GL (Fin 2) (TR.Rinf F)).val) = fun t => (c (-t)).val := by
      funext t; rw [hinv]
    change Continuous (fun t => ((c t)⁻¹ : GL (Fin 2) (TR.Rinf F)).val)
    rw [this]
    exact hv.comp continuous_neg
  · intro s t
    change c (-(s + t)) = c (-s) * c (-t)
    rw [neg_add, h.1]
  · have h2 : HasDerivAt (fun t => TR.toL (c t).val) Y (-(0 : ℝ)) := by simpa using h.2
    have := HasDerivAt.scomp (0 : ℝ) h2 (hasDerivAt_neg 0)
    simpa [Function.comp_def] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FstFinGL
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem fst_finGL' {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) k

private theorem det_fst {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    ((Matrix.GeneralLinearGroup.det (finGL E 2 k) : (A E)ˣ) : A E).1 = 1 := by
  have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k)
  rw [fst_finGL'] at h
  exact h.symm.trans (by simp)

private theorem norm_fst {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : (A E)ˣ) (hx : (x : A E).1 = 1) : ((ideleNorm F E x : (A F)ˣ) : A F).1 = 1 := by
  funext v
  rw [ideleNorm_fst, hx]
  exact Finset.prod_eq_one fun w _ => map_one _

private theorem dM_of_fst {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (t : (A F)ˣ) (ht : (t : A F).1 = 1) :
    finGL F 2 (Matrix.GeneralLinearGroup.map (pFin F) (dM t)) = dM t := by
  have h := TR.infGL_mul_finGL (dM t)
  have h1 : Matrix.GeneralLinearGroup.map (TR.pInf F) (dM t) = 1 := by
    have ht' : TR.pInf F (t : A F) = 1 := by
      change (TR.infEq F).symm (t : A F).1 = 1
      rw [ht]; exact map_one _
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht']
  rw [h1, map_one, one_mul] at h
  exact h

theorem UpperTheory.ConvolutionTheory.R2.Ff.finTr :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), FinTr F E := by
  intro F E _ _ _ _ _ _ _ _
  let κ : GL (Fin 2) (Af E) →* GL (Fin 2) (Af F) :=
    { toFun := fun k => Matrix.GeneralLinearGroup.map (pFin F) (dM (nu F (finGL E 2 k)))
      map_one' := by simp [nu]
      map_mul' := fun a b => by simp [nu, dM_mul] }
  refine ⟨κ, ?_, fun k => (dM_of_fst _ (norm_fst _ (det_fst k))).symm⟩
  have hp : Continuous (pFin F) := continuous_snd
  have hm : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (pFin F)) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id hp)
  have hf : Continuous (finGL E 2) := Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))
  exact hm.comp (continuous_dM.comp (continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp hf)))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormMatrixMulLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem ht_le {E : Type} [Field E] [NumberField E] (y : GL (Fin 2) (Cinf E)) :
    ‖toL y.val‖ ≤ GlobalTheory.CuspRep.height y ∧ ‖toL (y⁻¹).val‖ ≤ GlobalTheory.CuspRep.height y := by
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  refine ⟨?_, ?_⟩ <;> first | (unfold GlobalTheory.CuspRep.height; linarith) | fail "height"

private theorem norm_matrix_mul_le_two {E : Type} [Field E] [NumberField E]
    (x x' : Matrix (Fin 2) (Fin 2) (Cinf E)) : ‖toL (x * x')‖ ≤ 2 * ‖toL x‖ * ‖toL x'‖ := by
  have h0 : 0 ≤ 2 * ‖toL x‖ * ‖toL x'‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
    (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  have e1 : ∀ a b, ‖x a b w‖ ≤ ‖toL x‖ := fun a b =>
    (norm_le_pi_norm (x a b) w).trans ((norm_le_pi_norm (toL x a) b).trans (norm_le_pi_norm (toL x) a))
  have e2 : ∀ a b, ‖x' a b w‖ ≤ ‖toL x'‖ := fun a b =>
    (norm_le_pi_norm (x' a b) w).trans ((norm_le_pi_norm (toL x' a) b).trans (norm_le_pi_norm (toL x') a))
  have e : toL (x * x') i j w = x i 0 w * x' 0 j w + x i 1 w * x' 1 j w := by
    show (x * x') i j w = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  have p : ∀ k, ‖x i k w * x' k j w‖ ≤ ‖toL x‖ * ‖toL x'‖ := fun k => by
    rw [norm_mul]
    exact mul_le_mul (e1 _ _) (e2 _ _) (norm_nonneg _) (norm_nonneg _)
  have := norm_add_le (x i 0 w * x' 0 j w) (x i 1 w * x' 1 j w)
  linarith [p 0, p 1]

private theorem cont_toL {E : Type} [Field E] [NumberField E] :
    Continuous fun x : Matrix (Fin 2) (Fin 2) (Cinf E) => toL x :=
  continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j

theorem UpperTheory.ConvolutionTheory.R2.Ff.htLe :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], HtLe E := by
  intro E _ _ _
  refine ⟨?_, fun y => ⟨?_, ?_, fun y' => ?_⟩⟩
  · unfold Ht
    have c1 : Continuous fun y : GL (Fin 2) (Cinf E) => toL y.val := cont_toL.comp Units.continuous_val
    have c2 : Continuous fun y : GL (Fin 2) (Cinf E) => toL (y⁻¹).val :=
      cont_toL.comp (Units.continuous_val.comp continuous_inv)
    exact (continuous_const.add c1.norm).add c2.norm
  · have n1 := norm_nonneg (toL y.val)
    have n2 := norm_nonneg (toL (y⁻¹).val)
    unfold Ht
    linarith
  · have h := ht_le y
    have h1 := GlobalTheory.CuspRep.one_le_height y
    unfold Ht
    linarith [h.1, h.2]
  · have n1 := norm_nonneg (toL y.val)
    have n2 := norm_nonneg (toL (y⁻¹).val)
    have n3 := norm_nonneg (toL y'.val)
    have n4 := norm_nonneg (toL (y'⁻¹).val)
    have m1 := norm_matrix_mul_le_two y.val y'.val
    have m2 := norm_matrix_mul_le_two (y'⁻¹).val (y⁻¹).val
    have e1 : (y * y').val = y.val * y'.val := rfl
    have e2 : ((y * y')⁻¹).val = (y'⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
    unfold Ht
    rw [e1, e2]
    nlinarith [mul_nonneg n1 n3, mul_nonneg n1 n4, mul_nonneg n2 n3, mul_nonneg n2 n4]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LCen
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), LCen W := by
  intro F E _ _ _ _ _ _ _ D W z
  refine ⟨LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_), nu_scalar z⟩
  have hη : W.η.1 (ideleNorm F E z)⁻¹ = 1 := by rw [map_inv, W.η_norm, inv_one]
  have hs : (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ :=
    (map_inv _ _).symm
  have hv : D.act (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ v =
      fun i => (((ideleNorm F E z)⁻¹ : (A F)ˣ) : A F) * v i := by
    rw [hs, D.act_scalar, map_inv]; rfl
  rw [W.L_apply, W.Om_m, nu_scalar, hv, hη, ab_inv, ab_pow]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SumCoordPl
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem fiber_eq (w : InfinitePlace E) :
    (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk τ := by rw [InfinitePlace.mk_embedding, h]
    exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

private theorem emb_ne (w : InfinitePlace E) : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
    (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))

private theorem pl_eq (τ : E →+* ℂ) : Fo.pl F τ = (InfinitePlace.mk τ).comap (algebraMap F E) := by
  rw [InfinitePlace.comap_mk]; rfl

private theorem sum_coord_pl {M : Type*} [AddCommGroup M] [Module ℂ M] (s : Cinf E) (G : InfinitePlace F → M) :
    ∑ τ : E →+* ℂ, coord τ s • G (Fo.pl F τ) = ∑ v, ((trI F s v : ℝ) : ℂ) • G v := by
  have hr : ∀ v, ((trI F s v : ℝ) : ℂ) • G v =
      ∑ w : InfinitePlace E, (if w.comap (algebraMap F E) = v then ((2 * (s w).re : ℝ) : ℂ) • G v else 0) := by
    intro v
    simp only [trI]
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp only [hr]
  rw [Finset.sum_comm, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), fiber_eq, Finset.sum_pair (emb_ne w), pl_eq, pl_eq,
    InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding,
    UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding, ← add_smul, Complex.add_conj]

private theorem theta_ne (D : Dat F E) : D.θ ≠ 0 := by
  rw [← D.b1]; exact D.b.ne_zero 1

private theorem dE_sum (D : Dat F E) (O : Fo.Ops F) (τ : E →+* ℂ) :
    O.dE D τ 0 0 + O.dE D τ 1 1 = -O.h (Fo.pl F τ) := by
  have ht : τ D.θ ≠ 0 := fun h => theta_ne D ((map_eq_zero τ).1 h)
  have h2 : (2 : Module.End ℂ (S4 F)) = 1 + 1 := one_add_one_eq_two.symm
  simp only [Fo.Ops.dE, Fo.Ops.X, Fo.Ops.DX, Fo.Ops.h, Fin.sum_univ_two, Fin.sum_univ_four, h2]
  simp only [Fin.isValue, if_true, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val]
  generalize τ D.θ = t at ht
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  match_scalars <;> field_simp <;> ring

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), DLCen D O := by
  intro F E _ _ _ _ _ _ _ D O
  refine ⟨fun s => ?_, fun Y Y' => ?_, fun c Y => ?_, fun s => ?_⟩
  · have hz : ∀ i j, zE s i j = if i = j then s else 0 := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [zE, GlobalTheory.CuspRep.toL, Matrix.scalar_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.sum_univ_two, hz]
    simp only [Fin.isValue, if_true, one_ne_zero, zero_ne_one, if_false, map_zero, zero_smul, add_zero, zero_add]
    rw [← smul_add, dE_sum, smul_neg]
  · simp only [Fo.Ops.dL, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (Y + Y') i j = Y i j + Y' i j from rfl, map_add (f := _)]
  · simp only [Fo.Ops.dL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (c • Y) i j = c • Y i j from rfl, UpperTheory.V.FieldIso.coord_smul, Complex.real_smul, mul_smul]
  · rw [sum_coord_pl s (fun v => TR.Eop v 0 0 + TR.Eop v 1 1)]
    have hz : zF (trI F s) = ∑ v, trI F s v • (TR.toL (Matrix.single 0 0 (Pi.single v 1)) + TR.toL (Matrix.single 1 1 (Pi.single v 1)) : TR.Lie F 2) := by
      ext i j w
      fin_cases i <;> fin_cases j <;> simp [zF, TR.toL, Matrix.scalar_apply, Finset.sum_apply, Pi.single_apply, Matrix.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_add (f := _)]
    first
      | rfl
      | exact (Complex.coe_smul _ _).symm
      | (ext φ g; rfl)
end
