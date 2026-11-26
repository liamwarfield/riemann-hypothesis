module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestBump

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasSym
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.casSym :
    UpperTheory.V.Cj.H.CasSym := by
  intro E _ _ _ a ha μ _ _ n e c
  have hG := gardFacts E a ha μ
  have hC := (clFacts E a μ).1
  have hcomb : ∀ (s t : ℂ), ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (s • φ + t • ψ) = s • cl μ φ + t • cl μ ψ :=
    fun s t φ hφ ψ hψ => (hC φ ψ s t (hG φ hφ).2.1 (hG ψ hψ).2.1).2
  have hL : ∀ X, ∀ φ ∈ gard μ, lie E a X φ ∈ gard μ := fun X φ hφ => (hG φ hφ).2.2.2.1 X
  have hskew : ∀ X, ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ,
      inner ℂ (cl μ (lie E a X φ)) (cl μ ψ) = -inner ℂ (cl μ φ) (cl μ (lie E a X ψ)) := by
    intro X φ hφ ψ hψ
    have h := skew_lie_action_L2 E a μ X φ ψ (hG φ hφ).1 (hG ψ hψ).1 (hG φ hφ).2.1 (hG ψ hψ).2.1
      (hG _ (hL X φ hφ)).2.1 (hG _ (hL X ψ hψ)).2.1
    rw [cl_eq (hG φ hφ).2.1, cl_eq (hG ψ hψ).2.1, cl_eq (hG _ (hL X φ hφ)).2.1, cl_eq (hG _ (hL X ψ hψ)).2.1]
    exact eq_neg_of_add_eq_zero_left h
  let P : Module.End ℂ (Sm E a) → Prop := fun T => (∀ φ ∈ gard μ, T φ ∈ gard μ) ∧
    ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, inner ℂ (cl μ (T φ)) (cl μ ψ) = inner ℂ (cl μ φ) (cl μ (T ψ))
  have hP1 : P 1 := ⟨fun _ h => h, fun _ _ _ _ => rfl⟩
  have hPc : ∀ (s t : ℝ) (T S : Module.End ℂ (Sm E a)), P T → P S → P ((s : ℂ) • T + (t : ℂ) • S) := by
    intro s t T S hT hS
    refine ⟨fun φ hφ => ?_, fun φ hφ ψ hψ => ?_⟩
    · exact add_mem (Submodule.smul_mem _ _ (hT.1 φ hφ)) (Submodule.smul_mem _ _ (hS.1 φ hφ))
    · change inner ℂ (cl μ ((s : ℂ) • T φ + (t : ℂ) • S φ)) (cl μ ψ) =
        inner ℂ (cl μ φ) (cl μ ((s : ℂ) • T ψ + (t : ℂ) • S ψ))
      rw [hcomb _ _ _ (hT.1 φ hφ) _ (hS.1 φ hφ), hcomb _ _ _ (hT.1 ψ hψ) _ (hS.1 ψ hψ), inner_add_left,
        inner_add_right, inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, Complex.conj_ofReal,
        Complex.conj_ofReal, hT.2 φ hφ ψ hψ, hS.2 φ hφ ψ hψ]
  have hP0 : P 0 := by
    have h := hPc 0 0 1 1 hP1 hP1
    simpa using h
  have hPa : ∀ T S, P T → P S → P (T + S) := fun T S hT hS => by
    have h := hPc 1 1 T S hT hS
    simpa using h
  have hPs : ∀ (t : ℝ) T S, P T → P S → P (T - (t : ℂ) • S) := fun t T S hT hS => by
    have h := hPc 1 (-t) T S hT hS
    rwa [Complex.ofReal_one, one_smul, Complex.ofReal_neg, neg_smul, ← sub_eq_add_neg] at h
  have hPsq : ∀ X, P (lie E a X * lie E a X) := fun X =>
    ⟨fun φ hφ => hL X _ (hL X φ hφ), fun φ hφ ψ hψ => by
      change inner ℂ (cl μ (lie E a X (lie E a X φ))) (cl μ ψ) = inner ℂ (cl μ φ) (cl μ (lie E a X (lie E a X ψ)))
      rw [hskew X _ (hL X φ hφ) ψ hψ, hskew X φ hφ _ (hL X ψ hψ), neg_neg]⟩
  have hsh : shift (lie E a) 0 = lie E a := by
    refine LinearMap.ext fun X => ?_
    rw [shift_apply, zero_mul, zero_smul, add_zero]
  have hcas : P (casA 0 c e) := by
    unfold casA
    rw [hsh]
    refine hPs c _ _ ?_ hP1
    unfold cas
    refine Finset.sum_induction _ P hPa hP0 fun j _ => ?_
    have h := hPs 1 _ _ (hPsq (toL (e j).1)) (hPsq (toL (Complex.I • (e j).1)))
    rwa [Complex.ofReal_one, one_smul] at h
  exact hcas.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LiftCv
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.liftCv :
    UpperTheory.V.Cj.H.LiftCv := by
  intro E _ _ _ a ha μ _ _ T hT T' hL ψ φ F hψ hφ
  obtain ⟨c1, c2, -, c4⟩ := clFacts E a μ
  have hφg : φ ∈ gard μ := Submodule.subset_span ⟨ψ, F, hψ, hφ⟩
  obtain ⟨g1, g2⟩ := hL φ hφg
  let φ' : Sm E a := ⟨cv ψ.1 (T F), cvSm E a μ ψ hψ (T F)⟩
  have hφ'g : φ' ∈ gard μ := Submodule.subset_span ⟨ψ, T F, hψ, rfl⟩
  have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
  have hint : Integrable (fun y => ψ.1 y⁻¹) μ :=
    (hc.comp continuous_inv).integrable_of_hasCompactSupport
      (hψ.1.comp_homeomorph (Homeomorph.inv (GA E a)))
  have e : cl μ (T' φ) = cl μ φ' := by
    rw [g2, c4 ψ φ F hψ hφ, c4 ψ φ' (T F) hψ rfl]
    exact ropComm _ _ μ T hT _ hint F
  have hd : (1 : ℂ) • T' φ + (-1 : ℂ) • φ' ∈ gard μ :=
    add_mem (Submodule.smul_mem _ _ g1) (Submodule.smul_mem _ _ hφ'g)
  obtain ⟨d1, d2, -⟩ := gardFacts E a ha μ _ hd
  have h0 := c2 _ d1 d2 (by
    rw [(c1 _ _ 1 (-1) (gardFacts E a ha μ _ g1).2.1 (gardFacts E a ha μ _ hφ'g).2.1).2, e]
    simp)
  have h1 : T' φ = φ' := by
    rw [one_smul, neg_one_smul, add_neg_eq_zero] at h0
    exact h0
  rw [h1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CommOfZalg
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

namespace UpperTheory.V.Cj.H.CasimirOperatorShift

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem comm_of_zalg {z o : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (ho : ∀ τ u, Commute (cap τ u) o) :
    Commute z o := by
  refine Algebra.adjoin_induction (p := fun x _ => Commute x o) ?_ (fun r => Algebra.commutes r _)
    (fun _ _ _ _ hx hy => hx.add_left hy) (fun _ _ _ _ hx hy => hx.mul_left hy) hz
  rintro _ ⟨τ, u, rfl⟩
  exact ho τ u

private theorem uC_sh (r : ℝ) (X : Lie E a) : Cm.uC E a (shift (Cm.ιC E a) r X) = shift (lie E a) r X := by
  rw [shift_apply, shift_apply, map_add (f := _), Cm.uC_ιC, ← algebraMap_smul ℂ (r * ell E a X) (1 : Cm.UC E a), map_smul,
    map_one, algebraMap_smul]

private theorem cas_mem {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) (r : ℝ) :
    cas (shift (lie E a) r) e ∈ Zalg E a := by
  have hL : IsLieHom (shift (Cm.ιC E a) r) := (ellFacts E a).2.2.2 _ _ r Cm.isLieHom_ιC
  have hX : ∀ X, Commute (cas (shift (Cm.ιC E a) r) e) (Cm.ιC E a X) := fun X => by
    have h := casComm E a n e he _ _ hL X
    have h' : Cm.ιC E a X = shift (Cm.ιC E a) r X - (r * ell E a X) • 1 := by rw [shift_apply, add_sub_cancel_right]
    rw [h']
    exact h.sub_right ((Commute.one_right _).smul_right _)
  have hle : Algebra.adjoin ℂ {x : Cm.UC E a | ∃ τ i j, x = Cm.genC τ i j} ≤
      Subalgebra.centralizer ℂ {cas (shift (Cm.ιC E a) r) e} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (((hX _).sub_right ((hX _).smul_right _)).smul_right _).eq
  rw [Cm.adjoin_genC] at hle
  rw [Cm.Zalg_eq_map]
  exact ⟨_, Subalgebra.mem_center_iff.2 fun x => (hle Algebra.mem_top _ rfl).symm,
    by simp only [cas, map_sum, map_sub, map_mul, uC_sh, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]⟩

private theorem cap_rt (τ : E →+* ℂ) (u : ℂ) (g : GA E a) : Commute (cap τ u) (rt E a g) := by
  rw [← infGL_mul_finGL g, map_mul]
  exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _).mul_right (commute_cap_finRep τ u _)

private theorem sh_apply (r : ℝ) (X : Lie E a) (φ : Sm E a) :
    shift (lie E a) r X φ = lie E a X φ + ((r * ell E a X : ℝ) : ℂ) • φ := by
  rw [shift_apply]; rfl

end UpperTheory.V.Cj.H.CasimirOperatorShift

open UpperTheory.V.Cj.H.CasimirOperatorShift in
theorem UpperTheory.V.Cj.H.casOp :
    UpperTheory.V.Cj.H.CasOp := by
  intro E _ _ _ a n e he r c
  have hz := cas_mem he r
  have hc : ∀ o : Module.End ℂ (Sm E a), (∀ τ u, Commute (cap τ u) o) → Commute o (casA r c e) := fun o ho =>
    (comm_of_zalg hz ho).symm.sub_right ((Commute.one_right _).smul_right _)
  refine ⟨fun X => hc _ fun τ u => commute_cap_lie τ u X, fun g => hc _ fun τ u => cap_rt τ u g, fun N hN => ?_⟩
  have hs : ∀ X, ∀ φ ∈ N, shift (lie E a) r X φ ∈ N := fun X φ hφ => by
    rw [sh_apply]
    exact N.add_mem (hN X φ hφ) (N.smul_mem _ hφ)
  refine ⟨fun φ hφ => ?_, fun T hT φ hφ => ?_⟩
  · simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact N.sub_mem (N.sum_mem fun j _ => N.sub_mem (hs _ _ (hs _ _ hφ)) (hs _ _ (hs _ _ hφ))) (N.smul_mem _ hφ)
  · have ht : ∀ X, ∀ φ ∈ N, shift (lie E a) r X (T φ) = T (shift (lie E a) r X φ) := fun X φ hφ => by
      rw [sh_apply, sh_apply, hT.lie X φ hφ, map_add (f := _), map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ht _ _ hφ, ht _ _ (hs _ _ hφ), ht _ _ hφ, ht _ _ (hs _ _ hφ)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjectionAlt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardSep
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Approx
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.approx :
    UpperTheory.V.Cj.H.Approx := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ F hF
  by_contra hF0
  have hpos : 0 < ‖F‖ := norm_pos_iff.mpr hF0
  have hcont := GlobalTheory.AutomorphicL2Unitary.continuous_R (Γ := Γ) (μ := μ) F
  obtain ⟨f, hfc, hfs, hfr, hf1, hfW, hfF⟩ :=
    hF {g | ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2} (by
      apply (isOpen_lt (continuous_norm.comp (hcont.sub continuous_const))
        continuous_const).mem_nhds
      show ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ 1 F - F‖ < ‖F‖ / 2
      rw [map_one, ContinuousLinearMap.one_apply, sub_self, norm_zero]
      positivity)
  have hfre : ∀ y, f y = ((f y).re : ℂ) := by
    intro y
    obtain ⟨t, _, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
  have hfnn : ∀ y, 0 ≤ (f y).re := by
    intro y
    obtain ⟨t, ht0, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
    exact ht0
  have hint : MeasureTheory.Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hrep := (GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hint) F
  have hφ := hrep.1
  have hzero : ∫ g, f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F ∂μ = 0 := hrep.2.symm.trans hfF
  have hI : ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ = 0 := by
    rw [integral_re (hφ.const_inner F), integral_inner hφ F, hzero, inner_zero_right]
    simp
  have hbound : ∀ g, ‖F‖ ^ 2 / 2 * (f g).re
      ≤ RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) := by
    intro g
    have hre : RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F))
        = (f g).re * (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
      rw [inner_smul_right]
      conv_lhs => rw [hfre g]
      simp
    rw [hre]
    by_cases hg : ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2
    · have e1 : inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
          = inner ℂ F F - inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F) := by
        rw [inner_sub_right]
        ring
      have e2 : (inner ℂ F F).re = ‖F‖ ^ 2 := by
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) F
      have e3 := re_inner_le_norm (𝕜 := ℂ) F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
      rw [norm_sub_rev] at e3
      have e4 : ‖F‖ ^ 2 / 2 ≤ (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
        rw [e1, Complex.sub_re, e2]
        have e3' : (inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re ≤ ‖F‖ * (‖F‖ / 2) := by
          simp only [RCLike.re_to_complex] at e3
          exact e3.trans (mul_le_mul_of_nonneg_left hg.le (norm_nonneg F))
        nlinarith
      have h5 := mul_le_mul_of_nonneg_left e4 (hfnn g)
      linarith
    · have h0 : f g = 0 := hfW g hg
      rw [h0]
      simp
  have hpos2 : 0 < ∫ g, (f g).re ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp hfc) (hfs.comp_left Complex.zero_re) (fun y => hfnn y)
      (by
        intro h
        apply hf1
        rw [hfre 1, h, Complex.ofReal_zero])
  have hmono : ∫ g, ‖F‖ ^ 2 / 2 * (f g).re ∂μ
      ≤ ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ :=
    MeasureTheory.integral_mono (hint.re.const_mul _) ((hφ.const_inner F).re) hbound
  rw [hI, MeasureTheory.integral_const_mul] at hmono
  have h6 : 0 < ‖F‖ ^ 2 / 2 * ∫ g, (f g).re ∂μ := mul_pos (by positivity) hpos2
  linarith
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.gardSep :
    UpperTheory.V.Cj.H.GardSep := by
  open scoped Pointwise in
  intro E _ _ _ a μ _ _ W hW h
  rw [Submodule.eq_bot_iff]
  intro F hF
  refine approx (GA E a) (latticeGL E a) μ F fun U hU => ?_
  have hU' : (interior U)⁻¹ ∈ 𝓝 (1 : GA E a) := inv_mem_nhds_one _ (interior_mem_nhds.2 hU)
  obtain ⟨ψ, hψ, hpos, hne, hout⟩ := testBump E a {1} (interior U)⁻¹ isCompact_singleton isOpen_interior.inv
    (Set.singleton_subset_iff.2 (mem_of_mem_nhds hU'))
  have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
  have hc' : Continuous fun y => ψ.1 y⁻¹ := hc.comp continuous_inv
  have hs : HasCompactSupport fun y => ψ.1 y⁻¹ := hψ.1.comp_homeomorph (Homeomorph.inv (GA E a))
  refine ⟨fun y => ψ.1 y⁻¹, hc', hs, fun y => hpos _, by simpa using hne 1 rfl, fun y hy => hout _ ?_, ?_⟩
  · intro hh
    exact hy (interior_subset (by simpa using hh))
  · have e := (clFacts E a μ).2.2.2 ψ ⟨cv ψ.1 F, cvSm E a μ ψ hψ F⟩ F hψ rfl
    rw [← e]
    refine h _ (Submodule.subset_span ⟨ψ, F, hψ, rfl⟩) ?_
    rw [e]
    exact hW.Rop_mem (hc'.integrable_of_hasCompactSupport hs) hF
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsProj
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsDense
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.absDense :
    UpperTheory.V.Cj.H.AbsDense := by
  intro G H _ _ _ _ R D A hD hR hA hsym hirr s hs w hw
  set u : D → H := fun v => (A v : H) + (Complex.I * s) • (v : H) with hu
  have hinner : ∀ (g : G) (x y : H), inner ℂ (R g x) (R g y) = inner ℂ x y := fun g x y =>
    (LinearIsometry.mk (R g).toLinearMap (hR g)).inner_map_map x y
  have hinv : ∀ (g : G) (y : H), R g (R g⁻¹ y) = y := by
    intro g y
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let W : Submodule ℂ H :=
    { carrier := {x | ∀ v : D, inner ℂ x (u v) = 0}
      add_mem' := by
        intro a b ha hb v
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [inner_add_left, ha v, hb v, add_zero]
      zero_mem' := by
        intro v
        simp only [Set.mem_setOf_eq, inner_zero_left]
      smul_mem' := by
        intro c a ha v
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [inner_smul_left, ha v, mul_zero] }
  have hW : GlobalTheory.AutomorphicL2Unitary.IsSubrep R W := by
    refine ⟨?_, ?_⟩
    · have hset : (W : Set H) = ⋂ v : D, {x | inner ℂ x (u v) = 0} := by
        ext x
        simp [W]
      rw [hset]
      exact isClosed_iInter fun v => isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro g x hx v
      show inner ℂ (R g x) (u v) = 0
      have key : R g⁻¹ (u v) = u ⟨R g⁻¹ v, hD g⁻¹ v v.2⟩ := by
        simp only [hu, map_add (f := _), map_smul]
        rw [hA g⁻¹ v]
      rw [← hinv g (u v), hinner, key]
      exact hx _
  have hWD : W ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxD⟩ := Submodule.mem_inf.mp hx
    have h0 : inner ℂ x (u ⟨x, hxD⟩) = 0 := hxW ⟨x, hxD⟩
    have hre : (inner ℂ x (A ⟨x, hxD⟩ : H)).im = 0 := by
      have hs' := hsym ⟨x, hxD⟩ ⟨x, hxD⟩
      rw [← inner_conj_symm] at hs'
      exact Complex.conj_eq_iff_im.mp hs'
    simp only [hu] at h0
    rw [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
    have him := congrArg Complex.im h0
    simp [hre, hs] at him
    rw [← Complex.ofReal_pow, Complex.ofReal_re] at him
    rw [Submodule.mem_bot]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp him)
  have hwW : w ∈ W := hw
  rw [hirr W hW hWD] at hwW
  exact (Submodule.mem_bot ℂ).mp hwW
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsInv
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem UpperTheory.V.Cj.H.absInv_low {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x v : H) (s : ℝ)
    (h : inner ℂ x v = inner ℂ v x) : |s| * ‖v‖ ≤ ‖x + (Complex.I * s) • v‖ := by
  have hre : (inner ℂ x v).im = 0 := by
    have e := congrArg Complex.im h
    rw [← inner_conj_symm v x, Complex.conj_im] at e
    linarith
  have hsq : ‖x + (Complex.I * s) • v‖ ^ 2 = ‖x‖ ^ 2 + (|s| * ‖v‖) ^ 2 := by
    rw [@norm_add_sq ℂ, inner_smul_right, norm_smul]
    have hn : ‖Complex.I * (s : ℂ)‖ = |s| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hn]
    simp [Complex.mul_re, hre]
  have h0 : 0 ≤ |s| * ‖v‖ := mul_nonneg (abs_nonneg s) (norm_nonneg v)
  nlinarith [norm_nonneg (x + (Complex.I * s) • v), sq_nonneg ‖x‖]

theorem UpperTheory.V.Cj.H.absInv :
    UpperTheory.V.Cj.H.AbsInv := by
  intro H _ _ _ D A hA s hs hd
  let L : D →ₗ[ℂ] H := D.subtype.comp A + (Complex.I * s) • D.subtype
  have hL : ∀ v, L v = ↑(A v) + (Complex.I * s) • (v : H) := fun v => rfl
  have hs' : 0 < |s| := abs_pos.mpr hs
  have hlow : ∀ v : D, |s| * ‖(v : H)‖ ≤ ‖L v‖ := by
    intro v
    rw [hL]
    exact UpperTheory.V.Cj.H.absInv_low _ _ s (hA v v)
  have hinj : Function.Injective L := by
    intro a b hab
    have h1 := hlow (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h1
    have h2 : ‖((a - b : D) : H)‖ = 0 :=
      le_antisymm (le_of_mul_le_mul_left (by simpa using h1) hs') (norm_nonneg _)
    rw [norm_eq_zero, Submodule.coe_sub, sub_eq_zero] at h2
    exact Subtype.ext h2
  let R := LinearMap.range L
  let e := LinearEquiv.ofInjective L hinj
  have he : ∀ x : D, ((e x : R) : H) = L x := fun x => LinearEquiv.ofInjective_apply L (h := hinj) x
  let g : R →ₗ[ℂ] H := D.subtype.comp e.symm.toLinearMap
  have hg : ∀ y : R, |s| * ‖g y‖ ≤ ‖(y : H)‖ := by
    intro y
    have h1 : L (e.symm y) = y := by
      have h2 := he (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    have h3 := hlow (e.symm y)
    rw [h1] at h3
    exact h3
  let gc : R →L[ℂ] H := g.mkContinuous (|s|⁻¹) (fun y => by
    rw [inv_mul_eq_div, le_div_iff₀ hs']
    have := hg y
    change ‖g y‖ * |s| ≤ ‖(y : H)‖
    linarith)
  have hdense : Dense (R : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_orthogonal_eq_closure]
    have hb : Rᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      apply hd w
      intro v
      exact (Submodule.mem_orthogonal' R w).1 hw _ (LinearMap.mem_range_self L v)
    rw [hb, Submodule.bot_orthogonal_eq_top]
  have hdr : DenseRange (R.subtypeL : R → H) := hdense.denseRange_val
  have hui : IsUniformInducing (R.subtypeL : R → H) := isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨gc.extend R.subtypeL, ?_, ?_⟩
  · intro v
    have h1 := ContinuousLinearMap.extend_eq gc hdr hui ⟨L v, LinearMap.mem_range_self L v⟩
    have h2 : e.symm ⟨L v, LinearMap.mem_range_self L v⟩ = v := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (he v).symm
    calc gc.extend R.subtypeL (↑(A v) + (Complex.I * ↑s) • ↑v)
        = gc ⟨L v, LinearMap.mem_range_self L v⟩ := h1
      _ = ↑v := by
        show ((e.symm ⟨L v, LinearMap.mem_range_self L v⟩ : D) : H) = v
        rw [h2]
  · intro w
    refine hdense.induction (P := fun w => |s| * ‖gc.extend R.subtypeL w‖ ≤ ‖w‖) ?_ ?_ w
    · intro y hy
      have h1 : gc.extend R.subtypeL y = gc ⟨y, hy⟩ :=
        ContinuousLinearMap.extend_eq gc hdr hui ⟨y, hy⟩
      show |s| * ‖gc.extend R.subtypeL y‖ ≤ ‖y‖
      rw [h1]
      exact hg ⟨y, hy⟩
    · exact isClosed_le (continuous_const.mul (continuous_norm.comp (gc.extend R.subtypeL).continuous))
        continuous_norm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsLim
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem tendsto_zero_on_closure_of_lipschitz_family {H : Type} [NormedAddCommGroup H] (Q : ℕ → H → H)
    (hQ : ∀ k x y, ‖Q k x‖ ≤ ‖Q k y‖ + ‖x - y‖) (S : Set H)
    (hS : ∀ x ∈ S, Filter.Tendsto (fun k => Q k x) Filter.atTop (nhds 0)) (x : H)
    (hx : x ∈ closure S) :
    Filter.Tendsto (fun k => Q k x) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hS y hyS) (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  rw [dist_zero_right] at h1 ⊢
  rw [dist_eq_norm] at hxy
  calc ‖Q k x‖ ≤ ‖Q k y‖ + ‖x - y‖ := hQ k x y
    _ < ε / 2 + ε / 2 := add_lt_add h1 hxy
    _ = ε := by ring

theorem UpperTheory.V.Cj.H.absLim :
    UpperTheory.V.Cj.H.AbsLim := by
  intro H _ _ _ D A hA s hs hplus hminus T hT hTb P hP hPr w
  have hc : ∀ k, ‖(Complex.I * (s k : ℂ))‖ = |s k| := by
    intro k
    simp
  have hadj : ∀ k (v' : D), ContinuousLinearMap.adjoint (T k)
      ((A v' : H) - (Complex.I * (s k : ℂ)) • (v' : H)) = (v' : H) := by
    intro k v'
    apply sub_eq_zero.mp
    apply hplus k
    intro v
    rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left, hT k v]
    rw [inner_sub_left, inner_smul_left, inner_add_right, inner_smul_right, hA v' v]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hPfix : ∀ k, (Complex.I * (s k : ℂ)) • T k (P w) = P w := by
    intro k
    apply sub_eq_zero.mp
    apply hminus k
    intro v
    have h1 : inner ℂ (T k (P w)) ((A v : H) - (Complex.I * (s k : ℂ)) • (v : H))
        = inner ℂ (P w) (v : H) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hadj k v]
    rw [inner_sub_left, inner_smul_left, h1, inner_sub_right, inner_smul_right, hP w v]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hr : Filter.Tendsto (fun k => (Complex.I * (s k : ℂ)) • T k (w - P w)) Filter.atTop
      (nhds 0) := by
    refine tendsto_zero_on_closure_of_lipschitz_family (fun k x => (Complex.I * (s k : ℂ)) • T k x) ?_
      (Set.range fun v : D => (A v : H)) ?_ (w - P w) ?_
    · intro k x y
      have e : (Complex.I * (s k : ℂ)) • T k x = (Complex.I * (s k : ℂ)) • T k y
          + (Complex.I * (s k : ℂ)) • T k (x - y) := by
        rw [map_sub, smul_sub]
        abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, hc]
      exact hTb k (x - y)
    · rintro _ ⟨v, rfl⟩
      have e : ∀ k, (Complex.I * (s k : ℂ)) • T k (A v : H) = (Complex.I * (s k : ℂ)) • (v : H)
          - (Complex.I * (s k : ℂ)) • ((Complex.I * (s k : ℂ)) • T k (v : H)) := by
        intro k
        have h := hT k v
        rw [map_add (f := _), map_smul] at h
        rw [eq_sub_iff_add_eq, ← smul_add, h]
      apply squeeze_zero_norm (a := fun k => 2 * |s k| * ‖(v : H)‖)
      · intro k
        rw [e k]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_smul, norm_smul, hc]
        have h2 := mul_le_mul_of_nonneg_left (hTb k (v : H)) (abs_nonneg (s k))
        linarith
      · have h3 : Filter.Tendsto (fun k => |s k|) Filter.atTop (nhds 0) := by
          simpa using hs.abs
        have h4 := (h3.const_mul 2).mul_const ‖(v : H)‖
        rwa [mul_zero, zero_mul] at h4
    · have h := hPr w
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range] at h
      exact h
  have hsum : ∀ k, (Complex.I * (s k : ℂ)) • T k w
      = P w + (Complex.I * (s k : ℂ)) • T k (w - P w) := by
    intro k
    rw [map_sub, smul_sub, hPfix k]
    abel
  have h5 := (tendsto_const_nhds (x := P w) (f := Filter.atTop)).add hr
  rw [add_zero] at h5
  exact h5.congr (fun k => (hsum k).symm)
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem absProj_ext {H D : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : D → H) (hd : ∀ w : H, (∀ v : D, inner ℂ w (e v) = 0) → w = 0) (L : H →L[ℂ] H)
    (hL : ∀ v, L (e v) = 0) (w : H) : L w = 0 := by
  have hperp : (Submodule.span ℂ (Set.range e))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    apply hd u
    intro v
    rw [inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ u).1 hu (e v) (Submodule.subset_span ⟨v, rfl⟩)
  have hcl : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hperp, Submodule.bot_orthogonal_eq_top]
  have hle : Submodule.span ℂ (Set.range e) ≤ LinearMap.ker (L : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hL v
  have hle' : (Submodule.span ℂ (Set.range e)).topologicalClosure ≤ LinearMap.ker (L : H →ₗ[ℂ] H) :=
    Submodule.topologicalClosure_minimal _ hle L.isClosed_ker
  have hw : w ∈ LinearMap.ker (L : H →ₗ[ℂ] H) := hle' (hcl ▸ Submodule.mem_top)
  exact hw

theorem UpperTheory.V.Cj.H.absProj :
    UpperTheory.V.Cj.H.AbsProj := by
  intro G H _ _ _ _ R D A hD hiso hAR hsym hirr
  set s : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hsdef
  have hs : ∀ k : ℕ, s k ≠ 0 := fun k ↦ by
    simp only [hsdef]
    positivity
  have hs0 : Filter.Tendsto s Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdense : ∀ (t : ℝ), t ≠ 0 → ∀ (w : H),
      (∀ (v : ↥D), inner ℂ w (↑(A v) + (Complex.I * ↑t) • ↑v) = 0) → w = 0 :=
    absDense G H R D A hD hiso hAR hsym hirr
  have hdense' : ∀ (k : ℕ) (w : H),
      (∀ v : ↥D, inner ℂ w (↑(A v) - (Complex.I * ↑(s k)) • ↑v) = 0) → w = 0 := by
    intro k w hw
    refine hdense (-(s k)) (neg_ne_zero.2 (hs k)) w fun v ↦ ?_
    have h : (↑(A v) : H) + (Complex.I * ((-(s k) : ℝ) : ℂ)) • (↑v : H)
        = ↑(A v) - (Complex.I * ↑(s k)) • ↑v := by
      push_cast
      rw [mul_neg, neg_smul, ← sub_eq_add_neg]
    rw [h]
    exact hw v
  have hT : ∀ k : ℕ, ∃ T : H →L[ℂ] H,
      (∀ v : ↥D, T (↑(A v) + (Complex.I * ↑(s k)) • ↑v) = ↑v) ∧ ∀ w : H, |s k| * ‖T w‖ ≤ ‖w‖ :=
    fun k ↦ absInv H D A hsym (s k) (hs k) (hdense (s k) (hs k))
  choose T hTinv hTbd using hT
  have hTR : ∀ (k : ℕ) (g : G) (w : H), T k (R g w) = R g (T k w) := by
    intro k g w
    have key := absProj_ext (fun v : ↥D ↦ (↑(A v) + (Complex.I * ↑(s k)) • ↑v : H))
      (hdense (s k) (hs k)) ((T k).comp (R g) - (R g).comp (T k)) ?_ w
    · simpa [sub_eq_zero] using key
    · intro v
      have hv : (R g) ↑v ∈ D := hD g v v.2
      have h1 : (R g) (↑(A v) + (Complex.I * ↑(s k)) • ↑v)
          = ↑(A ⟨(R g) ↑v, hv⟩) + (Complex.I * ↑(s k)) • ↑(⟨(R g) ↑v, hv⟩ : ↥D) := by
        rw [map_add (f := _), map_smul, hAR g v]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      rw [h1, hTinv k ⟨(R g) ↑v, hv⟩, hTinv k v]
      simp
  set K : Submodule ℂ H := (D.subtype ∘ₗ A).range.topologicalClosure with hKdef
  set P : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - K.starProjection with hPdef
  have hPperp : ∀ (w : H) (v : ↥D), inner ℂ (P w) ↑(A v) = 0 := by
    intro w v
    have hAv : (↑(A v) : H) ∈ K :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (D.subtype ∘ₗ A) v)
    simp only [hPdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    exact Submodule.inner_left_of_mem_orthogonal hAv (K.sub_starProjection_mem_orthogonal w)
  have hclose : ∀ w : H, w - P w ∈ (D.subtype ∘ₗ A).range.topologicalClosure := by
    intro w
    simp only [hPdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, sub_sub_cancel]
    exact K.starProjection_apply_mem w
  have hlim := absLim H D A hsym s hs0 (fun k ↦ hdense (s k) (hs k)) hdense' T hTinv hTbd P
    hPperp hclose
  refine ⟨P, fun k ↦ (Complex.I * ↑(s k)) • T k, T, ?_, ?_, ?_, ?_, hPperp, ?_⟩
  · intro g w
    have h2 : Filter.Tendsto (fun k ↦ (Complex.I * ↑(s k)) • T k (R g w)) Filter.atTop
        (𝓝 (R g (P w))) := by
      refine (((R g).continuous.tendsto _).comp (hlim w)).congr fun k ↦ ?_
      simp [Function.comp_apply, map_smul, hTR k g w]
    exact tendsto_nhds_unique (hlim (R g w)) h2
  · intro k g w
    simp [ContinuousLinearMap.smul_apply, map_smul, hTR k g w]
  · intro k g w
    exact hTR k g w
  · intro k v
    have h := hTinv k v
    rw [map_add (f := _), map_smul] at h
    rw [ContinuousLinearMap.smul_apply]
    exact (eq_sub_of_add_eq h).symm
  · intro w
    simpa only [ContinuousLinearMap.smul_apply] using hlim w
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem transport {G H M : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup M] [Module ℂ M] (R : G →* (H →L[ℂ] H)) (f : M →ₗ[ℂ] H) (hf : Function.Injective f)
    (B : M →ₗ[ℂ] M) (ρ : G → M → M) (hR : ∀ g v, ‖R g v‖ = ‖v‖) (hρ : ∀ g m, f (ρ g m) = R g (f m))
    (hB : ∀ g m, B (ρ g m) = ρ g (B m)) (hs : ∀ m m', inner ℂ (f (B m)) (f m') = inner ℂ (f m) (f (B m')))
    (hW : ∀ W : Submodule ℂ H, GlobalTheory.AutomorphicL2Unitary.IsSubrep R W → (∀ m, f m ∈ W → f m = 0) → W = ⊥) :
    ∃ (P : H →L[ℂ] H) (Q S : ℕ → H →L[ℂ] H), (∀ g w, P (R g w) = R g (P w)) ∧ (∀ k g w, Q k (R g w) = R g (Q k w)) ∧
      (∀ k g w, S k (R g w) = R g (S k w)) ∧ (∀ k m, f m - Q k (f m) = S k (f (B m))) ∧
      (∀ w m, inner ℂ (P w) (f (B m)) = 0) ∧ ∀ w, Tendsto (fun k => Q k w) atTop (𝓝 (P w)) := by
  let ε : M ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hf
  let A : LinearMap.range f →ₗ[ℂ] LinearMap.range f := ε.toLinearMap ∘ₗ B ∘ₗ ε.symm.toLinearMap
  have hε : ∀ m, (ε m : H) = f m := fun _ => rfl
  have hA : ∀ m, (A (ε m) : H) = f (B m) := fun m => by
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hε]
  have hD : ∀ g, ∀ v ∈ LinearMap.range f, R g v ∈ LinearMap.range f := by
    rintro g _ ⟨m, rfl⟩
    exact ⟨ρ g m, hρ g m⟩
  obtain ⟨P, Q, S, h1, h2, h3, h4, h5, h6⟩ := absProj G H R (LinearMap.range f) A hD hR
    (by
      intro g v
      obtain ⟨m, rfl⟩ := ε.surjective v
      have : (⟨R g (ε m), hD g _ (ε m).2⟩ : LinearMap.range f) = ε (ρ g m) := Subtype.ext (hρ g m).symm
      rw [this, hA, hA, hB, hρ])
    (by
      intro v w
      obtain ⟨m, rfl⟩ := ε.surjective v
      obtain ⟨m', rfl⟩ := ε.surjective w
      rw [hA, hA, hε, hε, hs])
    (by
      intro W hs h
      refine hW W hs fun m hm => ?_
      have : f m ∈ W ⊓ LinearMap.range f := ⟨hm, m, rfl⟩
      rwa [h, Submodule.mem_bot] at this)
  refine ⟨P, Q, S, h1, h2, h3, fun k m => ?_, fun w m => ?_, h6⟩
  · rw [← hA]; exact h4 k (ε m)
  · rw [← hA]; exact h5 w (ε m)

theorem UpperTheory.V.Cj.H.casimir_resolvent_projection :
    UpperTheory.V.Cj.H.CasimirResolventProjection := by
  intro E _ _ _ a ha μ _ _ n e he c
  have hg := gardFacts E a ha μ
  obtain ⟨c1, c2, c3, -⟩ := clFacts E a μ
  obtain ⟨-, o2, o3⟩ := casOp E a n e he 0 c
  have hm : ∀ φ ∈ gard μ, casA 0 c e φ ∈ gard μ := (o3 (gard μ) fun X φ h => (hg φ h).2.2.2.1 X).1
  let f : gard μ →ₗ[ℂ] HL μ :=
    { toFun := fun φ => cl μ φ.1
      map_add' := fun φ ψ => by
        have := (c1 φ.1 ψ.1 1 1 (hg _ φ.2).2.1 (hg _ ψ.2).2.1).2
        simpa only [one_smul, Submodule.coe_add] using this
      map_smul' := fun s φ => by
        have := (c1 φ.1 φ.1 s 0 (hg _ φ.2).2.1 (hg _ φ.2).2.1).2
        simpa only [zero_smul, add_zero, Submodule.coe_smul, RingHom.id_apply] using this }
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro φ h
    exact Subtype.ext (c2 φ.1 (hg _ φ.2).1 (hg _ φ.2).2.1 h)
  obtain ⟨P, Q, S, h1, h2, h3, h4, h5, h6⟩ := transport (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ) f hf
    ((casA 0 c e).restrict hm) (fun g φ => ⟨rt E a g φ.1, (hg _ φ.2).2.2.2.2 g⟩)
    (fun g v => GlobalTheory.AutomorphicL2Unitary.norm_R g v)
    (fun g φ => c3 φ.1 g (hg _ φ.2).2.1)
    (fun g φ => Subtype.ext (LinearMap.congr_fun (o2 g).eq φ.1).symm)
    (fun φ ψ => casSym E a ha μ n e c φ.1 φ.2 ψ.1 ψ.2)
    (fun W hW h => gardSep E a μ W hW fun φ hφ => h ⟨φ, hφ⟩)
  exact ⟨P, Q, S, h1, h2, h3, fun k φ hφ => h4 k ⟨φ, hφ⟩, fun F φ hφ => h5 F ⟨φ, hφ⟩, h6⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpLim
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.opLim :
    UpperTheory.V.Cj.H.OpLim := by
  intro E _ _ _ a ha μ _ _ T P hT hP hlim T' P' hT' hP' φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ψ, F, hψ, hF⟩ := h
    intro C hC
    have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
    obtain ⟨-, hlin, -, hb⟩ := cvAlg (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1
    obtain ⟨B, hB⟩ := hb C hC
    have h1 : ∀ k, (T' k φ).1 = cv ψ.1 (T k F) := fun k =>
      liftCv E a ha μ (T k) (hT k) (T' k) (hT' k) ψ φ F hψ hF
    have h2 : (P' φ).1 = cv ψ.1 (P F) := liftCv E a ha μ P hP P' hP' ψ φ F hψ hF
    have h3 : Tendsto (fun k => B * ‖P F - T k F‖) atTop (𝓝 0) := by
      have h4 : Tendsto (fun k => P F - T k F) atTop (𝓝 (P F - P F)) := tendsto_const_nhds.sub (hlim F)
      have h5 := h4.norm.const_mul B
      simpa using h5
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [h3.eventually (gt_mem_nhds hε)] with k hk x hx
    rw [h1, h2, dist_eq_norm]
    have h6 := congrFun (hlin (P F) (T k F) 1 (-1)) x
    have h7 : (1 : ℂ) • P F + (-1 : ℂ) • T k F = P F - T k F := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [h7] at h6
    have h8 : cv ψ.1 (P F) x - cv ψ.1 (T k F) x = cv ψ.1 (P F - T k F) x := by
      rw [h6]; simp [sub_eq_add_neg]
    rw [h8]
    exact (hB _ x hx).trans_lt hk
  | zero =>
    intro C _
    simp only [map_zero]
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun k x _ => by simpa using hε
  | add φ ψ _ _ h1 h2 =>
    intro C hC
    simp only [map_add (f := _)]
    exact (h1 C hC).add (h2 C hC)
  | smul c φ _ h =>
    intro C hC
    simp only [map_smul]
    exact (uniformContinuous_const_smul c).comp_tendstoUniformlyOn (h C hC)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpComm
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.opComm :
    UpperTheory.V.Cj.H.OpComm := by
  intro E _ _ _ a ha μ _ _ T hT T' hL
  obtain ⟨c1, c2, c3, -⟩ := clFacts E a μ
  have gf := gardFacts E a ha μ
  refine ⟨fun φ h => (hL φ h).1, fun X φ hφ => ?_, fun g φ hφ => ?_⟩
  · induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨ψ, F, hψ, hφ⟩ := h
      have h1 := liftCv E a ha μ T hT T' hL ψ φ F hψ hφ
      have h2 := cvLie E a μ ψ _ hψ _ h1 X
      have h3 := cvLie E a μ ψ φ hψ F hφ X
      have h4 := liftCv E a ha μ T hT T' hL _ _ F (((testOps E a ψ).2 hψ).1 X) h3
      exact Subtype.ext (h2.trans h4.symm)
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul s x _ hx => simp only [map_smul, hx]
  · have m1 : rt E a g (T' φ) ∈ gard μ := (gf _ (hL φ hφ).1).2.2.2.2 g
    have m0 : rt E a g φ ∈ gard μ := (gf _ hφ).2.2.2.2 g
    have m2 : T' (rt E a g φ) ∈ gard μ := (hL _ m0).1
    have m3 : (1 : ℂ) • rt E a g (T' φ) + (-1 : ℂ) • T' (rt E a g φ) ∈ gard μ :=
      add_mem (Submodule.smul_mem _ _ m1) (Submodule.smul_mem _ _ m2)
    have e := (c1 _ _ 1 (-1) (gf _ m1).2.1 (gf _ m2).2.1).2
    rw [c3 _ g (gf _ (hL φ hφ).1).2.1, (hL φ hφ).2, (hL _ m0).2, c3 _ g (gf _ hφ).2.1, hT,
      ← add_smul, add_neg_cancel, zero_smul] at e
    have z := c2 _ (gf _ m3).1 (gf _ m3).2.1 e
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at z
    exact z
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpLift
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem lift_of_inj {M H : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup H] [Module ℂ H]
    (N : Submodule ℂ M) (c : N →ₗ[ℂ] H) (hc : Function.Injective c) (T : H →ₗ[ℂ] H)
    (hT : ∀ v : N, ∃ w : N, c w = T (c v)) :
    ∃ T' : M →ₗ[ℂ] M, ∀ v : N, ∃ h : T' v ∈ N, c ⟨T' v, h⟩ = T (c v) := by
  let l : N →ₗ[ℂ] N := (LinearEquiv.ofInjective c hc).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range c) (T ∘ₗ c) (fun v => hT v)
  have hl : ∀ v, c (l v) = T (c v) := fun v => by
    have := (LinearEquiv.ofInjective c hc).apply_symm_apply
      (LinearMap.codRestrict (LinearMap.range c) (T ∘ₗ c) (fun v => hT v) v)
    exact congrArg Subtype.val this
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (N.subtype ∘ₗ l)
  refine ⟨g, fun v => ?_⟩
  have e : g v = (l v : M) := LinearMap.congr_fun hg v
  refine ⟨e ▸ (l v).2, ?_⟩
  rw [← hl v]
  congr 1
  exact Subtype.ext e

theorem UpperTheory.V.Cj.H.opLift :
    UpperTheory.V.Cj.H.OpLift := by
  intro E _ _ _ a ha μ _ _ T hT
  have hG := gardFacts E a ha μ
  obtain ⟨hlin, hinj, -, hrop⟩ := clFacts E a μ
  have hadd : ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (φ + ψ) = cl μ φ + cl μ ψ := fun φ hφ ψ hψ => by
    have := (hlin φ ψ 1 1 (hG φ hφ).2.1 (hG ψ hψ).2.1).2
    simpa only [one_smul] using this
  have hsm : ∀ (s : ℂ), ∀ φ ∈ gard μ, cl μ (s • φ) = s • cl μ φ := fun s φ hφ => by
    have := (hlin φ φ s 0 (hG φ hφ).2.1 (hG φ hφ).2.1).2
    simpa only [zero_smul, add_zero] using this
  let c : gard μ →ₗ[ℂ] HL μ :=
    { toFun := fun v => cl μ v.1
      map_add' := fun v w => hadd v.1 v.2 w.1 w.2
      map_smul' := fun s v => hsm s v.1 v.2 }
  have hc : Function.Injective c := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact Subtype.ext (hinj v.1 (hG v.1 v.2).1 (hG v.1 v.2).2.1 hv)
  have key : ∀ φ ∈ gard μ, ∃ φ' ∈ gard μ, cl μ φ' = T (cl μ φ) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨ψ, F, hψ, e⟩ := h
      have hcont : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
      have hint : Integrable (fun y => ψ.1 y⁻¹) μ :=
        (hcont.comp continuous_inv).integrable_of_hasCompactSupport
          (hψ.1.comp_homeomorph (Homeomorph.inv (GA E a)))
      refine ⟨⟨cv ψ.1 (T F), cvSm E a μ ψ hψ (T F)⟩, Submodule.subset_span ⟨ψ, T F, hψ, rfl⟩, ?_⟩
      rw [hrop ψ φ F hψ e, hrop ψ _ (T F) hψ rfl]
      exact (ropComm _ _ μ T hT _ hint F).symm
    | zero =>
      have h0 : cl μ (0 : Sm E a) = 0 := map_zero c
      exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨x', hx', ex⟩ := ihx
      obtain ⟨y', hy', ey⟩ := ihy
      exact ⟨x' + y', Submodule.add_mem _ hx' hy', by
        rw [hadd x' hx' y' hy', hadd x hx y hy, ex, ey, map_add (f := _)]⟩
    | smul s x hx ihx =>
      obtain ⟨x', hx', ex⟩ := ihx
      exact ⟨s • x', Submodule.smul_mem _ s hx', by
        rw [hsm s x' hx', hsm s x hx, ex, map_smul]⟩
  obtain ⟨T', h⟩ := lift_of_inj (gard μ) c hc T.toLinearMap fun v => by
    obtain ⟨w, hw, e⟩ := key v.1 v.2
    exact ⟨⟨w, hw⟩, e⟩
  refine ⟨T', fun φ hφ => ?_⟩
  obtain ⟨h1, h2⟩ := h ⟨φ, hφ⟩
  exact ⟨h1, h2⟩
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.fnProj0 :
    UpperTheory.V.Cj.H.FnProj0 := by
  intro E _ _ _ a ha μ _ _ n e he c
  obtain ⟨P, Q, S, hP, hQ, hS, hres, hker, hlim⟩ := casimir_resolvent_projection E a ha μ n e he c
  obtain ⟨P', hP'⟩ := opLift E a ha μ P hP
  choose Q' hQ' using fun k => opLift E a ha μ (Q k) (hQ k)
  choose S' hS' using fun k => opLift E a ha μ (S k) (hS k)
  have hG := gardFacts E a ha μ
  obtain ⟨c1, c2, -, -⟩ := clFacts E a μ
  obtain ⟨-, -, hA⟩ := casOp E a n e he 0 c
  obtain ⟨hA1, hA2⟩ := hA (gard μ) fun X φ h => (hG φ h).2.2.2.1 X
  have hinj : ∀ φ ∈ gard μ, cl μ φ = 0 → φ = 0 := fun φ h h0 => c2 φ (hG φ h).1 (hG φ h).2.1 h0
  have hsub : ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (φ - ψ) = cl μ φ - cl μ ψ := by
    intro φ hφ ψ hψ
    have h := (c1 φ ψ 1 (-1) (hG φ hφ).2.1 (hG ψ hψ).2.1).2
    simpa only [one_smul, neg_smul, sub_eq_add_neg] using h
  have oS := fun k => opComm E a ha μ (S k) (hS k) (S' k) (hS' k)
  refine ⟨P', Q', S', opComm E a ha μ P hP P' hP', fun k => opComm E a ha μ (Q k) (hQ k) (Q' k) (hQ' k), oS,
    fun k φ hφ => ?_, fun φ hφ => ?_, opLim E a ha μ Q P hQ hP hlim Q' P' hQ' hP'⟩
  · rw [hA2 (S' k) (oS k) φ hφ]
    have h1 := hQ' k φ hφ
    have h2 := hS' k _ (hA1 φ hφ)
    have h3 := (gard μ).sub_mem hφ h1.1
    refine sub_eq_zero.1 (hinj _ ((gard μ).sub_mem h3 h2.1) ?_)
    rw [hsub _ h3 _ h2.1, hsub _ hφ _ h1.1, h1.2, h2.2, hres k φ hφ, sub_self]
  · have h1 := hP' φ hφ
    have h2 := hA1 _ h1.1
    refine hinj _ h2 (inner_self_eq_zero (𝕜 := ℂ).1 ?_)
    rw [casSym E a ha μ n e c _ h1.1 _ h2, h1.2]
    exact hker _ _ h2
