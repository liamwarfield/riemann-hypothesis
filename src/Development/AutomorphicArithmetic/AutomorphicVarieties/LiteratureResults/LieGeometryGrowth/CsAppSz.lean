module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.appSz :
    AppSz := by
  intro V W F _ _ _ _ _ _ k x
  refine ⟨?_, ?_, ?_⟩
  · intro f g a b hf hg ha hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    obtain ⟨u, hu, hfu⟩ := (hf.of_le hi').contDiffOn (m := i) le_rfl (by simp)
    obtain ⟨v, hv, hgv⟩ := (hg.of_le hi').contDiffOn (m := i) le_rfl (by simp)
    obtain ⟨s, hs, hso, hxs⟩ := mem_nhds_iff.1 (Filter.inter_mem hu hv)
    have key := norm_iteratedFDerivWithin_clm_apply (n := i)
      (hfu.mono fun y hy => (hs hy).1) (hgv.mono fun y hy => (hs hy).2) hso.uniqueDiffOn hxs le_rfl
    simp only [iteratedFDerivWithin_of_isOpen _ hso hxs] at key
    refine key.trans ?_
    have h0 := ha.nonneg
    have h1 := hb.nonneg
    calc _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * a * b := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have e1 := ha j (hj'.trans hi)
          have e2 := hb (i - j) ((Nat.sub_le _ _).trans hi)
          gcongr
      _ = 2 ^ i * a * b := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          simp
      _ ≤ 2 ^ k * a * b := by
          gcongr
          norm_num
  · intro L g b hg hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have key := L.iteratedFDeriv_comp_left hg (i := i) hi'
    have e : (fun y => L (g y)) = L ∘ g := rfl
    rw [e, key]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hb i hi) (norm_nonneg _))
  · intro ι s g b hg hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have key := iteratedFDeriv_fun_sum_apply (n := i) (u := s) (f := g) (x := x)
      (fun j hj => (hg j hj).of_le hi')
    rw [key]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hb j hj i hi)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmApply
open UpperTheory.V.Lit.Geo
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.omApply :
    OmApply := by
  intro Γ V S _ _ _ _ d G W hW q
  refine ⟨fun w s p hp => ?_, fun w s p hp => ?_⟩
  · refine toOm_apply G (z := fun s => pb (flow (W s) 1) (w.1 s)) (fun s x hx => ?_) s hp
    have hx' : flow (W s) 1 x ∈ G.Y := (hW.field s).2 x hx 1 ⟨zero_le_one, le_rfl⟩
    have h1 : ContDiffAt ℝ ∞ (W s) x := (hW.field s).1.contDiffAt (G.isOpen.mem_nhds hx)
    have h2 : ContDiffAt ℝ ∞ (flow (W s) 1) x := contDiffAt_id.add (h1.const_smul (1 : ℝ))
    have h3 : ContDiffAt ℝ ∞ (w.1 s) (flow (W s) 1 x) := (w.2 s).1.contDiffAt (G.isOpen.mem_nhds hx')
    exact (pbD V V (Fin d → ℂ) q _ _ x h2 h3).1.contDiffWithinAt
  · exact toOm_apply G (z := fun s => hom (W s) (w.1 s))
      (fun s => (hkSmooth V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) q (w.1 s) (w.2 s).1).2.2.2) s hp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.compSz :
    CompSz := by
  intro V W F _ _ _ _ _ _ k c
  have hD1 : (1 : ℝ) ≤ max 1 c := le_max_left _ _
  have hD0 : (0 : ℝ) ≤ max 1 c := zero_le_one.trans hD1
  refine ⟨(k.factorial : ℝ) * (max 1 c) ^ k, by positivity, ?_⟩
  intro g f x b hf hg hc hb i hi
  have hb0 : 0 ≤ b := hb.nonneg
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hne : ((k : ℕ) : WithTop ℕ∞) ≠ ∞ := by exact_mod_cast ENat.coe_ne_top k
  have hf' := (hf.of_le hk).eventually hne
  have hg' := (hg.of_le hk).eventually hne
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 hg'
  have hpre : ∀ᶠ y in 𝓝 x, f y ∈ t := hf.continuousAt.preimage_mem_nhds (hto.mem_nhds hxt)
  obtain ⟨s, hs, hso, hxs⟩ := eventually_nhds_iff.1 (hf'.and hpre)
  have hgt : ContDiffOn ℝ k g t := fun y hy => (ht y hy).contDiffWithinAt
  have hfs : ContDiffOn ℝ k f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := i) (C := b) (D := max 1 c) hgt hfs
    (by exact_mod_cast hi) hto.uniqueDiffOn hso.uniqueDiffOn (fun y hy => (hs y hy).2) hxs
    (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen j hto hxt]
      exact hb j (hj.trans hi))
    (fun j hj1 hj => by
      rw [iteratedFDerivWithin_of_isOpen j hso hxs]
      exact ((hc j hj1 (hj.trans hi)).trans (le_max_right 1 c)).trans
        (le_self_pow₀ hD1 (by omega)))
  rw [iteratedFDerivWithin_of_isOpen i hso hxs] at key
  refine key.trans ?_
  have h1 : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
  have h2 : (max 1 c) ^ i ≤ (max 1 c) ^ k := pow_le_pow_right₀ hD1 hi
  calc (i.factorial : ℝ) * b * (max 1 c) ^ i = ((i.factorial : ℝ) * (max 1 c) ^ i) * b := by ring
    _ ≤ _ := by gcongr
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem rat_split (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    infGL E a (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) *
        finGL E a (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * (infGL E a g * finGL E a x) := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem centre_zero : splitCentre E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext w
    simp [expU]
  rw [splitCentre, h, map_one, map_one]

private theorem scal_ex (r : ℝ) (hr : 0 < r) : ∃ (t : ℝ) (c : GL (Fin a) (Cinf E)),
    infGL E a c = splitCentre E a t ∧ ∀ p : HV E a, sand c p = r • p := by
  refine ⟨Real.log r / 2, _, rfl, fun p => Subtype.ext ?_⟩
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((Real.log r / 2 : ℝ) : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp (Real.log r / 2) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  have e : Real.exp (Real.log r / 2) * Real.exp (Real.log r / 2) = r := by
    rw [← Real.exp_add, add_halves, Real.exp_log hr]
  change Matrix.of (sand _ p).1 = r • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, e]

private theorem flow_eq {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a}
    {W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a} (hW : FCorr U Y W) (g h : GL (Fin a) (Cinf E))
    (x : GL (Fin a) (Af E)) (t : ℝ) (hh : h.val * star h.val = 1 + t • (Y (infGL E a g * finGL E a x)).1) :
    flow (W (x : GL (Fin a) (Af E) ⧸ U)) t (sand g (hOne E a)) = sand (g * h) (hOne E a) := by
  rw [flow, hW, ← map_smul, ← map_add (f := _), map_mul, ContinuousLinearMap.mul_apply]
  congr 1
  refine Subtype.ext ?_
  change (1 : Matrix (Fin a) (Fin a) (Cinf E)) + t • (Y (infGL E a g * finGL E a x)).1 = h.val * 1 * star h.val
  rw [mul_one, hh]

end UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.fieldFlow :
    FieldFlow := by
  intro E _ _ _ a ho U Ξ Y C hY W hW
  refine ⟨⟨fun s => ⟨fieldSm E a U Y C hY W hW s, ?_⟩, ?_, ?_⟩, flow_eq hW⟩
  · rintro p ⟨g, rfl⟩ t ht
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨h, hh, -⟩ := hY.root (infGL E a g * finGL E a x) t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩)
    rw [flow_eq hW g h x t hh]
    exact ⟨_, rfl⟩
  · rintro γ s p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ (sand g p) =
        sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1) * g) p := fun p => by
      rw [geo_ρ, map_mul]; rfl
    have hσ : (geo ho U Ξ).σ γ (x : GL (Fin a) (Af E) ⧸ U) =
        ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
    have hl := hY.left γ.1 0 (infGL E a g * finGL E a x)
    rw [centre_zero, mul_one] at hl
    rw [hσ, hs, hW, hW, hs, rat_split, hl]
  · rintro s r hr p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨t, c, hc, hp⟩ := scal_ex (E := E) (a := a) r hr
    have hl := hY.left 1 t (infGL E a g * finGL E a x)
    rw [map_one, one_mul, ← hc, ← mul_assoc, ← map_mul] at hl
    have hs : ∀ p : HV E a, r • sand g p = sand (c * g) p := fun p => by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    rw [hs, hW, hW, hs, hl]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevGood
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem one_kills {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))
    (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v}) : smLie Ξ (oneL E a) m = 0 := by
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  have hr' : Ξ.dmat (oneL E a) = (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := hr
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    change (lie E a (oneL E a)).rTensor _ (φ ⊗ₜ[ℂ] v) + (Matrix.toLin' (Ξ.dmat (oneL E a))).lTensor _ (φ ⊗ₜ[ℂ] v) = 0
    rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hφ.2.2 _ hr', hr', map_smul, Matrix.toLin'_one,
      LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.smul_tmul, ← TensorProduct.tmul_add, neg_smul, neg_add_cancel,
      TensorProduct.tmul_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private theorem d_basic {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} (α : Co Ξ q) (hα : IsLev U Ξ α)
    (X : Fin (q + 1) → Herm E a) (i : Fin (q + 1)) (hX : (X i).1 = 1) : dCo (smLie Ξ) α X = 0 := by
  rw [dCo_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : i = j
  · subst hj
    have h := one_kills U Ξ _ (hα.val (i.removeNth X))
    have e : oneL E a = toL (X i).1 := by rw [hX]
    rw [e] at h
    rw [h, smul_zero]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    have hz : α (j.removeNth X) = 0 := hα.basic _ k (by rw [← hX, ← hk]; rfl)
    rw [hz, map_zero, smul_zero]

theorem UpperTheory.V.Lit.Geo.levGood :
    LevGood := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α hα => ?_, fun w hw => ?_⟩
  · have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, h0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, h0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    exact ⟨w', hw', (corrInv E a ho U Ξ q _ _ hw').1 fun X => (hv X).1, (corrBasic E a U Ξ q _ _ hw').1 hα.basic,
      (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hw')).1 (d_basic U Ξ α hα)⟩
  · obtain ⟨α, hα⟩ := corrBwd E a ho U Ξ q w
    have b := (corrBasic E a U Ξ q _ _ hα).2 hw.basic
    have b' := (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hα)).2 hw.dbasic
    obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hα
    exact ⟨α, hα, c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hα).2 hw.inv X) (c2 X)
      (centralOf E a _ (smLie Ξ) q α b b' X)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtInv
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

private theorem open_stab {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

theorem UpperTheory.V.Lit.Geo.Pf.ptInv :
    UpperTheory.V.Lit.Geo.Pf.PtInv := by
  intro E _ _ _ a χ d G x y
  have h : ∀ g, Pf.pt χ G x y g = ∑ i, ∑ j, G i j *
      (starRingEnd ℂ ((mulChi a χ (cmp i x)).1 g) * (mulChi a χ (cmp j y)).1 g) := by
    intro g
    have hn : ((‖((chiDet a χ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        starRingEnd ℂ ((chiDet a χ g : ℂˣ) : ℂ) * ((chiDet a χ g : ℂˣ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; rfl
    simp only [Pf.pt, hn, mulChi_apply, Pf.cmp_ev, dotProduct, Matrix.mulVec, Finset.mul_sum, map_mul, Pi.star_apply,
      Complex.star_def]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hc : Pf.TwInv χ x → Pf.TwInv χ y → Pf.CInv (Pf.pt χ G x y) := by
    intro hx hy
    rw [show Pf.pt χ G x y = _ from funext h]
    refine Pf.CInv.sum _ fun i => Pf.CInv.sum _ fun j => ⟨?_, fun γ g => ?_, fun t g => ?_⟩
    · exact continuous_const.mul ((Complex.continuous_conj.comp (Pf.invLie E a _ (hx i)).1.cont).mul
        (Pf.invLie E a _ (hy j)).1.cont)
    · rw [(hx i).left, (hy j).left]
    · rw [(hx i).centre, (hy j).centre]
  refine ⟨h, hc, fun θ hθ hx hy => ⟨fun γ g => ?_, fun t g => ?_, ?_⟩⟩
  · rw [hθ, hθ, (hc hx hy).left]
  · rw [hθ, hθ, (hc hx hy).centre]
  · change IsOpen {k | finRep E a k θ = θ}
    have ox : IsOpen (⋂ i, {k | finRep E a k (mulChi a χ (cmp i x)) = mulChi a χ (cmp i x)}) :=
      isOpen_iInter_of_finite fun i => (hx i).level
    have oy : IsOpen (⋂ i, {k | finRep E a k (mulChi a χ (cmp i y)) = mulChi a χ (cmp i y)}) :=
      isOpen_iInter_of_finite fun i => (hy i).level
    refine open_stab (finRep E a) θ (ox.inter oy) ⟨by simp, by simp⟩ ?_
    rintro k ⟨h1, h2⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at h1 h2
    have e : ∀ φ : Sm E a, finRep E a k φ = φ → ∀ g, φ.1 (g * finGL E a k) = φ.1 g := fun φ hφ g =>
      congrFun (congrArg Subtype.val hφ) g
    refine Subtype.ext (funext fun g => ?_)
    change θ.1 (g * finGL E a k) = θ.1 g
    rw [hθ, hθ, h, h]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [e _ (h1 i), e _ (h2 j)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsFlowSz
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

private theorem norm_id_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (j : ℕ) (p : V) :
    ‖iteratedFDeriv ℝ (j + 1) (fun x : V => x) p‖ ≤ 1 := by
  rw [← norm_iteratedFDeriv_fderiv]
  have e : fderiv ℝ (fun x : V => x) = fun _ => ContinuousLinearMap.id ℝ V := by
    funext x
    exact fderiv_id
  rw [e]
  rcases j with _ | j
  · simpa using ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
    simp

theorem UpperTheory.V.Lit.Geo.Cs.flowSz :
    FlowSz := by
  intro V _ _ k c W t p ht hW hS
  have e : UpperTheory.V.Lit.Geo.flow W t = (fun x : V => x) + t • W := rfl
  have h1 : ContDiffAt ℝ ∞ (UpperTheory.V.Lit.Geo.flow W t) p := by
    rw [e]
    exact contDiffAt_id.add (hW.const_smul t)
  have h4 : ∀ i, 1 ≤ i → i ≤ k + 1 → ‖iteratedFDeriv ℝ i (UpperTheory.V.Lit.Geo.flow W t) p‖ ≤ 1 + c := by
    intro i h1i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hWj : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) W p := hW.of_le (by exact_mod_cast le_top)
    have hid : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun x : V => x) p := contDiffAt_id
    have htW : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (t • W) p := hWj.const_smul t
    rw [e, iteratedFDeriv_add_apply hid htW, iteratedFDeriv_const_smul_apply hWj]
    refine (norm_add_le _ _).trans (add_le_add (norm_id_le V j p) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (hS _ hi)
  refine ⟨h1, h1.fderiv_right (by simp), fun i hi => ?_, h4⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact h4 _ (by omega) (by omega)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAltSz
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

private theorem sz_ball {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (hf : ContDiff ℝ ∞ f) (k : ℕ) (c : ℝ) :
    ∃ C : ℝ, ∀ x : X, ‖x‖ ≤ c → Sz k f x C := by
  have hc : Continuous fun x => ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i f x‖ :=
    continuous_finsetSum _ fun i _ => (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : X) c).bddAbove_image hc.continuousOn
  refine ⟨C, fun x hx i hi => ?_⟩
  refine le_trans ?_ (hC ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩)
  exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f x‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

private theorem alt_fin (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q : ℕ) : FiniteDimensional ℝ (V [⋀^Fin q]→L[ℝ] F) := by
  let b := Module.finBasis ℝ V
  let E : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun a k => a fun i => b (k i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective E fun a a' h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact Module.Basis.ext_alternating b fun k _ => congrFun h k

theorem UpperTheory.V.Lit.Geo.Cs.altSz :
    AltSz := by
  intro V F _ _ _ _ _ _ q k c
  have h : ContDiff ℝ ∞ (fun L : V →L[ℝ] V => (ContinuousAlternatingMap.compContinuousLinearMapCLM L :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F))) := by
    haveI := alt_fin V F q
    rw [contDiff_clm_apply_iff]
    intro w
    rw [contDiff_iff_contDiffAt]
    intro L
    refine UpperTheory.V.Lit.Dr.altSmooth _ V F q _ L fun v => ?_
    exact UpperTheory.V.Lit.Dr.applySmooth (V →L[ℝ] V) V F q (fun _ => w) (fun i L => L (v i)) L contDiffAt_const
      fun i => (contDiffAt_id.clm_apply contDiffAt_const)
  exact ⟨h, sz_ball _ h k c⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbNat
open UpperTheory.V.Lit.Geo
open scoped ContDiff

private theorem pbNat_flow {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Set V} (hY : IsOpen Y)
    (ρ : V →L[ℝ] V) {W W' : V → V} (hW : IsField Y W) (hW' : IsField Y W') (hρ : ∀ p ∈ Y, ρ p ∈ Y)
    (he : ∀ p ∈ Y, W' (ρ p) = ρ (W p)) (t : ℝ) {p : V} (hp : p ∈ Y) :
    flow W' t (ρ p) = ρ (flow W t p) ∧ ∀ v, fderiv ℝ (flow W' t) (ρ p) (ρ v) = ρ (fderiv ℝ (flow W t) p v) := by
  have hd : ∀ (U : V → V) (x : V), DifferentiableAt ℝ U x → ∀ v : V,
      fderiv ℝ (flow U t) x v = v + t • fderiv ℝ U x v := by
    intro U x hU v
    have h := (hasFDerivAt_id x).add (hU.hasFDerivAt.const_smul t)
    have hfl : flow U t = id + t • U := by
      funext y
      simp [flow]
    rw [hfl, h.fderiv]
    simp
  constructor
  · simp only [flow]
    rw [he p hp]
    simp [map_add (f := _), map_smul]
  · intro v
    have hWd : DifferentiableAt ℝ W p :=
      (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
    have hW'd : DifferentiableAt ℝ W' (ρ p) :=
      (hW'.1.contDiffAt (hY.mem_nhds (hρ p hp))).differentiableAt (by simp)
    have heq : (fun x => W' (ρ x)) =ᶠ[nhds p] (fun x => ρ (W x)) := by
      filter_upwards [hY.mem_nhds hp] with x hx using he x hx
    have hder : fderiv ℝ W' (ρ p) (ρ v) = ρ (fderiv ℝ W p v) := by
      have h1 := heq.fderiv_eq (𝕜 := ℝ)
      have c1 : fderiv ℝ (fun x => W' (ρ x)) p = (fderiv ℝ W' (ρ p)).comp ρ :=
        (hW'd.hasFDerivAt.comp p ρ.hasFDerivAt).fderiv
      have c2 : fderiv ℝ (fun x => ρ (W x)) p = ρ.comp (fderiv ℝ W p) :=
        (ρ.hasFDerivAt.comp p hWd.hasFDerivAt).fderiv
      have h3 := congrArg (fun L => L v) (c1.symm.trans (h1.trans c2))
      simpa using h3
    rw [hd W' (ρ p) hW'd, hd W p hWd, hder]
    simp [map_add (f := _), map_smul]

theorem UpperTheory.V.Lit.Geo.pbNat :
    PbNat := by
  unfold PbNat
  intro V F _ _ _ _ _ _ Y hY ρ A W W' hW hW' hρ he q
  constructor
  · intro w w' hww t ht p hp v
    obtain ⟨h1, h2⟩ := pbNat_flow hY ρ hW hW' hρ he t hp
    rw [pb_apply, pb_apply, h1]
    simp only [h2]
    exact hww _ (hW.2 p hp t ht) _
  · intro w w' hww
    have hb1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Y, ∀ v : Fin q → V,
        (hk W' t w' (ρ p)) (fun i => ρ (v i)) = A ((hk W t w p) v) := by
      intro t ht p hp v
      obtain ⟨h1, h2⟩ := pbNat_flow hY ρ hW hW' hρ he t hp
      rw [hk_apply, hk_apply, h1, he p hp]
      simp only [h2]
      convert hww (flow W t p) (hW.2 p hp t ht)
        (Matrix.vecCons (W p) fun i => fderiv ℝ (flow W t) p (v i)) using 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    refine ⟨hb1, fun hwc hw'c p hp v => ?_⟩
    have hk1 := (hkSmooth V F Y hY W hW q w hwc).2.2.1 p hp
    have hk2 := (hkSmooth V F Y hY W' hW' q w' hw'c).2.2.1 (ρ p) (hρ p hp)
    have i1 : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact hk1
    have i2 : IntervalIntegrable (fun t => hk W' t w' (ρ p)) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact hk2
    have i3 : IntervalIntegrable (fun t => (hk W t w p) v) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (ContinuousAlternatingMap.apply ℝ V F v).continuous.comp_continuousOn hk1
    have e1 : (∫ t in (0 : ℝ)..1, hk W' t w' (ρ p)) (fun i => ρ (v i)) =
        ∫ t in (0 : ℝ)..1, (hk W' t w' (ρ p)) (fun i => ρ (v i)) :=
      ((ContinuousAlternatingMap.apply ℝ V F (fun i => ρ (v i))).intervalIntegral_comp_comm i2).symm
    have e2 : (∫ t in (0 : ℝ)..1, hk W t w p) v = ∫ t in (0 : ℝ)..1, (hk W t w p) v :=
      ((ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm i1).symm
    unfold hom
    rw [e1, e2, ← A.intervalIntegral_comp_comm i3]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hb1 t ht p hp v
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsSecOne
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem sub_smooth {f : X → HV E a} {x : X} (h : ContDiffAt ℝ ∞ (fun y => (f y).1) x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨r, hr⟩ := (HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1 :=
    funext fun y => (LinearMap.congr_fun hr (f y)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h

private theorem inv_smooth {τ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ContDiffAt ℝ ∞ (fun y => toL (τ y).val) x) (i j : Fin a) :
    ContDiffAt ℝ ∞ (fun y => (τ y)⁻¹.val i j) x := by
  have hd : ContDiffAt ℝ ∞ (fun y => (τ y).val.det) x := (contDiff_det (E := E) (a := a)).contDiffAt.comp x h
  have hu : IsUnit (τ x).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (τ x).isUnit
  have hi : ContDiffAt ℝ ∞ (fun y => Ring.inverse (τ y).val.det) x := by
    have := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
    rw [hu.unit_spec] at this
    exact this.comp x hd
  have ha : ContDiffAt ℝ ∞ (fun y => (τ y).val.adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    refine (contDiff_det (E := E) (a := a)).contDiffAt.comp x
      (f := fun y => toL ((τ y).val.updateRow j (Pi.single i 1))) ?_
    refine contDiffAt_pi.2 fun k => ?_
    by_cases hk : k = j
    · subst hk
      have : (fun y => toL ((τ y).val.updateRow k (Pi.single i 1)) k) = fun _ => Pi.single i 1 :=
        funext fun y => Matrix.updateRow_self
      rw [this]; exact contDiffAt_const
    · have : (fun y => toL ((τ y).val.updateRow j (Pi.single i 1)) k) = fun y => toL (τ y).val k :=
        funext fun y => Matrix.updateRow_ne hk
      rw [this]; exact contDiffAt_pi.1 h k
  have e : (fun y => (τ y)⁻¹.val i j) = fun y => Ring.inverse (τ y).val.det * (τ y).val.adjugate i j := by
    funext y
    rw [Matrix.coe_units_inv, Matrix.inv_def]; rfl
  rw [e]
  exact hi.mul ha

private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (v : HV E a) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) v) x := by
  refine sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)
  have e : (fun y => (sand (σ y) v).1 i j) =
      fun y => ∑ l, (∑ k, (σ y).val i k * v.1 k l) * star ((σ y).val j l) := by
    funext y
    change ((σ y).val * Matrix.of v.1 * star (σ y).val) i j = _
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul contDiffAt_const).mul ?_
  exact (starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)

private theorem clm_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {f : X → V →L[ℝ] V} {x : X} (h : ∀ v, ContDiffAt ℝ ∞ (fun y => f y v) x) : ContDiffAt ℝ ∞ f x := by
  let e₁ : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := .ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ := (e₁.arrowCongr (1 : V ≃L[ℝ] V)).trans (ContinuousLinearEquiv.piRing (Fin (Module.finrank ℝ V)))
  have e : f = fun y => e₂.symm (e₂ (f y)) := funext fun y => (e₂.symm_apply_apply _).symm
  rw [e]
  exact e₂.symm.contDiff.contDiffAt.comp x (contDiffAt_pi.2 fun i => h _)

end UpperTheory.V.Lit.Geo.Cs

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.secOne :
    SecOne := by
  intro E _ _ a
  obtain ⟨σ, hσ, hs⟩ := locSec E a (hOne E a) hOne_mem_cone
  set k := σ (hOne E a) with hk
  have hk1 : sand k⁻¹ (hOne E a) = hOne E a := by
    have h0 : sand k (hOne E a) = hOne E a := hs.self_of_nhds
    conv_lhs => rw [← h0]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have h1 : ∀ i j, ContDiffAt ℝ ∞ (fun p => (σ p * k⁻¹).val i j) (hOne E a) := fun i j => by
    simp only [Units.val_mul, Matrix.mul_apply]
    exact ContDiffAt.sum fun l _ => (contDiffAt_pi.1 (contDiffAt_pi.1 hσ i) l).mul contDiffAt_const
  have h2 : ContDiffAt ℝ ∞ (fun p => toL (σ p * k⁻¹).val) (hOne E a) :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h1 i j
  have h3 := inv_smooth (τ := fun p => σ p * k⁻¹) h2
  refine ⟨fun p => σ p * k⁻¹, mul_inv_cancel k, h2,
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h3 i j, ?_, ?_, ?_⟩
  · exact clm_smooth fun v => sand_smooth h1 v
  · exact clm_smooth fun v => sand_smooth (σ := fun p => (σ p * k⁻¹)⁻¹) h3 v
  · filter_upwards [hs] with p hp
    rw [map_mul, ContinuousLinearMap.mul_apply, hk1, hp]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BdBasis
open UpperTheory.V.Lit.Geo

private theorem absBd {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : W ≃ₗ[ℝ] V) (q : ℕ) :
    ∃ (T : Finset (Fin q → W)) (B : ℝ), 0 ≤ B ∧ ∀ (m : (Fin q → W) →ₘₗ[ℝ] F) (M : ℝ), 0 ≤ M →
      (∀ X ∈ T, ‖m X‖ ≤ M) → ∀ X, ‖m X‖ ≤ B * M * ∏ i, ‖e (X i)‖ := by
  classical
  let b := Module.finBasis ℝ V
  let c : Fin (Module.finrank ℝ V) → (V →L[ℝ] ℝ) := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  refine ⟨Finset.univ.image fun I : Fin q → Fin (Module.finrank ℝ V) => fun i => e.symm (b (I i)),
    ∑ I : Fin q → Fin (Module.finrank ℝ V), ∏ i, ‖c (I i)‖, by positivity, fun m M hM hT X => ?_⟩
  have hX : X = fun i => ∑ j, c j (e (X i)) • e.symm (b j) := by
    funext i
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    exact (b.sum_repr _).symm
  have h1 : m X = ∑ I : Fin q → Fin (Module.finrank ℝ V),
      (∏ i, c (I i) (e (X i))) • m fun i => e.symm (b (I i)) := by
    conv_lhs => rw [hX]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [m.map_sum]
    exact Finset.sum_congr rfl fun I _ => m.map_smul_univ _ _
  rw [h1, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  rw [norm_smul, norm_prod, mul_right_comm, ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => (c (I i)).le_opNorm _)
    (hT _ (Finset.mem_image_of_mem _ (Finset.mem_univ I))) (norm_nonneg _) (by positivity)

theorem UpperTheory.V.Lit.Geo.bdBasis :
    BdBasis := by
  intro E _ _ _ a Ξ q
  obtain ⟨T, B, hB, h⟩ := absBd (F := Fin Ξ.d → ℂ) (UpperTheory.V.Lit.Dr.hv (E := E) (a := a)) q
  refine ⟨T, B, hB, fun α g M hM hT X => ?_⟩
  exact h ((((LinearMap.proj _).comp UpperTheory.V.Lit.Dr.ev).restrictScalars ℝ).compMultilinearMap α.toMultilinearMap) M hM hT X
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsTens
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem cmp_lT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, smul_smul, ← Finset.sum_smul]
    rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]


variable (E a) in
private def csSub : Submodule ℂ (Sm E a) where
  carrier := {φ | Pf.Cs φ.1}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := by
    rintro φ ψ ⟨R, hR⟩ ⟨S, hS⟩
    refine ⟨max R S, fun g hg => ?_⟩
    have h1 := hR g (lt_of_le_of_lt (le_max_left _ _) hg)
    have h2 := hS g (lt_of_le_of_lt (le_max_right _ _) hg)
    show φ.1 g + ψ.1 g = 0
    rw [h1, h2, add_zero]
  smul_mem' := by
    rintro c φ ⟨R, hR⟩
    refine ⟨R, fun g hg => ?_⟩
    show c • φ.1 g = 0
    rw [hR g hg, smul_zero]

private theorem cs_iff {d : ℕ} (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Pf.Cs (ev x) ↔ x ∈ tens d (csSub E a) := by
  rw [mem_tens]
  constructor
  · rintro ⟨R, hR⟩ j
    exact ⟨R, fun g hg => by rw [Pf.cmp_ev, hR g hg]; rfl⟩
  · intro h
    choose R hR using h
    refine ⟨∑ j, |R j|, fun g hg => funext fun j => ?_⟩
    rw [← Pf.cmp_ev]
    refine hR j g (lt_of_le_of_lt ?_ hg)
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |R j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j))

end

theorem UpperTheory.V.Lit.Geo.Pf.csTens :
    UpperTheory.V.Lit.Geo.Pf.CsTens := by
  intro E _ _ _ a Ξ r X x hx
  rw [cs_iff] at hx
  rw [cs_iff, cs_iff]
  have hA : smA Ξ X x ∈ tens Ξ.d (csSub E a) := mem_tens.2 fun j => by
    rw [smA_apply, cmp_rT]
    exact Pf.csLie E a _ X (mem_tens.1 hx j)
  have hB : smB Ξ X x ∈ tens Ξ.d (csSub E a) := mem_tens.2 fun j => by
    rw [smB_apply, cmp_lT]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (mem_tens.1 hx k)
  constructor
  · have : smLie Ξ X x = smA Ξ X x + smB Ξ X x := by
      simp only [smB, LinearMap.sub_apply, add_sub_cancel]
    rw [this]
    exact Submodule.add_mem _ hA hB
  · rw [smAdj, adj_apply]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hB hA) ?_
    exact Submodule.smul_of_tower_mem _ _ hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldBd
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def pol0 (A B : Matrix (Fin a) (Fin a) (Cinf E)) : HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨toL (A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A), by
        have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
        change star (A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A) =
          A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A
        simp only [star_add, star_mul, star_star, hv, mul_assoc]
        exact add_comm _ _⟩
      map_add' := fun p p' => Subtype.ext (by
        change A * (Matrix.of p.1 + Matrix.of p'.1) * star B + B * (Matrix.of p.1 + Matrix.of p'.1) * star A =
          (A * Matrix.of p.1 * star B + B * Matrix.of p.1 * star A) +
            (A * Matrix.of p'.1 * star B + B * Matrix.of p'.1 * star A)
        simp only [mul_add, add_mul]; abel)
      map_smul' := fun c p => Subtype.ext (by
        change A * (c • Matrix.of p.1) * star B + B * (c • Matrix.of p.1) * star A =
          c • (A * Matrix.of p.1 * star B + B * Matrix.of p.1 * star A)
        simp only [mul_smul_comm, smul_mul_assoc, smul_add]) }

private theorem polarization_val (A B : Matrix (Fin a) (Fin a) (Cinf E)) (v : HV E a) :
    Matrix.of (pol0 A B v).1 = A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A := rfl

private theorem hv_ext {v w : HV E a} (h : Matrix.of v.1 = Matrix.of w.1) : v = w := Subtype.ext h

private theorem polarization_comm (A B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 A B = pol0 B A :=
  ContinuousLinearMap.ext fun v => hv_ext (by rw [polarization_val, polarization_val, add_comm])

private theorem polarization_add (A A' B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 (A + A') B = pol0 A B + pol0 A' B :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change _ = Matrix.of (pol0 A B v).1 + Matrix.of (pol0 A' B v).1
    simp only [polarization_val, star_add, mul_add, add_mul]; abel)

private theorem polarization_smul (c : ℝ) (A B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 (c • A) B = c • pol0 A B :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change _ = c • Matrix.of (pol0 A B v).1
    simp only [polarization_val, star_smul, star_trivial c, mul_smul_comm, smul_mul_assoc, smul_add])


variable (E a) in
private def pol : Lie E a →L[ℝ] Lie E a →L[ℝ] HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    LinearMap.mk₂ ℝ (fun A B : Lie E a => pol0 (Matrix.of A) (Matrix.of B)) (fun A A' B => polarization_add _ _ _)
      (fun c A B => polarization_smul c _ _)
      (fun A B B' => (polarization_comm _ _).trans ((polarization_add _ _ _).trans (congrArg₂ (· + ·) (polarization_comm _ _) (polarization_comm _ _))))
      (fun c A B => (polarization_comm _ _).trans ((polarization_smul c _ _).trans (congrArg (c • ·) (polarization_comm _ _)))))

private theorem pol_sand (g : GL (Fin a) (Cinf E)) :
    sand g = (2⁻¹ : ℝ) • pol E a (toL g.val) (toL g.val) :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change g.val * Matrix.of v.1 * star g.val =
      (2⁻¹ : ℝ) • (g.val * Matrix.of v.1 * star g.val + g.val * Matrix.of v.1 * star g.val)
    rw [← two_smul ℝ, smul_smul]; norm_num)

private theorem sand_der (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hX : HasDerivAt (fun t => toL (c t).val) X 0) :
    HasDerivAt (fun t => sand (c t)) (pol E a X (toL 1)) 0 := by
  have h1 := (((pol E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hX).clm_apply hX).const_smul (2⁻¹ : ℝ)
  simp only [Function.comp, h0, Units.val_one] at h1
  have e : pol E a (toL 1) X = pol E a X (toL 1) := polarization_comm _ _
  rw [e, ← two_smul ℝ, smul_smul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, one_smul] at h1
  exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => pol_sand _)

private theorem pol_one (v : HV E a) : pol E a ((2⁻¹ : ℝ) • v.1) (toL 1) (hOne E a) = v := by
  rw [map_smul]
  refine hv_ext ?_
  have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
  change (2⁻¹ : ℝ) • (Matrix.of v.1 * 1 * star 1 + 1 * 1 * star (Matrix.of v.1)) = _
  rw [hv, star_one, mul_one, mul_one, one_mul, one_mul, ← two_smul ℝ, smul_smul]; norm_num

private theorem flow_der {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : V → V} {p : V}
    (h : DifferentiableAt ℝ W p) (t : ℝ) (v : V) : fderiv ℝ (flow W t) p v = v + t • fderiv ℝ W p v := by
  have h4 : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p :=
    (hasFDerivAt_id p).add (h.hasFDerivAt.const_smul t)
  rw [h4.fderiv]
  rfl

theorem fieldBd : FieldBd := by
  intro E _ _ _ a U Y C hY W hW
  obtain ⟨B, hB, hD⟩ := fieldDer E a U Y C hY
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  set K : ℝ := ‖(pol E a).flip (toL 1)‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨1 + (K * B + B), by positivity, fun g x t ht v => ?_⟩
  obtain ⟨c, h0, -, -, hX, -⟩ := oneParam E a ((2⁻¹ : ℝ) • v.1)
  obtain ⟨hb, hz⟩ := hD (infGL E a g * finGL E a x)
  obtain ⟨Z, hZ, hd⟩ := hz c _ h0 hX
  have hn : ‖(2⁻¹ : ℝ) • v.1‖ ≤ ‖v‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  have hs := sand_der c _ h0 hX
  set P := pol E a ((2⁻¹ : ℝ) • v.1) (toL 1) with hP
  set y := hv (Y (infGL E a g * finGL E a x)) with hy
  have hPn : ‖P‖ ≤ K * ‖v‖ :=
    (((pol E a).flip (toL 1)).le_opNorm _).trans (mul_le_mul_of_nonneg_left hn hK0)
  have hWd : DifferentiableAt ℝ (W (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) :=
    ((fieldSm E a U Y C hY W hW x).contDiffAt (ho.mem_nhds ⟨g, rfl⟩)).differentiableAt (by simp)
  have h1 : HasDerivAt (fun r => sand g (sand (c r) (hOne E a))) (sand g v) 0 := by
    have h := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hs.clm_apply (hasDerivAt_const (0 : ℝ) (hOne E a)))
    rwa [map_zero, add_zero, hP, pol_one] at h
  have h2 : HasDerivAt (fun r => W (x : GL (Fin a) (Af E) ⧸ U) (sand g (sand (c r) (hOne E a)))) (sand g (P y + Z)) 0 := by
    have h := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hs.clm_apply hd)
    simp only [h0, map_one, mul_one, ContinuousLinearMap.one_apply] at h
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    have e : infGL E a (g * c r) * finGL E a x = infGL E a g * finGL E a x * infGL E a (c r) := by
      rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
    have e2 := hW (g * c r) x
    rw [e, map_mul] at e2
    exact e2
  have h3 : fderiv ℝ (W (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) (sand g v) = sand g (P y + Z) :=
    (hWd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [h0, map_one]; rfl)).unique h2
  refine ⟨v + t • (P y + Z), ?_, ?_⟩
  · have h4 : ‖P y‖ ≤ K * ‖v‖ * B :=
      (P.le_opNorm y).trans (mul_le_mul hPn hb (norm_nonneg _) (by positivity))
    have h5 : ‖Z‖ ≤ B * ‖v‖ := hZ.trans (mul_le_mul_of_nonneg_left hn hB)
    have h6 : ‖t • (P y + Z)‖ ≤ ‖P y‖ + ‖Z‖ := by
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (norm_add_le _ _)
    have h7 := norm_add_le v (t • (P y + Z))
    nlinarith
  · rw [flow_der hWd, h3, map_add (sand g) v, map_smul]

end UpperTheory.V.Lit.Geo
end
end
