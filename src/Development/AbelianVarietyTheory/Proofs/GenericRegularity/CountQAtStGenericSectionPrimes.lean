module

public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
public import Formalism.LocalToGlobal.ProjectiveLattices.GenSectT

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimes
namespace GlobalTheory.SecCount

open MvPolynomial

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ)


variable {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem mem_one (k : Fin N) : emb X la N (X.inc wL (w k)) ∈ Vw X la N (addL (wt0 D j) wL 1) := by
  rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k)

theorem sfr_eq_sum (i : Fin (WeightFamilies.dimY D j + 1)) :
    sfr X la w i = ∑ k, algebraMap (Kp X la N) ↥(Frac0 X la w) (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) *
      CurveLoc.fr0 X la N w 1 (X.inc wL (w k)) (mem_one X la N w k) := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_sfr, Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, ← Algebra.smul_def]
  rfl

theorem sfr_zero : sfr X la w 0 = 1 := by
  apply Subtype.ext
  rw [coe_sfr, frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl



set_option maxHeartbeats 1000000 in
theorem countQAt_of_trdeg_le {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (htr : Algebra.trdeg B.KO Ω ≤ WeightFamilies.dimY D j) : CurveLoc.CountQAt X la N w gF := by
  by_cases h0 : ∃ a, gF (X.inc wL (w a)) ≠ 0
  · obtain ⟨a, ha⟩ := h0
    exact CurveLoc.countQAt_of X la N w gF (fun i => gF (X.inc wL (w i))) (fun _ => rfl)
      ⟨a, ha, (trdeg_le_of_injective (IntermediateField.val _) Subtype.val_injective).trans htr⟩
  · intro 𝔮 h𝔮 _ hK
    exfalso
    push Not at h0
    refine h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← sfr_zero X la N w, sfr_eq_sum X la N w 0]
    refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hK ?_)
    rw [RingHom.mem_ker, CurveLoc.phiZ_fraction_base, h0, map_zero, zero_mul]

end Rec



set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem countQAtSt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), CountQAtSt h j hj hG hT := by
  intro D T h j hj hG hT ka wL wF G S g0 la _ Z
  exact countQAt_of_trdeg_le (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    ((GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2 Z).le

end GlobalTheory.SecCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countQAtSt_generic_section_primes : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), CountQAtSt h j hj hG hT := by
  first | exact @GlobalTheory.SecCount.countQAtSt | exact GlobalTheory.SecCount.countQAtSt | (intros; apply GlobalTheory.SecCount.countQAtSt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveModelExistsAllPrimesAllPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FiniteReducedSection
noncomputable section

namespace GlobalTheory.CurveRecord

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

theorem finite_reduced_of_eq {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
    [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K'] [CharZero K] {Dd m : ℕ}
    (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = Dd)
    (v : Fin m → Ω) (k₀ : Fin m) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v k₀)) = Dd)
    (t : Fin (Dd + 1) × Fin m → K') (ht : AlgebraicIndependent K t)
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    FiniteDimensional K' (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) ∧
      IsReduced (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) := by
  have e : a = GenSect.tsec K Kl t v := funext fun i => ha i
  subst e
  have := GenSect.s1T (Kl := Kl) hfg htr v k₀ hv₀ hbig t ht
  unfold GenSect.tJ at this
  exact this


set_option maxHeartbeats 1000000 in
theorem tv_indep {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) [Algebra B.KO (Kp X la N)]
    [IsScalarTower B.KO (X.Kl la) (Kp X la N)] :
    AlgebraicIndependent B.KO (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have h0 := (MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)).map' hinj
  have h1 := h0.map' (f := IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N))
    (IsFractionRing.injective (Op X la N) (Kp X la N))
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic _ (nonZeroDivisors (X.Ol la))
  have h2 := (Algebra.IsAlgebraic.algebraicIndependent_iff (X.Ol la) (X.Kl la)).mp h1
  have h3 := h2.restrictScalars (R := B.KO) (algebraMap B.KO (X.Kl la)).injective
  have hfun : (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) =
      ⇑(IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)) ∘
        (⇑(IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) ∘ MvPolynomial.X) := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, Tv]
  rw [hfun]
  exact h3

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem rzMap_sec_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem map_Jid_eq : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

theorem finite_reduced_record
    (hfg : (⊤ : IntermediateField B.KO Ω).FG) (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j)
    (v : Fin N → Ω) (hv : ∀ k, gF (X.inc wL (w k)) = v k) (k₀ : Fin N) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun k => v k / v k₀)) =
      WeightFamilies.dimY D j) :
    FiniteDimensional (Kp X la N) (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) ∧
      IsReduced (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) := by
  let iK : Algebra B.KO (Kp X la N) :=
    ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  have : IsScalarTower B.KO (X.Kl la) (Kp X la N) := IsScalarTower.of_algebraMap_eq' rfl
  rw [map_Jid_eq]
  exact finite_reduced_of_eq hfg htr v k₀ hv₀ hbig _ (tv_indep X la N)
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i)) (fun i => by rw [rzMap_sec_eq]; simp only [hv])

end Rec

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem finite_reduced_section (hfg : FnFG (T.Q.Xo j) T.Q.c) (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) := by
  intro ka wL wF G S g0 la hH Z
  obtain ⟨-, ⟨-, hB2⟩, -, -⟩ := hH
  obtain ⟨k₀, hk₀, htrZ⟩ := hB2 Z
  exact finite_reduced_record (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w (hfg Z) (htr Z)
    (fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun k => formsEvR_single j hG hT Z _ _) k₀ hk₀ htrZ

end GlobalTheory.CurveRecord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveModelExistsAllPrimesAllPoints
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CurveRecord

theorem ev_ne_zero_of_nonZeroComp {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    {wF wL : WeightFamilies.Wt D j} (g0 : B.Cusp j wF) (hg : X.NonZeroComp wF g0) (Z : ι) (g : B.Cusp j wL)
    (h1 : gF Z (X.inc wL g) ≠ 0) (h2 : ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0) : gF Z (X.inc wF g0) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul wF wL g0 g
  have hz : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases e : Z' = Z
    · subst e
      rw [h0, zero_mul]
    · rw [h2 Z' e, mul_zero]
  have hg0 : g = 0 := hg wL g (by rw [hH, hz, map_zero])
  exact h1 (by rw [hg0, map_zero, map_zero])

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)


include hT in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem evC_ne_zero (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) (g0 : (recB h.toLawsCore).Cusp j wF)
    (hg : (recPlus h j hj).NonZeroComp wF g0) (Z : Comp (T.Q.Xo j) T.Q.c) :
    evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0 := by
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, h1, h2⟩ := split_of h j hj hG hT hC G Z k
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z)
    (fun u F hF => hV u F fun Z => (formsEvR_inc h j hj hG hT Z u F).symm.trans (hF Z)) g0 hg Z g
    (fun h0 => hk ((formsEvR_inc h j hj hG hT Z wL (G.w k)).symm.trans (h1.symm.trans h0))) h2
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z wF g0).trans h0)

end Inst


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem curveInst : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), GenValInjSt h j hG → CompSplitSt h j hG → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → CurveInstSt h j hj := by
  intro D T h j hj hG hT hV hC hB
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  letI : Fintype (Comp (T.Q.Xo j) T.Q.c) := Fintype.ofFinite _
  obtain ⟨hfg, htr⟩ := GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj
  have hQ := countQAtSt_holds h j hj hG hT
  have hinj : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ f : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Z, phiI h j hj hG hT la G Z f = 0) → f = 0 :=
    fun ka wL wF G S g0 la _ f hf => curveInj h j hj hG hT hV G la f hf
  have hone := hone_of h j hj hG hT hC
  have hloc : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a := by
    intro ka wL wF G S g0 la hH Z r
    exact CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
      (birAt_of h j hj hG hT G (hB ka wL wF G hH.2.1) Z) (hQ ka wL wF G S g0 la hH Z) r
  have hS1 := finite_reduced_section h j hj hG hT hfg htr
  refine curveInst_of h j hj hG hT hinj hone hloc hS1 ?_ ?_
  · intro ka wL wF G S g0 la hH e w' θ hw hθ
    have h1 := LocalUnitReduction.finRed (Kp (recPlus h j hj) la G.N) ↥(Frac0 (recPlus h j hj) la G.w)
      (Jid (recPlus h j hj) la G.w) (Comp (T.Q.Xo j) T.Q.c)
      (fun Z => RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (fun Z => phiI h j hj hG hT la G Z) (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
      (hloc _ _ _ G S g0 la hH) (hS1 _ _ _ G S g0 la hH)
    exact unit_ideal_cusp_form_record h j hj hG hT G la g0 θ hw (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
      (hloc _ _ _ G S g0 la hH) h1.1 (evC_ne_zero h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2) hθ
  · intro ka wL wF G S g0 la hH
    exact nonzero_divisor_cusp_form_record h j hj hG hT G la g0 (hinj _ _ _ G S g0 la hH)
      (evC_ne_zero h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2)

end GlobalTheory.CurveRecord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveModelExistsAllPrimesAllPointsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveModel_exists_all_primes_allPoints : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), GenValInjSt h j hG → CompSplitSt h j hG → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → CurveInstSt h j hj := by
  exact GlobalTheory.CurveRecord.curveInst
end
end
