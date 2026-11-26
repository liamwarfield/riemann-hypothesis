module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.DdSNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalTheoryWindows

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Stage1OfUnipotentIntegralIsGroup
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.HTIntLeft
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CommonMult
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichESymmApply
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unimod_int (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {x v : (VS D).V} (hx : x ∈ Λ) (hv : v ∈ Λ) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT x v := by
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
  have hv' : v ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU']; exact hv
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hv'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hv' x hx)
  exact ⟨o, ho⟩

theorem smul_int_mem (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {k : D.host.E}
    (hk : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = k) {v : (VS D).V} (hv : v ∈ Λ) : k • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := hk
  rw [algebraMap_smul]
  exact Λ.smul_mem o hv

theorem eich_conds (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) {y0 : (VS D).V} (hy : InW D y0) :
    (VS D).hT (D.sp.hypE a) (D.sp.hypE a) = 0 ∧ (VS D).hT (D.sp.hypE a) ((2 : D.host.E) • y0) = 0 ∧
    (VS D).hT ((2 : D.host.E) • y0) (D.sp.hypE a) = 0 ∧
    (-2 * (VS D).hT y0 y0) + (-2 * (VS D).hT y0 y0) + (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 0 ∧
    (-2 * (VS D).hT y0 y0) + star (-2 * (VS D).hT y0 y0) +
      (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 0 := by
  have hh : star ((VS D).hT y0 y0) = (VS D).hT y0 y0 := (VS D).herm.eq y0 y0
  have h22 : (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 4 * (VS D).hT y0 y0 := by
    rw [LinearMap.map_smulₛₗ₂, map_smul, map_ofNat, smul_eq_mul, smul_eq_mul]
    ring
  refine ⟨D.sp.hyp_ee a a, ?_, ?_, ?_, ?_⟩
  · rw [map_smul, hy.1 a, smul_zero]
  · rw [LinearMap.map_smulₛₗ₂, ← (VS D).herm.eq (D.sp.hypE a) y0, hy.1 a, map_zero, smul_zero]
  · rw [h22]
    ring
  · have hs2 : star (-2 : D.host.E) = -2 := by simp
    rw [h22, star_mul', hs2, hh]
    ring

theorem eich_conds_neg (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) {y0 : (VS D).V} (hy : InW D y0) :
    (VS D).hT (D.sp.hypE a) (-((2 : D.host.E) • y0)) = 0 ∧
    (VS D).hT (-((2 : D.host.E) • y0)) (D.sp.hypE a) = 0 ∧
    (-2 * (VS D).hT y0 y0) + (-2 * (VS D).hT y0 y0) +
      (VS D).hT (-((2 : D.host.E) • y0)) (-((2 : D.host.E) • y0)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_neg, map_smul, hy.1 a, smul_zero, neg_zero]
  · rw [map_neg, LinearMap.neg_apply, LinearMap.map_smulₛₗ₂, ← (VS D).herm.eq (D.sp.hypE a) y0, hy.1 a,
      map_zero, smul_zero, neg_zero]
  · rw [map_neg, map_neg, LinearMap.neg_apply, neg_neg, LinearMap.map_smulₛₗ₂, map_smul, map_ofNat,
      smul_eq_mul, smul_eq_mul]
    ring

def eichE (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) :
    (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (eichL D (D.sp.hypE a) ((2 : D.host.E) • y0) (-2 * (VS D).hT y0 y0))
    (eichL D (D.sp.hypE a) (-((2 : D.host.E) • y0)) (-2 * (VS D).hT y0 y0))
    (LinearMap.ext fun v => by
      obtain ⟨he, -, -, -, -⟩ := eich_conds D a hy
      obtain ⟨n2, n3, n4⟩ := eich_conds_neg D a hy
      have := eich_inv D he n2 n3 n4 v
      rw [neg_neg] at this
      exact this)
    (LinearMap.ext fun v => by
      obtain ⟨he, h2, h3, h4, -⟩ := eich_conds D a hy
      exact eich_inv D he h2 h3 h4 v)

theorem eichE_apply (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    eichE D a y0 hy v = eichL D (D.sp.hypE a) ((2 : D.host.E) • y0) (-2 * (VS D).hT y0 y0) v := rfl

theorem eichE_symm_apply (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    (eichE D a y0 hy).symm v = eichL D (D.sp.hypE a) (-((2 : D.host.E) • y0)) (-2 * (VS D).hT y0 y0) v := rfl

theorem eichL_lat (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {e y : (VS D).V} {c : D.host.E} (he : e ∈ Λ) (hy : y ∈ Λ)
    (hc : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = c) {v : (VS D).V} (hv : v ∈ Λ) :
    eichL D e y c v ∈ Λ := by
  simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply]
  exact Λ.add_mem (Λ.sub_mem (Λ.add_mem hv (smul_int_mem D (unimod_int D hU he hv) hy))
    (smul_int_mem D (unimod_int D hU hy hv) he)) (smul_int_mem D hc (smul_int_mem D (unimod_int D hU he hv) he))

theorem eichE_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (a : Fin D.R.rS) {y0 : (VS D).V}
    (hy : InW D y0) (hyΛ : y0 ∈ Λ) : eichE D a y0 hy ∈ N0 F0 Λ := by
  have hFe : F0.e = D.sp.hypE := hF.2.2.1
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hF.2.1
  have hea : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hFe] at h1
  obtain ⟨he, h2, h3, -, h5⟩ := eich_conds D a hy
  have hy2 : (2 : D.host.E) • y0 ∈ Λ := smul_int_mem D (k := (2 : D.host.E)) ⟨2, map_ofNat _ 2⟩ hyΛ
  have hc : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = -2 * (VS D).hT y0 y0 := by
    obtain ⟨o, ho⟩ := unimod_int D hU hyΛ hyΛ
    exact ⟨-2 * o, by rw [map_mul, ho, map_neg, map_ofNat]⟩
  have hP : ∀ x ∈ Submodule.span D.host.E (Set.range D.sp.hypE),
      (∀ b, (VS D).hT (D.sp.hypE b) x = 0) ∧ (VS D).hT y0 x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨fun b => D.sp.hyp_ee b c, by rw [← (VS D).herm.eq (D.sp.hypE c) y0, hy.1 c, map_zero]⟩
    | zero => simp
    | add x z _ _ hx hz => exact ⟨fun b => by rw [map_add (f := _), hx.1 b, hz.1 b, add_zero], by
        rw [map_add (f := _), hx.2, hz.2, add_zero]⟩
    | smul c x _ hx => exact ⟨fun b => by rw [map_smul, hx.1 b, smul_zero], by
        rw [map_smul, hx.2, smul_zero]⟩
  have hspan : ∀ x ∈ Submodule.span D.host.E (Set.range D.sp.hypE), eichE D a y0 hy x = x := by
    intro x hx
    obtain ⟨h1, h2'⟩ := hP x hx
    rw [eichE_apply]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.map_smulₛₗ₂, h1 a, h2', smul_zero, zero_smul, add_zero, sub_zero]
  have hzm : ∀ a', (VS D).hT (D.sp.hypE a') D.sp.zm = 0 := fun a' => by
    rw [← (VS D).herm.eq D.sp.zm (D.sp.hypE a'), (D.sp.hyp_orthz a').1, map_zero]
  have hy0z : (VS D).hT y0 D.sp.zm = 0 := by
    rw [← (VS D).herm.eq D.sp.zm y0, hy.2.2, map_zero]
  simp only [N0, NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro u v
    exact eich_isom D he h2 h3 h5 u v
  · apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr fun v hv => eichL_lat D hU hea hy2 hc hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨(eichE D a y0 hy).symm v, ?_, (eichE D a y0 hy).apply_symm_apply v⟩
      rw [eichE_symm_apply]
      exact eichL_lat D hU hea (Λ.neg_mem hy2) hc hv
  · intro j x hx
    have hx' : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
      rw [← hFe]
      exact Submodule.span_mono (Set.image_subset_range _ _) hx
    rw [hspan x hx', sub_self]
    exact Submodule.zero_mem _
  · intro x hx
    have hex : (VS D).hT (D.sp.hypE a) x = 0 := by
      have h1 : x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range F0.e)) := hx
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker] at h1
      exact h1 _ (by rw [hFe]; exact Submodule.subset_span ⟨a, rfl⟩)
    show (eichE D a y0 hy) x - x ∈ Submodule.span D.host.E (Set.range F0.e)
    rw [eichE_apply, hFe]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, hex, zero_smul, add_zero, smul_zero, add_sub_cancel_left, zero_sub]
    rw [sub_sub_cancel_left]
    apply Submodule.neg_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro b
    rw [hFe]
    exact hspan _ (Submodule.subset_span ⟨b, rfl⟩)
  · obtain ⟨c, _, hcz⟩ := hF.2.2.2.2
    rw [hcz, map_smul]
    congr 1
    rw [eichE_apply]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.map_smulₛₗ₂, hzm a, hy0z, smul_zero, zero_smul, add_zero, sub_zero]

theorem eichE_pW (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    pW D (eichE D a y0 hy v) = pW D v + (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0) := by
  rw [eichE_apply]
  have hf : ∀ b, (VS D).hT (D.sp.hypF b) (D.sp.hypE a) = if a = b then 1 else 0 := fun b => by
    rw [← (VS D).herm.eq (D.sp.hypE a) (D.sp.hypF b), D.sp.hyp_ef]
    split_ifs <;> simp
  have hy2 : ∀ b, (VS D).hT (D.sp.hypF b) y0 = 0 := hy.2.1
  simp only [pW, eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, map_add, map_sub, map_smul, hf, hy.1, hy2, hy.2.2,
    D.sp.hyp_ee, (D.sp.hyp_orthz a).1, smul_eq_mul, mul_zero, add_zero, sub_zero, zero_add, mul_ite,
    mul_one, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, add_smul, sub_smul, zero_div]
  module

theorem eichE_hTe (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (a' : Fin D.R.rS)
    (v : (VS D).V) : (VS D).hT (D.sp.hypE a') (eichE D a y0 hy v) = (VS D).hT (D.sp.hypE a') v := by
  rw [eichE_apply]
  simp [eichL, D.sp.hyp_ee, hy.1 a']

theorem eich_all (hN : UnipotentIntegralIsGroup) (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (y0 : Fin D.R.rS → (VS D).V)
    (hy : ∀ a, InW D (y0 a)) (hyΛ : ∀ a, y0 a ∈ Λ) :
    ∃ n ∈ N0 F0 Λ, ∀ v, pW D (n v) = pW D v + ∑ a, (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0 a) := by
  have key : ∀ s : Finset (Fin D.R.rS), ∃ n ∈ N0 F0 Λ, ∀ v,
      pW D (n v) = pW D v + ∑ a ∈ s, (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0 a) ∧
      ∀ a', (VS D).hT (D.sp.hypE a') (n v) = (VS D).hT (D.sp.hypE a') v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨LinearEquiv.refl _ _, (hN D F0 Λ).1, fun v => ⟨by simp, fun a' => rfl⟩⟩
    | @insert a s ha ih =>
      obtain ⟨n, hn, hv⟩ := ih
      refine ⟨n.trans (eichE D a (y0 a) (hy a)),
        (hN D F0 Λ).2.2 n hn _ (eichE_mem D F0 Λ hF a (hy a) (hyΛ a)), fun v => ⟨?_, fun a' => ?_⟩⟩
      · rw [LinearEquiv.trans_apply, eichE_pW, (hv v).1, (hv v).2 a, Finset.sum_insert ha]
        abel
      · rw [LinearEquiv.trans_apply, eichE_hTe, (hv v).2 a']
  obtain ⟨n, hn, hv⟩ := key Finset.univ
  exact ⟨n, hn, fun v => (hv v).1⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gen_red {M : Type*} [AddCommGroup M] (P : Submodule ℤ M) (hP : P.FG) (N : ℤ) (hN : N ≠ 0) :
    ∃ Rs : Set M, Rs.Finite ∧ ∀ x ∈ P, ∃ q ∈ P, ∃ ρ ∈ Rs, x = N • q + ρ := by
  obtain ⟨s, hs⟩ := hP
  refine ⟨Set.range (fun r : s → Fin N.natAbs => ∑ g : s, ((r g : ℕ) : ℤ) • (g : M)), Set.finite_range _, ?_⟩
  intro x hx
  rw [← hs] at hx
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hx
  refine ⟨∑ g ∈ s, (f g / N) • g, ?_, ∑ g ∈ s, (f g % N) • g, ?_, ?_⟩
  · rw [← hs]
    exact Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (Submodule.subset_span hg)
  · refine ⟨fun g => ⟨(f g % N).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_nonneg (f g) hN
      have h2 := Int.emod_lt (f g) hN
      omega
    · rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hN)]
  · rw [← hf, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_smul, ← add_smul, Int.mul_ediv_add_emod]

theorem int_mult (D : Formalism.BasicNotions.D7) (s : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k ∈ s, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
  obtain ⟨n, hn, h⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  exact ⟨n, hn, fun k hk => ⟨⟨n • k, h k hk⟩, zsmul_eq_mul k n⟩⟩

theorem lat_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (v : (VS D).V) : ∃ n : ℤ, n ≠ 0 ∧ (n : D.host.E) • v ∈ Λ := by
  exact UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D hΛ v

theorem common_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (vs : Finset (VS D).V) (ks : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ (∀ v ∈ vs, (n : D.host.E) • v ∈ Λ) ∧
      ∀ k ∈ ks, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have hv : ∃ n : ℤ, n ≠ 0 ∧ ∀ v ∈ vs, (n : D.host.E) • v ∈ Λ := by
    induction vs using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert v vs hv ih =>
      obtain ⟨n, hn, h⟩ := ih
      obtain ⟨m, hm, hmv⟩ := lat_mult D hΛ v
      refine ⟨m * n, mul_ne_zero hm hn, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · have : ((m * n : ℤ) : D.host.E) • w = (n : D.host.E) • ((m : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul, mul_comm]
        rw [this]; exact smul_int_mem D ⟨n, by simp⟩ hmv
      · have : ((m * n : ℤ) : D.host.E) • w = (m : D.host.E) • ((n : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul]
        rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h w hw)
  obtain ⟨n, hn, h1⟩ := hv
  obtain ⟨m, hm, h2⟩ := int_mult D ks
  refine ⟨n * m, mul_ne_zero hn hm, fun v hv => ?_, fun k hk => ?_⟩
  · have : ((n * m : ℤ) : D.host.E) • v = (m : D.host.E) • ((n : D.host.E) • v) := by
      rw [smul_smul, Int.cast_mul, mul_comm]
    rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h1 v hv)
  · obtain ⟨o, ho⟩ := h2 k hk
    refine ⟨(n : 𝓞 D.host.E) * o, ?_⟩
    rw [map_mul, ho, map_intCast]; push_cast; ring

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inW_add (D : Formalism.BasicNotions.D7) {x y : (VS D).V} (hx : InW D x) (hy : InW D y) : InW D (x + y) := by
  unfold InW at *
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨k1, k2, k3⟩ := hy
  exact ⟨fun a => by rw [map_add (f := _), h1 a, k1 a, add_zero], fun a => by rw [map_add (f := _), h2 a, k2 a, add_zero],
    by rw [map_add (f := _), h3, k3, add_zero]⟩

theorem inW_smul (D : Formalism.BasicNotions.D7) (k : D.host.E) {x : (VS D).V} (hx : InW D x) : InW D (k • x) := by
  unfold InW at *
  obtain ⟨h1, h2, h3⟩ := hx
  exact ⟨fun a => by rw [map_smul, h1 a, smul_zero], fun a => by rw [map_smul, h2 a, smul_zero],
    by rw [map_smul, h3, smul_zero]⟩

theorem inW_zero (D : Formalism.BasicNotions.D7) : InW D 0 := by
  unfold InW
  exact ⟨fun a => map_zero _, fun a => map_zero _, map_zero _⟩

theorem inW_sum (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (x : ι → (VS D).V) (hx : ∀ i, InW D (x i)) :
    InW D (∑ i ∈ s, x i) := by
  exact Finset.sum_induction x (InW D) (fun a b ha hb => inW_add D ha hb) (inW_zero D) (fun i _ => hx i)

def LamW (D : Formalism.BasicNotions.D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {y | y ∈ Λ ∧ InW D y}
  add_mem' hx hy := ⟨Λ.add_mem hx.1 hy.1, inW_add D hx.2 hy.2⟩
  zero_mem' := ⟨Λ.zero_mem, inW_zero D⟩
  smul_mem' o _ hx := ⟨Λ.smul_mem o hx.1, by
    rw [← algebraMap_smul D.host.E o]; exact inW_smul D _ hx.2⟩

theorem hT_int_left (D : Formalism.BasicNotions.D7) (n : ℤ) (x y : (VS D).V) :
    (VS D).hT ((n : D.host.E) • x) y = (n : D.host.E) * (VS D).hT x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply, star_intCast]

private theorem hT_isIntegral_of_mem_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {y v : (VS D).V} (hy : y ∈ Λ) (hv : v ∈ Λ) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT y v := by
  have h : Formalism.E.hdual (VS D).hT Λ = Λ := hU
  have hv' : v ∈ Formalism.E.hdual (VS D).hT Λ := by rw [h]; exact hv
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hv'
  exact Submodule.mem_one.mp (hv' y hy)

theorem pW_lat (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (heΛ : ∀ a, D.sp.hypE a ∈ Λ) (d : ℤ)
    (hdF : ∀ a, (d : D.host.E) • D.sp.hypF a ∈ Λ)
    (hdz : ((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm ∈ Λ) {v : (VS D).V} (hv : v ∈ Λ) :
    (d : D.host.E) ^ 2 • pW D v ∈ Λ := by
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero
  have hsm : ∀ (o : 𝓞 D.host.E) {y : (VS D).V}, y ∈ Λ → algebraMap (𝓞 D.host.E) D.host.E o • y ∈ Λ :=
    fun o y hy => by rw [algebraMap_smul]; exact Λ.smul_mem o hy
  have hint : ∀ (n : ℤ) {y : (VS D).V}, y ∈ Λ → (n : D.host.E) • y ∈ Λ := fun n y hy => by
    have := hsm (n : 𝓞 D.host.E) hy; rwa [map_intCast] at this
  have hnat : ∀ (n : ℕ) {y : (VS D).V}, y ∈ Λ → (n : D.host.E) • y ∈ Λ := fun n y hy => by
    have := hsm (n : 𝓞 D.host.E) hy; rwa [map_natCast] at this
  unfold pW
  simp only [smul_add, smul_sub, Finset.smul_sum]
  refine Λ.add_mem (Λ.sub_mem (Λ.sub_mem ?_ ?_) ?_) ?_
  · rw [pow_two, mul_smul]; exact hint d (hint d hv)
  · refine Λ.sum_mem (fun a _ => ?_)
    obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU (hdF a) hv
    have heq : (d : D.host.E) ^ 2 • ((VS D).hT (D.sp.hypF a) v • D.sp.hypE a) =
        algebraMap (𝓞 D.host.E) D.host.E ((d : 𝓞 D.host.E) * o) • D.sp.hypE a := by
      simp only [smul_smul]
      rw [map_mul, map_intCast, ho, hT_int_left]
      congr 1
      ring
    rw [heq]; exact hsm _ (heΛ a)
  · refine Λ.sum_mem (fun a _ => ?_)
    obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU (heΛ a) hv
    have heq : (d : D.host.E) ^ 2 • ((VS D).hT (D.sp.hypE a) v • D.sp.hypF a) =
        algebraMap (𝓞 D.host.E) D.host.E ((d : 𝓞 D.host.E) * o) • ((d : D.host.E) • D.sp.hypF a) := by
      simp only [smul_smul]
      rw [map_mul, map_intCast, ho]
      congr 1
      ring
    rw [heq]; exact hsm _ (hdF a)
  · obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU hdz hv
    have hc : (VS D).hT (((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm) v =
        (d : D.host.E) * (D.sp.T : D.host.E)⁻¹ * (VS D).hT D.sp.zm v := by
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
      congr 1
      simp
    have hdzm : (d : D.host.E) • D.sp.zm ∈ Λ := by
      have := hnat D.sp.T hdz
      rwa [smul_smul, ← mul_assoc, mul_comm (D.sp.T : D.host.E) (d : D.host.E), mul_assoc,
        mul_inv_cancel₀ hT0, mul_one] at this
    have heq : (d : D.host.E) ^ 2 • (((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm) =
        algebraMap (𝓞 D.host.E) D.host.E o • ((d : D.host.E) • D.sp.zm) := by
      simp only [smul_smul]
      rw [ho, hc]
      congr 1
      rw [div_eq_mul_inv]
      ring
    rw [heq]; exact hsm _ hdzm

def Pm (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  1 - R * betaZ D Z

theorem beta_Pm (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (hR : betaZ D Z * R = 1) : betaZ D Z * Pm D Z R = 0 := by
  unfold Pm
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]

def Gfl (D : Formalism.BasicNotions.D7) (T' : D.host.E) (b1 b2 : Fin (D.R.rS + 1)) : D.host.E :=
  if b1 = Fin.last D.R.rS ∧ b2 = Fin.last D.R.rS then -T' else 0

def gam (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) (c0 : D.host.E)
    (b : Fin (D.R.rS + 1)) : D.host.E :=
  (∑ b', Pm D Z R b' b * (Z (Fin.last D.R.rS) b' / star c0)) / (D.sp.T : D.host.E)

def kap (D : Formalism.BasicNotions.D7) (T' : D.host.E) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (c0 : D.host.E) (b : Fin (D.R.rS + 1)) : D.host.E :=
  (∑ b1, ∑ b2, star (Pm D Z R b1 b) * Pm D Z R b2 b * Gfl D T' b1 b2) +
    (D.sp.T : D.host.E) * star (gam D Z R c0 b) * gam D Z R c0 b

def tv (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (x : (Fin D.R.rS → (VS D).V) × (VS D).V) (b : Fin (D.R.rS + 1)) : (VS D).V :=
  ∑ b', Pm D Z R b' b • pWf D x b'

private theorem hT_swap_eq_star' (D : Formalism.BasicNotions.D7) (p q : (VS D).V) :
    (VS D).hT q p = star ((VS D).hT p q) := by
  first
  | exact ((VS D).herm p q).symm
  | exact ((VS D).herm.eq p q).symm
  | simpa using ((VS D).herm p q).symm
  | simpa using ((VS D).herm.eq p q).symm

private theorem pW_add' (D : Formalism.BasicNotions.D7) (u v : (VS D).V) : pW D (u + v) = pW D u + pW D v := by
  unfold pW
  simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, add_div]
  abel

private theorem pW_smul' (D : Formalism.BasicNotions.D7) (c : D.host.E) (v : (VS D).V) :
    pW D (c • v) = c • pW D v := by
  unfold pW
  simp only [map_smul, smul_eq_mul, mul_div_assoc, mul_smul, smul_sub, smul_add, Finset.smul_sum]

private theorem pW_sum' (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (f : ι → (VS D).V) :
    pW D (∑ i ∈ s, f i) = ∑ i ∈ s, pW D (f i) := by
  exact map_sum (AddMonoidHom.mk' (pW D) (pW_add' D)) f s

private theorem hT_pW_self_of_hT_hypE_eq_zero (D : Formalism.BasicNotions.D7) (w : (VS D).V)
    (hw : ∀ a, (VS D).hT (D.sp.hypE a) w = 0) :
    (VS D).hT (pW D w) (pW D w) = (VS D).hT w w +
      (D.sp.T : D.host.E) * star ((VS D).hT D.sp.zm w / (D.sp.T : D.host.E)) *
        ((VS D).hT D.sp.zm w / (D.sp.T : D.host.E)) := by
  have hs : ∀ p q : (VS D).V, (VS D).hT q p = star ((VS D).hT p q) := fun p q => hT_swap_eq_star' D p q
  have hee : ∀ a a', (VS D).hT (D.sp.hypE a) (D.sp.hypE a') = 0 := D.sp.hyp_ee
  have hze : ∀ a, (VS D).hT D.sp.zm (D.sp.hypE a) = 0 := fun a => (D.sp.hyp_orthz a).1
  have hez : ∀ a, (VS D).hT (D.sp.hypE a) D.sp.zm = 0 := fun a => by rw [hs, hze, star_zero]
  have hwe : ∀ a, (VS D).hT w (D.sp.hypE a) = 0 := fun a => by rw [hs, hw a, star_zero]
  have hzz : (VS D).hT D.sp.zm D.sp.zm = -(D.sp.T : D.host.E) := D.sp.zm_norm
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero
  have hwz : (VS D).hT w D.sp.zm = star ((VS D).hT D.sp.zm w) := hs _ _
  unfold pW
  simp only [hw, zero_smul, Finset.sum_const_zero, sub_zero]
  set g := (VS D).hT D.sp.zm w / (D.sp.T : D.host.E) with hg
  set s := ∑ a, (VS D).hT (D.sp.hypF a) w • D.sp.hypE a with hsdef
  have hsy : ∀ y, (VS D).hT s y = ∑ a, star ((VS D).hT (D.sp.hypF a) w) * (VS D).hT (D.sp.hypE a) y := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hsdef, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂]
  have hys : ∀ y, (VS D).hT y s = ∑ a, (VS D).hT (D.sp.hypF a) w * (VS D).hT y (D.sp.hypE a) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hsdef, map_sum, map_smul, smul_eq_mul]
  have h1 : (VS D).hT s w = 0 := by rw [hsy]; simp [hw]
  have h2 : (VS D).hT s s = 0 := by rw [hsy]; simp [hys, hee]
  have h3 : (VS D).hT s D.sp.zm = 0 := by rw [hsy]; simp [hez]
  have h4 : (VS D).hT w s = 0 := by rw [hys]; simp [hwe]
  have h5 : (VS D).hT D.sp.zm s = 0 := by rw [hys]; simp [hze]
  have h6 : (VS D).hT D.sp.zm w = (D.sp.T : D.host.E) * g := by
    rw [hg, mul_div_assoc', mul_comm, mul_div_assoc, div_self hT0, mul_one]
  simp only [map_add (f := _), map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, h1, h2, h3, h4, h5, hzz, hwz, h6,
    starRingEnd_apply, star_mul', star_natCast]
  ring

theorem tv_norm (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (hR : betaZ D Z * R = 1) (he : F0.e = D.sp.hypE) {c0 : D.host.E} (hc0 : c0 ≠ 0) (hz : F0.z = c0 • D.sp.zm)
    {x : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (tv D Z R x b) (tv D Z R x b) = kap D T' Z R c0 b := by
  obtain ⟨-, hZ, hG⟩ := hx
  set w := ∑ b', Pm D Z R b' b • fr D x b' with hw
  have htv : tv D Z R x b = pW D w := by
    show ∑ b', Pm D Z R b' b • pW D (fr D x b') = pW D w
    rw [hw, pW_sum']
    simp only [pW_smul']
  have hEu : ∀ a b', (VS D).hT (D.sp.hypE a) (fr D x b') = Z (Fin.castSucc a) b' := by
    intro a b'
    have h := hZ (Fin.castSucc a) b'
    simpa [brS, FlagG.fvec, he] using h
  have hzu : ∀ b', (VS D).hT D.sp.zm (fr D x b') = Z (Fin.last D.R.rS) b' / star c0 := by
    intro b'
    have h := hZ (Fin.last D.R.rS) b'
    simp only [brS, FlagG.fvec, Fin.snoc_last, hz, LinearMap.map_smulₛₗ₂, smul_eq_mul,
      starRingEnd_apply] at h
    rw [eq_div_iff (star_ne_zero.mpr hc0), ← h, mul_comm]
  have hGu : ∀ b1 b2, (VS D).hT (fr D x b1) (fr D x b2) = Gfl D T' b1 b2 := by
    intro b1 b2
    rw [hG b1 b2]
    unfold Gfl
    split_ifs <;> first | rfl | (exfalso; tauto)
  have hEw : ∀ a, (VS D).hT (D.sp.hypE a) w = 0 := by
    intro a
    have h0 : (betaZ D Z * Pm D Z R) a b = 0 := by rw [beta_Pm D Z R hR]; rfl
    rw [Matrix.mul_apply] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul, hEu]
    simpa [betaZ, Matrix.submatrix_apply, mul_comm] using h0
  have hww : (VS D).hT w w =
      ∑ b1, ∑ b2, star (Pm D Z R b1 b) * Pm D Z R b2 b * Gfl D T' b1 b2 := by
    rw [hw]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, map_sum, map_smul, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b1 _ => Finset.sum_congr rfl (fun b2 _ => ?_))
    rw [hGu b1 b2]
    ring
  have hzw : (VS D).hT D.sp.zm w = ∑ b', Pm D Z R b' b * (Z (Fin.last D.R.rS) b' / star c0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul, hzu]
  rw [htv, hT_pW_self_of_hT_hypE_eq_zero D w hEw]
  unfold kap gam
  rw [hww, hzw]

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem stage1_riesz (D : Formalism.BasicNotions.D7) (φ : (VS D).V →ₗ[D.host.E] D.host.E) : ∃ μ : (VS D).V, ∀ v, (VS D).hT μ v = φ v := by
  classical
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis (VS D).hT (VS D).nondeg (VS D).frame
  refine ⟨∑ j, star (φ ((VS D).frame j)) • bs j, fun v => ?_⟩
  have key : (VS D).hT (∑ j, star (φ ((VS D).frame j)) • bs j) = φ := by
    apply (VS D).frame.ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
        φ ((VS D).frame j) * (if i = j then 1 else 0) := by
      intro j
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      congr 1
      rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
      split_ifs <;> simp
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]

private theorem stage1_span_eq_top_of_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨μ, hμ⟩ := stage1_riesz D φ
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using (hμ y).symm
  have hline (a : D.host.E) : a • μ ∈ Λ := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual (VS D).hT Λ
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← (VS D).herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule D.host.E (VS D).V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 D.host.E)
  have hmap (x : D.host.E) : x ∈ Λ.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 D.host.E)) (hL.map f)
  have hinj := IsFractionRing.injective (𝓞 D.host.E) D.host.E
  have hne {a : 𝓞 D.host.E} (ha : a ≠ 0) : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : D.host.E) : IsLocalization.IsInteger (𝓞 D.host.E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField D.host.E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 D.host.E) D.host.E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]


theorem inW_neg (D : Formalism.BasicNotions.D7) {x : (VS D).V} (hx : InW D x) : InW D (-x) := by
  simpa using inW_smul D (-1) hx

theorem stage1_of_unipotentIntegralIsGroup (hN : UnipotentIntegralIsGroup) : Stage1 := by
  intro D T T' F0 Λ hF Z R hR
  have hF' := hF
  obtain ⟨hlat, hU, he, heΛ0, c0, hc0, hz⟩ := hF
  have heΛ : ∀ a, D.sp.hypE a ∈ Λ := fun a => by rw [← he]; exact heΛ0 a
  let : Submodule.IsLattice D.host.E Λ := hlat
  have hfull : Submodule.IsFullLattice D.host.E Λ :=
    ⟨stage1_span_eq_top_of_unimodular D hlat.fg hU⟩
  obtain ⟨d, hd0, hdv, hdk⟩ := common_mult D hfull
    (Finset.univ.image D.sp.hypF ∪ {((D.sp.T : D.host.E)⁻¹) • D.sp.zm})
    (Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2) ∪
      Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2))
  have hdF : ∀ a, (d : D.host.E) • D.sp.hypF a ∈ Λ := fun a =>
    hdv _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
  have hdz : ((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm ∈ Λ := by
    rw [← smul_smul]; exact hdv _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hdR : ∀ b a, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * R b a := fun b a =>
    hdk _ (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2)
      (Finset.mem_univ (b, a))))
  have hdP : ∀ b' b, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * Pm D Z R b' b :=
    fun b' b => hdk _ (Finset.mem_union_right _ (Finset.mem_image_of_mem
      (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2) (Finset.mem_univ (b', b))))
  have hd2 : ∀ v ∈ Λ, (d : D.host.E) ^ 2 • pW D v ∈ Λ := fun v hv => pW_lat D hU heΛ d hdF hdz hv
  have hdE : (d : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hd0
  have hd3 : (d : D.host.E) ^ 3 ≠ 0 := pow_ne_zero 3 hdE
  have hΛfg : (Λ.restrictScalars ℤ).FG := Submodule.FG.restrictScalars hlat.fg

  let Sb : Fin (D.R.rS + 1) → Set (VS D).V := fun b =>
    {w | w ∈ Λ.restrictScalars ℤ ∧ (∀ a, (VS D).hT (D.sp.hypE a) w = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) w = 0) ∧
      (VS D).hT D.sp.zm w = 0 ∧ (VS D).hT w w = (d : D.host.E) ^ 6 * kap D T' Z R c0 b}
  have hSb : ∀ b, (Sb b).Finite := fun b => definite_finite D _ hΛfg _
  let Tset : Fin (D.R.rS + 1) → Set (VS D).V := fun b => (fun w => (((d : D.host.E) ^ 3)⁻¹) • w) '' Sb b

  have hLWfg : ((LamW D Λ).restrictScalars ℤ).FG := Submodule.FG.of_le hΛfg (fun y hy => hy.1)
  obtain ⟨Rs, hRs, hred⟩ := gen_red _ hLWfg (2 * d ^ 3) (mul_ne_zero two_ne_zero (pow_ne_zero 3 hd0))
  refine ⟨(fun p : (Fin (D.R.rS + 1) → (VS D).V) × (Fin D.R.rS → (VS D).V) =>
      fun b => p.1 b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • p.2 a) ''
      (Set.pi Set.univ Tset ×ˢ Set.pi Set.univ (fun _ => Rs)), ?_, ?_⟩
  · exact ((Set.Finite.pi (fun b => (hSb b).image _)).prod (Set.Finite.pi (fun _ => hRs))).image _
  intro x hx
  have hbeta : ∀ (a : Fin D.R.rS) b, (VS D).hT (D.sp.hypE a) (fr D x b) = betaZ D Z a b := by
    intro a b
    have := hx.2.1 (Fin.castSucc a) b
    simpa [brS, FlagG.fvec, he, betaZ] using this

  have hw2 : ∀ b, (d : D.host.E) ^ 2 • pWf D x b ∈ LamW D Λ := fun b =>
    ⟨hd2 _ (hx.1 b), inW_smul D _ (inW_pW D _)⟩
  have hu : ∀ a, (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) ∈ (LamW D Λ).restrictScalars ℤ := by
    intro a
    have : (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) =
        ∑ b, ((d : D.host.E) * R b a) • ((d : D.host.E) ^ 2 • pWf D x b) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [smul_smul, smul_smul]; ring_nf
    rw [Submodule.restrictScalars_mem, this]
    refine Submodule.sum_mem _ fun b _ => ?_
    obtain ⟨o, ho⟩ := hdR b a
    rw [← ho, algebraMap_smul]
    exact (LamW D Λ).smul_mem o (hw2 b)
  choose q hq ρ hρ hqρ using fun a => hred _ (hu a)
  obtain ⟨n, hn, hpW⟩ := eich_all hN D F0 Λ hF' (fun a => -q a) (fun a => inW_neg D (hq a).2)
    (fun a => Λ.neg_mem (hq a).1)
  refine ⟨n, hn, ⟨(tv D Z R x, ρ), ⟨fun b _ => ?_, fun a _ => hρ a⟩, ?_⟩⟩
  ·
    refine ⟨(d : D.host.E) ^ 3 • tv D Z R x b, ⟨?_, ?_, ?_, ?_, ?_⟩, inv_smul_smul₀ hd3 _⟩
    · rw [Submodule.restrictScalars_mem]
      have : (d : D.host.E) ^ 3 • tv D Z R x b =
          ∑ b', ((d : D.host.E) * Pm D Z R b' b) • ((d : D.host.E) ^ 2 • pWf D x b') := by
        rw [tv, Finset.smul_sum]
        exact Finset.sum_congr rfl fun b' _ => by rw [smul_smul, smul_smul]; ring_nf
      rw [this]
      refine Submodule.sum_mem _ fun b' _ => smul_int_mem D (hdP b' b) (hw2 b').1
    all_goals have hW : InW D ((d : D.host.E) ^ 3 • tv D Z R x b) :=
      inW_smul D _ (inW_sum D _ _ fun b' => inW_smul D _ (inW_pW D _))
    · exact hW.1
    · exact hW.2.1
    · exact hW.2.2
    · simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply,
        star_pow, star_intCast]
      rw [tv_norm D T' F0 Λ Z R hR he hc0 hz hx b]
      ring
  ·
    funext b
    have h2q : ∀ a, (2 : D.host.E) • q a = (∑ b', R b' a • pWf D x b') - (((d : D.host.E) ^ 3)⁻¹) • ρ a := by
      intro a
      have e1 := hqρ a
      rw [← Int.cast_smul_eq_zsmul D.host.E] at e1
      have e2 : ((2 * d ^ 3 : ℤ) : D.host.E) • q a = (d : D.host.E) ^ 3 • (∑ b', R b' a • pWf D x b') - ρ a := by
        rw [e1]; abel
      have e3 : (2 : D.host.E) • q a = (((d : D.host.E) ^ 3)⁻¹) • (((2 * d ^ 3 : ℤ) : D.host.E) • q a) := by
        rw [smul_smul]; congr 1; push_cast; field_simp
      rw [e3, e2, smul_sub, inv_smul_smul₀ hd3]
    symm
    show pW D (fr D (act D n x) b) = tv D Z R x b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • ρ a
    rw [fr_act, hpW]
    have e4 : ∀ a, (VS D).hT (D.sp.hypE a) (fr D x b) • ((2 : D.host.E) • -q a) =
        -(betaZ D Z a b • (∑ b', R b' a • pWf D x b')) + (((d : D.host.E) ^ 3)⁻¹) • (betaZ D Z a b • ρ a) := by
      intro a
      rw [hbeta, smul_neg, h2q, smul_neg, smul_sub, smul_comm (betaZ D Z a b) (((d : D.host.E) ^ 3)⁻¹) (ρ a)]
      abel
    rw [Finset.sum_congr rfl fun a _ => e4 a, Finset.sum_add_distrib, ← Finset.smul_sum]
    simp only [tv, Pm, Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mul_apply, Finset.sum_smul,
      Finset.sum_neg_distrib, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm (f := fun a b' => (betaZ D Z a b * R b' a) • pWf D x b')]
    have e5 : ∀ b' a, (betaZ D Z a b * R b' a) • pWf D x b' = (R b' a * betaZ D Z a b) • pWf D x b' :=
      fun b' a => by rw [mul_comm]
    simp only [e5]
    show pW D (fr D x b) + _ = _
    have e6 : pWf D x b = pW D (fr D x b) := rfl
    rw [← e6]
    abel

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepTop
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepGood
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_mem_ddS_zpow (D : Formalism.BasicNotions.D7) (k : ℕ) :
    (1 : D.host.E) ∈ ((ddS D) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h0 : ddS D ≠ 0 := PI.TripleFrameDeterminant.W.ddS_ne_zero D
  have hle : ddS D ^ k ≤ 1 := by
    rw [ddS, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  have h := FractionalIdeal.inv_anti_mono (pow_ne_zero k h0) hle
  rw [inv_one] at h
  rw [zpow_neg, zpow_natCast]
  exact h (FractionalIdeal.one_mem_one _)

theorem flag_gram (D : Formalism.BasicNotions.D7) {T' : D.host.E} (G : FlagG (VS D) D.R.rS T') (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (G.fvec a) (G.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0 := by
  have hs : ∀ x y, (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y) :=
    fun x y => ((VS D).herm.eq x y).symm
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_norm]
    | cast j =>
      rw [hs]
      simp [FlagG.fvec, G.z_orth j]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_orth i]
    | cast j => simp [FlagG.fvec, G.e_iso i j]

theorem good_places_integral : GoodEZ := by
  intro D T T' F0 Λ Z F' hF'
  obtain ⟨hT, -, -, hFr, hZ⟩ := hF'
  have hfr : fr D (F'.fl.e, F'.fl.z) = F'.fl.fvec := rfl
  refine ⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hfr]
    have h := PI.CntNotIntW.frame_mem Λ F' hFr.2 hT.1.1 b 1 (one_mem_ddS_zpow D _)
    rwa [one_smul] at h
  · rw [hfr, ← hZ]
    rfl
  · rw [hfr]
    exact flag_gram D F'.fl a b

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fixedOK_of_rows (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Λ ∈ what₂) : FixedOK D F0 Λ := by
  obtain ⟨hE, hz, hrr, -⟩ := hR
  obtain ⟨-, ⟨hlat, hunim, -, -⟩, hx⟩ := hrr.1 Λ hΛ
  refine ⟨hlat, hunim, hE, ?_, (D.cOf u)⁻¹, inv_ne_zero (D.cOf_ne u), ?_⟩
  · unfold XLam at hx
    intro a
    have hmem : F0.e a ∈ XS D F0 := by
      unfold XS
      clear hrr hz hunim hlat hΛ what₂ hE hx
      apply Submodule.subset_span
      refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
      unfold ddS
      have hne : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ :=
        Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
      have hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
        have := a.isLt
        omega
      rw [hk, zpow_neg, zpow_natCast, ← FractionalIdeal.coeIdeal_pow,
        FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ hne))]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    rw [← hx] at hmem
    exact hmem.1
  · rw [hz]
    rfl

theorem orbitReps_of (hN : UnipotentIntegralIsGroup) (hRk : RankG) (hG : GoodEZ) (h1 : Stage1) (h2 : Stage2) (hK : FinK) :
    OrbitReps := by
  intro D δ M hA L u u' hT F0 what₂ hR Z Λ hΛ
  have hF := fixedOK_of_rows D u F0 what₂ hR hΛ
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F1, hF1⟩ := hne
    have hGZ : GZ (Tn u) (Tn u') Z ≠ 0 := by
      have h := hF1.1.2.2
      rw [gz_eq, hF1.2.2.2.2] at h
      exact h
    obtain ⟨R, hRm⟩ := hRk D (Tn u) (Tn u') Z hGZ
    obtain ⟨Wf, hWf, hW⟩ := h1 D (Tn u') F0 Λ hF Z R hRm
    obtain ⟨Af, hAf, hAx⟩ := h2 D (Tn u') F0 Λ hF Z R hRm Wf hWf
    refine ⟨{x | Good D (Tn u') F0 Λ Z x ∧ pWf D x ∈ Wf ∧ alM D x * R ∈ Af},
      hK D (Tn u') F0 Λ hF Z R hRm Wf Af hWf hAf, fun F' hF' => ?_⟩
    have g0 := hG D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n1, hn1, hw1⟩ := hW _ g0
    have g1 := good_move D (Tn u') F0 Λ Z g0 hn1
    obtain ⟨n2, hn2, hw2, ha2⟩ := hAx _ g1 hw1
    have g2 := good_move D (Tn u') F0 Λ Z g1 hn2
    refine ⟨n1.trans n2, (hN D F0 Λ).2.2 n1 hn1 n2 hn2, ?_⟩
    have hact : act D (n1.trans n2) (F'.fl.e, F'.fl.z) = act D n2 (act D n1 (F'.fl.e, F'.fl.z)) := rfl
    show act D (n1.trans n2) (F'.fl.e, F'.fl.z) ∈ _
    rw [hact]
    exact ⟨g2, hw2 ▸ hw1, ha2⟩
  · refine ⟨∅, Set.finite_empty, fun F' hF' => absurd ⟨F', hF'⟩ hne⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepRank
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_gram : RankG := by
  intro D T T' Z hG
  classical
  by_cases hdet : Z.det = 0
  · have hm : leadMinorE Z D.R.rS ≠ 0 := by
      intro hm
      apply hG
      have h1 : leadMinorE Z (D.R.rS + 1) = 0 := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos le_rfl, Fin.castLE_rfl, Matrix.submatrix_id_id]
        exact hdet
      simp [Formalism.L2.SG.CntLocal.GZ, h1, hm]
    have h : D.R.rS ≤ D.R.rS + 1 := Nat.le_succ _
    set B := Z.submatrix (Fin.castLE h) (Fin.castLE h) with hB
    have hBdet : B.det ≠ 0 := by
      have e : leadMinorE Z D.R.rS = B.det := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos h]
      rwa [← e]
    refine ⟨Matrix.of fun j i => if hj : (j : ℕ) < D.R.rS then B⁻¹ ⟨j, hj⟩ i else 0, ?_⟩
    have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hBdet)
    ext a i
    rw [← hBB]
    simp only [Matrix.mul_apply, betaZ, Matrix.submatrix_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
      Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, not_false_eq_true, dif_neg, mul_zero,
      add_zero, id]
    rfl
  · refine ⟨(Z⁻¹).submatrix id Fin.castSucc, ?_⟩
    have hZ : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z (isUnit_iff_ne_zero.2 hdet)
    unfold betaZ
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hZ]
    exact Matrix.submatrix_one_embedding Fin.castSuccEmb

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem orbit_count_first_stage : Stage1 := stage1_of_unipotentIntegralIsGroup unipotent_integral_isGroup

theorem orbitReps_of_stage2 (h2 : Stage2) : OrbitReps :=
  orbitReps_of unipotent_integral_isGroup rank_gram good_places_integral orbit_count_first_stage h2 finite_level_index

end PI.UnitaryGroupMassFormula.CntFormula
