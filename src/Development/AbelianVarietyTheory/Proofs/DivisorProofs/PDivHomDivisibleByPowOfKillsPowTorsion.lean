module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenChartOfSmoothFamilyGeomFibreInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionCompStructureEqGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymmStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsion
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup.DivP

open WithConv

variable {p : ℕ} {k : Type} [Field k]

theorem conv_eq_one_of_succ {G H : PDivGroup p k} (f : G ⟶ H) (n : ℕ) (h : f.conv (n + 1) = 1) :
    f.conv n = 1 := by
  have h1 : ∀ b, f.app (n + 1) b = algebraMap k _ (counit b) := fun b => by
    have := DFunLike.congr_fun (congrArg ofConv h) b
    simpa using this
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective n a
  change f.app n (H.res n b) = algebraMap k _ (counit (H.res n b))
  rw [← res_app, h1, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

theorem conv_eq_one_of_le {G H : PDivGroup p k} (f : G ⟶ H) {m n : ℕ} (hmn : m ≤ n)
    (h : f.conv n = 1) : f.conv m = 1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (conv_eq_one_of_succ f n h)

theorem app_kill {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) (n : ℕ) :
    ∀ {E : Type} [CommRing E] [Algebra k E] (x : G.A (n + 1) →ₐ[k] E), toConv x ^ p = 1 →
      ∀ c, x (f.app (n + 1) c) = algebraMap k E (counit c) := by
  induction n with
  | zero =>
    intro E _ _ x _ c
    have h1 : f.app 1 c = algebraMap k _ (counit c) := by
      have := DFunLike.congr_fun (congrArg ofConv hf) c
      simpa using this
    rw [h1, AlgHom.commutes]
  | succ n ih =>
    intro E _ _ x hx c
    have hx' : toConv x ^ p ^ (n + 1) = 1 := by
      rw [pow_succ', pow_mul, hx, one_pow]
    obtain ⟨y, hy⟩ := (G.exists_comp_res_iff (n + 1) x).2 hx'
    have hy' : toConv y ^ p = 1 := by
      have e : pointsMap E (G.res (n + 1)) (toConv y ^ p) = 1 := by
        rw [map_pow]
        change (toConv (y.comp (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1)))) ^ p = 1
        rw [hy, hx]
      apply ofConv_injective
      refine AlgHom.ext fun a => ?_
      obtain ⟨b, rfl⟩ := G.res_surjective (n + 1) a
      have e2 := DFunLike.congr_fun (congrArg ofConv e) b
      rw [ptsMap_ofConv, AlgHom.comp_apply] at e2
      refine e2.trans ?_
      show algebraMap k E (counit b) = algebraMap k E (counit (G.res (n + 1) b))
      rw [CoalgHomClass.counit_comp_apply]
    rw [← hy, AlgHom.comp_apply]
    change y (G.res (n + 1) (f.app (n + 2) c)) = _
    rw [res_app, ih y hy', CoalgHomClass.counit_comp_apply]

theorem exists_factor [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1)
    (n : ℕ) : ∃ g : H.A (n + 1) →ₐc[k] G.A n, ∀ b, G.mulP n (g b) = f.app (n + 1) b := by
  obtain ⟨r, hrs, hrk⟩ := G.exists_res_le (m := 1) (n := n + 1) (by omega)
  rw [pow_one] at hrk
  obtain ⟨B, _, _, _, _, j, hji, hjk, hjr⟩ := GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup k (G.A (n + 1)) (G.A 1) r hrs
  have hP : kerIdeal (G.mulP n) = RingHom.ker r := by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective n), mulP_comp_res, hrk]
  have h1 : ∀ a, G.mulP n a ∈ Set.range j := hjr (G.A n) (G.mulP n) hP.le
  have hmk : toConv (Ideal.Quotient.mkₐ k (torsionIdeal (R := k) (A := G.A (n + 1)) p)) ^ p = 1 :=
    (torsionIdeal_le_ker_iff p _).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h2 : ∀ b, f.app (n + 1) b ∈ Set.range j := by
    refine hjr (H.A (n + 1)) (f.app (n + 1)) ?_
    rw [hrk]
    intro a ha
    have := (kerIdeal_le_ker_iff (f.app (n + 1)) (Ideal.Quotient.mkₐ k _)).2
      (fun c => app_kill f hf n _ hmk c) ha
    rw [RingHom.mem_ker] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  let jl := (j : B →ₐ[k] G.A (n + 1)).toLinearMap
  let ml := (G.mulP n : G.A n →ₐ[k] G.A (n + 1)).toLinearMap
  have hle : LinearMap.range ml ≤ LinearMap.range jl := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := h1 a
    exact ⟨b, hb⟩
  have e1 := finrank_eq_ker_mul_range k (G.A (n + 1)) (G.A n) (G.mulP n)
  have e2 := finrank_eq_ker_mul_range k (G.A (n + 1)) B j
  rw [hP] at e1
  rw [hjk] at e2
  have hpos : 0 < Module.finrank k (G.A (n + 1) ⧸ RingHom.ker r) := by
    apply Nat.pos_of_ne_zero
    intro h0
    have : Nontrivial (G.A (n + 1)) := (counitAlgHom k (G.A (n + 1))).domain_nontrivial
    have h3 := Module.finrank_pos (R := k) (M := G.A (n + 1))
    rw [e1, h0, zero_mul] at h3
    exact lt_irrefl _ h3
  have heq : LinearMap.range ml = LinearMap.range jl :=
    Submodule.eq_of_le_of_finrank_eq hle (Nat.eq_of_mul_eq_mul_left hpos (e1.symm.trans e2))
  have h3 : ∀ b, f.app (n + 1) b ∈ Set.range (G.mulP n) := by
    intro b
    obtain ⟨c, hc⟩ := h2 b
    have : f.app (n + 1) b ∈ LinearMap.range ml := by
      rw [heq]
      exact ⟨c, hc⟩
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective ml
    (LinearMap.ker_eq_bot.2 (Test.mulP_injective G n))
  exact GlobalTheory.bialgHom_factor_through_split k (G.A (n + 1)) (G.A n) (H.A (n + 1)) (G.mulP n) ρ
    (f.app (n + 1)) (fun a => LinearMap.congr_fun hρ a) h3

theorem exists_eq_p_smul [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  choose g' hg' using exists_factor f hf
  have hker : ∀ n, RingHom.ker (H.res n) ≤ RingHom.ker (g' n) := by
    intro n
    rw [H.ker_res]
    refine (kerIdeal_le_ker_iff _ (g' n : H.A (n + 1) →ₐ[k] G.A n)).2 fun c => ?_
    change g' n (mulBy k _ (p ^ n) c) = _
    rw [map_mulBy, G.mulBy_pow_self, CoalgHomClass.counit_comp_apply]
  let gapp : ∀ n, H.A n →ₐc[k] G.A n := fun n =>
    liftSurj (H.res n) (H.res_surjective n) (g' n) (hker n)
  have hg : ∀ n b, gapp n (H.res n b) = g' n b := fun n b => liftSurj_apply ..
  have hcomm : ∀ n, (G.res n).comp (gapp (n + 1)) = (gapp n).comp (H.res n) := by
    intro n
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective (n + 1) a
    apply Test.mulP_injective G n
    change G.mulP n (G.res n (gapp (n + 1) (H.res (n + 1) b))) =
      G.mulP n (gapp n (H.res n (H.res (n + 1) b)))
    rw [hg, hg, mulP_res, hg' n, ← res_app, ← hg' (n + 1) b, res_mulP]
  refine ⟨⟨gapp, hcomm⟩, hom_ext_conv fun n => ?_⟩
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self n _)]
  have hfa : f.app n = (mulBy k (G.A n) p).comp (gapp n) := by
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective n a
    rw [← res_app, ← hg' n b, res_mulP, BialgHom.comp_apply, hg]
  change toConv (f.app n) = toConv (gapp n) ^ p
  rw [hfa, mulBy_comp, toConv_ofConv]

theorem conv_eq_one_of_p_smul [Fact p.Prime] {G H : PDivGroup p k} (g : G ⟶ H) (m : ℕ)
    (h : ((p : ℤ_[p]) • g).conv (m + 1) = 1) : g.conv m = 1 := by
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self _ _)] at h
  have h' : ∀ b, mulBy k (G.A (m + 1)) p (g.app (m + 1) b) = algebraMap k _ (counit b) := by
    intro b
    have e := DFunLike.congr_fun (congrArg ofConv h) b
    have e2 := DFunLike.congr_fun (mulBy_comp (g.app (m + 1)) p) b
    rw [BialgHom.comp_apply] at e2
    rw [e2]
    simpa using e
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective m a
  apply Test.mulP_injective G m
  change G.mulP m (g.app m (H.res m b)) = G.mulP m (algebraMap k _ (counit (H.res m b)))
  rw [← res_app, mulP_res, h', CoalgHomClass.counit_comp_apply]
  exact (AlgHomClass.commutes (G.mulP m) _).symm

theorem exists_eq_pow_smul [Fact p.Prime] {G H : PDivGroup p k} (m : ℕ) :
    ∀ f : G ⟶ H, f.conv m = 1 → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g := by
  induction m with
  | zero => exact fun f _ => ⟨f, by rw [pow_zero, one_smul]⟩
  | succ m ih =>
    intro f hf
    obtain ⟨g, rfl⟩ := exists_eq_p_smul f (conv_eq_one_of_le f (by omega) hf)
    obtain ⟨g2, rfl⟩ := ih g (conv_eq_one_of_p_smul g m hf)
    exact ⟨g2, by rw [smul_smul, ← pow_succ']⟩

theorem divisible_of_conv_eq_one : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (m : ℕ) (f : G ⟶ H), f.conv m = 1 →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g :=
  fun _ _ _ _ _ _ _ m f hf => exists_eq_pow_smul m f hf

end GlobalTheory.PDivGroup.DivP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsionStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (m : ℕ) (f : G ⟶ H), f.conv m = 1 → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g := by
  first | exact @GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one | exact GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one | (intros; apply GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightReciprocityTwoSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedWeilDivisorSumSymmNoCommonDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedWeilDivisorSumSymmNoCommonDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt

theorem finsum_mul_comp_eq_sum_indicator {W Z : Type*} (c : W → ℝ) (hc : (Function.support c).Finite) (f : W → Z)
    (F : Finset Z) (hF : f '' Function.support c ⊆ ↑F) (g : Z → ℝ) :
    ∑ᶠ w, c w * g (f w) = ∑ x ∈ F, g x * ∑ᶠ w, c w * Set.indicator {x} 1 (f w) := by
  classical
  have hsub : ∀ h : Z → ℝ, Function.support (fun w => c w * h (f w)) ⊆ ↑hc.toFinset := fun h w hw => by
    rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hw
  rw [finsum_eq_sum_of_support_subset _ (hsub g)]
  have e : ∀ x : Z, ∑ᶠ w, c w * Set.indicator {x} 1 (f w) = ∑ w ∈ hc.toFinset, c w * Set.indicator {x} 1 (f w) :=
    fun x => finsum_eq_sum_of_support_subset _ (hsub (Set.indicator {x} 1))
  simp_rw [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hwF : f w ∈ F := hF ⟨w, (Set.Finite.mem_toFinset hc).1 hw, rfl⟩
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq F (f w) (fun x => g x * c w), if_pos hwF, mul_comm]

theorem exists_finset_resCyc {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {q : Y ⟶ Sp k} (hq : IsAmb q) {B : LB Y} (hB : B.IsLB) (t : B.Sec) (z : Y) :
    ∃ F : Finset Y, ∀ F' : Finset Y, F ⊆ F' → ∀ g : Y → ℝ,
      resCyc hB t g z = ∑ x ∈ F', g x * resCyc hB t (Set.indicator {x} 1) z := by
  classical
  by_cases h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z))
  · have : IsNoetherian (clo z) := (hq.sub (cloι z)).isNoetherian
    set D := divOfSec (LB.isLB_pull hB (cloι z)) _ h
    have hc : (Function.support fun w => (D.mult w : ℝ)).Finite :=
      D.finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
    refine ⟨(hc.image fun w => cloι z w).toFinset, fun F' hF' g => ?_⟩
    simp only [resCyc, dif_pos h]
    refine finsum_mul_comp_eq_sum_indicator _ hc _ F' ?_ g
    intro y hy
    exact hF' ((Set.Finite.mem_toFinset _).2 hy)
  · refine ⟨∅, fun F' _ g => ?_⟩
    simp [resCyc, dif_neg h]

end GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem iterDiv_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ g : Y → ℝ, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t g z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s g z := by
  intro k _ Y _ _ q hq A B hA hB s t hs ht hst g
  classical
  have : IsNoetherian Y := hq.isNoetherian
  choose Ft hFt using exists_finset_resCyc hq hB t
  choose Fs hFs using exists_finset_resCyc hq hA s
  have hms : (Function.support fun z => ((divOfSec hA s hs).mult z : ℝ)).Finite :=
    (divOfSec hA s hs).finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
  have hmt : (Function.support fun z => ((divOfSec hB t ht).mult z : ℝ)).Finite :=
    (divOfSec hB t ht).finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
  set F := hms.toFinset.biUnion Ft ∪ hmt.toFinset.biUnion Fs
  have Ls : ∀ h : Y → ℝ, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t h z =
      ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t h z := fun h =>
    finsum_eq_sum_of_support_subset _ fun z hz => by
      rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hz
  have Lt : ∀ h : Y → ℝ, ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s h z =
      ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s h z := fun h =>
    finsum_eq_sum_of_support_subset _ fun z hz => by
      rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hz
  have Es : ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t g z =
      ∑ x ∈ F, g x * ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z := by
    rw [Finset.sum_congr rfl fun z hz => by
      rw [hFt z F (Finset.subset_union_left.trans' (Finset.subset_biUnion_of_mem Ft hz)) g]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have Et : ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s g z =
      ∑ x ∈ F, g x * ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
    rw [Finset.sum_congr rfl fun z hz => by
      rw [hFs z F (Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem Fs hz)) g]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Ls, Lt, Es, Et]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Ls, ← Lt, GlobalTheory.T.finsum_mult_resCyc_indicator_symm' k Y q hq A B hA hB s t hs ht hst x]

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedWeilDivisorSumSymmNoCommonDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedWeilDivisorSum_symm_no_common_divisor : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ g : Y → ℝ, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t g z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s g z := by
  first | exact @GlobalTheory.MixHt.iterDiv_symm | exact GlobalTheory.MixHt.iterDiv_symm | (intros; apply GlobalTheory.MixHt.iterDiv_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightReciprocityTwoSections
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

set_option autoImplicit false

theorem mixRecVal_cons_eq_resCyc_sub_resArch {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hA : IsAmb q) {e : ℕ} (hdim : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
    {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (N : HermLB q) (L : Fin e → HermLB q)
    (t : N.B.Sec) {z : Y} (hz : Order.coheight z = 1) (hzt : z ∈ nonzeroLocus t) :
    T (e + 1) (Fin.cons N L) z = resCyc N.isLB t (T e L) z - resArch L N t z := by
  have hg : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]
    exact hzt
  have hd : topologicalKrullDim (clo z) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hA (e + 1) hdim).2 z (genericPoint (clo z)) hz).1
  have h := hT.recur (clo z) (cloι z ≫ q) (cloι z) rfl e le_rfl hd N L (N.restr (cloι z))
    (fun a => (L a).restr (cloι z)) (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) _
    (isRatSec_ratOfSec _ hg)
  rw [cloι_genericPoint] at h
  rw [h, resCyc, resArch, dite_eq_left hg, dite_eq_left hg]
  rfl

end GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem finite_support_mult_mul {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
  D.finite_support_mult.subset fun z hz => by
    simp only [Function.mem_support] at hz ⊢
    intro h
    simp [h] at hz

theorem recVal_cons_recip : ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
  intro hAR k _ Y _ _ q hA e hdim T hT M N L s t hs ht hcov
  have : IsNoetherian Y := hA.isNoetherian
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * T (e + 1) (Fin.cons B L) z =
        ((divOfSec A.isLB a ha).mult z : ℝ) * resCyc B.isLB b (T e L) z -
          ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [mixRecVal_cons_eq_resCyc_sub_resArch hA hdim hT B L b hz ((hab z hz).resolve_left hza), mul_sub]
  have hL : recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) =
      (∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resCyc N.isLB t (T e L) z -
        ∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resArch L N t z) -
        mixArch (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) := by
    rw [recVal, finsum_congr (key M N s t hs hcov), finsum_sub_distrib (finite_support_mult_mul _ _)
      (finite_support_mult_mul _ _)]
  have hR : recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) =
      (∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resCyc M.isLB s (T e L) z -
        ∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resArch L M s z) -
        mixArch (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
    rw [recVal, finsum_congr (key N M t s ht fun z hz => (hcov z hz).symm),
      finsum_sub_distrib (finite_support_mult_mul _ _) (finite_support_mult_mul _ _)]
  have hC := GlobalTheory.T.iteratedWeilDivisorSum_symm_no_common_divisor k Y q hA M.B N.B M.isLB N.isLB s t hs ht hcov (T e L)
  rw [hL, hR, hC]
  rcases GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hA (e + 1 + 1) hdim with ⟨l, _, _, hno⟩ | ⟨e', he', hav⟩
  · have z₀ := GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k Y q hno
    rw [(z₀ (e + 1) (Fin.cons N L) M).1, (z₀ (e + 1) (Fin.cons M L) N).1]
    simp only [(z₀ e L N).2, (z₀ e L M).2, mul_zero, finsum_zero]
  · obtain rfl : e' = e + 1 := by omega
    have hA' := hAR k Y q e hav M N L s t hs ht hcov
    linarith

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightReciprocityTwoSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections : ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
  first | exact @GlobalTheory.MixHt.recVal_cons_recip | exact GlobalTheory.MixHt.recVal_cons_recip | (intros; apply GlobalTheory.MixHt.recVal_cons_recip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedDescendFiniteSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedDescendFiniteSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem surjective_to_spec_field {T : Scheme.{0}} (K : Type) [Field K] (h : T ⟶ Spec (CommRingCat.of K))
    (t : T) : Surjective h := by
  refine ⟨fun x ↦ ⟨t, ?_⟩⟩
  have : Subsingleton (PrimeSpectrum K) := inferInstance
  exact Subsingleton.elim (α := PrimeSpectrum K) _ _

theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X}
    {q : Y' ⟶ Y} (hsq : IsPullback p f' f q) [Surjective q] [GeometricallyConnected f'] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd hz ↦ ?_⟩
  have hb : Surjective (pullback.snd q y) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback q y) inferInstance
  have k : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  obtain ⟨z, -⟩ := (pullback.snd q y).surjective k
  let t := (pullback q y).fromSpecResidueField z
  let L := (pullback q y).residueField z
  let W := pullback f' (t ≫ pullback.fst q y)
  have hW : ConnectedSpace W :=
    GeometricallyConnected.geometrically_connectedSpace (f := f') (t ≫ pullback.fst q y)
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hbig : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.fst q y) ≫ q) := (IsPullback.of_hasPullback _ _).paste_horiz hsq
  have hbig' : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.snd q y) ≫ y) := by
    convert hbig using 1
    simp [pullback.condition]
  let w : W ⟶ Z := hz.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _ ≫ t ≫ pullback.snd q y) (by
    simpa using hbig'.w)
  have hw : IsPullback w (pullback.snd f' (t ≫ pullback.fst q y)) snd (t ≫ pullback.snd q y) := by
    refine IsPullback.of_right (h₁₂ := fst) (v₁₃ := f) (h₂₂ := y) ?_ (by simp [w]) hz
    convert hbig' using 1
    simp [w]
  have hs : Surjective (t ≫ pullback.snd q y) := surjective_to_spec_field K _ (IsLocalRing.closedPoint L)
  have : Surjective w := MorphismProperty.of_isPullback (P := @Surjective) hw.flip hs
  exact w.surjective.connectedSpace w.continuous

theorem good_of_isPullback_finite_surjective : ∀ (X X' Y Y' : Scheme.{0}) (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X)
    (q : Y' ⟶ Y) (g : ℕ), IsPullback p f' f q → IsFinite q → Surjective q → SmoothOfRelativeDimension g f →
    GlobalTheory.DualCon.Good g f' → GlobalTheory.DualCon.Good g f := by
  intro X X' Y Y' f f' p q g hsq hq hqs hf hf'
  have := hf'.proper
  have := hf'.conn
  have : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hqs
  have : IsFinite p := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip hq
  have : IsProper (p ≫ f) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective p f
  have : IsSeparated f := GlobalTheory.NilProper.isSeparated_of_comp_surjective p f
  have : Smooth f := hf.smooth
  have : LocallyOfFiniteType f := inferInstance
  exact ⟨{}, hf, geometricallyConnected_of_isPullback hsq⟩

end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedDescendFiniteSurjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properSmoothGeomConnected_descend_finite_surjective : ∀ (X X' Y Y' : Scheme.{0}) (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X) (q : Y' ⟶ Y) (g : ℕ), IsPullback p f' f q → IsFinite q → Surjective q → SmoothOfRelativeDimension g f → GlobalTheory.DualCon.Good g f' → GlobalTheory.DualCon.Good g f := by
  first | exact @GlobalTheory.DualCon.good_of_isPullback_finite_surjective | exact GlobalTheory.DualCon.good_of_isPullback_finite_surjective | (intros; apply GlobalTheory.DualCon.good_of_isPullback_finite_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.Assemble

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_ev {U Y : Over S} {M : LB (A ⊗ U).left} (h : Fam A M) (u : Y ⟶ U) :
    Fam A (ev M (fst A Y) (snd A Y ≫ u)) := by
  have hN : (ev M (fst A Y) (snd A Y ≫ u)).IsLB := pull_isLB h.isLB _
  refine ⟨hN, (isAdditive_iff hN).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Z a a' _


omit [GrpObj A] in
theorem same_comp {T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) (z : Z ⟶ Y) :
    evc hN (fst A Z) (snd A Z ≫ z ≫ y) = evc hM (fst A Z) (snd A Z ≫ z ≫ u) := by
  have e := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM y u).1 h)
  simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using e

theorem exists_lift {S' : Over S} [IsFinite S'.hom] [Surjective S'.hom] {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ S) : Nonempty (Over.mk s ⟶ S') := by
  obtain ⟨t, ht⟩ := exists_lift_pt S'.hom s
  exact ⟨Over.homMk t ht⟩

theorem fibInj {B S' U : Over S} [IsFinite S'.hom] [Surjective S'.hom] {b : B ⟶ S'} {P : LB (A ⊗ B).left}
    (hP : Rep A b P) {M : LB (A ⊗ U).left} (hM : Fam A M) {j : U ⊗ S' ⟶ B} (hj : j ≫ b = snd U S')
    [IsOpenImmersion j.left] (h : Same A M P (fst U S') j) : FibInj A M := by
  intro K _ _ s Y y u u' huu
  obtain ⟨t⟩ := exists_lift (S' := S') s
  have : Mono j := (Over.forget S).mono_of_mono_map (show Mono j.left from inferInstance)
  have k : ∀ v : Y ⟶ U, evc hM.isLB (fst A Y) (snd A Y ≫ v) =
      evc hP.fam.isLB (fst A Y) (snd A Y ≫ lift v (y ≫ t) ≫ j) := fun v ↦ by
    simpa only [lift_fst] using same_comp hM.isLB hP.fam.isLB h (lift v (y ≫ t))
  have hN := fam_ev hM u
  have e : lift u (y ≫ t) ≫ j = lift u' (y ≫ t) ≫ j := by
    refine (hP.univ Y (y ≫ t) _ hN).unique ⟨by rw [Category.assoc, hj, lift_snd], ?_⟩
      ⟨by rw [Category.assoc, hj, lift_snd], ?_⟩
    · exact (cls_eq_iff hN.isLB (pull_isLB hP.fam.isLB _)).1 (k u)
    · exact (cls_eq_iff hN.isLB (pull_isLB hP.fam.isLB _)).1
        (((same_iff hM.isLB hM.isLB u u').1 huu).trans (k u'))
  have e' := congrArg (· ≫ fst U S') ((cancel_mono j).1 e)
  simpa only [lift_fst] using e'

theorem exists_point {B S' U : Over S} {P : LB (A ⊗ B).left} (hP : P.IsLB) {M : LB (A ⊗ U).left} (hM : M.IsLB)
    {j : U ⊗ S' ⟶ B} [IsOpenImmersion j.left] (h : Same A M P (fst U S') j) {K : Type} [Field K]
    {s : Sp K ⟶ S} {N : LB (A ⊗ Over.mk s).left} (hN : N.IsLB) (x : Over.mk s ⟶ B)
    (hx : LBIso N (ev P (fst A _) (snd A _ ≫ x))) (hr : x.left (default : PrimeSpectrum K) ∈ Set.range j.left) :
    ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  have hr' : Set.range x.left ⊆ Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) z default]
  have fac := IsOpenImmersion.lift_fac j.left x.left hr'
  let v : Over.mk s ⟶ U ⊗ S' := Over.homMk (IsOpenImmersion.lift j.left x.left hr') (by
    rw [← Over.w j, ← Category.assoc, fac]; exact Over.w x)
  have hv : v ≫ j = x := Over.OverMorphism.ext fac
  refine ⟨v ≫ fst U S', (same_id_iff hN hM _).2 ((cls_eq_iff hN (pull_isLB hM _)).1 ?_)⟩
  rw [(cls_eq_iff hN (pull_isLB hP _)).2 hx, cls_ev hP, cls_ev hM, same_comp hM hP h v, hv]

theorem isPullback_prod (X Y : Over S) : IsPullback (fst X Y) (snd X Y) (toUnit X) (toUnit Y) :=
  ⟨⟨toUnit_unique _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst c.snd) (fun _ ↦ lift_fst _ _)
    (fun _ ↦ lift_snd _ _) fun c m h₁ h₂ ↦ by ext <;> simp [h₁, h₂]⟩⟩

theorem toUnit_left (X : Over S) : (toUnit X).left = X.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit X))

end GlobalTheory.DualCon.Assemble

namespace GlobalTheory.DualCon
open Assemble

theorem hasRep_of_liftAt (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (B S' : Over (Sp R)) (b : B ⟶ S')
    (P : LB (A ⊗ B).left) (hf : IsFinite S'.hom) (hs : Surjective S'.hom) (hP : Rep A b P)
    (hb : GlobalTheory.DualCon.Good g b.left) (hl : ∀ x : B.left, LiftAt A g b P x) : HasRep A g (𝟙_ _) := by
  choose U M j hM hU hj ho hx h using hl
  have hc : ∀ x, IsChart A (M x) := fun x ↦
    GlobalTheory.T.openChart_of_smoothFamily_geomFibreInjective R A g hA hg (U x) (M x) (hU x) (hM x) (fibInj hP (hM x) (hj x) (h x))
  obtain ⟨B₀, P₀, i, hP₀, hi, hcov, -⟩ := GlobalTheory.T.glue_openCharts_additiveFamilies_representing (Sp R) A hA B.left U M hc (by
    intro K _ _ s N hN
    obtain ⟨t⟩ := exists_lift (S' := S') s
    obtain ⟨x, ⟨-, hxN⟩, -⟩ := hP.univ _ t N hN
    exact ⟨_, exists_point hP.fam.isLB (hM _).isLB (h _) hN.isLB x hxN (hx _)⟩)
  have hsm : SmoothOfRelativeDimension g B₀.hom := by
    have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension g)
      (Scheme.Cover.mkOfCovers B.left (fun x ↦ (U x).left) (fun x ↦ (i x).left) hcov hi) fun x ↦ ?_
    have e : (i x).left ≫ B₀.hom = (U x).hom := Over.w _
    exact (congrArg (@SmoothOfRelativeDimension g _ _) e).mpr (hU x)
  have hpb := isPullback_prod B₀ S'
  obtain ⟨e, he, -⟩ := rep_unique (Sp R) A B (B₀ ⊗ S') S' b P _ _ hP
    (GlobalTheory.T.rep_ev_of_isPullback (Sp R) A B₀ _ S' _ _ P₀ _ _ _ hP₀ hpb)
  have hpb' : IsPullback (e.hom ≫ fst B₀ S') b (toUnit B₀) (toUnit S') :=
    hpb.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [← he]) (by simp) (by simp)
  refine ⟨B₀, toUnit B₀, P₀, hP₀, GlobalTheory.T.properSmoothGeomConnected_descend_finite_surjective _ _ _ _ _ _ _ _ g (hpb'.map (Over.forget _)) ?_ ?_ ?_ hb⟩
  · exact (congrArg (@IsFinite _ _) (toUnit_left S')).mpr hf
  · exact (congrArg (@Surjective _ _) (toUnit_left S')).mpr hs
  · exact (congrArg (@SmoothOfRelativeDimension g _ _) (toUnit_left B₀)).mpr hsm

end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLiftStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representingScheme_of_finite_surjective_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (B S' : Over (Sp R)) (b : B ⟶ S') (P : LB (A ⊗ B).left), IsFinite S'.hom → Surjective S'.hom → Rep A b P → GlobalTheory.DualCon.Good g b.left → (∀ x : B.left, LiftAt A g b P x) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualCon.hasRep_of_liftAt | exact GlobalTheory.DualCon.hasRep_of_liftAt | (intros; apply GlobalTheory.DualCon.hasRep_of_liftAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchSecOfUnf
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open GlobalTheory.FlatDenom

noncomputable section

namespace GlobalTheory.FlatDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}


theorem framesOn_eq {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hgeo : FnAlgClosed (Xo := Xo) (c := c)) (Z : Comp Xo c) : ∃ k, framesOn U Z = {z | z.1 = k ∧ z.2 ∈ (U.X z.1).dom} := by
  obtain ⟨q, hq⟩ : ∃ q : U.Comp ≃ Comp Xo c, ∀ k (y : (U.X k).dom) (s : Sp (CAt σ)),
      GlobalTheory.AllWt.ptF (U.un k y) s ∈ (q k).1 :=
    GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU
      (fun k => GlobalTheory.CompBij.frames_nonempty _) hgeo
  refine ⟨q.symm Z, Set.ext fun ⟨k, y⟩ => ⟨?_, ?_⟩⟩
  · rintro ⟨hy, hl⟩
    refine ⟨?_, hy⟩
    have hk : q k = Z := by
      by_contra hne
      let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) (hq k ⟨y, hy⟩ s) (hl s)
    exact (Equiv.eq_symm_apply q).2 hk
  · rintro ⟨hk, hy⟩
    obtain rfl : k = q.symm Z := hk
    refine ⟨hy, fun s => ?_⟩
    have := hq (q.symm Z) ⟨y, hy⟩ s
    rwa [Equiv.apply_symm_apply] at this


open GlobalTheory.BdryUnit in
theorem const_length {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hgeo : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c} {τ : Psi H} {Y : Model Xo c (RingHom.id c.F)} {V : (Xo.XF c).Opens}
    {sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1} {f : Rul Xo c} (hV : (V : Set (Xo.XF c)) = Z)
    (hn : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig) (hh : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig) (hr : Reads Y V τ sig f) :
    ∃ b : ℝ, 0 < b ∧ homN U x (wtOf Dw (flatWt Dw τ) 0) f '' framesOn U Z = {b} := by
  obtain ⟨k, hk⟩ := framesOn_eq U hσ hU hgeo Z
  have hτ : relab c σ τ.1 ∈ (U.X k).Ψ := by
    refine ((hU.2.1 k).2 _).2 ?_
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext τ.2)).trans hσ0
  obtain ⟨a, ha⟩ := rdU_eq_mul_horizGen U hσ hU τ hn hh hr k hτ
  obtain ⟨y, hy⟩ := GlobalTheory.CompBij.frames_nonempty (U.X k)
  have hy' : (⟨k, y⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z := by rw [hk]; exact ⟨rfl, hy⟩
  have ha0 : a ≠ 0 := by
    obtain ⟨h1, h2⟩ := ha ⟨y, hy⟩ (hV ▸ hy'.2)
    exact left_ne_zero_of_mul (h2 ▸ h1)
  refine ⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 (U.X k).Gm.det‖),
    mul_pos (lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 ha0) (Real.sqrt_pos.2 (norm_pos_iff.2
      ((map_ne_zero _).2 (U.X k).Gm_det)))), image_eq_singleton_iff.2 ⟨⟨_, hy'⟩, ?_⟩⟩
  rintro ⟨k', y'⟩ hz
  have hz' := hz
  rw [hk] at hz'
  obtain ⟨rfl, hy₁⟩ : k' = k ∧ y' ∈ (U.X k').dom := hz'
  have h1 := (ha ⟨y', hy₁⟩ (hV ▸ hz.2)).2
  rw [← pnorm_horizGen (U.X k') ⟨_, hτ⟩ hy₁, homN, ptN, modelWt_flatWt U hσ hU τ k' hτ]
  simp only at h1
  simp only [Data.pnorm, h1, norm_mul, mul_assoc]

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}

theorem evR_sig_mul_inv (s : ArchSec U x Z (flatWt Dw τ)) {k : Type} [Field k] [Algebra c.F k] {y : FrPt Xo c k}
    (h : LiesOn Z y) : evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
  rw [← CompSplitPfB.cspB_evR_mul, s.mul_inv, evR_idem h (GlobalTheory.FlagTan.fromTest_of_isLocalRing y)]

theorem detLaw_sig (s : ArchSec U x Z (flatWt Dw τ)) : DetLaw Z s.sig τ.1 (conjEmb τ.1) :=
  ⟨s.sig_mem.1, fun _ _ _ z y _ h g₁ g₂ h₁ h₂ => GlobalTheory.FlatGL.evR_flat_chg τ s.sig_mem z y h g₁ g₂ h₁ h₂⟩

theorem detLaw_inv (s : ArchSec U x Z (flatWt Dw τ)) : DetLaw Z s.inv (conjEmb τ.1) τ.1 := by
  refine ⟨s.inv_mem.1, fun k _ _ z y hy h g₁ g₂ h₁ h₂ => ?_⟩
  have hz : LiesOn Z z := by
    have e : GlobalTheory.AllWt.ptF z = GlobalTheory.AllWt.ptF y := by
      apply pullback.hom_ext
      · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_fst, pullback.lift_fst, h]
      · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_snd, pullback.lift_snd]
    exact fun p => e ▸ hy p
  have k1 := GlobalTheory.FlatGL.evR_flat_chg τ s.sig_mem z y h g₂ g₁ h₂ h₁
  have k2 := evR_sig_mul_inv s hy
  have k3 := evR_sig_mul_inv s hz
  linear_combination (-(evR Xo c s.inv z * evR Xo c s.inv y)) * k1 + (g₂.det * evR Xo c s.inv y) * k3 -
    (g₁.det * evR Xo c s.inv z) * k2


set_option synthInstance.maxHeartbeats 400000 in
theorem archSec_denom (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (s : ArchSec U x Z (flatWt Dw τ))
    (hs : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) →
      (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0) :
    ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv) := by
  have hb : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) →
      (letI := io.toAlgebra; LiesOn Z y₀.1) →
      evI y₀ s.sig ∈ (algebraMap T.V T.Fr).range ∧ evI y₀ s.inv ∈ (algebraMap T.V T.Fr).range := by
    intro T io y₀ h1 h2
    letI := io.toAlgebra
    have h3 := hs T io y₀ h1 h2
    have h4 : evI y₀ s.sig * evI y₀ s.inv = 1 := evR_sig_mul_inv s h2
    have h5 := left_ne_zero_of_mul_eq_one h4
    have h6 := right_ne_zero_of_mul_eq_one h4
    rw [nval_of_ne h5, EReal.coe_eq_zero, Nat.cast_one, div_one, Int.cast_eq_zero] at h3
    have h7 := vV_mul (V := T.V) h5 h6
    rw [h4, show vV T.V (1 : T.Fr) = 0 by simp [vV], h3] at h7
    exact ⟨Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) h3.ge,
      Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) (by omega)⟩
  obtain ⟨m₁, hm₁, h₁⟩ := Cover.exists_denom hpq hA Z (detLaw_sig s) fun T io y₀ h1 h2 => (hb T io y₀ h1 h2).1
  obtain ⟨m₂, hm₂, h₂⟩ := Cover.exists_denom hpq hA Z (detLaw_inv s) fun T io y₀ h1 h2 => (hb T io y₀ h1 h2).2
  have hn : ∀ (n : ℕ), 0 < n → ∀ la, ∀ v ∈ valOn Z la, ∀ f : Rul Xo c, 0 ≤ v f → 0 ≤ v ((n : c.F) • f) := by
    intro n hn la v hv f hf
    rw [(isVal_valOn hv).smul _ _ (Nat.cast_ne_zero.2 hn.ne')]
    refine add_nonneg (EReal.coe_nonneg.2 ?_) hf
    have := Formalism.L2.Pj.vAdd_int_nonneg la (a := (n : 𝓞 c.F)) (by
      have : (n : c.F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      simpa using this)
    have h2 : 0 ≤ Formalism.BasicNotions.vAdd la (n : c.F) := by simpa using this
    exact_mod_cast h2
  refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun la v hv => ⟨?_, ?_⟩⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact hn _ hm₂ la v hv _ (h₁ la v hv)
  · rw [Nat.cast_mul, mul_smul]
    exact hn _ hm₁ la v hv _ (h₂ la v hv)

end GlobalTheory.FlatDenom


namespace GlobalTheory.FlatDenom

section Powers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)

def HasBddSec (la : GlobalTheory.AllWt.Weight Dw) : Prop :=
  ∃ (s : ArchSec U x Z la) (m : ℕ), 0 < m ∧ ∀ w, ∀ v ∈ valOn Z w, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv)

variable {U x Z} {la la' : GlobalTheory.AllWt.Weight Dw}

theorem homN_sig (s : ArchSec U x Z la) {σ : c.F →+* ℂ} {z} (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (wtOf Dw la 0) s.sig z = s.cInf σ := (image_eq_singleton_iff.1 (s.norm_inf σ)).2 z hz

theorem homN_inv (s : ArchSec U x Z la) {σ : c.F →+* ℂ} {z} (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (wtOf Dw (-la) 0) s.inv z = (s.cInf σ)⁻¹ := by
  have h := homN_mul (U (goodOf c σ)) x (even_wtOf (-la) 0) (even_wtOf la 0) s.inv s.sig z hz.1
  rw [← wtOf_add', neg_add_cancel, wtOf_zero, mul_comm s.inv, s.mul_inv, homN_sig s hz,
    homN_idem _ x hz.1 hz.2 (tested_of_homN_ne _ x hz.1 ((homN_sig s hz).symm ▸ (s.cInf_pos σ).ne'))] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem HasBddSec.neg (h : HasBddSec U x Z la) : HasBddSec U x Z (-la) := by
  obtain ⟨s, m, hm, h⟩ := h
  exact ⟨⟨s.inv, s.sig, exOf_neg la ▸ s.inv_mem, by rw [exOf_neg, neg_neg]; exact s.sig_mem, s.idem_inv, s.idem_sig,
    by rw [mul_comm, s.mul_inv], s.cInf⁻¹, fun σ => inv_pos.2 (s.cInf_pos σ), fun σ => image_eq_singleton_iff.2
      ⟨(image_eq_singleton_iff.1 (s.norm_inf σ)).1, fun z hz => homN_inv s hz⟩⟩, m, hm,
    fun w v hv => (h w v hv).symm⟩


set_option synthInstance.maxHeartbeats 400000 in
theorem HasBddSec.add (h : HasBddSec U x Z la) (h' : HasBddSec U x Z la') : HasBddSec U x Z (la + la') := by
  obtain ⟨s, m, hm, h⟩ := h
  obtain ⟨t, m', hm', h'⟩ := h'
  refine ⟨⟨s.sig * t.sig, s.inv * t.inv, exOf_add' la la' ▸ mul_mem_secZ s.sig_mem t.sig_mem,
    by rw [exOf_add', neg_add]; exact mul_mem_secZ s.inv_mem t.inv_mem, by rw [← mul_assoc, s.idem_sig],
    by rw [← mul_assoc, s.idem_inv], by rw [mul_mul_mul_comm, s.mul_inv, t.mul_inv, idem_mul_idem],
    s.cInf * t.cInf, fun σ => mul_pos (s.cInf_pos σ) (t.cInf_pos σ), fun σ => image_eq_singleton_iff.2
      ⟨(image_eq_singleton_iff.1 (s.norm_inf σ)).1, fun z hz => ?_⟩⟩, m * m', Nat.mul_pos hm hm', fun w v hv => ?_⟩
  · rw [wtOf_add', homN_mul _ x (even_wtOf _ _) (even_wtOf _ _) _ _ _ hz.1, homN_sig s hz, homN_sig t hz]; rfl
  · have hV := isVal_valOn hv
    constructor
    · show 0 ≤ v (_ • (s.sig * t.sig))
      rw [Nat.cast_mul, ← smul_mul_smul_comm, hV.mul]
      exact add_nonneg (h w v hv).1 (h' w v hv).1
    · show 0 ≤ v (_ • (s.inv * t.inv))
      rw [Nat.cast_mul, ← smul_mul_smul_comm, hV.mul]
      exact add_nonneg (h w v hv).2 (h' w v hv).2

theorem HasBddSec.zsmul (h : HasBddSec U x Z la) (n : ℤ) : HasBddSec U x Z (n • la) := by
  induction n using Int.induction_on with
  | zero => rw [zero_smul, ← add_neg_cancel la]; exact h.add h.neg
  | succ n ih => rw [add_smul, one_smul]; exact ih.add h
  | pred n ih => rw [sub_smul, one_smul, sub_eq_add_neg]; exact ih.add h.neg

end Powers

theorem exists_nat_vAdd {K : Type} [Field K] [NumberField K] {a : K} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ Formalism.BasicNotions.vAdd w ((n : K) * a) := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have := Algebra.IsAlgebraic.trans ℤ ℚ K
  obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_integral_multiple
  have hn : IsIntegral ℤ ((y.natAbs : K) * a) := by
    rw [zsmul_eq_mul] at hy
    rcases Int.natAbs_eq y with e | e
    · rw [e, Int.cast_natCast] at hy; exact hy
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at hy; simpa using hy.neg
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun w => ?_⟩
  exact Formalism.L2.Pj.vAdd_int_nonneg w (a := (⟨_, hn⟩ : 𝓞 K))
    (mul_ne_zero (Nat.cast_ne_zero.2 (Int.natAbs_pos.2 hy0).ne') ha)

end GlobalTheory.FlatDenom


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedExtensionOfSeriesPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedExtensionOfSeriesPair
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

noncomputable section

namespace GlobalTheory.Katz

theorem exists_rigMap (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d) :
    ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))),
      (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) →
        (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  classical
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₗ[k] (∀ n, G.A n ⊗[k] G.A n) :=
    LinearMap.pi fun n => (c.ev₂ n).toLinearMap
  let S : Submodule k (MvPowerSeries (Fin d ⊕ Fin d) k) := G.cocycles.comap L
  let T₀ : S →ₗ[k] G.cocycles := L.restrict (fun x hx => hx)
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  have hU := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1
  let U : (Fin d → k) →ₗ[k] G.omega :=
    { toFun := fun w => ⟨fun n => ∑ i, w i • dUnit (R := k) (c.x n i), hU w⟩
      map_add' := fun a b => Subtype.ext (funext fun n => by
        simp [add_smul, Finset.sum_add_distrib])
      map_smul' := fun r a => Subtype.ext (funext fun n => by
        simp [Finset.smul_sum, smul_smul]) }
  refine ⟨G.rigMk ∘ₗ T.prodMap U, fun s w z u hz hu => ?_⟩
  have hs : s ∈ S := by
    change L s ∈ G.cocycles
    have : L s = z.1 := funext fun n => (hz n).symm
    rw [this]; exact z.2
  have h1 : T s = z := by
    have := LinearMap.congr_fun hT ⟨s, hs⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    exact Subtype.ext (funext fun n => (hz n).symm)
  have h2 : U w = u := Subtype.ext (funext fun n => (hu n).symm)
  change G.rigMk (T s, U w) = G.rigMk (z, u)
  exact congrArg G.rigMk (Prod.ext h1 h2)

end GlobalTheory.Katz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedExtensionOfSeriesPairStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidifiedExtension_of_series_pair : ∀ (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  first | exact @GlobalTheory.Katz.exists_rigMap | exact GlobalTheory.Katz.exists_rigMap | (intros; apply GlobalTheory.Katz.exists_rigMap <;> assumption)
end
end
