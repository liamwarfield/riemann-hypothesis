module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfIntersectionMonoOfIsNef

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFubiniStudyBoxFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeGeometricDegreeOfIsNef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeGeometricDegreeOfIsNef
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef.RankNef

theorem rank_le_gdeg_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), P.L.IsNef D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  intro hAr hHS k _ X _ p D hX P hL J _ e x he hx hbox
  have hcz : CharZero X.functionField := by
    have := hX.charZero
    exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 this
  have htb : IsTranscendenceBasis ℤ x := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).2 x hx
  obtain ⟨A, hAamp, hAnef, s, hs, hs0⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hAr k X p D hX
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  let Q : Pair p := ⟨P.L, A, P.r, r', P.hr, hr'⟩
  have hQbox : ∀ c, boxFam e x c ∈ Q.H 1 0 := by
    intro c z i j hi _
    obtain ⟨j', hj'⟩ : ∃ j', z ∈ P.A.B.U j' := by
      have h1 : z ∈ (⨆ j, P.A.B.U j) := by rw [P.A.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 h1
    have h2 := hbox c z i j' hi hj'
    simpa [Pair.loc, Q] using h2
  have hbd : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ Q.Bl 1 0 (Real.exp u) :=
    fun c => GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX Q 1 0 _ (hQbox c)
  choose u hu0 hu using hbd
  set t₀ : ℝ := ∑ c, u c with ht₀
  have ht₀0 : 0 ≤ t₀ := Finset.sum_nonneg fun c _ => hu0 c
  have hBl : ∀ c, boxFam e x c ∈ Q.Bl 1 0 (Real.exp t₀) := fun c =>
    ⟨(hu c).1, fun σ y => ((hu c).2 σ y).trans
      (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c)))⟩
  obtain ⟨ε, hεinj, hεrange, hεnu, -⟩ := RepDict.rep_dict k X p Q 0 1 Q.A (Pair.rep_base k X p Q).2.1
  have hsm : ∀ w ∈ A.smallSec, ε w ∈ Q.Bl 0 1 1 := by
    intro w hw
    refine ⟨?_, fun σ y => ?_⟩
    · rw [← SetLike.mem_coe, ← hεrange]; exact ⟨w, rfl⟩
    · have hnn : 0 ≤ Q.nu 0 1 σ y (ε w) := by
        unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      have h2 : Q.nu 0 1 σ y (ε w) ^ 2 ≤ 1 := by rw [hεnu]; exact hw σ y
      exact (pow_le_one_iff_of_nonneg hnn two_ne_zero).1 h2
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ Q.Bl 0 1 1, g ≠ 0 := by
    by_cases h : ε s = 0
    · refine ⟨ε 0, hsm 0 (HermLB.zero_mem_smallSec _), fun h0 => hs0 ?_⟩
      exact (hεinj (h0.trans h.symm)).symm
    · exact ⟨ε s, hsm s hs, h⟩
  have key : ∀ n : ℕ, 0 < n →
      (D.factorial : ℝ) * ((Fintype.card J * n ^ D : ℕ) : ℝ) ≤ gdeg ((P.L.pow n).tens A) D := by
    intro n hn
    have hrep : Q.Rep (n : ℤ) 1 ((Q.L.pow n).tens Q.A) := by
      have h1 := Pair.rep_pow k X p Q 1 0 Q.L n (Pair.rep_base k X p Q).1
      have h2 := Pair.rep_tens k X p Q _ _ 0 1 _ _ h1 (Pair.rep_base k X p Q).2.1
      simpa using h2
    have hamp : IsAmpleLB ((P.L.pow n).tens A).B :=
      GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX (P.L.pow n) A
        (nefFib_of_isNef (GlobalTheory.NefPow.isNef_pow hAr k X p D hX P.L n hL)) hAamp
    have hsp : ((P.L.pow n).tens A).SemiPos D := (hL.semiPos.pow n).tens hAnef.semiPos
    have hvec : ∀ m : ℕ, 0 < m → ∃ v : Fin ((Fintype.card J * n ^ D) * m ^ D) → X.functionField,
        LinearIndependent ℤ v ∧ ∀ i, v i ∈ Q.Bl (m * (n : ℤ)) (m * 1) (Real.exp ((t₀ * n) * m)) := by
      intro m hm
      obtain ⟨v0, hv0, hv0s⟩ := GlobalTheory.T.exists_linearIndependent_products_function_field X.functionField D x htb J e he (n * m) (Nat.mul_pos hn hm)
      have hcard : Fintype.card J * (n * m) ^ D = (Fintype.card J * n ^ D) * m ^ D := by rw [mul_pow]; ring
      have hgm : g ^ m ∈ Q.H ((m : ℤ) * 0) ((m : ℤ) * 1) :=
        (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).1
      have hgm0 : g ^ m ≠ 0 := pow_ne_zero _ hg0
      refine ⟨fun i => v0 (Fin.cast hcard.symm i) * g ^ m, ?_, fun i => ?_⟩
      · have hli := hv0.map' (LinearMap.mulRight ℤ (g ^ m))
          (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hgm0))
        exact hli.comp _ (Fin.cast_injective _)
      · obtain ⟨w, a, ha, hw⟩ := hv0s (Fin.cast hcard.symm i)
        have hprod := GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt k X p Q D J e x 1 0 (Real.exp t₀) (Real.exp_pos _).le hBl (n * m) w a ha
        rw [← hw] at hprod
        obtain ⟨hmem, hnu⟩ := NuMul.mul_mem_H_and_nu_mul k X p Q _ _ _ _ _ _ hprod.1 hgm
        have e1 : (((n * m : ℕ) : ℤ) * 1 + (m : ℤ) * 0) = (m : ℤ) * n := by push_cast; ring
        have e2 : (((n * m : ℕ) : ℤ) * 0 + (m : ℤ) * 1) = (m : ℤ) * 1 := by push_cast; ring
        rw [e1, e2] at hmem hnu
        refine ⟨hmem, fun σ y => ?_⟩
        rw [hnu, (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).2 σ y]
        have hA1 := hprod.2 σ y
        have hB1 : Q.nu 0 1 σ y g ^ m ≤ 1 := by
          have hnn : 0 ≤ Q.nu 0 1 σ y g := by
            unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
          exact pow_le_one₀ hnn (hg.2 σ y)
        have hnn' : 0 ≤ Q.nu ((n * m : ℕ) * 1) ((n * m : ℕ) * 0) σ y (v0 (Fin.cast hcard.symm i)) := by
          unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        have hexp : Real.exp t₀ ^ (n * m) = Real.exp ((t₀ * n) * m) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        calc _ ≤ Real.exp t₀ ^ (n * m) * 1 := mul_le_mul hA1 hB1 (pow_nonneg (by unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) _) (pow_nonneg (Real.exp_pos _).le _)
          _ = _ := by rw [mul_one, hexp]
    have := GlobalTheory.T.factorial_mul_rank_le_degree_of_indep_small_sections hAr hHS k X p D hX Q n 1 _ hrep hamp hsp (Fintype.card J * n ^ D) (t₀ * n) hvec
    exact this
  have hlim := GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow hAr k X p D hX P.L A
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnD : (0 : ℝ) < (n : ℝ) ^ D := by positivity
  rw [le_div_iff₀ hnD]
  have := key n hn
  push_cast at this
  nlinarith [this]

end GlobalTheory.HSNef.RankNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeGeometricDegreeOfIsNefStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_le_geometricDegree_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), P.L.IsNef D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  first | exact @GlobalTheory.HSNef.RankNef.rank_le_gdeg_of_isNef | exact GlobalTheory.HSNef.RankNef.rank_le_gdeg_of_isNef | (intros; apply GlobalTheory.HSNef.RankNef.rank_le_gdeg_of_isNef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFubiniStudyRatFnsMemPairSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFubiniStudyRatFnsMemPairSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isFS_mem_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → ∃ P : Pair p, P.L = M ∧ ∀ j, f j ∈ P.H 1 0 := by
  intro k _ X _ p M J _ f w h
  obtain ⟨ρ, hρ, hreg, -⟩ := h
  refine ⟨⟨M, M, ρ, ρ, hρ, hρ⟩, rfl, fun j x i c hi _ => ?_⟩
  have e : Pair.loc ⟨M, M, ρ, ρ, hρ, hρ⟩ 1 0 (f j) i c = f j * (ρ i : X.functionField) := by
    simp [Pair.loc]
  rw [e]
  exact (hreg x i hi).1 j

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFubiniStudyRatFnsMemPairSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFubiniStudy_ratFns_mem_pairSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → ∃ P : Pair p, P.L = M ∧ ∀ j, f j ∈ P.H 1 0 := by
  first | exact @GlobalTheory.HSNef.isFS_mem_pair | exact GlobalTheory.HSNef.isFS_mem_pair | (intros; apply GlobalTheory.HSNef.isFS_mem_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFubiniStudyBoxFamily
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fs_box_rank_le : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J]
    (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ),
    LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) →
    IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  intro hAr hHS k _ X _ p D hD M J _ e x w he hx hw hFS
  have hNef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hAr k X p D hD M _ (boxFam e x) w hFS hw
  obtain ⟨P, hPL, hmem⟩ := GlobalTheory.T.isFubiniStudy_ratFns_mem_pairSections k X p M _ (boxFam e x) w hFS
  subst hPL
  exact GlobalTheory.T.rank_le_geometricDegree_of_isNef hAr hHS k X p D hD P hNef J e x he hx hmem

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFubiniStudyBoxFamilyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_le_fubiniStudy_boxFamily : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) → IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  first | exact @GlobalTheory.HSNef.fs_box_rank_le | exact GlobalTheory.HSNef.fs_box_rank_le | (intros; apply GlobalTheory.HSNef.fs_box_rank_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamily
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_ne_zero {x : X} {h : X.functionField} (hh : UnitAt x h) : h ≠ 0 := by
  obtain ⟨b, hb, rfl⟩ := hh
  intro e
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField (b * ↑hb.unit⁻¹) = 1 := by
    rw [IsUnit.mul_val_inv, map_one]
  rw [map_mul, e, zero_mul] at h1
  exact zero_ne_one h1

theorem regAt_div_unitAt {x : X} {g h : X.functionField} (hg : RegAt x g) (hh : UnitAt x h) :
    RegAt x (g / h) := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb, hbh⟩ := hh
  refine ⟨a * ↑hb.unit⁻¹, ?_⟩
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField b *
      algebraMap (X.presheaf.stalk x) X.functionField ↑hb.unit⁻¹ = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [map_mul, ha, div_eq_mul_inv, ← hbh, eq_inv_of_mul_eq_one_right h1]

theorem le_shift_of_isFS_sub : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ)
      (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' →
      (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  intro k _ X _ p M M' J J' _ _ f w w' ι Δ hι hM hM' hw
  rw [GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients]
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨ρ', hρ', hreg', hφ'⟩ := hM'
  simp only [Function.comp_apply] at hreg' hφ'

  have hq : ∀ (x : X) c d (j' : J'), UnitAt x (f (ι j') * (ρ' d : X.functionField)) →
      (ρ c : X.functionField) / (ρ' d : X.functionField) =
        f (ι j') * (ρ c : X.functionField) / (f (ι j') * (ρ' d : X.functionField)) := by
    intro x c d j' hu
    have hf : f (ι j') ≠ 0 := left_ne_zero_of_mul (unitAt_ne_zero hu)
    rw [mul_div_mul_left _ _ hf]
  have hτ : ∀ (x : X) c d, x ∈ M.B.U c → x ∈ M'.B.U d →
      RegAt x ((ρ c : X.functionField) / (ρ' d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨-, j', hj'⟩ := hreg' x d hd
    rw [hq x c d j' hj']
    exact regAt_div_unitAt ((hreg x c hc).1 (ι j')) hj'
  refine ⟨ρ, ρ', hρ, hρ', hτ, ?_⟩
  intro σ y c d hc hd
  have hc' := mem_ptsIn.1 hc
  have hd' := mem_ptsIn.1 hd
  set τ : X.functionField := (ρ c : X.functionField) / (ρ' d : X.functionField) with hτdef
  have hτr : RegAt (under y) τ := hτ _ c d hc' hd'

  have hval : ∀ j' : J', ratVal (f (ι j') * (ρ c : X.functionField)) y =
      ratVal τ y * ratVal (f (ι j') * (ρ' d : X.functionField)) y := by
    intro j'
    have e : f (ι j') * (ρ c : X.functionField) = τ * (f (ι j') * (ρ' d : X.functionField)) := by
      rw [hτdef]; field_simp
    rw [e, ratVal_mul hτr ((hreg' _ d hd').1 j')]
  set S : ℝ := ∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) with hS
  set S' : ℝ := ∑ j', ‖ratVal (f (ι j') * (ρ' d : X.functionField)) y‖ ^ 2 * Real.exp (2 * w' j') with hS'
  have e1 : (M.φ σ).φ c y = Real.log S := hφ σ y c hc
  have e2 : ((M'.shift (fun _ => Δ) fun _ => rfl).φ σ).φ d y = Real.log S' + 2 * Δ := by
    change (M'.φ σ).φ d y + 2 * Δ = _
    rw [hφ' σ y d hd]
  have hS'pos : 0 < S' := by
    obtain ⟨-, j₀, hj₀⟩ := hreg' _ d hd'
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨j₀, Finset.mem_univ _, ?_⟩
    have : ratVal (f (ι j₀) * (ρ' d : X.functionField)) y ≠ 0 := ratVal_ne_zero hj₀
    have : 0 < ‖ratVal (f (ι j₀) * (ρ' d : X.functionField)) y‖ := norm_pos_iff.2 this
    positivity
  set t : ℝ := ‖ratVal τ y‖ with ht
  have hineq : t ^ 2 * Real.exp (2 * Δ) * S' ≤ S := by
    classical
    calc t ^ 2 * Real.exp (2 * Δ) * S'
        = ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * (w' j' + Δ)) := by
          rw [hS', Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [hval, norm_mul, ← ht, mul_add, Real.exp_add]; ring
      _ ≤ ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w (ι j')) := by
          refine Finset.sum_le_sum fun j' _ => ?_
          gcongr
          exact hw j'
      _ = ∑ j ∈ Finset.univ.image ι, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) :=
          by rw [Finset.sum_image (fun a _ b _ h => hι h)]
      _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity
  rw [e1, e2]
  have ht0 : 0 ≤ t := norm_nonneg _
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact zero_le_one
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hineq
  have hE : Real.exp (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) ^ 2 = S' * Real.exp (2 * Δ) / S := by
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) = (Real.log S' + 2 * Δ) - Real.log S := by
      push_cast; ring
    rw [this, Real.exp_sub, Real.exp_add, Real.exp_log hS'pos, Real.exp_log hSpos]
  rw [← sq_le_one_iff₀ (by positivity), mul_pow, hE]
  rw [← mul_div_assoc, div_le_one hSpos]
  linarith [hineq]

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamilyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ) (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' → (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  first | exact @GlobalTheory.HSNef.le_shift_of_isFS_sub | exact GlobalTheory.HSNef.le_shift_of_isFS_sub | (intros; apply GlobalTheory.HSNef.le_shift_of_isFS_sub <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem Total.comp {X : Scheme.{0}} [IsIntegral X] {J J' : Type} {f : J → X.functionField} (h : Total f)
    (ι : J' → J) : Total (f ∘ ι) :=
  ⟨fun j => h.1 (ι j), fun x j l => h.2 x (ι j) (ι l)⟩

theorem selfInter_nonneg_of_isFS (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) {k : Type} [CommRing k]
    {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {M : HermLB p} {J : Type} [Fintype J]
    {f : J → X.functionField} {w : J → ℝ} (hM : IsFS M f w) (hw : ∀ j, 0 ≤ w j) {μ : ℝ} (hμ : M.IsSelfInter μ) :
    0 ≤ μ := by
  have hnef := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M J f w hM hw
  have hht := (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX M hnef).2
  obtain ⟨h, hh, rfl⟩ := hμ
  exact hht h hh _

theorem levels_le_selfInter (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (x : Fin D → X.functionField) (Δ : ℝ)
    (hx : AlgebraicIndependent ℤ x) (hΔ : 0 < Δ) :
    ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ),
      LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) →
      M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ∑ j, (n j : ℝ) ≤ μ := by
  intro N
  induction N with
  | zero =>
    intro J _ e n M μ _ hn _ hM hμ
    have h0 : ∀ j, n j = 0 := fun j => Nat.le_zero.1 (hn j)
    simp only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
    exact selfInter_nonneg_of_isFS hC hA hS hX hM (fun c => by simp [h0]) hμ
  | succ N ih =>
    intro J _ e n M μ he hn ht hM hμ
    classical
    have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
    by_cases hJ : ∀ j, n j = 0
    · simp only [hJ, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
      exact selfInter_nonneg_of_isFS hC hA hS hX hM hw0 hμ
    push_neg at hJ
    obtain ⟨j₀, hj₀⟩ := hJ
    let J' := {j // 1 ≤ n j}
    let e' : J' → X.functionField := fun j => e j.1
    let n' : J' → ℕ := fun j => n j.1 - 1
    let ι : J' × Finset (Fin D) → J × Finset (Fin D) := fun c => (c.1.1, c.2)
    have hι : Function.Injective ι := by
      rintro ⟨⟨a, ha⟩, s⟩ ⟨⟨b, hb⟩, t⟩ h
      simp only [ι, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hbox : boxFam e' x = boxFam e x ∘ ι := rfl
    haveI : Nonempty (J' × Finset (Fin D)) := ⟨(⟨j₀, Nat.one_le_iff_ne_zero.2 hj₀⟩, ∅)⟩
    have ht' : Total (boxFam e' x) := hbox ▸ ht.comp ι
    obtain ⟨M', hM'⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k X p (J' × Finset (Fin D)) (boxFam e' x) (fun c => (n' c.1 : ℝ) * Δ) ht'
    obtain ⟨h', hh'⟩ := (hC.arExists k X p D hX).1 M'
    have hμ' : M'.IsSelfInter (h' (genericPoint X)) := ⟨h', hh', rfl⟩
    have he' : LinearIndependent ℤ e' := he.comp _ Subtype.val_injective
    have hn' : ∀ j, n' j ≤ N := fun j => by
      have := hn j.1
      simp only [n']
      omega
    have IH := ih J' e' n' M' _ he' hn' ht' hM' hμ'
    have hw0' : ∀ c : J' × Finset (Fin D), 0 ≤ (n' c.1 : ℝ) * Δ := fun c => by positivity
    have hstep : ∀ c : J' × Finset (Fin D), (n' c.1 : ℝ) * Δ + Δ ≤ (n (ι c).1 : ℝ) * Δ := fun c => by
      have h1 := c.1.2
      simp only [n', ι]
      rw [Nat.cast_sub h1]
      push_cast
      linarith
    have hle : Le (M'.shift (fun _ => Δ) fun _ => rfl) M :=
      GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family k X p M M' (J × Finset (Fin D)) (J' × Finset (Fin D)) (boxFam e x) (fun c => (n c.1 : ℝ) * Δ)
        (fun c => (n' c.1 : ℝ) * Δ) ι Δ hι hM (hbox ▸ hM') hstep
    have hnefM := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M _ _ _ hM hw0
    have hnefM' := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M' _ _ _ hM' hw0'
    have hnefS := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX M' Δ hΔ.le hnefM'
    have hsh := hC.arShift k X p D hX M' _ Δ hμ'
    have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hC hA hS k X p D hX M _ μ _ hnefM hnefS hle hμ hsh
    have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M' J' e' x (fun c => (n' c.1 : ℝ) * Δ) he' hx hw0' hM'
    have hsum : ∑ j, (n j : ℝ) = ∑ j : J', (n' j : ℝ) + Fintype.card J' := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 1 ≤ n j) (fun j => (n j : ℝ))]
      have h2 : ∑ j : {j // ¬ 1 ≤ n j}, (n j.1 : ℝ) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          have := j.2
          have : n j.1 = 0 := by omega
          simp [this]
      rw [h2, add_zero]
      have h3 : ∀ j : J', (n j.1 : ℝ) = (n' j : ℝ) + 1 := fun j => by
        simp only [n']
        rw [Nat.cast_sub j.2]
        ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rfl
    have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J' ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := by
      calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J' = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J') := by
            rw [hf]; ring
        _ ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := mul_le_mul_of_nonneg_left hrk (by positivity)
    rw [hsum, mul_add]
    linarith

theorem chain_moving_parts : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  intro hC hA hS k _ X _ p D hX x Δ hx hΔ N J _ e n M μ he hn ht hM hμ
  have key := levels_le_selfInter hC hA hS k X p D hX x Δ hx hΔ N J e n M μ he hn ht hM hμ
  have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
  have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M J e x (fun c => (n c.1 : ℝ) * Δ) he hx hw0 hM
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J ≤ ((D : ℝ) + 1) * Δ * gdeg M D := by
    calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J) := by
          rw [hf]; ring
      _ ≤ ((D : ℝ) + 1) * Δ * gdeg M D := mul_le_mul_of_nonneg_left hrk (by positivity)
  have hsum : ((∑ j, (n j + 1) : ℕ) : ℝ) = ∑ j, (n j : ℝ) + Fintype.card J := by
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum, mul_add]
  linarith

end GlobalTheory.HSNef
