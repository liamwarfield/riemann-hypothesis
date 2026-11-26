module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstTwistedSumFockVectorsPrincipalDatum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalLevelLeLevelCharactersAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalLevelLeLevelCharactersAgree
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatVecSum

theorem princ_levJ_le_levLam_eq : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ hle : (GlobalTheory.FlatVecSum.princ B).levJ ψ ≤ B.levJ ψ, ∀ (k : Bridge.Gf S) (hk : k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ),
      (((GlobalTheory.FlatVecSum.princ B).levLam ψ ⟨k, hk⟩ : ℂˣ) : ℂ) = ((B.levLam ψ ⟨k, hle hk⟩ : ℂˣ) : ℂ) := by
  intro D S T B _ ψ _
  have hle : (GlobalTheory.FlatVecSum.princ B).levJ ψ ≤ B.levJ ψ := by
    intro k hk
    obtain ⟨h1, h2⟩ := hk
    refine ⟨h1, ?_⟩
    have h2' : Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _ ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) := h2
    rw [Subgroup.mem_bot.1 h2']
    exact Subgroup.one_mem _
  refine ⟨hle, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hk
  have h2' : Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _ ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) := h2
  have e := Subgroup.mem_bot.1 h2'
  show ((Formalism.L2.DIV.levFn B.F.βS ((GlobalTheory.FlatVecSum.princ B).levS ψ) _ : ℂˣ) : ℂ) =
    ((Formalism.L2.DIV.levFn B.F.βS (B.levS ψ) _ : ℂˣ) : ℂ)
  unfold Formalism.L2.DIV.levFn
  congr 2
  · congr 1
    · show Formalism.L2.DIV.ext1 (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) (⇑(1 : _ →* ℂˣ))
          (Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _) = Formalism.L2.DIV.ext1 B.G.P.H B.G.P.chi (Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _)
      have key : ∀ y, y = Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) ((Formalism.UG.bc (Lev.swapAE D)) ((finHom S).range.subtype k)) →
          Formalism.L2.DIV.ext1 (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) (⇑(1 : _ →* ℂˣ)) y =
            Formalism.L2.DIV.ext1 B.G.P.H B.G.P.chi y := by
        rintro y rfl
        rw [e]
        exact (Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ (1 : _ →* ℂˣ)).trans (Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one B.G.P.H B.G.P.chi).symm
      exact key _ rfl

end GlobalTheory.FlatVecSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalLevelLeLevelCharactersAgreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_le_level_characters_agree : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ hle : (GlobalTheory.FlatVecSum.princ B).levJ ψ ≤ B.levJ ψ, ∀ (k : Bridge.Gf S) (hk : k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ),
      (((GlobalTheory.FlatVecSum.princ B).levLam ψ ⟨k, hk⟩ : ℂˣ) : ℂ) = ((B.levLam ψ ⟨k, hle hk⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.FlatVecSum.princ_levJ_le_levLam_eq | exact GlobalTheory.FlatVecSum.princ_levJ_le_levLam_eq | (intros; apply GlobalTheory.FlatVecSum.princ_levJ_le_levLam_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumTermsInvariantPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumTermsInvariantPrincipalLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.PrincClassSum

theorem fin_symm {D : D7} (S : HSp D) (y : Bridge.Gf S) :
    finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) = y :=
  (GlobalTheory.ClassRegroup.finEquiv S).apply_symm_apply y

theorem left_inv {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ψ : Twist D Circle) (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ω : PairRep S T) (hω : B.IsWeil ψ.chi ω) {F : Bridge.Gf S → _} (hF : F ∈ B.formsC ψ)
    (g : GA D T) (γ : GQ S) (y : Bridge.Gf S) :
    series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
        (F (Bridge.ratF S γ * y)) g =
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  have e : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S) =
      Bridge.ratF S γ * finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) *
        ((1 : (GlobalTheory.FlatVecSum.princ B).levJ ψ) : Bridge.Gf S) := by
    rw [fin_symm, fin_symm, OneMemClass.coe_one, mul_one]
  have hm := GlobalTheory.BaseClassSum.series_move (GlobalTheory.FlatVecSum.princ_good hB) hS hψ hQ hω (Subtype.property _) (Subtype.property _)
    γ 1 e (F (Bridge.ratF S γ * y))
  have hl := (B.mem_formsC.1 hF).2 γ y 1
  rw [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at hl
  have hinv : B.act ((γ⁻¹ : GQ S) : GA D S) (B.act (γ : GA D S) (F y)) = F y := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [map_one, Units.val_one, inv_one, one_smul] at hm
  rw [hl] at hm ⊢
  rw [show (GlobalTheory.FlatVecSum.princ B).act = B.act from rfl, hinv] at hm
  exact congrFun hm g

set_option maxHeartbeats 8000000 in
theorem right_inv {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ψ : Twist D Circle) (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ω : PairRep S T) (hω : B.IsWeil ψ.chi ω) {F : Bridge.Gf S → _} (hF : F ∈ B.formsC ψ)
    (g : GA D T) (k : Bridge.Gf S) (hk : k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) (y : Bridge.Gf S) :
    series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
        (F (y * k)) g =
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  obtain ⟨hle, hlam⟩ := GlobalTheory.T.principalLevel_le_level_characters_agree B hB ψ hQ
  have e : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S) =
      Bridge.ratF S 1 * finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) *
        ((⟨k, hk⟩ : (GlobalTheory.FlatVecSum.princ B).levJ ψ) : Bridge.Gf S) := by
    rw [fin_symm, fin_symm, (Bridge.ratF S).map_one, one_mul]
  have hm := GlobalTheory.BaseClassSum.series_move (GlobalTheory.FlatVecSum.princ_good hB) hS hψ hQ hω (Subtype.property _) (Subtype.property _)
    1 ⟨k, hk⟩ e (F (y * k))
  have hl := (B.mem_formsC.1 hF).2 1 y ⟨k, hle hk⟩
  rw [(Bridge.ratF S).map_one, one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply] at hl
  rw [show (GlobalTheory.FlatVecSum.princ B).act = B.act from rfl, inv_one, OneMemClass.coe_one, map_one,
    Module.End.one_apply, hlam k hk] at hm
  rw [hl] at hm ⊢
  rw [LinearMap.map_smul, LinearMap.map_smul, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at hm
  rw [LinearMap.map_smul]
  exact congrFun hm g

theorem terms_inv : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ F ∈ B.formsC ψ, ∀ g : GA D T,
      (∀ (γ : GQ S) (y : Bridge.Gf S),
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
          (F (Bridge.ratF S γ * y)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g) ∧
      ∀ k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ, ∀ y : Bridge.Gf S,
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
          (F (y * k)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g :=
  fun B hB hS ψ hψ hQ ω hω _ hF g =>
    ⟨fun γ y => left_inv B hB hS ψ hψ hQ ω hω hF g γ y, fun k hk y => right_inv B hB hS ψ hψ hQ ω hω hF g k hk y⟩

end GlobalTheory.PrincClassSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumTermsInvariantPrincipalLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSumTerms_invariant_principalLevel : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ F ∈ B.formsC ψ, ∀ g : GA D T,
      (∀ (γ : GQ S) (y : Bridge.Gf S),
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
          (F (Bridge.ratF S γ * y)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g) ∧
      ∀ k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ, ∀ y : Bridge.Gf S,
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
          (F (y * k)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  first | exact @GlobalTheory.PrincClassSum.terms_inv | exact GlobalTheory.PrincClassSum.terms_inv | (intros; apply GlobalTheory.PrincClassSum.terms_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCosetRepresentativesLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowerRightBlockMulBlockTriangular
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix

namespace GlobalTheory.FirstBlocksReduction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ExportSeries GlobalTheory.FlatVecSum

variable {D : D7} {S T : HSp D}
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem exists_reps {G X : Type} [Group G] (J J' : Subgroup G) (φ : G → X) (A : Set X) (hA : A.Finite)
    (hφ : ∀ κ ∈ J, φ κ ∈ A) (h : ∀ u ∈ J, ∀ κ ∈ J, u⁻¹ * κ ∈ J' ↔ φ u = φ κ) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ J) ∧ ∀ κ ∈ J, ∃! u : G, u ∈ F ∧ u⁻¹ * κ ∈ J' := by
  classical
  have hfin : (φ '' (J : Set G)).Finite := hA.subset (by rintro _ ⟨κ, hκ, rfl⟩; exact hφ κ hκ)
  have hs : ∀ x : ↥(φ '' (J : Set G)), ∃ u, u ∈ J ∧ φ u = x.1 := fun x => x.2
  choose s hsJ hsφ using hs
  haveI := hfin.fintype
  refine ⟨Finset.univ.image s, fun u hu => ?_, fun κ hκ => ⟨s ⟨φ κ, κ, hκ, rfl⟩, ⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    exact hsJ x
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · exact (h _ (hsJ _) _ hκ).2 (hsφ _)
  · rintro u ⟨hu, hu'⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    congr 1
    exact Subtype.ext ((hsφ x).symm.trans ((h _ (hsJ x) _ hκ).1 hu'))

theorem extension_by_one_mul {G H : Type} [Group G] [Monoid H] (K : Subgroup G) (f : K →* H) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    ext1 K f (a * b) = ext1 K f a * ext1 K f b := by
  unfold ext1
  rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left (mul_mem ha hb), ← map_mul]
  rfl

theorem lowerRightBlock_mul_blockTriangular {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) {a b : GL (Fin n) κ} (ha : a ∈ blockTri (blk2 r))
    (hb : b ∈ blockTri (blk2 r)) : upperLeftBlock hr (a * b) = upperLeftBlock hr a * upperLeftBlock hr b :=
  extension_by_one_mul _ _ ha hb

def firstBlocks (B : Base S T) (ψ : Twist D Circle) (k : Bridge.Gf S) : G0 B.G.Pg T.rank :=
  rTup B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1)

theorem firstBlocks_mul (B : Base S T) (ψ : Twist D Circle) {a b : Bridge.Gf S} (ha : a ∈ B.levJ ψ) (hb : b ∈ B.levJ ψ) :
    firstBlocks B ψ (a * b) = firstBlocks B ψ a * firstBlocks B ψ b := by
  have pa := lev_le_parLev ha
  have pb := lev_le_parLev hb
  funext PP
  show upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) (a.1 * b.1))) =
    upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1)) * upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1))
  have e : redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1 * Formalism.UG.bc (Lev.swapAE D) b.1) =
      redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1) * redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1) :=
    extension_by_one_mul (St B.F.βS) (redAt B.F.βS PP.1) (Base.mem_St_of_mem_levJ ha) (Base.mem_St_of_mem_levJ hb)
  rw [map_mul, e]
  exact lowerRightBlock_mul_blockTriangular _ (blockTri_blkOf_le _ _ (parLev_g pa PP.2)) (blockTri_blkOf_le _ _ (parLev_g pb PP.2))

theorem mem_princ_iff (B : Base S T) (ψ : Twist D Circle) {k : Bridge.Gf S} (hk : k ∈ B.levJ ψ) :
    k ∈ (princ B).levJ ψ ↔ firstBlocks B ψ k = 1 :=
  ⟨fun h => Subgroup.mem_bot.1 h.2, fun h => ⟨mem_parLev.2 (by exact mem_parLev.1 hk.1), Subgroup.mem_bot.2 h⟩⟩

theorem exists_reps_levJ : ∀ {D : Formalism.BasicNotions.D7} {S T : Formalism.BasicNotions.TH.HSp D} (B : GlobalTheory.ExportSeries.Base S T), GlobalTheory.ExportSeries.Base.Good B → ∀ (ψ : GlobalTheory.ExportSeries.Twist D Circle), GlobalTheory.ExportSeries.Base.admitted B (GlobalTheory.ExportSeries.Twist.Q ψ) → ∃ (F : Finset ↥(Formalism.IndefR.Bridge.Gf S)), (∀ u ∈ F, u ∈ GlobalTheory.ExportSeries.Base.levJ B ψ) ∧ ∀ κ ∈ GlobalTheory.ExportSeries.Base.levJ B ψ, ∃! u : ↥(Formalism.IndefR.Bridge.Gf S), u ∈ F ∧ u⁻¹ * κ ∈ GlobalTheory.ExportSeries.Base.levJ (GlobalTheory.FlatVecSum.princ B) ψ := by
  intro D S T B _ ψ _
  refine exists_reps _ _ (firstBlocks B ψ) (B.G.P.H : Set _) (Set.finite_coe_iff.1 (finite_H B.G.P)) (fun κ hκ => hκ.2)
    fun u hu κ hκ => ?_
  have hm := mul_mem (inv_mem hu) hκ
  have e := firstBlocks_mul B ψ hu hm
  rw [mul_inv_cancel_left] at e
  rw [mem_princ_iff B ψ hm, e]
  exact left_eq_mul.symm

end GlobalTheory.FirstBlocksReduction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCosetRepresentativesLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.LevReps

theorem reps : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ F : Finset (Bridge.Gf S), (∀ u ∈ F, u ∈ B.levJ ψ) ∧
      ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ := by
  first
  | exact @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | (apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ ..)

end GlobalTheory.LevReps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCosetRepresentativesLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_coset_representatives_level : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ F : Finset (Bridge.Gf S), (∀ u ∈ F, u ∈ B.levJ ψ) ∧
      ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ := by
  first | exact @GlobalTheory.LevReps.reps | exact GlobalTheory.LevReps.reps | (intros; apply GlobalTheory.LevReps.reps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumRegroupFinerLevelCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumRegroupFinerLevelCosets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.ClassRefineBridge

open GlobalTheory.ClassRefine
open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

theorem injective_of_isReps {J : Subgroup G} {I : Type} {y : I → G} (hy : Bridge.IsReps ι J y) :
    Function.Injective y := by
  intro i j hij
  have h1 : ∃ (γ : Γ) (k : J), y i = ι γ * y i * k := ⟨1, 1, by simp⟩
  have h2 : ∃ (γ : Γ) (k : J), y i = ι γ * y j * k := ⟨1, 1, by simp [hij]⟩
  exact (hy (y i)).unique h1 h2

theorem image_reps {J : Subgroup G} {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι J y) :
    ∀ g : G, ∃! t, t ∈ Finset.univ.image y ∧ ∃ (γ : ι.range) (κ : G), κ ∈ J ∧ g = (γ : G) * t * κ := by
  intro g
  obtain ⟨i, ⟨γ, k, e⟩, hu⟩ := hy g
  refine ⟨y i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ⟨ι γ, γ, rfl⟩, k, k.2, e⟩, ?_⟩
  rintro t ⟨ht, ⟨_, δ, rfl⟩, κ, hκ, e'⟩
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
  rw [hu j ⟨δ, ⟨κ, hκ⟩, e'⟩]

theorem card_stab_eq (hι : Function.Injective ι) (J : Subgroup G) (t : G) :
    Nat.card (Bridge.stab ι J t) = Nat.card (stabQ ι.range J t) := by
  refine Nat.card_congr (Equiv.ofBijective (fun γ => ⟨⟨ι γ, γ, rfl⟩, ?_⟩) ⟨?_, ?_⟩)
  · rw [mem_stabQ]; exact (Bridge.mem_stab ι).1 γ.2
  · intro a b h
    apply Subtype.ext
    apply hι
    have := congrArg (fun x : stabQ ι.range J t => ((x : ι.range) : G)) h
    simpa using this
  · rintro ⟨⟨_, γ, rfl⟩, hq⟩
    refine ⟨⟨γ, (Bridge.mem_stab ι).2 (mem_stabQ.1 hq)⟩, rfl⟩

theorem sum_image_eq {I : Type} [Fintype I] {y : I → G} (hy : Function.Injective y) (f : G → ℂ) :
    ∑ i, f (y i) = ∑ t ∈ Finset.univ.image y, f t := by
  rw [Finset.sum_image (fun a _ b _ h => hy h)]

theorem sum_isReps_refine : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G), Function.Injective ι → ∀ {J J₀ : Subgroup G}, J₀ ≤ J →
    ∀ {F : Finset G}, (∀ u ∈ F, u ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J₀) →
    ∀ {I₀ : Type} [Fintype I₀] (y₀ : I₀ → G), Bridge.IsReps ι J₀ y₀ → ∀ {I : Type} [Fintype I] (y : I → G), Bridge.IsReps ι J y →
    ∀ (Φ : G → ℂ), (∀ γ g, Φ (ι γ * g) = Φ g) → (∀ k ∈ J₀, ∀ g, Φ (g * k) = Φ g) →
    ∑ i, ((Nat.card (Bridge.stab ι J₀ (y₀ i)) : ℂ))⁻¹ * Φ (y₀ i) =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ∑ u ∈ F, Φ (y i * u) := by
  intro G Γ _ _ ι hι J J₀ hJ F hF hFu I₀ _ y₀ hy₀ I _ y hy Φ hl hr
  have key := sum_classReps_refine (Q := ι.range) hJ (image_reps ι hy) (image_reps ι hy₀) Φ
    (by rintro ⟨_, γ, rfl⟩ g; exact hl γ g) hr hF hFu
  simp only [card_stab_eq ι hι]
  rw [sum_image_eq (injective_of_isReps ι hy₀) (fun t => ((Nat.card (stabQ ι.range J₀ t) : ℂ))⁻¹ * Φ t),
    sum_image_eq (injective_of_isReps ι hy) (fun t => ((Nat.card (stabQ ι.range J t) : ℂ))⁻¹ * ∑ u ∈ F, Φ (t * u))]
  exact key

end GlobalTheory.ClassRefineBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumRegroupFinerLevelCosetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_regroup_finerLevel_cosets : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G), Function.Injective ι → ∀ {J J₀ : Subgroup G}, J₀ ≤ J →
    ∀ {F : Finset G}, (∀ u ∈ F, u ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J₀) →
    ∀ {I₀ : Type} [Fintype I₀] (y₀ : I₀ → G), Bridge.IsReps ι J₀ y₀ → ∀ {I : Type} [Fintype I] (y : I → G), Bridge.IsReps ι J y →
    ∀ (Φ : G → ℂ), (∀ γ g, Φ (ι γ * g) = Φ g) → (∀ k ∈ J₀, ∀ g, Φ (g * k) = Φ g) →
    ∑ i, ((Nat.card (Bridge.stab ι J₀ (y₀ i)) : ℂ))⁻¹ * Φ (y₀ i) =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ∑ u ∈ F, Φ (y i * u) := by
  first | exact @GlobalTheory.ClassRefineBridge.sum_isReps_refine | exact GlobalTheory.ClassRefineBridge.sum_isReps_refine | (intros; apply GlobalTheory.ClassRefineBridge.sum_isReps_refine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumPrincipalLevelEqConstMulClassSum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.ClassSumPrinc

theorem ratF_injective {D : D7} (S : HSp D) : Function.Injective (Bridge.ratF S) := by
  refine (injective_iff_map_eq_one _).2 fun γ hγ => ?_
  have h1 : GlobalTheory.ClassRegroup.finPt S (γ : GA D S) = 1 := by
    show (GlobalTheory.ClassRegroup.finEquiv S).symm ((finHom S).rangeRestrict (γ : GA D S)) = 1
    have : (finHom S).rangeRestrict (γ : GA D S) = 1 := hγ
    rw [this, map_one]
  exact Subtype.ext (GlobalTheory.ClassRegroup.eq_one_of_finPt S γ.2 h1)

end GlobalTheory.ClassSumPrinc

namespace GlobalTheory.ClassSumPrinc

theorem symm_finPt {D : D7} (S : HSp D) {k : GA D S} (hk : k ∈ GfC S) :
    (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S k) : GfC S) : GA D S) = k := by
  have : (GlobalTheory.ClassRegroup.finEquiv S) ⟨k, hk⟩ = finPt S k := rfl
  rw [← this, MulEquiv.symm_apply_apply]

theorem inner_sum {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) (ω : PairRep S T)
    {Fs : Finset (Bridge.Gf S)} (hF : ∀ u ∈ Fs, u ∈ B.levJ ψ) {κ : ℂ}
    (hκ : ∀ P : Links.PolF D T.rank S.rank,
      ∑ u ∈ Fs.attach, ((B.levLam ψ ⟨u.1, hF u.1 u.2⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S), 1) (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) P) =
      κ • B.F.fock (B.vecFlat ψ) P)
    {F : Bridge.Gf S → Links.PolF D T.rank S.rank} (hlaw : B.HasLaw ψ F) {x : GA D S} (hx : x ∈ GfC S) (g : GA D T) :
    ∑ u ∈ Fs, series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)
        (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) (F (finPt S x * u)) g =
      κ * series B.F ω (B.vecFlat ψ) x (F (finPt S x)) g := by
  have hu : ∀ u (hu : u ∈ Fs), series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)
      (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) (F (finPt S x * u)) g =
      ω (x, g) (((B.levLam ψ ⟨u, hF u hu⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), 1)
          (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (F (finPt S x)))) 0 := by
    intro u hu
    have e1 : F (finPt S x * u) = ((B.levLam ψ ⟨u, hF u hu⟩ : ℂˣ) : ℂ) • F (finPt S x) := by
      have := hlaw 1 (finPt S x) ⟨u, hF u hu⟩
      rw [map_one, one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply] at this
      exact this
    have e2 : (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) =
        x * (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S) := by
      have e3 := map_mul (GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x) u
      rw [e3, Subgroup.coe_mul, symm_finPt S hx]
    rw [series_apply, e2]
    simp only [e1, map_smul]
    have e4 : ω (x * (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), g) =
        ω (x, g) * ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    have e5 := LinearMap.congr_fun e4 (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (F (finPt S x)))
    rw [Module.End.mul_apply] at e5
    simp only [e5]
  rw [← Finset.sum_attach Fs, Finset.sum_congr rfl fun u _ => hu u.1 u.2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_apply, ← map_sum, hκ, map_smul, Pi.smul_apply, smul_eq_mul, series_apply]

theorem classSum_princ_eq : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (m : ℕ) (h₀ : Fin m → GA D S), IsClassSystem S ((GlobalTheory.FlatVecSum.princ B).levJ ψ) h₀ →
    ∀ (I : Type) [Fintype I] (h : I → GA D S), IsClassSystem S (B.levJ ψ) h →
    ∃ κ : ℂ, ∀ F ∈ B.formsC ψ, (GlobalTheory.FlatVecSum.princ B).classSum ω ψ h₀ F = κ • B.classSum ω ψ h F := by
  intro D S T B hB hS ψ hψ hQ ω hω m h₀ hC₀ I _ h hC
  obtain ⟨hle, -⟩ := GlobalTheory.T.principalLevel_le_level_characters_agree B hB ψ hQ
  obtain ⟨Fs, hF, hFu⟩ := GlobalTheory.T.finite_coset_representatives_level B hB ψ hQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_const_twistedSum_fockVectors_principalDatum B hB hS ψ hψ hQ ω hω Fs hF hFu
  refine ⟨κ, fun F hFm => ?_⟩
  have hinv := GlobalTheory.T.classSumTerms_invariant_principalLevel B hB hS ψ hψ hQ ω hω F hFm
  have hlaw := ((B.mem_formsC).1 hFm).2
  funext g
  rw [Base.classSum_apply, Base.classSum_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_apply]
  have key := GlobalTheory.T.classSum_regroup_finerLevel_cosets (Bridge.ratF S) (ratF_injective S) hle hF hFu (fun i => finPt S (h₀ i)) hC₀.reps
    (fun i => finPt S (h i)) hC.reps
    (fun y => series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g)
    (fun γ y => (hinv g).1 γ y) (fun k hk y => (hinv g).2 k hk y)
  simp only [symm_finPt S (hC₀.fin _), inner_sum B ψ ω hF hκ hlaw (hC.fin _)] at key
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, show (GlobalTheory.FlatVecSum.princ B).F = B.F from rfl]
  rw [key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.ClassSumPrinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumPrincipalLevelEqConstMulClassSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_principalLevel_eq_const_mul_classSum : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (m : ℕ) (h₀ : Fin m → GA D S), IsClassSystem S ((GlobalTheory.FlatVecSum.princ B).levJ ψ) h₀ →
    ∀ (I : Type) [Fintype I] (h : I → GA D S), IsClassSystem S (B.levJ ψ) h →
    ∃ κ : ℂ, ∀ F ∈ B.formsC ψ, (GlobalTheory.FlatVecSum.princ B).classSum ω ψ h₀ F = κ • B.classSum ω ψ h F := by
  first | exact @GlobalTheory.ClassSumPrinc.classSum_princ_eq | exact GlobalTheory.ClassSumPrinc.classSum_princ_eq | (intros; apply GlobalTheory.ClassSumPrinc.classSum_princ_eq <;> assumption)
end
