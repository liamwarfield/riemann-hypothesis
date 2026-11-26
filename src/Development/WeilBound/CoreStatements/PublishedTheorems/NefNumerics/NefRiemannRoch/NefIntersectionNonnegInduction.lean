module

public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.IntersectionNumberNonnegEffective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberNonnegOfNefAmpleAddNef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberNonnegOfAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberNonnegOfAmple
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_nonneg_of_isAmpleLB_of_isProjOver :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)],
      IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) →
        ∀ P : Fin d → LB X, (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F P := by
  intro k _ _ X _ hp d
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hd P _
    rw [interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k hd]
    exact Nat.cast_nonneg _
  | succ d ih =>
    intro F _ hd P hP
    obtain ⟨n, hn, s, hs, -⟩ := (hP 0).exists_mono_cutHom F
    have hL := isLB_lbPow (hP 0).isLB n
    have h1 := ih (cut F hL s) (suppDim_cut_le F hL s hd) (Fin.tail P) fun i => hP i.succ
    rw [← interNum_cons_eq_interNum_cut hL s (P := Fin.tail P) (fun i => (hP i.succ).isLB)
      (finiteCohTwists_of_isProjOver hf F hp)] at h1
    have h2 := (diffVanish_chiPic_of_isProjOver hf F hp hd).interNum_update_of_cls_eq_zsmul
      (L := P) (by simp) (fun i => (hP i).isLB) 0 hL (hP 0).isLB (n : ℤ)
      (by rw [cls_lbPow (hP 0).isLB, natCast_zsmul])
    have e : Function.update P 0 (lbPow (P 0) n) =
        (Fin.cons (lbPow (P 0) n) (Fin.tail P) : Fin (d + 1) → LB X) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Fin.tail]
    rw [Function.update_eq_self, e] at h2
    rw [h2] at h1
    exact nonneg_of_mul_nonneg_right h1 (Nat.cast_pos.2 hn)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberNonnegOfAmpleStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_nonneg_of_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F P := by
  first | exact @GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver | exact GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver | (intros; apply GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberNonnegOfNefAmpleAddNef
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_nonneg_of_isNef_of_ample_tens_nef (k : Type) [Field k] [Infinite k]
    (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k (X := X)))
    (hAN : ∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N))
    (d : ℕ) (F : X.Modules) [IsFiniteQC F] (hd : suppDim F ≤ (d : ℕ))
    (P : Fin d → LB X) (hP : ∀ i, IsNef k (P i)) : 0 ≤ interNum k F P := by
  classical
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hX
  have hD : DiffVanish (d + 1) (chiPic k F) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) F hX hd
  have key : ∀ S : Finset (Fin d), ∀ Q : Fin d → LB X, (∀ i ∈ S, IsNef k (Q i)) →
      (∀ i ∉ S, IsAmpleLB (Q i)) → 0 ≤ interNum k F Q := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun Q _ h ↦ GlobalTheory.T.lineBundleIntersectionNumber_nonneg_of_ample k X hX d F hd Q fun i ↦ h i (by simp)
    | insert i S hi ih =>
      intro Q hn ha
      have hi' : IsNef k (Q i) := hn i (Finset.mem_insert_self _ _)
      have hL : ∀ j, (Q j).IsLB := fun j ↦ by
        by_cases h : j ∈ insert i S
        · exact (hn j h).isLB
        · exact (ha j h).isLB
      have h1 : ∀ B : LB X, IsAmpleLB B → 0 ≤ interNum k F (Function.update Q i B) := by
        intro B hB
        refine ih _ (fun j hj ↦ ?_) (fun j hj ↦ ?_)
        · rw [Function.update_of_ne (by rintro rfl; exact hi hj)]
          exact hn j (Finset.mem_insert_of_mem hj)
        · by_cases h : j = i
          · subst h; rwa [Function.update_self]
          · rw [Function.update_of_ne h]
            exact ha j (by simp [h, hj])
      have h2 : ∀ m : ℕ, ∃ B : LB X, IsAmpleLB B ∧ interNum k F (Function.update Q i B) =
          interNum k F (Function.update Q i A) + m * interNum k F Q := by
        intro m
        induction m with
        | zero => exact ⟨A, hA, by simp⟩
        | succ m ihm =>
          obtain ⟨B, hB, e⟩ := ihm
          refine ⟨tens B (Q i), hAN _ _ hB hi', ?_⟩
          rw [hD.interNum_update_tens (by simp) hL i hB.isLB (hL i), e, Function.update_eq_self]
          push_cast
          ring
      by_contra hneg
      obtain ⟨B, hB, e⟩ := h2 ((interNum k F (Function.update Q i A)).toNat + 1)
      have h3 := h1 B hB
      have h4 := h1 A hA
      rw [e] at h3
      push_cast at h3
      rw [Int.toNat_of_nonneg h4] at h3
      nlinarith
  exact key Finset.univ P (fun i _ ↦ hP i) (fun i h ↦ absurd (Finset.mem_univ i) h)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberNonnegOfNefAmpleAddNefStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_nonneg_of_nef_ample_add_nef : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → (∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k F P := by
  first | exact @GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef | exact GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef | (intros; apply GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegInduction
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.KleimanDim

theorem interNum_nonneg_of_ample_tens_nef : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ),
    (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) →
      ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) →
    ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) →
      (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X,
        (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) := by
  intro k _ _ d H X _ hX E _ hE P hP
  refine SheafCycle.interNum_nonneg_of_interNumRed_nonneg k X hX d E hE P (fun i => (hP i).isLB) ?_
  intro Z hZirr hZdim
  haveI := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  letI : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
    ((redι Z).appTop.hom.comp (algebraMap k Γ(X, ⊤))).toAlgebra
  have hcompat : ∀ r : k, (redι Z).appTop.hom (algebraMap k Γ(X, ⊤) r) =
      algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r => rfl
  rw [InterModel.interNumRed_eq_interNumOn k (redι Z) Z (range_redι Z) P,
    interNumOn_eq_interNum_pull hcompat (fun i => (hP i).isLB)]
  have hYproj : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    rw [← comp_strHom hcompat]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion (redι Z) hX
  have hYdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (d : WithBot ℕ∞) := by
    have hmem : ∀ y, (redι Z) y ∈ (Z : Set X) := fun y => by
      rw [← range_redι Z]; exact Set.mem_range_self y
    have hind := ((redι Z).isClosedEmbedding.isInducing.codRestrict hmem).topologicalKrullDim_le
    rw [hZdim] at hind
    exact hind
  have hsupp : suppDim (QCoh.structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ≤ (d : WithBot ℕ∞) :=
    (QCoh.suppDim_le _).trans hYdim
  exact T.intersectionNumber_nonneg_of_nef_ample_add_nef k _ hYproj (fun A N hA hN => H _ hYproj hYdim A N hA hN) d _ hsupp
    (fun i => (P i).pull (redι Z)) (fun i => (hP i).pull_of_isClosedImmersion (redι Z) hcompat)

end GlobalTheory.KleimanDim
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegInductionStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_intersection_nonneg_induction : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) := by
  first | exact @GlobalTheory.KleimanDim.interNum_nonneg_of_ample_tens_nef | exact GlobalTheory.KleimanDim.interNum_nonneg_of_ample_tens_nef | (intros; apply GlobalTheory.KleimanDim.interNum_nonneg_of_ample_tens_nef <;> assumption)
end
