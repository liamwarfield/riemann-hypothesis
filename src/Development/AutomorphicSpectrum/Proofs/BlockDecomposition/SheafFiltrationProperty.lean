module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

theorem dividedPowerFiltration_one_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : pdP δ 1 ≤ J := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  induction l with
  | nil => simp at hr
  | cons q t ih =>
    have hq : q.2 ∈ J := hl q (by simp)
    rw [List.map_cons, List.prod_cons]
    by_cases h0 : q.1 = 0
    · refine J.mul_mem_left _ (ih (fun q' h' => hl q' (List.mem_cons_of_mem _ h')) ?_)
      simpa [h0] using hr
    · exact J.mul_mem_right _ (δ.dpow_mem h0 hq)

theorem dividedPowerFiltration_mul_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r r' : ℕ) :
    pdP δ r * pdP δ r' ≤ pdP δ (r + r') := by
  unfold pdP
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with h | h
    · exact hl q h
    · exact hl' q h
  · simpa using Nat.add_le_add hr hr'
  · simp

theorem dpow_mem_pdP {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (k : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow k x ∈ pdP δ k :=
  Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simp, by simp⟩

theorem isFil_sFil : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q) := by
  intro b L Q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.obj.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.obj.pdPow_zero
  · intro T
    change T.obj.pdPow (1 : ℤ).toNat = T.obj.J
    exact le_antisymm (dividedPowerFiltration_one_le T.obj.δ) T.obj.J_le_pdPow_one
  · intro r r' h T
    exact T.obj.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.obj.B from x) ∈ pdP T.obj.δ r := by
      have : (show T.obj.B from x) ∈ T.obj.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.obj.B from y) ∈ pdP T.obj.δ r' := by
      have : (show T.obj.B from y) ∈ T.obj.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := dividedPowerFiltration_mul_le T.obj.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.obj.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.obj.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact dpow_mem_pdP T.obj.δ k hx

end GlobalTheory.CompanionTheory.DPFil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheaf_filtration_property : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q) := by
  first | exact @GlobalTheory.CompanionTheory.DPFil.isFil_sFil | exact GlobalTheory.CompanionTheory.DPFil.isFil_sFil | (intros; apply GlobalTheory.CompanionTheory.DPFil.isFil_sFil <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CoordRes

theorem etale_rs {X : Scheme.{0}} {V W : X.Opens} (h : W ≤ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    (rs h).Etale := by
  have key := HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance ⟨V, hV⟩ ⟨W, hW⟩ h
  have e : Scheme.Hom.appLE (𝟙 X) V W h = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE] <;> rfl
  rw [e] at key
  exact key

theorem rs_comp_strV {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V W : X.Opens}
    (h : W ≤ V) : (rs h).comp (strV q V) = strV q W := by
  simp only [rs, strV]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

theorem main : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {V W : X.Opens} {d : ℕ}
    (c : Coord q V d) (h : W ≤ V) (hW : IsAffineOpen W), ∃ c' : Coord q W d, ∀ i, c'.t i = rs h (c.t i) := by
  intro O _ X q V W d c h hW
  refine ⟨⟨hW, fun i => rs h (c.t i), ?_⟩, fun i => rfl⟩
  have e1 : MvPolynomial.eval₂Hom (strV q W) (fun i => rs h (c.t i)) =
      (rs h).comp (MvPolynomial.eval₂Hom (strV q V) c.t) := by
    rw [MvPolynomial.comp_eval₂Hom, rs_comp_strV]
  rw [e1]
  exact RingHom.Etale.stableUnderComposition _ _ c.etale (etale_rs h c.affine hW)

end GlobalTheory.CompanionTheory.CoordRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinates_restrict_affine_open : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {V W : X.Opens} {d : ℕ}
    (c : Coord q V d) (h : W ≤ V) (hW : IsAffineOpen W), ∃ c' : Coord q W d, ∀ i, c'.t i = rs h (c.t i) := by
  first | exact @GlobalTheory.CompanionTheory.CoordRes.main | exact GlobalTheory.CompanionTheory.CoordRes.main | (intros; apply GlobalTheory.CompanionTheory.CoordRes.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CovEx

variable {O : Type} [CommRing O] {X : Scheme.{0}}

theorem strV_basicOpen (q : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (f : Γ(X, V)) :
    strV q (X.basicOpen f) = (algebraMap Γ(X, V) Γ(X, X.basicOpen f)).comp (strV q V) := by
  rw [RingHom.algebraMap_toAlgebra]
  simp only [strV]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

theorem coord_basicOpen (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} (hV : IsAffineOpen V) (f : Γ(X, V)) {d : ℕ}
    (g : MvPolynomial (Fin d) O →+* Localization.Away f)
    (hg : g.comp MvPolynomial.C = (algebraMap Γ(X, V) (Localization.Away f)).comp (strV q V)) (he : g.Etale) :
    Nonempty (Coord q (X.basicOpen f) d) := by
  have := hV.isLocalization_basicOpen f
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
  let G : MvPolynomial (Fin d) O →+* Γ(X, X.basicOpen f) := (e.toAlgHom.toRingHom).comp g
  have hG : (MvPolynomial.eval₂Hom (strV q (X.basicOpen f)) fun k => G (MvPolynomial.X k)) = G := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => by simp
    have h1 := RingHom.congr_fun hg r
    have h2 : G (MvPolynomial.C r) = e (g (MvPolynomial.C r)) := rfl
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, h2, strV_basicOpen]
    have h3 : g (MvPolynomial.C r) = algebraMap Γ(X, V) (Localization.Away f) (strV q V r) := h1
    rw [h3, AlgEquiv.commutes]
    rfl
  refine ⟨⟨hV.basicOpen f, fun k => G (MvPolynomial.X k), ?_⟩⟩
  rw [hG]
  exact RingHom.Etale.stableUnderComposition _ _ he (RingHom.Etale.of_bijective e.bijective)

theorem exists_basicOpen (Q : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hQ : RingHom.RespectsIso Q) (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} (hV : IsAffineOpen V)
    (h : RingHom.Locally Q (q.appLE ⊤ V le_top).hom) {x : X} (hx : x ∈ V) :
    ∃ f : Γ(X, V), x ∈ X.basicOpen f ∧ Q ((algebraMap Γ(X, V) (Localization.Away f)).comp (strV q V)) := by
  obtain ⟨s, hs, hl⟩ := h
  have hc : ⨆ f : s, X.basicOpen (U := V) f.1 = V := (hV.iSup_basicOpen_eq_self_iff (s := s)).2 hs
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge hx)
  refine ⟨f.1, hf, ?_⟩
  exact hQ.2 _ (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv (hl f.1 f.2)

theorem inter_affine (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) :=
  isAffineHom_diagonal_iff.1 (inferInstance : IsAffineHom (Limits.pullback.diagonal q)) ⊤ (isAffineOpen_top _)
    _ le_top _ le_top hU hV

theorem cov_of_local (P : ℕ → Prop) (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] [QuasiCompact q]
    (h : ∀ x : X, ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ P d ∧ Nonempty (Coord q V d)) :
    ∃ U : Cov q, ∀ α, P (U.d α) := by
  classical
  choose V d hx hP hc using h
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).2)
    fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨{ ι := t, U := fun a => V a.1, d := fun a => d a.1, c := fun a => (hc a.1).some, cover := ?_, inter := ?_ },
    fun a => hP a.1⟩
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  · intro S hS
    induction hS using Finset.Nonempty.cons_induction with
    | singleton a => simpa using (hc a.1).some.affine
    | cons a s ha hs ih =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert]
      exact inter_affine q (hc a.1).some.affine ih

theorem exists_cov : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q]
    [QuasiCompact q], (Smooth q → Nonempty (Cov q)) ∧
      ∀ d, SmoothOfRelativeDimension d q → ∃ U : Cov q, ∀ α, U.d α = d := by
  intro O _ X q _ _
  refine ⟨fun hs => ?_, fun d hd => ?_⟩
  · obtain ⟨U, -⟩ := cov_of_local (fun _ => True) q fun x => by
      obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
      have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V le_top).hom :=
        RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
      obtain ⟨f, hf, hst⟩ := exists_basicOpen RingHom.IsStandardSmooth RingHom.isStandardSmooth_respectsIso q hV h hx
      obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
      exact ⟨_, n, hf, trivial, coord_basicOpen q hV f g hg he⟩
    exact ⟨U⟩
  · refine cov_of_local (fun n => n = d) q fun x => ?_
    obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
    have h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (q.appLE ⊤ V le_top).hom :=
      HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) q hd ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    obtain ⟨f, hf, hst⟩ := exists_basicOpen (RingHom.IsStandardSmoothOfRelativeDimension d)
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso q hV h hx
    obtain ⟨g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨_, d, hf, rfl, coord_basicOpen q hV f g hg he⟩

end GlobalTheory.CompanionTheory.CovEx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_coordinate_cover : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] [QuasiCompact q],
    (Smooth q → Nonempty (Cov q)) ∧ ∀ d, SmoothOfRelativeDimension d q → ∃ U : Cov q, ∀ α, U.d α = d := by
  first | exact @GlobalTheory.CompanionTheory.CovEx.exists_cov | exact GlobalTheory.CompanionTheory.CovEx.exists_cov | (intros; apply GlobalTheory.CompanionTheory.CovEx.exists_cov <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.CosieveMV

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

def Cob (W : ObjectProperty C) : ∀ j : ℕ, CrystallineSemistableComparison.CH.Cn F j → Prop
  | 0, x => ∀ s : ComposableArrows C 0, W (s.obj 0) → x s = 0
  | j + 1, x => ∃ y : CrystallineSemistableComparison.CH.Cn F j, ∀ s : ComposableArrows C (j + 1), W (s.obj 0) → x s = CrystallineSemistableComparison.CH.d F j y s

def Van (W : ObjectProperty C) (j : ℕ) : Prop :=
  ∀ x : CrystallineSemistableComparison.CH.Cn F j, (∀ s : ComposableArrows C (j + 1), W (s.obj 0) → CrystallineSemistableComparison.CH.d F j x s = 0) → Cob F W j x

variable {F}

theorem face_start {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (i : Fin (n + 2))
    (s : ComposableArrows C (n + 1)) (h : W (s.obj 0)) : W ((face i s).obj 0) :=
  hW (s.map (homOfLE (Fin.zero_le _))) h

theorem d_congr {n : ℕ} (x y : CrystallineSemistableComparison.CH.Cn F n) (s : ComposableArrows C (n + 1))
    (h : ∀ i, x (face i s) = y (face i s)) : CrystallineSemistableComparison.CH.d F n x s = CrystallineSemistableComparison.CH.d F n y s := by
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (x (face i s)) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (y (face i s))
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

def liftCh {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (s : ComposableArrows C n) (h : W (s.obj 0)) :
    ComposableArrows W.FullSubcategory n :=
  W.lift s fun i => hW (s.map (homOfLE (Fin.zero_le i))) h


open Classical in
def extZ {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (y : CrystallineSemistableComparison.CH.Cn (W.ι ⋙ F) n) : CrystallineSemistableComparison.CH.Cn F n :=
  fun s => if h : W (s.obj 0) then y (liftCh hW s h) else 0

theorem pull_extZ {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (y : CrystallineSemistableComparison.CH.Cn (W.ι ⋙ F) n) :
    (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC n (extZ hW y) = y := by
  funext t
  have h : W ((t ⋙ W.ι).obj 0) := (t.obj 0).property
  change extZ hW y (t ⋙ W.ι) = y t
  unfold extZ
  rw [dite_eq_left h]
  rfl

theorem van_of_subsingleton {W : ObjectProperty C} (hW : Cosieve W) (j : ℕ)
    (hs : Subsingleton (HU F W j)) : Van F W j := by
  intro x hx
  have hz : CrystallineSemistableComparison.CH.d (W.ι ⋙ F) j ((CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC j x) = 0 := by
    rw [CrystallineSemistableComparison.CH.Mor.d_pullC]
    funext t
    exact hx (t ⋙ W.ι) (t.obj 0).property
  have hB := ((CrystallineSemistableComparison.P.cls_surj (CrystallineSemistableComparison.CH.cx (W.ι ⋙ F)) j).2.1 _ hz).1 (Subsingleton.elim _ _)
  cases j with
  | zero =>
    intro s h
    have e : (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC 0 x = 0 := hB
    exact congrFun e (liftCh hW s h)
  | succ j =>
    obtain ⟨y, hy⟩ := hB
    refine ⟨extZ hW y, fun s h => ?_⟩
    have e : (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC (j + 1) x =
        (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC (j + 1) (CrystallineSemistableComparison.CH.d F j (extZ hW y)) := by
      rw [← CrystallineSemistableComparison.CH.Mor.d_pullC, pull_extZ]
      exact hy.symm
    exact congrFun e (liftCh hW s h)

theorem van_sup {U V : ObjectProperty C} (hU : Cosieve U) (hV : Cosieve V) {j : ℕ}
    (h1 : Van F U j) (h2 : Van F V j) (h3 : ∀ i, j = i + 1 → Van F (fun T => U T ∧ V T) i) :
    Van F (fun T => U T ∨ V T) j := by
  intro x hx
  have ca := h1 x fun s h => hx s (Or.inl h)
  have cb := h2 x fun s h => hx s (Or.inr h)
  cases j with
  | zero =>
    rintro s (h | h)
    · exact ca s h
    · exact cb s h
  | succ n =>
    obtain ⟨a, ha⟩ := ca
    obtain ⟨b, hb⟩ := cb
    have hz : ∀ s : ComposableArrows C (n + 1), (U (s.obj 0) ∧ V (s.obj 0)) →
        CrystallineSemistableComparison.CH.d F n (a - b) s = 0 := by
      intro s hs
      rw [map_sub, Pi.sub_apply, ← ha s hs.1, ← hb s hs.2, sub_self]
    have hc := h3 n rfl (a - b) hz
    obtain ⟨a', ha', hab⟩ : ∃ a' : CrystallineSemistableComparison.CH.Cn F n,
        (∀ s : ComposableArrows C (n + 1), U (s.obj 0) → x s = CrystallineSemistableComparison.CH.d F n a' s) ∧
        ∀ s : ComposableArrows C n, U (s.obj 0) → V (s.obj 0) → a' s = b s := by
      cases n with
      | zero => exact ⟨a, ha, fun s h h' => sub_eq_zero.1 (hc s ⟨h, h'⟩)⟩
      | succ m =>
        obtain ⟨c, hc⟩ := hc
        refine ⟨a - CrystallineSemistableComparison.CH.d F m c, fun s h => ?_, fun s h h' => ?_⟩
        · rw [map_sub, CrystallineSemistableComparison.CH.d_d, sub_zero]
          exact ha s h
        · have e := hc s ⟨h, h'⟩
          rw [Pi.sub_apply] at e ⊢
          rw [← e]
          abel
    classical
    refine ⟨fun s => if U (s.obj 0) then a' s else b s, fun s hs => ?_⟩
    by_cases hu : U (s.obj 0)
    · rw [ha' s hu]
      exact d_congr _ _ s fun i => (if_pos (face_start hU i s hu)).symm
    · have hv : V (s.obj 0) := hs.resolve_left hu
      rw [hb s hv]
      refine d_congr _ _ s fun i => ?_
      by_cases hui : U ((face i s).obj 0)
      · exact (hab _ hui (face_start hV i s hv)).symm.trans (if_pos hui).symm
      · exact (if_neg hui).symm

theorem van_congr {W W' : ObjectProperty C} (h : ∀ T, W T ↔ W' T) {j : ℕ} (hv : Van F W j) : Van F W' j := by
  obtain rfl : W = W' := funext fun T => propext (h T)
  exact hv

theorem van_empty {W : ObjectProperty C} (h : ∀ T, ¬ W T) (j : ℕ) : Van F W j := by
  intro x _
  cases j with
  | zero => exact fun s hs => (h _ hs).elim
  | succ j => exact ⟨0, fun s hs => (h _ hs).elim⟩

def Wc {ι : Type} (U : ι → ObjectProperty C) (A S : Finset ι) : ObjectProperty C :=
  fun T => (∃ α ∈ A, U α T) ∧ capS U S T

theorem cosieve_capS {ι : Type} {U : ι → ObjectProperty C} (hU : ∀ α, Cosieve (U α)) (S : Finset ι) :
    Cosieve (capS U S) :=
  fun _ _ f h α hα => hU α f (h α hα)

theorem cosieve_Wc {ι : Type} {U : ι → ObjectProperty C} (hU : ∀ α, Cosieve (U α)) (A S : Finset ι) :
    Cosieve (Wc U A S) := by
  rintro T T' f ⟨⟨α, hα, hT⟩, hS⟩
  exact ⟨⟨α, hα, hU α f hT⟩, cosieve_capS hU S f hS⟩

theorem van_Wc {ι : Type} [DecidableEq ι] {U : ι → ObjectProperty C} (hU : ∀ α, Cosieve (U α))
    (D : ℕ → ℕ → Prop) (E : ℕ → Prop) (hD : ∀ n j, D (n + 1) j → D n j ∧ E j ∧ ∀ i, j = i + 1 → D n i)
    (hcap : ∀ S : Finset ι, S.Nonempty → ∀ j, E j → Van F (capS U S) j) (A : Finset ι) :
    ∀ (S : Finset ι) (j : ℕ), D A.card j → Van F (Wc U A S) j := by
  induction A using Finset.induction_on with
  | empty =>
    intro S j _
    exact van_empty (fun T hT => by simpa using hT.1) j
  | insert a A ha ih =>
    intro S j hj
    rw [Finset.card_insert_of_notMem ha] at hj
    obtain ⟨d1, d2, d3⟩ := hD _ _ hj
    have key := van_sup (cosieve_Wc hU A S) (cosieve_capS hU (insert a S)) (ih S j d1)
      (hcap _ (Finset.insert_nonempty _ _) j d2) fun i hi => van_congr (fun T => ⟨fun h =>
        ⟨⟨h.1, fun α hα => h.2 α (Finset.mem_insert_of_mem hα)⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩)
        (ih (insert a S) i (d3 i hi))
    refine van_congr (fun T => ⟨?_, ?_⟩) key
    · rintro (⟨⟨α, hα, hT⟩, hS⟩ | h)
      · exact ⟨⟨α, Finset.mem_insert_of_mem hα, hT⟩, hS⟩
      · exact ⟨⟨a, Finset.mem_insert_self _ _, h a (Finset.mem_insert_self _ _)⟩,
          fun α hα => h α (Finset.mem_insert_of_mem hα)⟩
    · rintro ⟨⟨α, hα, hT⟩, hS⟩
      rcases Finset.mem_insert.1 hα with rfl | h
      · refine Or.inr fun β hβ => ?_
        rcases Finset.mem_insert.1 hβ with rfl | h'
        · exact hT
        · exact hS β h'
      · exact Or.inl ⟨⟨α, h, hT⟩, hS⟩

theorem subsingleton_of_van {W : ObjectProperty C} (hW : ∀ T, W T) {j : ℕ} (h : Van F W j) :
    Subsingleton (CrystallineSemistableComparison.CH.H F j) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 x
  refine ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 a ha).2 ?_
  have hc := h a fun s _ => congrFun ha s
  cases j with
  | zero => exact funext fun s => hc s (hW _)
  | succ j =>
    obtain ⟨y, hy⟩ := hc
    exact ⟨y, funext fun s => (hy s (hW _)).symm⟩

theorem vanishing_of_cover : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS U S) j)) → ∀ j < s, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS U S) j)) → ∀ j, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS U S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H F j)) := by
  intro R _ C _ F ι _ U hU hc s
  classical
  have key : ∀ (D : ℕ → ℕ → Prop) (E : ℕ → Prop),
      (∀ n j, D (n + 1) j → D n j ∧ E j ∧ ∀ i, j = i + 1 → D n i) →
      (∀ S : Finset ι, S.Nonempty → ∀ j, E j → Subsingleton (HU F (capS U S) j)) →
      ∀ j, D (Fintype.card ι) j → Subsingleton (CrystallineSemistableComparison.CH.H F j) := by
    intro D E hD h j hj
    refine subsingleton_of_van (W := Wc U Finset.univ ∅) (fun T => ?_)
      (van_Wc hU D E hD (fun S hS j hE => van_of_subsingleton (cosieve_capS hU S) j (h S hS j hE))
        Finset.univ ∅ j (by simpa using hj))
    obtain ⟨α, hα⟩ := hc T
    exact ⟨⟨α, Finset.mem_univ _, hα⟩, fun β hβ => by simp at hβ⟩
  refine ⟨fun h j hj => key (fun _ j => j < s) (fun j => j < s) ?_ (fun S hS j hE => h S hS j hE) j hj,
    fun h j => key (fun _ _ => True) (fun _ => True) ?_ (fun S hS j _ => h S hS j) j trivial,
    fun h j hj => key (fun n j => s + n ≤ j) (fun j => j > s) ?_ (fun S hS j hE => h S hS j hE) j hj⟩
  · intro n j hj
    exact ⟨hj, hj, fun i hi => by omega⟩
  · intro n j _
    exact ⟨trivial, trivial, fun _ _ => trivial⟩
  · intro n j hj
    exact ⟨by omega, by omega, fun i hi => by omega⟩

end GlobalTheory.CompanionTheory.CosieveMV
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_vanishing_from_cover : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS U S) j)) → ∀ j < s, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS U S) j)) → ∀ j, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS U S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H F j)) := by
  first | exact @GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | exact GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | (intros; apply GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClass
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClass
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SerreFin

theorem finite_mid {R : Type} [CommRing R] [IsNoetherianRing R] {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g)
    [Module.Finite R M₁] [Module.Finite R M₃] : Module.Finite R M₂ := by
  have hk : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.1 h
  haveI : Module.Finite R (LinearMap.ker g) := by
    rw [hk]
    exact Module.Finite.range f
  haveI : IsNoetherian R M₃ := isNoetherian_of_isNoetherianRing_of_finite R M₃
  haveI : Module.Finite R (M₂ ⧸ LinearMap.ker g) := Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem exists_serre_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∃ 𝒮 : Serre.{1} R,
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ Module.Finite R M := by
  intro R _ _
  refine ⟨⟨fun M _ _ => Module.Finite R M, fun M _ _ _ => ?_, ?_⟩, fun M _ _ => Iff.rfl⟩
  · exact Module.Finite.of_surjective (0 : (Fin 0 → R) →ₗ[R] M)
      (fun x => ⟨0, Subsingleton.elim _ _⟩)
  · intro M₁ M₂ M₃ _ _ _ _ _ _ f g h h₁ h₃
    exact finite_mid f g h

end GlobalTheory.CompanionTheory.SerreFin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_modules_serre_class : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∃ 𝒮 : Serre.{1} R,
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ Module.Finite R M := by
  first | exact @GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite | exact GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite | (intros; apply GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltration
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltration
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerEnd

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

abbrev Q (A : C ⥤ CommAlgCat.{0} R) (j : ℕ) : Type 1 := CH.Cn (CH.modF A) j

abbrev dQ (A : C ⥤ CommAlgCat.{0} R) (j : ℕ) : Q A j →ₗ[R] Q A (j + 1) := CH.d (CH.modF A) j

abbrev val {j : ℕ} (x : Q A j) (s : ComposableArrows C j) : A.obj (s.obj (Fin.last j)) := x s

def Vals (a : IdF A) {j : ℕ} (x : Q A j) : Prop := ∀ s, val x s ∈ a.S (s.obj (Fin.last j))

theorem dQ_apply {j : ℕ} (x : Q A j) (s : ComposableArrows C (j + 1)) :
    val (dQ A j x) s = ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (val x (face i s)) := rfl

theorem Vals.sub {a : IdF A} {j : ℕ} {x y : Q A j} (hx : Vals a x) (hy : Vals a y) : Vals a (x - y) :=
  fun s => (a.S _).sub_mem (hx s) (hy s)

theorem Vals.dQ {a : IdF A} {j : ℕ} {x : Q A j} (hx : Vals a x) : Vals a (dQ A j x) := fun s => by
  rw [dQ_apply]
  exact Submodule.sum_mem _ fun i _ => (a.S _).toAddSubgroup.zsmul_mem (a.map_mem _ (hx _)) _

def cl (a b : IdF A) {j : ℕ} (x : Q A j) (hx : Vals a x) : CH.Cn (sq a b) j :=
  fun s => sqMk a b (val x s) (hx s)

theorem cl_surj (a b : IdF A) {j : ℕ} (f : CH.Cn (sq a b) j) : ∃ (x : Q A j) (hx : Vals a x), cl a b x hx = f := by
  have h : ∀ s : ComposableArrows C j, ∃ x : A.obj (s.obj (Fin.last j)), ∃ hx : x ∈ a.S _, sqMk a b x hx = f s := by
    intro s
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from f s).2
    exact ⟨y, hy, Subtype.ext e⟩
  choose x hx e using h
  exact ⟨x, hx, funext e⟩

theorem cl_eq_zero (a b : IdF A) {j : ℕ} {x : Q A j} {hx : Vals a x} (h : cl a b x hx = 0) : Vals b x := fun s => by
  have h1 := congrArg (fun g : CH.Cn (sq a b) j => (show sqM a b _ from g s).1) h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

theorem d_cl (a b : IdF A) {j : ℕ} (x : Q A j) (hx : Vals a x) :
    CH.d (sq a b) j (cl a b x hx) = cl a b (dQ A j x) hx.dQ := by
  funext s
  apply Subtype.ext
  change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s)) (sqMk a b (val x (face i s)) (hx _)) :
    sqM a b _) = Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (val x (face i s)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  rfl

theorem cl_sub (a b : IdF A) {j : ℕ} {x y : Q A j} (hx : Vals a x) (hy : Vals a y) :
    cl a b (x - y) (hx.sub hy) = cl a b x hx - cl a b y hy := by
  funext s
  apply Subtype.ext
  exact map_sub (Ideal.Quotient.mk _) _ _

theorem d_cl_zero (a b : IdF A) {j : ℕ} {z : Q A j} (hz : Vals a z) (hd : dQ A j z = 0) :
    CH.d (sq a b) j (cl a b z hz) = 0 := by
  rw [d_cl]
  funext s
  apply Subtype.ext
  change Ideal.Quotient.mk _ (val (dQ A j z) s) = 0
  rw [hd]
  exact map_zero (Ideal.Quotient.mk _)

theorem step_zero (a b : IdF A) (h : Subsingleton (CH.H (sq a b) 0)) {z : Q A 0} (hz : Vals a z)
    (hd : dQ A 0 z = 0) : Vals b z := by
  have hc := d_cl_zero a b hz hd
  have h0 : (CH.cx (sq a b)).cls (cl a b z hz) hc = 0 := Subsingleton.elim _ _
  exact cl_eq_zero a b ((CechClassBoundaries.class_zero_eq_zero_iff _ _).1 h0)

theorem step_succ (a b : IdF A) {n : ℕ} (h : Subsingleton (CH.H (sq a b) (n + 1))) {z : Q A (n + 1)} (hz : Vals a z)
    (hd : dQ A (n + 1) z = 0) : ∃ y : Q A n, Vals a y ∧ Vals b (z - dQ A n y) := by
  have hc := d_cl_zero a b hz hd
  have h0 : (CH.cx (sq a b)).cls (cl a b z hz) hc = 0 := Subsingleton.elim _ _
  obtain ⟨f, hf⟩ := (CechClassBoundaries.mem_Bs _).1 ((CechClassBoundaries.cls_eq_zero _ _).1 h0)
  obtain ⟨y, hy, rfl⟩ := cl_surj a b f
  refine ⟨y, hy, cl_eq_zero a b (hx := hz.sub hy.dQ) ?_⟩
  rw [cl_sub a b hz hy.dQ, ← d_cl a b y hy]
  exact sub_eq_zero.2 hf.symm

abbrev St (a : ℕ → IdF A) (n k : ℕ) : Type 1 := {z : Q A (n + 1) // Vals (a k) z ∧ dQ A (n + 1) z = 0}

theorem exists_seq (a : ℕ → IdF A) {n : ℕ} (h : ∀ k, Subsingleton (CH.H (sq (a k) (a (k + 1))) (n + 1)))
    {z : Q A (n + 1)} (hz : Vals (a 0) z) (hd : dQ A (n + 1) z = 0) :
    ∃ y : ℕ → Q A n, (∀ k, Vals (a k) (y k)) ∧
      ∀ k, Vals (a k) (z - dQ A n (∑ i ∈ Finset.range k, y i)) := by
  have hs : ∀ (k : ℕ) (w : St a n k), ∃ y : Q A n, Vals (a k) y ∧ Vals (a (k + 1)) (w.1 - dQ A n y) :=
    fun k w => step_succ _ _ (h k) w.2.1 w.2.2
  choose f hf hg using hs
  let w : ∀ k, St a n k := fun k => Nat.rec ⟨z, hz, hd⟩ (fun k wk => ⟨wk.1 - dQ A n (f k wk), hg k wk, by
    have e : dQ A (n + 1) (dQ A n (f k wk)) = 0 := CH.d_d _ _ _
    rw [map_sub, wk.2.2, e, sub_zero]⟩) k
  refine ⟨fun k => f k (w k), fun k => hf k (w k), fun k => ?_⟩
  have e : ∀ k, (w k).1 = z - dQ A n (∑ i ∈ Finset.range k, f i (w i)) := by
    intro k
    induction k with
    | zero => simp [w]
    | succ k ih =>
      rw [Finset.sum_range_succ, map_add (f := _), ← sub_sub, ← ih]
  rw [← e]
  exact (w k).2.1

theorem exists_primitive (a : ℕ → IdF A) (ha : ∀ k T, (a (k + 1)).S T ≤ (a k).S T) (he : ∀ T, ∃ k, (a k).S T = ⊥)
    {n : ℕ} (h : ∀ k, Subsingleton (CH.H (sq (a k) (a (k + 1))) (n + 1)))
    {z : Q A (n + 1)} (hz : Vals (a 0) z) (hd : dQ A (n + 1) z = 0) :
    ∃ Y : Q A n, Vals (a 0) Y ∧ z = dQ A n Y := by
  classical
  have hle : ∀ {k m : ℕ}, k ≤ m → ∀ T, (a m).S T ≤ (a k).S T := by
    intro k m hkm T
    induction m, hkm using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact (ha m T).trans ih
  choose K hK using he
  have hbot : ∀ (T : C) {m : ℕ}, K T ≤ m → (a m).S T = ⊥ := fun T m hm =>
    le_bot_iff.1 ((hle hm T).trans (hK T).le)
  obtain ⟨y, hy, hz'⟩ := exists_seq a h hz hd
  let P : ℕ → Q A n := fun N => ∑ i ∈ Finset.range N, y i
  have hP : ∀ (s : ComposableArrows C n) {N : ℕ}, K (s.obj (Fin.last n)) ≤ N →
      val (P N) s = val (P (K (s.obj (Fin.last n)))) s := by
    intro s N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      have h0 : val (y m) s = 0 := by
        have := hy m s
        rwa [hbot _ hm, Ideal.mem_bot] at this
      have e : val (P (m + 1)) s = val (P m) s + val (y m) s := by
        simp only [P, Finset.sum_range_succ]
        rfl
      rw [e, h0, add_zero, ih]
  let Y : Q A n := fun s => val (P (K (s.obj (Fin.last n)))) s
  have hP0 : ∀ N, Vals (a 0) (P N) := by
    intro N
    induction N with
    | zero => intro s; simp only [P, Finset.range_zero, Finset.sum_empty]; exact (a 0 |>.S _).zero_mem
    | succ m ih =>
      intro s
      have e : val (P (m + 1)) s = val (P m) s + val (y m) s := by
        simp only [P, Finset.sum_range_succ]
        rfl
      rw [e]
      exact (a 0 |>.S _).add_mem (ih s) (hle (Nat.zero_le m) _ (hy m s))
  refine ⟨Y, fun s => hP0 _ s, ?_⟩
  funext s
  let N : ℕ := max (K (s.obj (Fin.last (n + 1)))) (Finset.univ.sup fun i : Fin (n + 2) => K ((face i s).obj (Fin.last n)))
  have h1 : val (z - dQ A n (P N)) s = 0 := by
    have := hz' N s
    rwa [hbot _ (le_max_left _ _), Ideal.mem_bot] at this
  have h2 : val (dQ A n (P N)) s = val (dQ A n Y) s := by
    rw [dQ_apply, dQ_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP (face i s) ((Finset.le_sup (f := fun i : Fin (n + 2) => K ((face i s).obj (Fin.last n))) (Finset.mem_univ i)).trans (le_max_right _ _))]
  have h3 : val z s = val (dQ A n (P N)) s := sub_eq_zero.1 h1
  exact h3.trans h2

end GlobalTheory.CompanionTheory.TowerEnd


open GlobalTheory.CompanionTheory.TowerEnd in
theorem GlobalTheory.CompanionTheory.TowerEnd.vanish {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a : ℕ → IdF A) :
    (∀ k T, (a (k + 1)).S T ≤ (a k).S T) → (∀ T, ∃ k, (a k).S T = ⊥) →
    (∀ k j, Subsingleton (CH.H (sq (a k) (a (k + 1))) j)) → ∀ j, Subsingleton (CH.H (sq (a 0) (IdF.bot A)) j) := by
  intro ha he h j
  have key : ∀ x : CH.H (sq (a 0) (IdF.bot A)) j, x = 0 := by
    intro x
    obtain ⟨f, hf, rfl⟩ := CechClassBoundaries.clsSurj x
    obtain ⟨z, hz, rfl⟩ := cl_surj _ _ f
    have hd : dQ A j z = 0 := by
      rw [d_cl] at hf
      funext s
      exact cl_eq_zero _ _ hf s
    cases j with
    | zero =>
      have hall : ∀ k, Vals (a k) z := by
        intro k
        induction k with
        | zero => exact hz
        | succ k ih => exact step_zero _ _ (h k 0) ih hd
      have h0 : cl (a 0) (IdF.bot A) z hz = 0 := by
        funext s
        obtain ⟨k, hk⟩ := he (s.obj (Fin.last 0))
        have h1 := hall k s
        rw [hk, Ideal.mem_bot] at h1
        apply Subtype.ext
        change Ideal.Quotient.mk _ (val z s) = 0
        rw [h1]
        exact map_zero (Ideal.Quotient.mk _)
      exact (CechClassBoundaries.class_zero_eq_zero_iff _ _).2 h0
    | succ n =>
      obtain ⟨Y, hY, e⟩ := exists_primitive a ha he (fun k => h k (n + 1)) hz hd
      refine (CechClassBoundaries.cls_eq_zero _ _).2 ((CechClassBoundaries.mem_Bs _).2 ⟨cl _ _ Y hY, ?_⟩)
      rw [d_cl]
      subst e
      rfl
  exact ⟨fun x y => (key x).trans (key y).symm⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltrationStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishing_along_ideal_filtration : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a : ℕ → IdF A),
    (∀ k T, (a (k + 1)).S T ≤ (a k).S T) → (∀ T, ∃ k, (a k).S T = ⊥) →
    (∀ k j, Subsingleton (CH.H (sq (a k) (a (k + 1))) j)) → ∀ j, Subsingleton (CH.H (sq (a 0) (IdF.bot A)) j) := by
  first | exact @GlobalTheory.CompanionTheory.TowerEnd.vanish | exact GlobalTheory.CompanionTheory.TowerEnd.vanish | (intros; apply GlobalTheory.CompanionTheory.TowerEnd.vanish <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.USt
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh

namespace GlobalTheory.CompanionTheory.Axis

def USt {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module R M] (z : ∀ T : C, M ⊗[R] F.obj T),
    (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
    ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T)

def evZ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T T' : C} (φ : T ⟶ T') :
    Z1 F →ₗ[R] F.obj T' where
  toFun f := f.1 T T' φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.CompanionTheory.Axis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfBijective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.WedgeField

theorem exists_finite_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s]
    [CompactSpace X] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  have hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _) U le_top W le_top hU hW
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := fun x _ => by
    have hx : x ∈ (⨆ U : X.affineOpens, U.1 : X.Opens) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact Set.mem_iUnion.2 ⟨U, hU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) hcov
  let A : Set X.Opens := (fun U : X.affineOpens => U.1) '' (t : Set X.affineOpens)
  have hfin : (infClosure A).Finite := (t.finite_toSet.image _).infClosure
  have haff : infClosure A ⊆ {V : X.Opens | IsAffineOpen V} :=
    infClosure_min (by rintro _ ⟨U, _, rfl⟩; exact U.2) fun a ha b hb => hinter a b ha hb
  letI inst : SemilatticeInf (infClosure A) :=
    Subtype.semilatticeInf fun x y hx hy => infClosed_infClosure hx hy
  refine ⟨infClosure A, inst, hfin.to_subtype, ⟨⟨fun p => ⟨p.1, haff p.2⟩, fun a b => rfl, ?_⟩⟩⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨⟨U.1, subset_infClosure ⟨U, hU, rfl⟩⟩, hx⟩

def sqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

theorem sqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    sqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem wedge_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) (h2 : Function.Bijective m.pull2) (h : Wedge F') : Wedge F := by
  obtain ⟨e, he⟩ := h
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  let E2 : H2 F ≃ₗ[R] H2 F' := LinearEquiv.ofBijective m.pull2 h2
  refine ⟨(sqEquiv E1).trans (e.trans E2.symm), fun a b => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, sqEquiv_ιMulti, he, LinearEquiv.symm_apply_eq]
  exact (m.pullCohomologyTwo_cup a b).symm

theorem vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

end GlobalTheory.CompanionTheory.Hodge.WedgeField
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResLoc
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem resLoc : CrystallineSemistableComparison.E.ResLoc := by
  intro R _ F s U x hx
  exact (GlobalTheory.EtC.resSec R F U).2.2.1 (s : ℤ) ((s + 1 : ℕ) : ℤ) ((s + 1 + 1 : ℕ) : ℤ) (by omega) (by omega) x (by omega) hx

end GlobalTheory.CompanionTheory.EdgeMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtRes

theorem resZero : CrystallineSemistableComparison.E.ResZero := by
  intro R _ F U
  obtain ⟨h0, h1, -, h3⟩ := GlobalTheory.EtC.resSec R F U
  exact ⟨h1, h0, h3⟩

end GlobalTheory.CompanionTheory.EtRes
end
