module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpolyHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEmbAll
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplexModelPointsOfGenericFiberEmbedding
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFApprox
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocLat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPFrameEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkLat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkPerf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkInj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkOnto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PJLine
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PArchEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PJStruct
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTypeIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.TTSymmApply
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRDicEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlaceLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PGUnif
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PAdCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PWitOfAd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PInvMin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlacePer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlaceEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionFubiniStudyPositive
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PIsogCoord
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLevelChange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PIsogAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixFwd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.FixZOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PSheetOf
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU
open scoped Matrix

namespace UpperTheory.Gal.W2

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}

private theorem refl_marked {Λ : Type} (N : ℕ) (D : PLat O bar) (t : Λ → D.La) :
    IsMarkedIsom N D D t t (LinearEquiv.refl O D.La) :=
  ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩⟩

private theorem commutes_rho {D : PLat O bar} {P P' : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ρ P) (hP' : IsPeriod D ρ P') (w : D.La ≃ₗ[O] D.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hw : ∀ x, P' (w x) = h (P x)) (a : O) (z : Fin g → ℂ) :
    h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by
    rw [hP.2.2.2.1]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    rw [← hP.1, ← hw, ← hw, map_smul, hP'.1]
  | zero => simp
  | add x y _ _ hx hy => simp only [Matrix.mulVec_add, map_add (f := _), hx, hy]
  | smul c x _ hx =>
    have e : ∀ v : Fin g → ℂ, h (c • v) = c • h v := fun v =>
      (h.toLinearMap.restrictScalars ℝ).map_smul c v
    rw [Matrix.mulVec_smul, e, e, hx, Matrix.mulVec_smul]

theorem sheetOf_of : SheetOf := by
  intro O _ bar g ρ Λ F N Cl U i hN hfull
  have hN0 : 0 < N := by omega
  have key : ∀ (P P' : (U.Di i).La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsPeriod (U.Di i) ρ P' → (∀ x, P' x = h (P x)) →
      ∀ (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A))
        (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' →
      UnifAt F (RingHom.id ℂ) ρ N (U.Di i) (U.t i) P y e →
      UnifAt F (RingHom.id ℂ) ρ N (U.Di i) (U.t i) P' y' e' →
      ∀ z, (e' (h z)).left = (e z).left := by
    intro P P' h hP' hx y y' e e' hy a b z
    subst hy
    have h2 := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N (U.Di i) (U.Di i) (U.t i) (U.t i) P P' y e
      (LinearEquiv.refl O _) h hN0 a (refl_marked N _ _) (fun x => hx x) hP'
    have h3 := congrFun (GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking O bar g ρ ℂ (RingHom.id ℂ) Λ F N (U.Di i) (U.t i) P' y _ _ hN hfull h2 b) (h z)
    simp only [LinearEquiv.symm_apply_apply] at h3
    rw [← h3]
  refine ⟨{ u := U.u i, ex := U.ex i, ov := fun P hP => (U.unif i P hP).1,
            exp := fun P hP => (U.unif i P hP).2.2.1, ker := fun P hP => (U.unif i P hP).2.2.2.1,
            lin := ?_, hol := U.hol i, lift := ?_ }, fun _ => rfl, fun _ _ => rfl⟩
  · intro P P' h hP hP' hx z
    have e : U.u i P = U.u i P' :=
      (U.fibre i P P' hP hP').2 ⟨LinearEquiv.refl O _, h, refl_marked N _ _, fun x => hx x⟩
    exact key P P' h hP' hx _ _ _ _ e (U.unif i P hP) (U.unif i P' hP') z
  · intro m B y hB hy hhol b₀ hb₀ P₀ hP₀ hyb
    obtain ⟨B', i', P, hB', hb', hsub, hP, hu⟩ := U.lift m B y hB hy hhol b₀ hb₀
    have hPb := hP.1 b₀ hb'
    obtain rfl : i' = i := U.disj i' i (P b₀) P₀ hPb hP₀ ((hu b₀ hb').trans hyb)
    obtain ⟨w, h, hw, hwx⟩ := (U.fibre i' (P b₀) P₀ hPb hP₀).1 ((hu b₀ hb').trans hyb)
    have hc := commutes_rho hPb hP₀ w h hwx
    let P' : (Fin _ → ℂ) → ((U.Di i').La →+ (Fin g → ℂ)) := fun b =>
      (h.toLinearMap.toAddMonoidHom.comp (P b)).comp w.symm.toLinearMap.toAddMonoidHom
    have ev : ∀ b x, P' b x = h (P b (w.symm x)) := fun _ _ => rfl
    have hper : ∀ b ∈ B', IsPeriod (U.Di i') ρ (P' b) := fun b hb =>
      isPeriod_comp_isometry_symm _ _ w hw.1 _
        (GlobalTheory.T.comp_linearEquiv_intertwining O bar _ g ρ ρ (P b) h (hP.1 b hb) hc)
    refine ⟨B', P', hB', hb', hsub, ⟨hper, fun x => ?_⟩, ?_, fun b hb => ?_⟩
    · exact (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable.comp_differentiableOn
        (hP.2 (w.symm x))
    · ext1 x
      rw [ev, ← hwx, LinearEquiv.apply_symm_apply]
    · rw [← hu b hb]
      exact ((U.fibre i' (P b) (P' b) (hP.1 b hb) (hper b hb)).2
        ⟨w, h, hw, fun x => by rw [ev, LinearEquiv.symm_apply_apply]⟩).symm

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCoordMove
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rd_add' {p : ℕ} [Fact (Nat.Prime p)] {D : UPel.HT.Datum p} {G : HTGroup p}
    (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (a b : VQ D) :
    rd L x h (a + b) = rd L x h a + rd L x h b := by
  simp only [rd, TensorProduct.tmul_add, map_add (f := _)]

private theorem rd_nsmul' {p : ℕ} [Fact (Nat.Prime p)] {D : UPel.HT.Datum p} {G : HTGroup p}
    (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (N : ℕ) (a : VQ D) :
    rd L x h (N • a) = N • rd L x h a := by
  induction N with
  | zero => simp only [zero_smul, rd, TensorProduct.tmul_zero, map_zero]
  | succ n ih => rw [succ_nsmul, rd_add', ih, succ_nsmul]

theorem UpperTheory.Gal.W2.coordMove_of :
    UpperTheory.Gal.W2.CoordMove := by
  intro p _ D G L v t₀ ρ B PD RD N D' t P D'' t'' P'' w hw hP j j'' hj a ha
  obtain ⟨hiso, hmark⟩ := hw
  obtain ⟨⟨hinj, hact, hsurj, s, hs, hform⟩, ⟨hA1, hA2⟩, hloc, Q, hQ, hQj, hrel⟩ := ha
  have key : ∀ w0 : VQ D, (∃ u : D'.La, w0 = j u) ↔ ∃ u : D''.La, w0 = j'' u := by
    intro w0
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨w.symm u, by rw [hj, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨w u, hj u⟩
  refine ⟨⟨?_, ?_, ?_, s, hs, ?_⟩, ⟨?_, ?_⟩, ?_, Q, hQ, ?_, hrel⟩
  · intro u u' huu
    rw [hj, hj] at huu
    exact w.injective (hinj huu)
  · intro c u
    rw [hj, hj, map_smul, hact]
  · intro w0
    obtain ⟨m, u, hm, hmu⟩ := hsurj w0
    exact ⟨m, w.symm u, hm, by rw [hj, LinearEquiv.apply_symm_apply, hmu]⟩
  · intro u u'
    rw [hj, hj, ← hform, hiso]
  · intro w0
    rw [← hA1 w0]
    constructor
    · rintro ⟨r, u, hu⟩
      exact ⟨r, w u, by rw [hu, hj]⟩
    · rintro ⟨r, u, hu⟩
      exact ⟨r, w.symm u, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩
  · intro a0
    obtain ⟨e, he⟩ := hmark a0
    obtain ⟨w1, hw1, hw1e⟩ := hA2 a0
    have he' : rd L (trivX B) a.1.1 (j e) ∈ LaHat D := (hA1 (j e)).1 ⟨0, e, by simp⟩
    refine ⟨w1 + rd L (trivX B) a.1.1 (j e), add_mem hw1 he', ?_⟩
    rw [hj, he, map_add (f := _), map_nsmul, rd_add', rd_nsmul', hw1e, smul_add, add_assoc]
  · intro w0
    rw [← hloc w0]
    constructor
    · rintro ⟨m, u, hm, hu⟩
      exact ⟨m, w u, hm, by rw [hu, hj]⟩
    · rintro ⟨m, u, hm, hu⟩
      exact ⟨m, w.symm u, hm, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩
  · intro u
    rw [hj, hQj, hP]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PUnifG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem u_eq_of_marked {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hw : IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w) (hh : ∀ u, P (w u) = h (P' u)) :
    U.u i' P' = U.u i P := by
  obtain rfl := U.distinct i' i w hw
  exact (U.fibre i' P' P hP' hP).2 ⟨w, h, hw, hh⟩

private theorem marked_of_u_eq {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (e : U.u i' P' = U.u i P) :
    ∃ (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w ∧ ∀ u, P (w u) = h (P' u) := by
  obtain rfl := U.disj i' i P' P hP' hP e
  exact (U.fibre i' P' P hP' hP).1 e

private theorem isPeriod_comp {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {D' D'' : PLat O bar} {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ρ P) (w : D''.La ≃ₗ[O] D'.La)
    (hw : IsIsom D'' D' w) : IsPeriod D'' ρ (P.comp w.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hEF⟩ := hP
  have hs : Set.range (P.comp w.toLinearMap.toAddMonoidHom) = Set.range P := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨w x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨w.symm x, by simp⟩
  have hr : (P.comp w.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    exact Set.ext_iff.1 hs z
  refine ⟨fun a x => ?_, h2.comp w.injective, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · show P (w (a • x)) = _
    rw [map_smul, h1]
    rfl
  · rw [hr]
    exact h3
  · rw [hs]
    exact h4
  · show (hermForm Hm (P (w x)) (P (w y))).im = _
    rw [hEF, hw x y]

private theorem marked_symm {O : Type} [Ring O] {bar : O → O} {Λ : Type} {N : ℕ} {D₁ D₂ : PLat O bar}
    {t₁ : Λ → D₁.La} {t₂ : Λ → D₂.La} {w : D₁.La ≃ₗ[O] D₂.La} (h : IsMarkedIsom N D₁ D₂ t₁ t₂ w) :
    IsMarkedIsom N D₂ D₁ t₂ t₁ w.symm := by
  refine ⟨fun x y => ?_, fun a => ?_⟩
  · have := h.1 (w.symm x) (w.symm y)
    simpa using this.symm
  · obtain ⟨e, he⟩ := h.2 a
    refine ⟨-(w.symm e), ?_⟩
    have h2 := congrArg w.symm he
    rw [LinearEquiv.symm_apply_apply, map_add (f := _), map_nsmul] at h2
    rw [h2, smul_neg]
    abel

theorem UpperTheory.Gal.W2.unifG_of :
    UpperTheory.Gal.W2.CoordEx → UpperTheory.Gal.W2.CoordOcc → UpperTheory.Gal.W2.CoordIso → UpperTheory.Gal.W2.CoordMove → UpperTheory.Gal.W2.UnifG := by
  intro hEx hOcc hIso hMove p _ D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp F U
  have hch : ∀ x : CxPts F.s (RingHom.id ℂ), ∃ (i : Fin U.n) (P : (U.Di i).La →+ (Fin D.g → ℂ))
      (q : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β) (j : (U.Di i).La →+ VQ D),
      IsPeriod (U.Di i) ρ P ∧ x.1 = U.u i P ∧ IsCoord L (Quot.out q) (PD _) (RD _) N (U.Di i) (U.t i) P j a := by
    intro x
    obtain ⟨i, P, hP, hu⟩ := U.onto x.1 x.2
    obtain ⟨q, a, j, hc⟩ := hEx p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (U.Di i) (U.t i) P (U.mem i) hP
    exact ⟨i, P, q, a, j, hP, hu.symm, hc⟩
  choose i P q a j hP hu hc using hch
  let Φ₀ : CxPts F.s (RingHom.id ℂ) → GlobalTheory.LKCx.AllPts G v (L.KN N) (KHT p G.m G.n 1 G.Fw) :=
    fun x => ⟨q x, Quot.mk _ (a x)⟩
  have hinj : Function.Injective Φ₀ := by
    intro x x' e
    obtain ⟨w, h, hw, hh⟩ := (hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di (i x)) (U.t (i x)) (P x)
      (U.Di (i x')) (U.t (i x')) (P x') (U.mem _) (U.mem _) (q x) (q x') (a x) (a x') (j x) (j x')
      (hc x) (hc x')).2 e
    apply Subtype.ext
    rw [hu x, hu x']
    exact (u_eq_of_marked U _ _ _ _ (hP x) (hP x') w h hw hh).symm
  have hsurj : Function.Surjective Φ₀ := by
    rintro ⟨q₀, c⟩
    obtain ⟨a₀, rfl⟩ := Quot.exists_rep c
    obtain ⟨D', t, Pd, jd, hCl, hPd, hcd⟩ :=
      hOcc p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (Quot.out q₀) a₀
    obtain ⟨i₀, w, hw⟩ := U.all D' t hCl ⟨Pd, hPd⟩
    have hws := marked_symm hw
    let P₀ := Pd.comp w.symm.toLinearMap.toAddMonoidHom
    have hP₀ : IsPeriod (U.Di i₀) ρ P₀ := isPeriod_comp hPd w.symm hws.1
    let j₀ := jd.comp w.symm.toLinearMap.toAddMonoidHom
    have hc₀ : IsCoord L (Quot.out q₀) (PD _) (RD _) N (U.Di i₀) (U.t i₀) P₀ j₀ a₀ :=
      hMove p D G L v t₀ ρ (Quot.out q₀) (PD _) (RD _) N D' t Pd (U.Di i₀) (U.t i₀) P₀ w.symm hws
        (fun _ => rfl) jd j₀ (fun _ => rfl) a₀ hcd
    let x : CxPts F.s (RingHom.id ℂ) := ⟨U.u i₀ P₀, (U.unif i₀ P₀ hP₀).1⟩
    refine ⟨x, ?_⟩
    obtain ⟨w', h', hw', hh'⟩ := marked_of_u_eq U i₀ (i x) P₀ (P x) hP₀ (hP x) (hu x).symm
    exact ((hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di i₀) (U.t i₀) P₀ (U.Di (i x)) (U.t (i x)) (P x)
      (U.mem _) (U.mem _) q₀ (q x) a₀ (a x) j₀ (j x) hc₀ (hc x)).1 ⟨w', h', hw', hh'⟩).symm
  exact ⟨Equiv.ofBijective Φ₀ ⟨hinj, hsurj⟩, fun x => ⟨q x, a x, i x, P x, j x, rfl, hP x, hu x, hc x⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLatIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.LatticeIsomorphism

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem rd_add (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (u v : VQ D) :
    rd L x h (u + v) = rd L x h u + rd L x h v := by
  simp only [rd, TensorProduct.tmul_add, map_add (f := _)]

private noncomputable def rdHom (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) : VQ D →+ AfP p ⊗[ℚ] VQ D :=
  AddMonoidHom.mk' (rd L x h) (rd_add L x h)

private theorem rd_sub (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (u v : VQ D) :
    rd L x h (u - v) = rd L x h u - rd L x h v := by
  exact map_sub (rdHom L x h) u v

private theorem rd_nsmul (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (n : ℕ) (u : VQ D) :
    rd L x h (n • u) = n • rd L x h u := by
  exact map_nsmul (rdHom L x h) n u

private theorem actY_inv {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y (actY L y⁻¹ w) = w := by
  show L.rep _ (L.rep _ w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem inv_actY {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y⁻¹ (actY L y w) = w := by
  show L.rep ((y⁻¹ : GlobalTheory.LKCx.grp G β) : G.Cˣ × ℚˣ).1 (L.rep ((y : G.Cˣ × ℚˣ).1 : G.C) w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private noncomputable def placeY {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv} (j'' : D''.La →+ VQ D) :
    D''.La →+ VQ D :=
  (LinearMap.toAddMonoidHom (actY L y)).comp j''

private theorem placeY_apply {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv} (j'' : D''.La →+ VQ D)
    (u : D''.La) : placeY L y j'' u = actY L y (j'' u) := rfl

private theorem coordA_placeY (hR : RdAct) (B : GlobalTheory.LKCx.Form G) (y : GlobalTheory.LKCx.grp G B.β) {N : ℕ}
    {D'' : PLat D.O D.inv} {t'' : D.La → D''.La} {j'' : D''.La →+ VQ D} {h : G.GAf}
    (hc : IsCoordA L (trivX B) N D'' t'' j'' h) :
    IsCoordA L (trivX B) N D'' t'' (placeY L y j'') (B.toAf y * h) := by
  have key : ∀ w, rd L (trivX B) (B.toAf y * h) (actY L y w) = rd L (trivX B) h w := by
    intro w
    rw [hR p D G L B y (B.toAf y * h) h w]
    have e : (B.toAf y * h)⁻¹ * B.toAf y * h = 1 := by group
    rw [e, map_one, Module.End.one_apply]
  refine ⟨fun w => ?_, fun a => ?_⟩
  · have hw : w = actY L y (actY L y⁻¹ w) := (actY_inv L y w).symm
    rw [hw, key, ← hc.1 (actY L y⁻¹ w), ← hw]
    constructor
    · rintro ⟨r, u, hu⟩
      refine ⟨r, u, ?_⟩
      rw [placeY_apply] at hu
      rw [← map_nsmul, hu, inv_actY]
    · rintro ⟨r, u, hu⟩
      refine ⟨r, u, ?_⟩
      rw [placeY_apply, ← hu, map_nsmul, actY_inv]
  · obtain ⟨w1, hw1, e⟩ := hc.2 a
    exact ⟨w1, hw1, by rw [placeY_apply, key, e]⟩

private theorem locP_placeY {β : G.Cˣ} (PD : PDic L β) (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv}
    {j'' : D''.La →+ VQ D} {hp : Gr G 1} (hl : IsLocP D'' j'' (PD.lat hp)) :
    IsLocP D'' (placeY L y j'') (PD.lat (GlobalTheory.LKCx.toP1 G β y * hp)) := by
  intro w
  have hw : w = actY L y (actY L y⁻¹ w) := (actY_inv L y w).symm
  rw [hw, PD.equiv y hp, ← hl (actY L y⁻¹ w), ← hw]
  constructor
  · rintro ⟨m, u, hm, hu⟩
    refine ⟨m, u, hm, ?_⟩
    rw [placeY_apply] at hu
    rw [← map_nsmul, hu, inv_actY]
  · rintro ⟨m, u, hm, hu⟩
    refine ⟨m, u, hm, ?_⟩
    rw [placeY_apply, ← hu, map_nsmul, actY_inv]

private theorem range_le {x : (AfP p ⊗[ℚ] G.C)ˣ} {N : ℕ} {D₁ D₂ : PLat D.O D.inv} {t₁ : D.La → D₁.La}
    {t₂ : D.La → D₂.La} {j₁ : D₁.La →+ VQ D} {j₂ : D₂.La →+ VQ D} {h : G.GAf} {M : AddSubgroup (VQ D)}
    (hc₁ : IsCoordA L x N D₁ t₁ j₁ h) (hc₂ : IsCoordA L x N D₂ t₂ j₂ h)
    (hl₁ : IsLocP D₁ j₁ M) (hl₂ : IsLocP D₂ j₂ M) (u : D₁.La) : ∃ u₂, j₂ u₂ = j₁ u := by
  obtain ⟨r, u₂, hu₂⟩ := (hc₂.1 (j₁ u)).2 ((hc₁.1 (j₁ u)).1 ⟨0, u, by simp⟩)
  obtain ⟨m, u₃, hm, hu₃⟩ := (hl₂ (j₁ u)).2 ((hl₁ (j₁ u)).1 ⟨1, u, Nat.coprime_one_left p, one_smul _ _⟩)
  have hcop : IsCoprime ((p ^ r : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left r hm.symm)
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • u₂ + b • u₃, ?_⟩
  calc j₂ (a • u₂ + b • u₃) = a • j₂ u₂ + b • j₂ u₃ := by rw [map_add (f := _), map_zsmul, map_zsmul]
    _ = (a * ((p ^ r : ℕ) : ℤ) + b * (m : ℤ)) • j₁ u := by
      rw [← hu₂, ← hu₃, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
    _ = j₁ u := by rw [hab, one_smul]

private theorem mark_div {x : (AfP p ⊗[ℚ] G.C)ˣ} {N : ℕ} (hN0 : 0 < N) (hNp : N.Coprime p) {D₁ : PLat D.O D.inv}
    {j : D₁.La →+ VQ D} (hj : Function.Injective j) {h : G.GAf}
    (hc : ∀ w, (∃ (r : ℕ) (u : D₁.La), p ^ r • w = j u) ↔ rd L x h w ∈ LaHat D)
    (d : D₁.La) {w₃ : AfP p ⊗[ℚ] VQ D} (hw₃ : w₃ ∈ LaHat D) (hd : rd L x h (j d) = N • w₃) :
    ∃ e : D₁.La, d = N • e := by
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
  set w : VQ D := (N : ℚ)⁻¹ • j d with hwdef
  have hNw : N • w = j d := by
    rw [hwdef, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hN, one_smul]
  have e : rd L x h w = w₃ := by
    have h1 : (N : ℚ) • rd L x h w = (N : ℚ) • w₃ := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← rd_nsmul, hNw, hd]
    have h2 := congrArg (fun z => (N : ℚ)⁻¹ • z) h1
    simpa only [smul_smul, inv_mul_cancel₀ hN, one_smul] using h2
  obtain ⟨r, u, hu⟩ := (hc w).2 (e ▸ hw₃)
  have h3 : j (p ^ r • d) = j (N • u) := by
    rw [map_nsmul, map_nsmul, ← hNw, ← hu, smul_comm]
  have h4 := hj h3
  have hcop : IsCoprime (N : ℤ) ((p ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right r hNp)
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • d + b • u, ?_⟩
  calc d = (a * (N : ℤ) + b * ((p ^ r : ℕ) : ℤ)) • d := by rw [hab, one_smul]
    _ = N • (a • d + b • u) := by
      rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, h4, smul_add, smul_comm N a d,
        smul_comm N b u]

end UpperTheory.Gal.W2.LatticeIsomorphism

open UpperTheory.Gal.W2.LatticeIsomorphism

theorem UpperTheory.Gal.W2.latIso_of :
    UpperTheory.Gal.W2.RdAct → UpperTheory.Gal.W2.CoordKN → UpperTheory.Gal.W2.ClsScalar → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.LatIso := by
  intro hR hK hS hA p _ D G L B PD N hN hNp D' t D'' t'' j j'' a a'' N₁ N₂ t₁ t₂ hc₁ hc₂ hpl hpl'' hca hca''
    hlp hlp'' y
  have hcaY : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') (B.toAf y * a''.1) := coordA_placeY L hR B y hca''
  have hlpY : IsLocP D'' (placeY L y j'') (PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2)) := locP_placeY L PD y hlp''
  constructor
  · rintro ⟨hm1, hm2⟩
    have hcaY' : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') a.1 :=
      (hK p D G L (trivX B) N hN hNp D'' t'' (placeY L y j'') _ _ hcaY).2 (by rwa [← _root_.mul_assoc])
    have hlat : PD.lat a.2 = PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2) :=
      (PD.inj _ _).2 (by rwa [← _root_.mul_assoc])
    have hlpY' : IsLocP D'' (placeY L y j'') (PD.lat a.2) := by
      rw [hlat]
      exact hlpY
    have hex : ∀ u : D''.La, ∃ u', j u' = placeY L y j'' u := range_le L hcaY' hca hlpY' hlp
    have hex' : ∀ u' : D'.La, ∃ u, placeY L y j'' u = j u' := range_le L hca hcaY' hlp hlpY'
    choose f hf using hex
    have hinj := hpl.1
    have hadd : ∀ u v, f (u + v) = f u + f v := fun u v => hinj (by simp only [map_add (f := _), hf])
    have hsmul : ∀ (c : D.O) u, f (c • u) = c • f u := fun c u => hinj (by
      rw [hf, hpl.2.1, hf, placeY_apply, placeY_apply, hpl''.2.1, (hA p D G L B.β y).2.1])
    let fl : D''.La →ₗ[D.O] D'.La := { toFun := f, map_add' := hadd, map_smul' := hsmul }
    have hYinj : Function.Injective (placeY L y j'') := by
      intro u v huv
      rw [placeY_apply, placeY_apply] at huv
      have e := congrArg (actY L y⁻¹) huv
      rw [inv_actY, inv_actY] at e
      exact hpl''.1 e
    have hbij : Function.Bijective fl := by
      refine ⟨fun u v huv => hYinj ?_, fun u' => ?_⟩
      · rw [← hf, ← hf]
        exact congrArg j huv
      · obtain ⟨u, hu⟩ := hex' u'
        exact ⟨u, hinj ((hf u).trans hu)⟩
    let w := LinearEquiv.ofBijective fl hbij
    have hjw : ∀ u, j (w u) = actY L y (j'' u) := fun u => hf u
    obtain ⟨s, hs, hsf⟩ := hpl.2.2.2
    obtain ⟨s'', hs'', hsf''⟩ := hpl''.2.2.2
    have hy2 : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    have hsc : ∀ u u' : D''.La, (((D'.EF (w u)) (w u') : ℤ) : ℚ) =
        s * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) / s'' * (((D''.EF u) u' : ℤ) : ℚ) := by
      intro u u'
      rw [hsf, hjw, hjw, (hA p D G L B.β y).1, hsf'']
      field_simp
    have hr := hS p D N₁ N₂ D' t₁ D'' t₂ hc₁ hc₂ w.toAddEquiv _ (by positivity) hsc
    have hiso : IsIsom D'' D' w := by
      intro u u'
      have e := hsc u u'
      rw [hr, _root_.one_mul] at e
      exact_mod_cast e
    refine ⟨w, ⟨hiso, fun a0 => ?_⟩, hjw⟩
    obtain ⟨w1, hw1, e1⟩ := hca.2 a0
    obtain ⟨w2, hw2, e2⟩ := hcaY'.2 a0
    have hd : rd L (trivX B) a.1 (j (w (t'' a0) - t a0)) = N • (w2 - w1) := by
      rw [map_sub, rd_sub, hjw, ← placeY_apply, e2, e1, smul_sub]
      abel
    obtain ⟨e, he⟩ := mark_div L hN hNp hinj hca.1 _ (sub_mem hw2 hw1) hd
    exact ⟨e, eq_add_of_sub_eq' he⟩
  · rintro ⟨w, ⟨hiso, hmark⟩, hjw⟩
    have hjY : ∀ u, placeY L y j'' u = j (w u) := fun u => (hjw u).symm
    have hcaY' : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') a.1 := by
      refine ⟨fun w0 => ?_, fun a0 => ?_⟩
      · rw [← hca.1 w0]
        constructor
        · rintro ⟨r, u, hu⟩
          exact ⟨r, w u, by rw [hu, hjY]⟩
        · rintro ⟨r, u, hu⟩
          exact ⟨r, w.symm u, by rw [hu, hjY, LinearEquiv.apply_symm_apply]⟩
      · obtain ⟨e, he⟩ := hmark a0
        obtain ⟨w1, hw1, e1⟩ := hca.2 a0
        have he' : rd L (trivX B) a.1 (j e) ∈ LaHat D := (hca.1 (j e)).1 ⟨0, e, by simp⟩
        refine ⟨w1 + rd L (trivX B) a.1 (j e), add_mem hw1 he', ?_⟩
        rw [hjY, he, map_add (f := _), map_nsmul, rd_add, rd_nsmul, e1, smul_add, add_assoc]
    have hkn := (hK p D G L (trivX B) N hN hNp D'' t'' (placeY L y j'') _ _ hcaY).1 hcaY'
    have hlpY' : IsLocP D'' (placeY L y j'') (PD.lat a.2) := by
      intro w0
      rw [← hlp w0]
      constructor
      · rintro ⟨m, u, hm, hu⟩
        exact ⟨m, w u, hm, by rw [hu, hjY]⟩
      · rintro ⟨m, u, hm, hu⟩
        exact ⟨m, w.symm u, hm, by rw [hu, hjY, LinearEquiv.apply_symm_apply]⟩
    have hlat : PD.lat a.2 = PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2) := by
      ext w0
      rw [← hlpY' w0, ← hlpY w0]
    have hkh := (PD.inj _ _).1 hlat
    exact ⟨by rw [_root_.mul_assoc]; exact hkn, by rw [_root_.mul_assoc]; exact hkh⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_pos_toV_mulVec_of_pos {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : LKCx.grp G β) (z : Fin G.n → ℂ) (hz : 0 < (star z ⬝ᵥ LKCx.herm G v β *ᵥ z).re) :
    0 < (star (↑(LKCx.toV G v β y) *ᵥ z) ⬝ᵥ LKCx.herm G v β *ᵥ (↑(LKCx.toV G v β y) *ᵥ z)).re := by
  have hM : (↑(LKCx.toV G v β y) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v ↑(↑y : G.Cˣ × ℚˣ).1 := rfl
  have hs := GlobalTheory.ArchBound.herm_sim G β y v
  have hpos : (0 : ℝ) < ((↑(↑y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) := by exact_mod_cast y.2.2
  rw [hM, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_pos hpos hz

private theorem actY_actY_inv {p : ℕ} [Fact p.Prime] {D : UPel.HT.Datum p} {G : HTGroup p} (L : Link D G)
    {β : G.Cˣ} (a : LKCx.grp G β) (w : VQ D) : actY L a (actY L a⁻¹ w) = w := by
  show L.rep _ (L.rep _ w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  have h1 : ((↑(↑a : G.Cˣ × ℚˣ).1 : G.C) * ↑(↑a⁻¹ : G.Cˣ × ℚˣ).1) = 1 := by
    rw [← Units.val_mul, ← Prod.fst_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Prod.fst_one,
      Units.val_one]
  rw [h1, map_one, Module.End.one_apply]

theorem UpperTheory.Gal.W2.fixLine_of :
    UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.FixLine := by
  intro hA
  unfold ActY at hA
  unfold FixLine
  intro p _ D G L v t₀ ρ β RD Q z hQ hrel y
  have hz0 : z.1 ≠ 0 := by
    intro h0
    have h1 := z.2
    rw [h0] at h1
    simp at h1
  have hinvmul : ∀ (y' : LKCx.grp G β) (x : Fin G.n → ℂ),
      (LKCx.toV G v β y'⁻¹).val *ᵥ ((LKCx.toV G v β y').val *ᵥ x) = x := by
    intro y' x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have hne : ∀ (y' : LKCx.grp G β) (c : ℂ), (LKCx.toV G v β y').val *ᵥ z.1 = c • z.1 → c ≠ 0 := by
    rintro y' c hc rfl
    rw [zero_smul] at hc
    apply hz0
    rw [← hinvmul y' z.1, hc, Matrix.mulVec_zero]
  have inv : ∀ y' : LKCx.grp G β, LKCx.FixL G v β y' z.1 → LKCx.FixL G v β y'⁻¹ z.1 := by
    rintro y' ⟨c, hc⟩
    have hc0 := hne y' c hc
    have h1 : z.1 = c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1) := by
      rw [← Matrix.mulVec_smul, ← hc, hinvmul]
    refine ⟨c⁻¹, ?_⟩
    calc (LKCx.toV G v β y'⁻¹).val *ᵥ z.1
        = c⁻¹ • (c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • z.1 := by rw [← h1]
  let zi : LKCx.PosV G v β := ⟨(LKCx.toV G v β y⁻¹).val *ᵥ z.1, herm_pos_toV_mulVec_of_pos G v β y⁻¹ z.1 z.2⟩
  let Q₂ : VQ D →+ Fin D.g → ℂ := Q.comp (actY L y).toAddMonoidHom
  have hQ₂ : ∀ w, Q₂ w = Q (actY L y w) := fun w => rfl
  have hback : ∀ w, Q₂ (actY L y⁻¹ w) = Q w := by
    intro w
    rw [hQ₂, actY_actY_inv]
  have hper : IsPerQ L β ρ Q₂ := (hA p D G L β y⁻¹).2.2.1 ρ Q Q₂ hQ hback
  have hrel₂ : RD.rel Q₂ zi.1 := RD.equiv y⁻¹ Q Q₂ z.1 hback hrel
  have key := RD.uniq Q Q₂ z zi hQ hper hrel hrel₂
  refine ⟨⟨fun hF => ?_, fun ⟨H, hH⟩ => ?_⟩, inv y⟩
  · obtain ⟨c, hc⟩ := inv y hF
    obtain ⟨h, hh⟩ := key.mpr ⟨c, hne _ c hc, hc⟩
    refine ⟨LinearMap.toMatrix' (h : (Fin D.g → ℂ) →ₗ[ℂ] Fin D.g → ℂ), fun w => ?_⟩
    rw [LinearMap.toMatrix'_mulVec, ← hQ₂, hh w]
    rfl
  · have hsurj : Function.Surjective (Matrix.toLin' H) := by
      rw [← LinearMap.range_eq_top]
      have hle : Submodule.span ℝ (Set.range ⇑Q) ≤ (LinearMap.range (Matrix.toLin' H)).restrictScalars ℝ := by
        rw [Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        refine ⟨Q (actY L y⁻¹ w), ?_⟩
        rw [Matrix.toLin'_apply, ← hH, actY_actY_inv]
      rw [hQ.2.1] at hle
      exact eq_top_iff.mpr (fun x _ => hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ (Fin D.g → ℂ))))
    have hinj := LinearMap.injective_iff_surjective.mpr hsurj
    obtain ⟨c, hc0, hc⟩ := key.mp ⟨LinearEquiv.ofBijective (Matrix.toLin' H) ⟨hinj, hsurj⟩, fun w => by
      show Q₂ w = Matrix.toLin' H (Q w)
      rw [Matrix.toLin'_apply, hQ₂, hH]⟩
    have h2 := inv y⁻¹ ⟨c, hc⟩
    rwa [inv_inv] at h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLatForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem nsmul_canc {V : Type} [AddCommGroup V] [Module ℚ V] {a : ℕ} (ha : a ≠ 0) {x y : V}
    (h : a • x = a • y) : x = y := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have h' : (a : ℚ) • x = (a : ℚ) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact h
  exact (smul_right_injective V ha') h'

private theorem ext_lin {Λ V V' : Type} [AddCommGroup Λ] [AddCommGroup V] [AddCommGroup V'] [Module ℚ V]
    [Module ℚ V'] (j : Λ →+ V) (hj : Function.Injective j)
    (hs : ∀ v, ∃ (m : ℕ) (u : Λ), m ≠ 0 ∧ m • v = j u) (f : Λ →+ V') :
    ∃ A : V →ₗ[ℚ] V', ∀ u, A (j u) = f u := by
  choose m u hm hu using hs
  let g : V → V' := fun v => ((m v : ℚ))⁻¹ • f (u v)
  have hg : ∀ v, m v • g v = f (u v) := by
    intro v
    have h0 : (m v : ℚ) ≠ 0 := by exact_mod_cast hm v
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have key : ∀ (a : ℕ) (x : Λ) (v : V), a ≠ 0 → a • v = j x → a • g v = f x := by
    intro a x v ha hx
    have e : m v • x = a • u v := by
      apply hj
      rw [map_nsmul, map_nsmul, ← hx, ← hu v, smul_comm]
    apply nsmul_canc (hm v)
    rw [smul_comm, hg, ← map_nsmul, ← map_nsmul, e]
  have hadd : ∀ v₁ v₂, g (v₁ + v₂) = g v₁ + g v₂ := by
    intro v₁ v₂
    have h12 : m v₁ * m v₂ ≠ 0 := mul_ne_zero (hm _) (hm _)
    apply nsmul_canc h12
    rw [key (m v₁ * m v₂) (m v₂ • u v₁ + m v₁ • u v₂) (v₁ + v₂) h12 ?_]
    · rw [map_add (f := _), map_nsmul, map_nsmul, smul_add, ← hg v₁, ← hg v₂, smul_smul, smul_smul, mul_comm (m v₂),
        mul_comm (m v₁) (m v₂)]
    · rw [map_add (f := _), map_nsmul, map_nsmul, ← hu v₁, ← hu v₂, smul_add, smul_smul, smul_smul, mul_comm (m v₂)]
  refine ⟨(AddMonoidHom.mk' g hadd).toRatLinearMap, fun x => ?_⟩
  show g (j x) = f x
  have h1 : (1 : ℕ) • g (j x) = f x := key 1 x (j x) one_ne_zero (one_nsmul _)
  simpa using h1

theorem UpperTheory.Gal.W2.latForm_of :
    UpperTheory.Gal.W2.LatForm := by
  intro p _ D G L β β' D' D'' j j'' hP hP'' w m hm hw
  obtain ⟨hj, hjO, hjs, s₀, hs₀, hjF⟩ := hP
  obtain ⟨hj2, hjO2, hjs2, s₂, hs₂, hjF2⟩ := hP''
  obtain ⟨A, hA⟩ := ext_lin j'' hj2 hjs2 (j.comp w.toAddMonoidHom)
  replace hA : ∀ u, A (j'' u) = j (w u) := hA
  haveI := D.finLa
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun v hv => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    have h1 : j (w u) = 0 := by rw [← hA, ← hu, map_nsmul, hv, smul_zero]
    have h2 : w u = 0 := hj (by rw [h1, map_zero])
    have h3 : u = 0 := by
      refine D''.nondeg u fun u' => ?_
      have := hw u u'
      rw [h2] at this
      simp only [map_zero, LinearMap.zero_apply] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h hm.ne'
      · exact h
    apply nsmul_canc ha
    rw [hu, h3, map_zero, smul_zero]
  let Ae := LinearEquiv.ofInjectiveEndo A hAinj
  let B : Module.End ℚ (VQ D) := (Ae.symm : VQ D →ₗ[ℚ] VQ D)
  have hAB : A * B = 1 := LinearEquiv.ofInjectiveEndo_right_inv A hAinj
  have hBA : B * A = 1 := LinearEquiv.ofInjectiveEndo_left_inv A hAinj
  have hcomm : ∀ b, A * actQ D b = actQ D b * A := by
    intro b
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    apply nsmul_canc ha
    show a • A (actQ D b v) = a • actQ D b (A v)
    calc a • A (actQ D b v) = A (actQ D b (a • v)) := by rw [map_nsmul, map_nsmul]
      _ = A (j'' (b • u)) := by rw [hu, hjO2]
      _ = j (w (b • u)) := hA _
      _ = j (b • w u) := by rw [map_smul]
      _ = actQ D b (j (w u)) := hjO _ _
      _ = actQ D b (A (a • v)) := by rw [hu, hA]
      _ = a • actQ D b (A v) := by rw [map_nsmul, map_nsmul]
  have hBcomm : ∀ b, B * actQ D b = actQ D b * B := by
    intro b
    calc B * actQ D b = B * actQ D b * (A * B) := by rw [hAB, _root_.mul_one]
      _ = B * (actQ D b * A) * B := by simp only [_root_.mul_assoc]
      _ = B * (A * actQ D b) * B := by rw [hcomm]
      _ = (B * A) * actQ D b * B := by simp only [_root_.mul_assoc]
      _ = actQ D b * B := by rw [hBA, _root_.one_mul]
  obtain ⟨x, hx⟩ := (L.rep_range A).2 hcomm
  obtain ⟨x', hx'⟩ := (L.rep_range B).2 hBcomm
  have hxx' : x * x' = 1 := L.rep_inj (by rw [map_mul, hx, hx', hAB, map_one])
  have hx'x : x' * x = 1 := L.rep_inj (by rw [map_mul, hx, hx', hBA, map_one])
  let y : G.Cˣ := ⟨x, x', hxx', hx'x⟩
  have hform : ∀ v v', s₀ * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) (A v') =
      (m : ℚ) * s₂ * D.EF.baseChange ℚ (L.rep ((β'⁻¹ : G.Cˣ) : G.C) v) v' := by
    intro v v'
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    obtain ⟨b, u', hb, hu'⟩ := hjs2 v'
    have e1 := hjF (w u) (w u')
    have e2 := hjF2 u u'
    have e3 : ((D'.EF (w u) (w u') : ℤ) : ℚ) = (m : ℚ) * (D''.EF u u' : ℤ) := by
      rw [hw u u']; push_cast; ring
    unfold formB at e1 e2
    rw [← hA, ← hA, ← hu, ← hu', map_nsmul, map_nsmul, map_nsmul] at e1
    rw [← hu, ← hu', map_nsmul] at e2
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at e1 e2
    have hab : (a : ℚ) * b ≠ 0 := mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hb)
    apply mul_left_cancel₀ hab
    linear_combination -e1 + e3 + (m : ℚ) * e2
  have hnd : ∀ a : VQ D, (∀ v, D.EF.baseChange ℚ a v = 0) → a = 0 := by
    intro a ha
    obtain ⟨c, u, hc, hu⟩ := hjs (L.rep (β : G.C) a)
    have hinv : ∀ z : VQ D, L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (β : G.C) z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
    have hu0 : u = 0 := by
      refine D'.nondeg u fun u' => ?_
      have e := hjF u u'
      unfold formB at e
      rw [← hu, map_nsmul, hinv] at e
      simp only [map_nsmul, LinearMap.smul_apply, ha, smul_zero, mul_zero] at e
      exact_mod_cast e
    have h0 : c • L.rep (β : G.C) a = c • (0 : VQ D) := by rw [hu, hu0, map_zero, smul_zero]
    have := nsmul_canc hc h0
    rw [← hinv a, this, map_zero]
  set r : ℚ := (m : ℚ) * s₂ / s₀ with hr
  have hr0 : 0 < r := by
    have : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hs₀' : s₀ ≠ 0 := hs₀.ne'
  have hshsh : sh G (sh G x) = x := G.star_star x
  have hkey : sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x = algebraMap ℚ G.C r * ((β'⁻¹ : G.Cˣ) : G.C) := by
    apply L.rep_inj
    refine LinearMap.ext fun v => ?_
    rw [← sub_eq_zero]
    refine hnd _ fun v' => ?_
    have e := hform v v'
    have e2 := L.adj (sh G x) (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) v'
    rw [hshsh, hx] at e2
    simp only [map_mul, Module.End.mul_apply, hx, AlgHom.commutes, Module.algebraMap_end_apply,
      map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [e2, hr]
    field_simp
    linear_combination e
  refine ⟨y, Units.mk0 r hr0.ne', hr0, ?_, fun u => ?_⟩
  · show x * (β' : G.C) * sh G x = algebraMap ℚ G.C r * (β : G.C)
    have h1 : x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) = r • x := by
      calc x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x)
          = x * (β' : G.C) * (sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x) := by simp only [_root_.mul_assoc]
        _ = r • (x * ((β' : G.C) * ((β'⁻¹ : G.Cˣ) : G.C))) := by
            rw [hkey, ← Algebra.smul_def, mul_smul_comm, _root_.mul_assoc]
        _ = r • x := by rw [Units.mul_inv, _root_.mul_one]
    calc x * (β' : G.C) * sh G x
        = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * (x * x') * (β : G.C)) := by
          rw [hxx', _root_.mul_one, Units.inv_mul, _root_.mul_one]
      _ = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) * (x' * (β : G.C)) := by
          simp only [_root_.mul_assoc]
      _ = r • (x * x' * (β : G.C)) := by rw [h1, smul_mul_assoc, _root_.mul_assoc]
      _ = algebraMap ℚ G.C r * (β : G.C) := by rw [hxx', _root_.one_mul, Algebra.smul_def]
  · show j (w u) = L.rep x (j'' u)
    rw [hx, hA]
end

namespace UpperTheory.Gal.W2

theorem ModelEx_holds : ModelEx := GlobalTheory.UPel.HT.model_nonempty

theorem GenCmp_holds : GenCmp := GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre

theorem GenPts_holds : GenPts := UpperTheory.Cb.complexModel_points_of_genericFiber_embedding

theorem EmbAll_holds : EmbAll := embAll_of

theorem FTrace_holds : FTrace := fTrace_of EmbAll_holds

theorem FInt_holds : FInt := fInt_of EmbAll_holds

theorem FApprox_holds : FApprox := fApprox_of EmbAll_holds

theorem TrDual_holds : TrDual := trDual_of

theorem MemDual_holds : MemDual := memDual_of TrDual_holds

theorem KpMem_holds : KpMem := kpMem_of

theorem LocLat_holds : LocLat := locLat_of

theorem OOnto_holds : OOnto := oOnto_of

theorem FMat_holds : FMat := fMat_of

theorem FForm_holds : FForm := fForm_of

theorem SN_holds : SN := sN_of

theorem PFrameEx_holds : PFrameEx := pFrameEx_of FMat_holds FForm_holds SN_holds FTrace_holds FInt_holds FApprox_holds

theorem PLatOf_holds : PLatOf := pLatOf_of

theorem PkLat_holds : PkLat := pkLat_of OOnto_holds MemDual_holds PLatOf_holds

theorem PkEquiv_holds : PkEquiv := pkEquiv_of

theorem PkPerf_holds : PkPerf := pkPerf_of MemDual_holds

theorem PkInj_holds : PkInj := pkInj_of MemDual_holds EmbAll_holds

theorem PkOnto_holds : PkOnto := pkOnto_of LocLat_holds FApprox_holds FInt_holds PkLat_holds PkPerf_holds OOnto_holds

theorem ArchSpan_holds : ArchSpan := archSpan_of

theorem ArchEx_holds : ArchEx := archEx_of FMat_holds FForm_holds SN_holds ArchSpan_holds

theorem SigB_holds : SigB := sigB_of

theorem PerExt_holds : PerExt := perExt_of

theorem JStruct_holds : JStruct := jStruct_of ArchSpan_holds

theorem JLine_holds : JLine := jLine_of

theorem HermOfJ_holds : HermOfJ := hermOfJ_of

theorem LineBasis_holds : LineBasis := lineBasis_of

theorem PlaceT_holds : PlaceT := placeT_of

theorem TypeIso_holds : TypeIso := typeIso_of SimDiag_holds ExtendEmb_holds TypeCount_holds PlaceT_holds

theorem RPer_holds : RPer := rPer_of SigB_holds LineBasis_holds TypeIso_holds HermOfJ_holds PlaceT_holds

theorem RDicEx_holds : RDicEx := rDicEx_of ArchEx_holds SigB_holds PerExt_holds JStruct_holds JLine_holds RPer_holds PlaceT_holds

theorem RhoSig_holds : RhoSig := rhoSig_of

theorem BaseC_holds : BaseC := baseC_of

theorem GFine_holds : GFine := gFine_of

theorem GUnif_holds : GUnif := gUnif_of ModelEx_holds GenCmp_holds GenPts_holds BaseC_holds GFine_holds

theorem SheetOf_holds : SheetOf := sheetOf_of

theorem FixFinite_holds : FixFinite := fixFinite_of

theorem RdAct_holds : RdAct := rdAct_of

theorem RdForm_holds : RdForm := rdForm_of

theorem RdDense_holds : RdDense := rdDense_of

theorem AdCore_holds : AdCore := adCore_of

theorem AdOfWit_holds : AdOfWit := adOfWit_of AdCore_holds

theorem WitOfAd_holds : WitOfAd := witOfAd_of RdForm_holds RdDense_holds RdAct_holds

theorem CoordKN_holds : CoordKN := coordKN_of RdDense_holds

theorem PlacePer_holds : PlacePer := placePer_of

theorem PlaceLoc_holds : PlaceLoc := placeLoc_of

theorem LatForm_holds : LatForm := latForm_of

theorem ClsScalar_holds : ClsScalar := clsScalar_of

theorem ActY_holds : ActY := actY_of

theorem LatIso_holds : LatIso := latIso_of RdAct_holds CoordKN_holds ClsScalar_holds ActY_holds

theorem CoordMove_holds : CoordMove := coordMove_of

theorem PlaceEx_holds : PlaceEx := placeEx_of AdCore_holds LatForm_holds

theorem CoordEx_holds : CoordEx := coordEx_of PlaceEx_holds AdOfWit_holds PlaceLoc_holds PlacePer_holds

theorem CoordOcc_holds : CoordOcc := coordOcc_of WitOfAd_holds PlacePer_holds

theorem CoordIso_holds : CoordIso := coordIso_of LatForm_holds LatIso_holds ActY_holds

theorem UnifG_holds : UnifG := unifG_of CoordEx_holds CoordOcc_holds CoordIso_holds CoordMove_holds

theorem Rigid_holds : Rigid := rigid_of

theorem FixLine_holds : FixLine := fixLine_of ActY_holds

theorem StabTriv_holds : StabTriv := stabTriv_of CoordOcc_holds LatIso_holds FixLine_holds Rigid_holds

theorem IsogForm_holds : IsogForm := isogForm_of RdForm_holds

theorem IsogCoord_holds : IsogCoord := isogCoord_of AdOfWit_holds CoordKN_holds IsogForm_holds RdDense_holds

theorem IntMult_holds : IntMult := intMult_of

theorem RegSep_holds : RegSep := regSep_of

theorem InvMin_holds : InvMin := invMin_of

theorem MinBridge_holds : MinBridge := minBridge_of

theorem EigSame_holds : EigSame := eigSame_of

theorem SumPts_holds : SumPts := sumPts_of EigSame_holds

theorem LevelChange_holds : LevelChange := levelChange_of EigSame_holds

theorem TateWit_holds : TateWit := tateWit_of

theorem IsogAt_holds : IsogAt := isogAt_of TateWit_holds PerLin_holds

theorem HeckeCoord_holds : HeckeCoord := heckeCoord_of IsogAt_holds IsogCoord_holds

theorem OneAt_holds : OneAt := oneAt_of HeckeCoord_holds LatIso_holds

theorem FixFwd_holds : FixFwd := fixFwd_of HeckeCoord_holds OneAt_holds LatForm_holds LatIso_holds FixLine_holds ActY_holds

theorem FixGa_holds : FixGa := fixGa_of HeckeCoord_holds LatIso_holds FixLine_holds ActY_holds IntMult_holds

theorem FixEq_holds : FixEq := fixEq_of HeckeCoord_holds OneAt_holds LatIso_holds

theorem PwOver_holds : PwOver := pwOver_of

theorem PowCorr_holds : PowCorr := powCorr_of PwOver_holds PtFibre_holds

theorem PowSm_holds : PowSm := powSm_of

theorem FixLoc_holds : FixLoc := fixLoc_of SheetOf_holds FixGa_holds FixEq_holds OneAt_holds PowCorr_holds CspDim_holds AdExists_holds EigTop_holds LocSum_holds RegSep_holds InvMin_holds MinBridge_holds CorrChart_holds PtFibre_holds

theorem PDicEx_holds : PDicEx := pkTop_of PFrameEx_holds PkLat_holds PkEquiv_holds PkPerf_holds PkInj_holds PkOnto_holds KpMem_holds

theorem fixedPoints_int_base_holds : HeckeFixedPointCMCycleClass := fixedPoints_integral_base_of_uniformisation RhoSig_holds GUnif_holds PDicEx_holds RDicEx_holds UnifG_holds StabTriv_holds FixFwd_holds FixEq_holds FixGa_holds FixLoc_holds TanExists_holds FixFinite_holds PowSm_holds PwOver_holds SumPts_holds EigSame_holds

theorem FixZ_holds : FixZ := fixZ_of fixedPoints_int_base_holds LevelChange_holds

end UpperTheory.Gal.W2
