module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.LinOfPoly
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.CountSpanSingletonAlgebraMapEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.FrBC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem isRigIso_iff {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) :
    IsRigIso m L' L w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl))

theorem exists_rigIso_cancel {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w'' : LB.Iso L''.L (L.L.pull n.F)) (hw : IsRigIso m L' L w) (hw'' : IsRigIso n L'' L w'') :
    ∃ w' : LB.Iso L''.L (L'.L.pull m'.F), IsRigIso m' L'' L' w' ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ G''.left) (y : Y) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        m.F (m'.F (f y)) ∈ L.L.U j → m'.F (f y) ∈ L'.L.U i → f y ∈ L''.L.U k →
        gw w'' f y j k = gw w (f ≫ m'.F) y j i * gw w' f y i k := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  rw [isRigIso_iff] at hw hw''
  obtain ⟨g, r⟩ := hw
  obtain ⟨g'', r''⟩ := hw''
  obtain ⟨w', T⟩ := exists_cancel L.isLB w w'' g g'' L'.isLB L''.isLB
  exact ⟨w', (isRigIso_iff _ _ _ _).2 ⟨T.pgen_cancel L.isLB g g'',
    T.pmaps_cancel L.isLB (fun _ => m'.e_comm) r r''⟩, T⟩

theorem gs_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} {θ : LB.Sec L} (h : IsoMaps w σ s) (p : PullSec F θ s)
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have a := congrArg (gs r z _) (h (fun _ => j) k)
  have le : (L.pull F).U (fun _ => j) ≤ F ⁻¹ᵁ L.U j := fun q hq => mem_pull.1 hq
  refine Eq.trans ?_ ((gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _)))))
  rw [p (fun _ => j) le]
  exact (gs_appLE F _ _ le r z (mem_pull.2 hj) _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isoMaps_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {x : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (n : SABMap t'' t x) (hx : x = g ≫ f)
    (hφ : n.φ = m'.φ ≫ m.φ) {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {w'' : LB.Iso t''.PP.L (t.PP.L.pull n.φ)}
    (hw : RigIso m w) (hw'' : RigIso n w'') {θ : LB.Sec t.PP.L} {θ' : LB.Sec t'.PP.L} {σ : LB.Sec t''.PP.L}
    {s : LB.Sec (t.PP.L.pull m.φ)} {s'' : LB.Sec (t.PP.L.pull n.φ)} (i : IsoMaps w θ' s) (p : PullSec m.φ θ s)
    (i'' : IsoMaps w'' σ s'') (p'' : PullSec n.φ θ s'') :
    ∃ w' : LB.Iso t''.PP.L (t'.PP.L.pull m'.φ), RigIso m' w' ∧ IsoMaps w' σ (thfPull t'.PP.L m'.φ θ') := by
  have he : n.cm.e = m'.cm.e ≫ m.cm.e := by rw [n.base, m'.base, m.base, hx]
  obtain ⟨w', r', tri⟩ := exists_rigIso_cancel m.cm m'.cm n.cm hφ he t''.PP t'.PP t.PP w w'' hw hw''
  refine ⟨w', r', fun (a : PUnit → t'.PP.L.ι) k => fn_ext fun y hy => ?_⟩
  have hi : m'.φ y ∈ t'.PP.L.U (a PUnit.unit) := mem_pull.1 hy.1
  obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (m'.φ y))
  have pt : n.φ y = m.φ (m'.φ y) := congrArg (fun q => q y) hφ
  have e1 := gs_of_isoMaps i p (𝟙 _ ≫ m'.φ) y j (a PUnit.unit) hj hi
  have e2 := gs_of_isoMaps i'' p'' (𝟙 _) y j k (pt ▸ hj) hy.2
  have e3 := tri _ (𝟙 _) y j (a PUnit.unit) k hj hi hy.2
  have e4 : (𝟙 _ ≫ m'.φ) ≫ m.φ = 𝟙 _ ≫ n.φ := by rw [Category.assoc, hφ]
  rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
  refine (gs_res _ y _ hy _).trans ((gs_appLE m'.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
  refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
  exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (φ.comp io) = spMap φ ≫ spMap io := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← spMap_comp', ← spMap_comp']
  congr 1
  exact Formalism.L2.Pj.dualMap_alg φ

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (dualMap (φ.comp io)) = spMap (dualMap φ) ≫ spMap (dualMap io) := by
  rw [← spMap_comp']
  congr 1
  exact Formalism.L2.Pj.dualMap_comp io φ

end GlobalTheory.ArcQ.FrBC

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames


open FrBC in
theorem isArcFr_witBC : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A'] (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A') (p : Out.IsPullDeg f a.D₀ a'.D₀) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)), Mono Y.j → InBC f a a' p → WitBC f p W W' → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A')) th th', (∀ τ k, LetBC p (e τ k) (e' τ k)) → ThBC p th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι' : PowerSeries A' →+* S) (y : FrPt Xo c S), IsArcFr W e th (ι'.comp (PowerSeries.map f)) y → IsArcFr W' e' th' ι' y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W A' _ _ _ _ b' a' f p W' hj hin hwit e e' th th' he hth
    S _ _ ι' y h
  obtain ⟨m, hm, hlie, hθ⟩ := GlobalTheory.T.tangentVectors_thetaSection_arcWitness_baseChange
    hL hL2 E H Dw l Xo c O β Y A b a χ W A' b' a' f p W' hin hwit
  obtain ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hT, r1, r2, i1, i2, p2, hg⟩ := h
  have hio : spMap (ι'.comp (PowerSeries.map f)) = spMap ι' ≫ spMap (PowerSeries.map f) := spMap_comp' _ _
  have key : ∀ (g : Sp S ⟶ Sp (PowerSeries A)) (n : SABMap G W.t g), g = spMap ι' ≫ spMap (PowerSeries.map f) →
      ∃ m' : SABMap G W'.t (spMap ι'), n.φ = m'.φ ≫ m.φ := by
    intro g n hg
    subst hg
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
  obtain ⟨m', e₂⟩ := key _ m2 hio
  obtain ⟨w, θ', rw', iw⟩ := pull_sec W.t W'.t m θ
  have pw : PullSec m.φ θ (thfPull W.t.PP.L m.φ θ) := fun _ _ => rfl
  obtain ⟨w', r', i'⟩ := exists_isoMaps_cancel m m' m2 hio e₂ rw' r2 iw pw i2 p2
  refine ⟨z, G, m1, m', φ, ?_, zx, φb, φ1, ?_, fun τ k => ?_, θ', w1, w', σ, s1, _,
    hθ w th th' θ θ' _ rw' hth hT pw iw, r1, r', i1, i', fun _ _ => rfl, hg⟩
  · rw [zj, hio, Category.assoc]
  · rw [φ2, hm, e₂, Category.assoc]
  · obtain ⟨v, q₀, h1, h2, h3, -⟩ := hu τ k
    have vb : v.left ≫ W.t.G.hom = spMap (algebraMap _ (DualNumber (PowerSeries A))) := Over.w v
    have pb : (q₀ ≫ G.G.hom) ≫ spMap (ι'.comp (PowerSeries.map f)) =
        spMap (algebraMap S (DualNumber S)) ≫ spMap (ι'.comp (PowerSeries.map f)) := by
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc]
      exact (congrArg (· ≫ W.t.G.hom) h3).trans (by rw [Category.assoc, vb, dual_alg])
    have pz : (q₀ ≫ G.G.hom) ≫ z = spMap (algebraMap S (DualNumber S)) ≫ z := by
      rw [← cancel_mono Y.j, Category.assoc, zj, ← Category.assoc, pb, Category.assoc, Category.assoc, zj]
    let q := m1.cart.1.lift (y.u τ k) _ (y.tan τ k).1
    have hq : q ≫ m1.φ = y.u τ k := m1.cart.1.lift_fst _ _ _
    have qb : q ≫ G.G.hom = spMap (algebraMap S (DualNumber S)) := m1.cart.1.lift_snd _ _ _
    have qφ : q ≫ φ = q₀ ≫ φ := by
      apply Y.m0.toSABMap.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc]
        exact ((congrArg _ φ1).trans (hq.trans h2.symm)).trans (congrArg _ φ1.symm)
      · rw [Category.assoc, Category.assoc, φb, ← Category.assoc, ← Category.assoc, qb, pz]
    have q2 : q ≫ m2.φ = q₀ ≫ m2.φ := by
      apply W.m.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc]
        refine (congrArg _ φ2.symm).trans (Eq.trans ?_ (congrArg _ φ2))
        rw [← Category.assoc, qφ, Category.assoc]
      · rw [Category.assoc, Category.assoc, m2.cart.1.w, ← Category.assoc, ← Category.assoc, qb, pb]
    have cond : (spMap (dualMap (PowerSeries.map f)) ≫ v.left) ≫ W.t.G.hom =
        spMap (algebraMap (PowerSeries A') (DualNumber (PowerSeries A'))) ≫ spMap (PowerSeries.map f) := by
      rw [Category.assoc, vb, dual_alg]
    let v' : epsR (PowerSeries A') ⟶ W'.t.G := Over.homMk (m.cart.1.lift _ _ cond) (m.cart.1.lift_snd _ _ cond)
    have hv : v'.left ≫ m.φ = spMap (dualMap (PowerSeries.map f)) ≫ v.left := m.cart.1.lift_fst _ _ cond
    have vb' : v'.left ≫ W'.t.G.hom = spMap (algebraMap _ (DualNumber (PowerSeries A'))) := Over.w v'
    refine ⟨v', q, hlie _ _ v v' (he τ k) h1 hv, hq, ?_, qb⟩
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      refine (congrArg _ e₂.symm).trans ((q2.trans h3).trans (Eq.trans ?_ (congrArg _ hv.symm)))
      rw [dual_comp, Category.assoc]
    · rw [Category.assoc, Category.assoc, m'.cart.1.w, vb', dual_alg, ← Category.assoc, qb]

end GlobalTheory.ArcQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChangeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFramedPoint_of_arc_baseChange :
    Out.Laws → Out.Laws2 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
      (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
      (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
      (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ)
      (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A']
      (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A')
      (p : Out.IsPullDeg f a.D₀ a'.D₀) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)),
      Mono Y.j → InBC f a a' p → WitBC f p W W' →
      ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A))
        (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A')) th th',
        (∀ τ k, GlobalTheory.ArcQ.LetBC p (e τ k) (e' τ k)) → ThBC p th th' →
        ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι' : PowerSeries A' →+* S) (y : FrPt Xo c S),
          GlobalTheory.ArcQ.IsArcFr W e th (ι'.comp (PowerSeries.map f)) y →
            GlobalTheory.ArcQ.IsArcFr W' e' th' ι' y :=
  @GlobalTheory.ArcQ.isArcFr_witBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.TransvPrinc

theorem transvIn_of_princ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {M N : ℕ}
    (hMN : M ∣ N) (la : Wt X.Ψ r)
    (hP : ∀ gm : GL (Fin r) E, IsUStab X.Gm X.Λ gm →
      (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (gm : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → gm ∈ X.Γ)
    (hχ : ∀ gm ∈ X.Γ, X.χ la gm = 1) : TransvIn X N la := by
  intro ξ hξ s hs hc
  have hκ : cc (s * X.κ0) = -(s * X.κ0) := by
    have h0 := X.ξ0_im
    simp only [cc] at hs h0 ⊢
    rcases X.κ0_xi with h | h <;> simp [h, hs, h0, map_ofNat]
  have hn : ∀ (n : ℕ) u, u ∈ X.Λ → (n : E) • u ∈ X.Λ := fun n u hu => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hu n
  have hmem : GlobalTheory.FlagData.transv X.Gm hξ.2.1 (s * X.κ0) ∈ X.Γ := by
    refine hP _ ⟨fun x y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩ (fun x hx => ?_)
    · exact GlobalTheory.FlagData.herm_transvMat X.Gm_herm hξ.2.1 hκ x y
    · obtain ⟨u, hu, e⟩ := hc x hx
      rw [sub_eq_iff_eq_add] at e
      change (transvMat _ _ _).mulVec x ∈ _
      rw [e]; exact add_mem (hn _ u hu) hx
    · change (transvMat _ _ _).mulVec x ∈ _ at hx
      obtain ⟨u, hu, e⟩ := hc _ hx
      have : x = (transvMat X.Gm ξ (s * X.κ0)).mulVec x - (N : E) • u := by
        rw [← e, GlobalTheory.FlagData.transvMat_mulVec _ _ (Matrix.mulVec _ _), GlobalTheory.FlagData.transvMat_mulVec,
          GlobalTheory.FlagData.herm_add_smul_left, hξ.2.1]
        simp
      rw [this]; exact sub_mem hx (hn _ u hu)
    · obtain ⟨m, hm⟩ := hMN
      obtain ⟨u, hu, e⟩ := hc x hx
      refine ⟨(m : E) • u, hn m u hu, ?_⟩
      change (transvMat _ _ _).mulVec x - x = _
      rw [e, hm, smul_smul]
      push_cast; rfl
  exact ⟨_, hmem, rfl, hχ _ hmem⟩

theorem transvIn_of_hasPrinc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.FrameNorm.HasPrinc U l.M → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → ∀ k, TransvIn (U.X k) l.M' (laU U a' n k) := by
  intro E _ _ _ H Dw l Xo c σ r U a' n hP hχ k
  exact transvIn_of_princ (U.X k) (Nat.dvd_lcm_left _ _) _ (hP k) (hχ k)

end GlobalTheory.TransvPrinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointExpEqOfIsometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem isHolTo_comp_univ {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set W} {y : W → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {φ : V → W}
    (hφ : Differentiable ℂ φ) (hB : ∀ z, φ z ∈ B) : IsHolTo Set.univ (fun z => y (φ z)) := by
  unfold IsHolTo at hy ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hset : {b | b ∈ (Set.univ : Set V) ∧ ⊤ ≤ (fun z => y (φ z)) b ⁻¹ᵁ U} =
      φ ⁻¹' {b | b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ, true_and, hB b]
  rw [hset]
  exact ⟨ho.preimage hφ.continuous, hd.comp hφ.differentiableOn (fun b hb => hb)⟩

theorem isHolTo_exp_of_isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (Fu.Di i) ty P) : IsHolTo Set.univ (fun z => (Fu.ex i P z).left) := by

  have hper : IsHolPeriods (Fu.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have hjoint : IsHolTo ((Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)))
      (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (Fu.ex i P bz.2).left) :=
    (Fu.21 i 0 Set.univ (fun _ => P) isOpen_univ hper).2
  have hφ : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  have hmem : ∀ z : Fin g → ℂ, ((0 : Fin 0 → ℂ), z) ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
    fun z => Set.mk_mem_prod (Set.mem_univ _) (Set.mem_univ _)
  have hcomp := isHolTo_comp_univ hjoint hφ hmem
  exact hcomp

theorem point_exp_eq_of_isometry : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i').La) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i') ty P' → (∀ u v, (Fu.Di i').EF (gm u) (gm v) = (Fu.Di i).EF u v) → (∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gm (Fu.t i v) = Fu.t i' v + l.M • e) → (∀ u, P' (gm u) = L (P u)) → Fu.u i P = Fu.u i' P' ∧ ∀ z, (Fu.ex i' P' (L z)).left = (Fu.ex i P z).left := by
  intro hK E _ _ _ H D l Xo σ g ty Fu i i' P P' gm L hpq hρ hty hA hP hP' hiso hmark hPL

  have hpt : Fu.u i P = Fu.u i' P' := by
    refine (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hK.theta hK.laws E H D l Xo σ g ty hpq hρ hty
      (Fu.Di i) (Fu.Di i') (Fu.t i) (Fu.t i') P P' (Fu.u i P) (Fu.u i' P') (Fu.ex i P) (Fu.ex i' P')
      ⟨Fu.over_σ i P hP, hP, ⟨Fu.ex_add i P hP, Fu.ex_onto i P hP, isHolTo_exp_of_isPeriod Fu i P hP,
        (Fu.22 i P hP).1, (Fu.22 i P hP).2⟩, Fu.ex_ker i P hP, Fu.ex_lin i P hP, Fu.ex_weil i P hP,
        Fu.ex_eta i P hP, Fu.ex_etaA i P hP⟩
      ⟨Fu.over_σ i' P' hP', hP', ⟨Fu.ex_add i' P' hP', Fu.ex_onto i' P' hP', isHolTo_exp_of_isPeriod Fu i' P' hP',
        (Fu.22 i' P' hP').1, (Fu.22 i' P' hP').2⟩, Fu.ex_ker i' P' hP', Fu.ex_lin i' P' hP', Fu.ex_weil i' P' hP',
        Fu.ex_eta i' P' hP', Fu.ex_etaA i' P' hP'⟩).2 ?_

    exact ⟨gm, L, hiso, hmark, fun a => ⟨gm (Fu.t i a) - Fu.t i' a, by rw [hA, one_smul]; abel⟩, hPL⟩

  have hii : i = i' := Fu.disj i i' P P' hP hP' hpt
  subst hii

  letI := H.starRing
  have hex := GlobalTheory.ArcPts.exp_eq_of_matching_markings E H D l Xo σ g ty Fu i P P' gm L rfl hP hP' hiso hmark
    (fun v => ⟨gm (Fu.t i v) - Fu.t i v, by rw [hA, one_smul]; abel⟩) hPL
  exact ⟨hpt, hex.2⟩

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalIffOfIsPullDegTauBimult
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalIffOfIsPullDegTauBimult
noncomputable section

namespace GlobalTheory.TauCanPull

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TauTwist GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem cPoint_unit (D : DegPre R) (y : D.X) : cP D (𝟙_ (Over (Sp R))) y = D.c y := by
  rw [cP, toUnit_unit, Category.id_comp]

theorem c_pow_eq_one_iff (D : DegPre R) (n : ℕ) (y : D.X) : D.c y ^ n = 1 ↔ D.c (n • y) = D.c 0 := by
  rw [← cPoint_unit D (n • y), ← cPoint_unit D 0, cPoint_nsmul, cPoint_zero, cPoint_unit]

theorem c_eq_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (x x' : D'.X) :
    D.c (hD.xe x) = D.c (hD.xe x') ↔ D'.c x = D'.c x' := by
  constructor
  · intro h
    refine Over.OverMorphism.ext ((pull_grp hD).1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hD.c_pr, h]
  · intro h
    haveI : IsDominant (spMap φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)⟩
    haveI : IsProper D.P.A.hom := D.P.isAb.proper
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) D.P.A.hom
      ((Over.w _).trans (Over.w _).symm) (spMap φ)
      ((hD.c_pr x).symm.trans ((congrArg (fun q => q.left ≫ _) h).trans (hD.c_pr x'))))

theorem torsion_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (n : ℕ) :
    (∀ y, D.c y ^ n = 1) ↔ ∀ y, D'.c y ^ n = 1 := by
  rw [hD.xe.surjective.forall]
  refine forall_congr' fun y => ?_
  rw [c_pow_eq_one_iff, c_pow_eq_one_iff, ← c_eq_iff hD hφ, map_nsmul, map_zero]

theorem val_tau_kappa {n : ℕ} (hc : ∀ y, D.c y ^ n = 1) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val (D.tau (n • a) (n • b)) r z J = unitAt r z (kappa hc a b) := by
  have h : LB.Gen.Corr D.P.L _ _ _ _ (D.tau (n • a) (n • b)) (scaleGen (unitOn (kappa hc a b)) (LB.oneGen D.P.L)) :=
    corr_of_val D.P.isLB fun y I hI => (unitAt_kappa hc a b hI).symm.trans
      ((val_scale _ _ _ hI).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))).symm
  exact (val_corr hJ h r).trans ((val_scale _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans
    (_root_.mul_one _)))

theorem kappa_pull (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) {n : ℕ} (hc : ∀ y, D.c y ^ n = 1)
    (hc' : ∀ y, D'.c y ^ n = 1) (a b : D'.X) :
    kappa hc' a b = Units.map (fracMap hφ).toMonoidHom (kappa hc (hD.xe a) (hD.xe b)) := by
  let z : (TK R').left := IsLocalRing.closedPoint (FractionRing R')
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  have e := tau_val hD _ _ (fracMap_sq hφ) hJ hJ' (n • a) (n • b)
  have a₁ : ∀ w : D'.X, D'.xK (n • w) = (1 : TK R' ⟶ D'.P.A).left := fun w =>
    congrArg (fun q => q.left) (cPoint_nsmul_eq_one hc' (TK R') w)
  rw [map_nsmul, map_nsmul, val_tau_kappa hc _ _ _ hJ, val_tau_kappa hc' _ _ _ hJ', ← nsmul_add, a₁, a₁, a₁,
    inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at e
  refine unitAt_injective z (e.symm.trans ?_)
  exact (congrArg (fun q => unitAt q z _) (Category.id_comp (genMap hφ)).symm).trans
    (unitAt_spMap (𝟙 _) (fracMap hφ) z _)

theorem tauCan_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (n : ℕ) :
    ArcCM.TauCan D n ↔ ArcCM.TauCan D' n := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨(torsion_iff hD hφ n).1 hc, fun y y' => ?_⟩
    rw [kappa_pull hD hφ hc, h, map_one]
  · rintro ⟨hc', h⟩
    refine ⟨(torsion_iff hD hφ n).2 hc', fun y y' => ?_⟩
    obtain ⟨y, rfl⟩ := hD.xe.surjective y
    obtain ⟨y', rfl⟩ := hD.xe.surjective y'
    apply Units.map_injective (f := (fracMap hφ).toMonoidHom) (fracMap hφ).injective
    rw [← kappa_pull hD hφ _ hc', h, map_one]

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem tauCan_iff_of_isPullDeg : Known → ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (D₀ : Out.DegPre R) (D₁ : Out.DegPre R') (p : Out.IsPullDeg f D₀ D₁) (n : ℕ), Function.Injective f → D₀.TauBimult → D₁.TauBimult → (TauCan D₀ n ↔ TauCan D₁ n) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ p n hf _ _ => tauCan_iff p hf n

end GlobalTheory.TauCanPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalIffOfIsPullDegTauBimultStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTauCanonical_iff_of_isPullDeg_tauBimult : Known → ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (D₀ : Out.DegPre R) (D₁ : Out.DegPre R') (p : Out.IsPullDeg f D₀ D₁) (n : ℕ), Function.Injective f → D₀.TauBimult → D₁.TauBimult → (TauCan D₀ n ↔ TauCan D₁ n) := by
  first | exact @GlobalTheory.TauCanPull.tauCan_iff_of_isPullDeg | exact GlobalTheory.TauCanPull.tauCan_iff_of_isPullDeg | (intros; apply GlobalTheory.TauCanPull.tauCan_iff_of_isPullDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsSplit
noncomputable section

namespace GlobalTheory.ArcCM.Split

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

def quo (θ : A → A → A → U) (k : ℕ) (x b : A) : U := cubN θ k 1 x b * (cubN θ k 1 b x)⁻¹

variable (h : IsCub θ)
include h

theorem coc_four (a b c d x : A) :
    θ (a * b) (c * d) x * θ a b x * θ c d x = θ (a * c) (b * d) x * θ a c x * θ b d x := by
  have e₁ := h.coc a b (c * d) x
  have e₂ := h.coc b c d x
  have e₃ := h.coc a c (b * d) x
  have e₄ := h.coc c b d x
  rw [mul_left_comm c b d] at e₃
  rw [mul_comm c b, h.s01 c b] at e₄
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a₁ - a₂ - a₃ + a₄

theorem cubN_mul_left (k : ℕ) (m m' x : A) :
    cubN θ k 1 (m * m') x * θ m m' x ^ k = θ (m ^ k) (m' ^ k) x * cubN θ k 1 m x * cubN θ k 1 m' x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := coc_four h (m ^ k) (m' ^ k) m m' x
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ m, pow_succ m', pow_succ (θ m m' x), mul_pow]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem quo_one (k : ℕ) (b : A) : quo θ k 1 b = 1 := by
  rw [quo, h.N_one, inv_one, _root_.mul_one]
  exact Finset.prod_eq_one fun _ _ => h.face₂ _ _

theorem quo_mul_left {k : ℕ} {x x' : A} (hx : x ^ k = 1) (b : A) :
    quo θ k (x * x') b * θ x x' (b ^ k) = quo θ k x b * quo θ k x' b := by
  have e₁ := cubN_mul_left h k x x' b
  have e₂ := h.N_add k 1 b x x'
  rw [hx, h.face] at e₁
  rw [h.face, _root_.one_mul, h.s01 b, h.s12 x b, h.s01 (b ^ k), h.s12 x (b ^ k)] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₁ - a₂

theorem quo_mul_right {k : ℕ} {x : A} (hx : x ^ k = 1) (b b' : A) :
    quo θ k x (b * b') * θ x (b ^ k) (b' ^ k) = quo θ k x b * quo θ k x b' := by
  have e₁ := cubN_mul_left h k b b' x
  have e₂ := h.N_add k 1 x b b'
  rw [hx, h.face, _root_.one_mul, h.face] at e₂
  rw [h.s12 b, h.s01 b, h.s12 (b ^ k), h.s01 (b ^ k)] at e₁
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₂ - a₁

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {n : ℕ}

theorem val_cubAtT {T : Over (Sp R)} {y : T.left} {J} (hJ : Good D.P.L y J) (x x' w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T x x' w) (𝟙 _) y J = th D y J x x' w := by
  have := val_cub D.cub (𝟙 T) hJ x x' w
  rwa [Category.id_comp, Category.id_comp, Category.id_comp] at this

theorem prod_gtT {T : Over (Sp R)} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (cP D _ χ * b).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

variable (hc : ∀ y, D.c y ^ n = 1)
include hc

theorem cPoint_pow_eq_one (T : Over (Sp R)) (χ : D.X) : cP D T χ ^ n = 1 :=
  (cPoint_nsmul D T n χ).symm.trans (GlobalTheory.TauTwist.cPoint_nsmul_eq_one hc T χ)

theorem exists_coord (T : Over (Sp R)) (b : T ⟶ D.P.A) (χ : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (b ^ n) χ) DegPre.gtε), t.IsGen ∧
      ∀ (T' : Over (Sp R)) (ρ : T' ⟶ T) (z : T'.left) (J), Good D.P.L z J →
        val t ρ.left z J = quo (th D z J) n (cP D T' χ) (ρ ≫ b) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN D.cub 1 (cP D T χ) b n
  obtain ⟨u, hu, hw⟩ := exists_cubN D.cub 1 b (cP D T χ) n
  obtain ⟨t', ht', hv'⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T (b ^ n) χ) (ε' := DegPre.gtε) (fun U _ h => by
      rw [prod_gtT, cPoint_pow_eq_one hc, mul_comm (cP D T χ) (b ^ n), mul_comm b (cP D T χ)]
      apply Additive.ofMul.injective
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ u))
    (mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ hu))
  refine ⟨t', ht', fun T' ρ z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (hv T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (hw T' ρ z J hJ)))).trans ?_))⟩
  rw [MonObj.comp_one, comp_cP]
  rfl

theorem val_coord (T : Over (Sp R)) (b : T ⟶ D.P.A) (χ : D.X) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (exists_coord hc T b χ).choose (𝟙 _) z J = quo (th D z J) n (cP D T χ) b := by
  have := (exists_coord hc T b χ).choose_spec.2 T (𝟙 T) z J hJ
  rwa [Category.id_comp] at this

def liftPt (T : Over (Sp R)) (b : T ⟶ D.P.A) : GtPt D T where
  b := b ^ n
  s χ := (exists_coord hc T b χ).choose
  isGen χ := (exists_coord hc T b χ).choose_spec.1
  s_zero := corr_of_val D.P.isLB fun y J hJ => (val_coord hc T b 0 hJ).trans (Eq.trans (by
    rw [cPoint_zero]; exact quo_one (isCub_cubV D.cub hJ) n b) (val_one _).symm)
  mult χ χ' := corr_of_val D.P.isLB fun y J hJ =>
    (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_cubAtT hJ _ _ _)).trans (Eq.trans (by
      rw [cPoint_add]; exact quo_mul_left (isCub_cubV D.cub hJ) (cPoint_pow_eq_one hc T χ) b)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_coord hc T b _ hJ))).symm))

theorem isSplit_liftPt : IsSplit D n (liftPt hc) := by
  refine ⟨fun _ _ => rfl, fun T b b' => ⟨mul_pow b b' n, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩,
    fun T T' h b => ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  · exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_coord hc T _ _ hJ) (val_cubAtT hJ _ _ _)).trans
      ((quo_mul_right (isCub_cubV D.cub hJ) (cPoint_pow_eq_one hc T χ) b b').trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_coord hc T b' _ hJ))).symm))
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (map_pow (preHom h) b n).symm
  · refine (val_coord hc T' _ _ hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]
    exact ((exists_coord hc T b χ).choose_spec.2 T' h y J hJ).symm

end GlobalTheory.ArcCM.Split

namespace GlobalTheory.ArcCM

open AlgebraicGeometry CategoryTheory MonObj ReciprocityTheory.ChartRestriction.G

theorem exists_isSplit : Known → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D₀ : Out.DegPre R) (n : ℕ),
    0 < n → (∀ y, D₀.c y ^ n = 1) → ∃ sB, IsSplit D₀ n sB :=
  fun _ _ _ _ _ _ _ _ hc => ⟨_, Split.isSplit_liftPt hc⟩

end GlobalTheory.ArcCM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ModelsAtOfGoodLevel
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem modelsAt_of_good_level : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ModelsAt Xo c := by
  intro hK E _ _ _ H Dw l Xo c hr hg
  classical
  have key : ∀ Xs : ∀ l' : Level H, Moduli Dw l', ModelsAt (Xs l) c := by
    intro Xs p W hp hW
    obtain ⟨Y, hY, -⟩ := hK.models.2 E H Dw hr Xs
    obtain ⟨h2, h4⟩ := hY p W hp hW
    exact ⟨Y p W hp hW ⟨l, c, hg p hp⟩, (h4 _).2.2, (h2.1 ⟨l, c, hg p hp⟩).2.2.1⟩
  have h := key (Function.update (fun l' => Classical.choice (hK.n1ab E H Dw l' hr)) l Xo)
  rwa [Function.update_self] at h

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.ArcCM.cfOf_linear_and_degree : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∃ φ : sec Xo c a' n →ₗ[c.F] K₁, ∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ ∀ F ∈ sec Xo c a' n, cfOf d.yF d.μ d.jj F ≠ 0 → ∑ v, d.μ v = absA Dw a' := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ d a' n
  have hP : ∀ F ∈ sec Xo c a' n, ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁),
      algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (absA Dw a') := fun F hF =>
    GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d a' n F hF
  have hcomp : ∀ a : c.F, algebraMap c.F (ArcS Dw K₁) a =
      algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)
        (algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a) := fun _ => rfl
  have hnum : ∀ F : sec Xo c a' n,
      algebraMap _ (ArcS Dw K₁) (arcNum (evR Xo c F.1 d.yF)) = evR Xo c F.1 d.yF := fun F =>
    (hP F.1 F.2).elim fun P hP' => by
      rw [← hP'.1, LinOfPoly.arcNum_map]
  have hadd : ∀ F G : sec Xo c a' n, arcNum (evR Xo c (F + G).1 d.yF) =
      arcNum (evR Xo c F.1 d.yF) + arcNum (evR Xo c G.1 d.yF) := fun F G =>
    LinOfPoly.inj _ K₁ (by
      rw [map_add (f := _), hnum, hnum, hnum, Submodule.coe_add, LinOfPoly.evR_add])
  have hsmul : ∀ (a : c.F) (F : sec Xo c a' n), arcNum (evR Xo c (a • F).1 d.yF) =
      algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a *
        arcNum (evR Xo c F.1 d.yF) := fun a F =>
    LinOfPoly.inj _ K₁ (by
      rw [hnum, Submodule.coe_smul, LinOfPoly.evR_smul, map_mul, hnum F, hcomp])
  refine ⟨⟨{ toFun := fun F => cfOf d.yF d.μ d.jj F.1, map_add' := ?_, map_smul' := ?_ }, fun F => rfl⟩, ?_⟩
  · intro F G
    simp only [cfOf]
    rw [hadd, MvPolynomial.coeff_add, HahnSeries.coeff_add]
  · intro a F
    simp only [cfOf]
    rw [hsmul, MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C_mul, LinOfPoly.laur_alg,
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, RingHom.id_apply]
    simp [Algebra.smul_def]
  · intro F hF hne
    obtain ⟨P, hP1, hP2⟩ := hP F hF
    rw [← Finsupp.degree_eq_sum]
    by_contra hd
    apply hne
    simp only [cfOf]
    rw [← hP1, LinOfPoly.arcNum_map, hP2.coeff_eq_zero hd]
    rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegreeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.arcDatum_coefficientFunctional_linear_degree : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∃ φ : sec Xo c a' n →ₗ[c.F] K₁, ∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ ∀ F ∈ sec Xo c a' n, cfOf d.yF d.μ d.jj F ≠ 0 → ∑ v, d.μ v = absA Dw a' := by
  first | exact @GlobalTheory.ArcCM.cfOf_linear_and_degree | exact GlobalTheory.ArcCM.cfOf_linear_and_degree | (intros; apply GlobalTheory.ArcCM.cfOf_linear_and_degree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNumberFieldFunctionalBoundedCompExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNumberFieldFunctionalBoundedCompExtension
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

section

variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

theorem ordAt_eq_count (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    ordAt v x = FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) := by
  rw [ordAt, valuation_eq_exp_neg_count v hx, WithZero.log_exp, neg_neg]

theorem ordAt_algebraMap_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {v : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w v) (x : K) :
    ordAt w (algebraMap K K₁ x) = (w.asIdeal.ramificationIdx (𝓞 K) : ℤ) * ordAt v x := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨h.symm⟩
  rw [ordAt, ordAt, ← HeightOneSpectrum.valuation_liesOver K₁ v w x, WithZero.log_pow,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  simp

theorem count_bcI_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {v : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w v) (N : MLine K) (hN : N.I ≠ 0) :
    FractionalIdeal.count K₁ w (bcI (K1 := K₁) N.I) =
      (w.asIdeal.ramificationIdx (𝓞 K) : ℤ) * FractionalIdeal.count K v N.I := by
  obtain ⟨c, hc⟩ := v.valuation_surjective K (WithZero.exp (-FractionalIdeal.count K v N.I))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have h1 : ordAt v c = FractionalIdeal.count K v N.I := by
    rw [ordAt, hc, WithZero.log_exp, neg_neg]
  have hg : IsLocGen v c N.I := ⟨hc0, by rw [← ordAt_eq_count v hc0, h1]⟩
  have h2 := local_generator_base_change K K₁ N ⟨bcI N.I, fun σ => N.n (σ.comp (algebraMap K K₁))⟩ v w c hN
    ⟨coe_bcI N.I, fun _ => rfl⟩ (fun a => by rw [← h]; rfl) hg
  rw [← h1, ← ordAt_algebraMap_of_liesOver h, ordAt_eq_count w h2.1]
  exact h2.2.symm

end

theorem numGood_comp : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (M : Set V) (S : (K →+* ℂ) → V → ℝ) (be : HeightOneSpectrum (𝓞 K) → ℝ) (Carch Bdeg : ℝ) (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁] [Algebra K K₁] (f : K' →ₐ[K] K₁) (φ : V →ₗ[K] K'), NumGood M S be Carch Bdeg K' φ → NumGood M S be Carch Bdeg K₁ (f.toLinearMap.comp φ) := by
  intro K V _ _ _ _ M S be Carch Bdeg K' K₁ _ _ _ _ _ _ f φ ⟨N, hG, hd, hc, hf, ha⟩
  letI : Algebra K' K₁ := f.toRingHom.toAlgebra
  haveI : IsScalarTower K K' K₁ := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hap : ∀ F, (f.toLinearMap.comp φ) F = algebraMap K' K₁ (φ F) := fun _ => rfl
  have hne : ∀ F, (f.toLinearMap.comp φ) F ≠ 0 → φ F ≠ 0 := fun F h h0 => h (by rw [hap, h0, map_zero])
  have hb := nondegenerate_base_change K' K₁ N ⟨bcI N.I, fun σ => N.n (σ.comp (algebraMap K' K₁))⟩ hG
    ⟨coe_bcI N.I, fun _ => rfl⟩
  refine ⟨⟨bcI N.I, fun σ => N.n (σ.comp (algebraMap K' K₁))⟩, hb.1, hb.2.le.trans hd, fun σ => ?_, ?_, ?_⟩
  · exact hc (σ.comp (algebraMap K' K₁))
  · intro la w hw F hF h0
    let v : HeightOneSpectrum (𝓞 K') := w.under (𝓞 K')
    have hwv : LiesOver w v := rfl
    have hv : LiesOver v la := by
      have hw' : w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁)) = la.asIdeal := hw
      rw [IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 K') (𝓞 K₁), ← Ideal.comap_comap] at hw'
      exact hw'
    have : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
    have h1 := hf la v hv F hF (hne F h0)
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (w.asIdeal.ramificationIdx (𝓞 K')))
    rw [hap, ordAt_algebraMap_of_liesOver hwv, count_bcI_of_liesOver hwv N hG.1,
      Ideal.ramificationIdx_tower (R := 𝓞 K) v.asIdeal w.asIdeal]
    push_cast
    linarith
  · intro σ F hF h0
    have h1 := ha (σ.comp (algebraMap K' K₁)) F hF (hne F h0)
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at h1
    exact h1

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNumberFieldFunctionalBoundedCompExtensionStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNumberFieldFunctionalBounded_comp_extension : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (M : Set V) (S : (K →+* ℂ) → V → ℝ) (be : HeightOneSpectrum (𝓞 K) → ℝ) (Carch Bdeg : ℝ) (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁] [Algebra K K₁] (f : K' →ₐ[K] K₁) (φ : V →ₗ[K] K'), NumGood M S be Carch Bdeg K' φ → NumGood M S be Carch Bdeg K₁ (f.toLinearMap.comp φ) := by
  first | exact @GlobalTheory.ArcCM.numGood_comp | exact GlobalTheory.ArcCM.numGood_comp | (intros; apply GlobalTheory.ArcCM.numGood_comp <;> assumption)
end
end
