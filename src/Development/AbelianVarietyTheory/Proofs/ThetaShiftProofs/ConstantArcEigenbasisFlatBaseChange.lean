module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
noncomputable section

namespace GlobalTheory.BasisUniv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp JetR IsTan
open scoped CategoryTheory.Obj

section Coord

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem isUnivChart_iso {G' : Over (Spec (CommRingCat.of S))} [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsUnivChart G' n (fun m => x m ≫ e.inv) := by
  have one : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G') ≫ e.hom = 1 := fun T =>
    map_one (IsMonHom.monoidHom e.hom T)
  have one' : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G) ≫ e.inv = 1 := fun T => by
    rw [← one, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hm y hy => ?_⟩
  · rw [← Category.assoc, hx.1]
  · rw [← Category.assoc, hx.2.1, one']
  · have := hx.2.2 A aug m hm (y ≫ e.hom) (by rw [← Category.assoc, hy, one])
    simpa only [← Category.assoc, Iso.eq_comp_inv] using this

theorem exists_chart_of_pullback {R : Type} [CommRing R] [IsLocalRing R] {G₀ : Over (Spec (CommRingCat.of R))} [GrpObj G₀]
    [Smooth G₀.hom] (f : R →+* S) {φ : G.left ⟶ G₀.left} (h : IsGrpPullback G G₀ (Geo.Tor.spMap f) φ) :
    ∃ (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G), IsUnivChart G n x := by
  let _ := f.toAlgebra
  obtain ⟨n, x, hx⟩ := univChartLoc G₀
  obtain ⟨x', hx', -⟩ := tanBC_alg (R' := S) G₀ n x hx
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G₀ (fB R S))
  exact ⟨n, _, isUnivChart_iso e hx'⟩

variable {n : ℕ} {y : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hy : IsUnivChart G n y)
  {g : ℕ} {v : Fin g → (epsR S ⟶ G)}
include hy

theorem isTangent_of_comb (hv : ∀ i, IsTangent (v i)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) :
    IsTangent w := by
  obtain ⟨k, -⟩ := prodPts_tan hy z v fun i => (isTan_iff _).2 (hv i)
  rw [(isLieComb_iff _ _ _).1 hw]
  exact (isTan_iff _).1 k

theorem coord_inj (hv : IsLieBasis v) (tv : ∀ i, IsTan (v i)) {c c' : Fin g → S}
    (h : ∑ i, c i • tcoord hy (v i) (tv i) = ∑ i, c' i • tcoord hy (v i) (tv i)) : c = c' := by
  obtain ⟨k, e⟩ := prodPts_tan hy c v tv
  exact (hv.2 _ ((isTan_iff _).1 k)).unique ((comb_iff_coord hy c tv k).2 e)
    ((comb_iff_coord hy c' tv k).2 (e.trans h))

theorem comb_iff (hv : IsLieBasis v) {m : ℕ} {u : Fin m → (epsR S ⟶ G)} {U : Fin m → Fin g → S}
    (hU : ∀ k, IsLieComb (U k) v (u k)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) (cf : Fin m → S) :
    IsLieComb cf u w ↔ z = ∑ k, cf k • U k := by
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tu := fun k => (isTan_iff _).2 (isTangent_of_comb hy hv.1 (hU k))
  have tw := (isTan_iff _).2 (isTangent_of_comb hy hv.1 hw)
  have e : ∑ i, cf i • tcoord hy (u i) (tu i) = ∑ j, (∑ k, cf k • U k) j • tcoord hy (v j) (tv j) := by
    simp only [(comb_iff_coord hy _ tv (tu _)).1 (hU _), Finset.smul_sum, Finset.sum_smul, smul_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_comm
  rw [comb_iff_coord hy cf tu tw, e, (comb_iff_coord hy z tv tw).1 hw]
  exact ⟨fun q => coord_inj hy hv tv q, fun q => by rw [q]⟩

theorem tcoord_comp (f : G ⟶ G) [IsMonHom f] {w : epsR S ⟶ G} (tw : IsTan w) :
    tcoord hy (w ≫ f) (isTan_comp tw f) = tmap hy f (tcoord hy w tw) :=
  tcoord_congr hy (congrArg (· ≫ f) (tcoord_spec hy w tw)) _ (isTan_comp (isTan_tvec hy _) f)

theorem eig_iff (hv : IsLieBasis v) (f : G ⟶ G) [IsMonHom f] {M : Matrix (Fin g) (Fin g) S}
    (hM : ∀ i, IsLieComb (M i) v (v i ≫ f)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) (r : S) :
    (w ≫ f).left = Geo.Tor.spMap (epsScaleR r) ≫ w.left ↔ z ᵥ* M = r • z := by
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tw := (isTan_iff _).2 (isTangent_of_comb hy hv.1 hw)
  have ew := (comb_iff_coord hy z tv tw).1 hw
  have e1 : tcoord hy (w ≫ f) (isTan_comp tw f) = ∑ j, (z ᵥ* M) j • tcoord hy (v j) (tv j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [tcoord_comp hy f tw, ew, map_sum]
    simp only [map_smul, ← tcoord_comp hy f, (comb_iff_coord hy _ tv (isTan_comp (tv _) f)).1 (hM _),
      Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have e2 : tcoord hy (spMap (scaleD r) ≫ w) (isTan_scale r tw) = ∑ j, (r • z) j • tcoord hy (v j) (tv j) := by
    rw [tcoord_scale hy r tw, ew, Finset.smul_sum]
    simp only [smul_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro q
    have q' : w ≫ f = spMap (scaleD r) ≫ w := Over.OverMorphism.ext q
    exact coord_inj hy hv tv (e1.symm.trans ((tcoord_congr hy q' _ _).trans e2))
  · intro q
    have q' : w ≫ f = spMap (scaleD r) ≫ w :=
      tan_ext hy (isTan_comp tw f) (isTan_scale r tw) (by rw [e1, e2, q])
    exact congrArg (fun t => t.left) q'


omit hy in
theorem exists_lift {R : Type} [CommRing R] {G₀ : Over (Spec (CommRingCat.of R))} [GrpObj G₀]
    (f : R →+* S) {φ : G.left ⟶ G₀.left} (h : IsGrpPullback G G₀ (Geo.Tor.spMap f) φ) (w : epsR R ⟶ G₀) :
    ∃ w' : epsR S ⟶ G, w'.left ≫ φ = Geo.Tor.spMap (dualMapR f) ≫ w.left := by
  have c : (Geo.Tor.spMap (dualMapR f) ≫ w.left) ≫ G₀.hom = (epsR S).hom ≫ Geo.Tor.spMap f := by
    rw [Category.assoc, Over.w w]
    exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg Geo.Tor.spMap (RingHom.ext fun r => by
      ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl])).trans (Geo.Tor.spMap_comp _ _))
  exact ⟨Over.homMk (h.1.lift _ _ c) (h.1.lift_snd _ _ c), h.1.lift_fst _ _ c⟩

end Coord

theorem eig_powerSeries {A : Type} [CommRing A] [IsNoetherianRing A] {I : Type} {g m : ℕ}
    (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A) (U : Fin m → Fin g → A)
    (hU : ∀ k i, U k ᵥ* M i = ρ i • U k)
    (h : ∀ w : Fin g → PowerSeries A, (∀ i, w ᵥ* (M i).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (ρ i) • w) →
      ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j))
    {S : Type} [CommRing S] (f : A →+* S) (hf : f.Flat) (w : Fin g → S)
    (hw : ∀ i, w ᵥ* (M i).map f = f (ρ i) • w) : ∃! cf : Fin m → S, w = ∑ k, cf k • fun j => f (U k j) := by
  let _ := f.toAlgebra
  have : Module.Flat A S := hf
  refine (GlobalTheory.commonEigenvectors_flat_baseChange A I g m M ρ).1 A U hU (fun z hz => ?_) S w hw
  simp only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_id, Matrix.map_id] at hz ⊢
  obtain ⟨cf, hcf, huniq⟩ := h (fun j => PowerSeries.C (R := A) (z j)) (fun i => by
    funext j
    have := congrArg (PowerSeries.C (R := A)) (congrFun (hz i) j)
    simpa [Matrix.vecMul, dotProduct] using this)
  have key : ∀ c : Fin m → A, (z = ∑ k, c k • fun j => U k j) →
      (fun k => PowerSeries.C (R := A) (c k)) = cf := fun c hc => huniq _ (by
    funext j
    have := congrArg (PowerSeries.C (R := A)) (congrFun hc j)
    simpa [Finset.sum_apply] using this)
  refine ⟨fun k => PowerSeries.constantCoeff (R := A) (cf k), ?_, fun c hc => ?_⟩
  · funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun hcf j)
    simpa [Finset.sum_apply] using this
  · rw [← key c hc]
    funext k
    simp

end GlobalTheory.BasisUniv

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames


open Matrix GlobalTheory.BasisUniv in
theorem GlobalTheory.ArcQ.arcBasis_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e hB S _ ι hflat t' m2
  obtain ⟨v₀, hv₀, hB⟩ := hB
  obtain ⟨g, e₁, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.T.exists_constantLieBasis_arcGroup hG E H Dw l Xo c O β Y A b a χ W
  have hsm : Smooth W.t.G.hom := W.t.semi.smooth
  have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
  have hmon' : ∀ x, IsMonHom (t'.act.act x) := t'.act.hom
  obtain ⟨n, y, hy⟩ := Chart.univChartLoc W.t.G
  obtain ⟨n', y', hy'⟩ := exists_chart_of_pullback ι m2.cart

  have hU : ∀ τ k, ∃ U : Fin g → A, IsLieComb (fun j => PowerSeries.C (R := A) (U j)) v (v₀ τ k) := fun τ k => by
    have ht : GtTanR (e τ k) :=
      ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1
    obtain ⟨U, hU, -⟩ := hcomb _ ht
    exact ⟨U, (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W g U e₁ (e τ k) v _ (fun i => (hev i).2) hU).1 (hv₀ τ k)⟩
  choose U hU using hU
  choose u hu using fun τ k => exists_lift ι m2.cart (v₀ τ k)
  choose v' hv' using fun j => exists_lift ι m2.cart (v j)
  have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange ι m2.cart hv hv'
  have hU' : ∀ τ k, IsLieComb (fun j => (ι.comp (PowerSeries.C (R := A))) (U τ k j)) v' (u τ k) := fun τ k =>
    Chart.comb_baseChange ι m2.cart (hU τ k) hv' (hu τ k)
  have hM' : ∀ x i, IsLieComb ((M x).map (ι.comp (PowerSeries.C (R := A))) i) v' (v' i ≫ t'.act.act x) := fun x i =>
    Chart.comb_baseChange ι m2.cart (hM x i) hv' (by
      rw [Over.comp_left, Category.assoc, m2.act, ← Category.assoc, hv', Category.assoc, Over.comp_left])
  have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
  have hUe : ∀ τ k x, U τ k ᵥ* M x = ρ τ x • U τ k := fun τ k x => by
    have := (eig_iff hy hv _ (hMR x) (hU τ k) _).1 (((hB τ).1 k).2 x)
    funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  refine ⟨u, fun τ k => ⟨v₀ τ k, hv₀ τ k, hu τ k⟩, fun τ => ⟨fun k => ⟨isTangent_of_comb hy' hb'.1 (hU' τ k), fun x => ?_⟩,
    fun w hw hwe => ?_⟩⟩
  · refine (eig_iff hy' hb' _ (hM' x) (hU' τ k) _).2 ?_
    funext j
    have := congrArg (ι.comp (PowerSeries.C (R := A))) (congrFun (hUe τ k x) j)
    simpa [Matrix.vecMul, dotProduct] using this
  · obtain ⟨z, hz, -⟩ := hb'.2 w hw
    simp only [comb_iff hy' hb' (hU' τ) hz]
    refine eig_powerSeries M (fun x => ρ τ x) (U τ) (hUe τ) (fun s hs => ?_) _ hflat z
      (fun x => (eig_iff hy' hb' _ (hM' x) hz _).1 (hwe x))
    have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
    have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
    simpa only [comb_iff hy hv (hU τ) hc] using this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChangeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
  first | exact @GlobalTheory.ArcQ.arcBasis_baseChange | exact GlobalTheory.ArcQ.arcBasis_baseChange | (intros; apply GlobalTheory.ArcQ.arcBasis_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLetters
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLetters
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_letters_equivariant (h1 : Out.Laws) (h2 : Out.Laws2) (hev : GlobalTheory.Reg.EvLaws Xo c)
    {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (hY : Mono Y.j)
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] {b₀ : O →+* K₁} {A : ArcIn Dw l β K₁ b₀}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X} (W : Wit Y A χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt A.D₀ (epsR K₁)) (th : A.D₀.P.L.Sec) (hth : ThNZ th)
    (ζ : K₁) (y₀ yF : FrPt Xo c (ArcS Dw K₁)) (hy₀ : IsArcFr W e th (arcι Dw K₁) y₀)
    (hchg : FrChg (letM Dw K₁) (cst Dw ζ) y₀ yF)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c) (hF : F ∈ sec Xo c a n)
    (T : Type) [Field T] (φ ψ : ArcS Dw K₁ →+* T) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T)
    (hφψ : ∀ g : LaurentSeries K₁, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C g)) =
      ψ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C g)))
    (hb : ∀ τ i j, i < j → b τ i j = 0)
    (hX : ∀ τ i k, ψ (arcX Dw K₁ τ i k) = ∑ j, b τ i j * φ (arcX Dw K₁ τ j k)) :
    ψ (evR Xo c F yF) = (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) * φ (evR Xo c F yF) := by
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  obtain ⟨hdom, -, -, hconst⟩ := GlobalTheory.ArcConst.algebraic_const E H Dw K₁
  obtain ⟨f₀, hf₀⟩ := hconst c.F (algebraMap c.F (ArcS Dw K₁))
  have hι : φ.comp (arcι Dw K₁) = ψ.comp (arcι Dw K₁) := RingHom.ext fun p => hφψ _
  letI : Algebra c.F T := (φ.comp (algebraMap c.F (ArcS Dw K₁))).toAlgebra
  let φ' : ArcS Dw K₁ →ₐ[c.F] T := { φ with commutes' := fun _ => rfl }
  let ψ' : ArcS Dw K₁ →ₐ[c.F] T :=
    { ψ with
      commutes' := fun r => by
        change ψ (algebraMap c.F (ArcS Dw K₁) r) = φ (algebraMap c.F (ArcS Dw K₁) r)
        rw [hf₀]
        exact (RingHom.congr_fun hι _).symm }
  obtain ⟨y₁, hy₁⟩ := hev.bc _ _ φ' y₀
  obtain ⟨y₂, hy₂⟩ := hev.bc _ _ ψ' y₀
  obtain ⟨z₁, hz₁⟩ := hev.bc _ _ φ' yF
  obtain ⟨z₂, hz₂⟩ := hev.bc _ _ ψ' yF
  have hS := GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c O β Y K₁ b₀ A χ W e th hth _ _ y₀ hy₀
  have a₁ : IsArcFr W e th (φ.comp (arcι Dw K₁)) y₁ := hS.2 hY T φ' y₁ hy₁
  have a₂ : IsArcFr W e th (ψ.comp (arcι Dw K₁)) y₂ := hS.2 hY T ψ' y₂ hy₂
  rw [← hι] at a₂
  obtain rfl : y₂ = y₁ :=
    (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c O β Y K₁ b₀ A χ W e th hth _ _ y₁ a₁).1 hY y₂ a₂
  have cS := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c (ArcS Dw K₁)
  have cT := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c T
  have c₁ := (cS.2.2.1 T φ' _ _ _ _ _ _ hchg hy₁).1 hz₁
  have c₂ := (cS.2.2.1 T ψ' _ _ _ _ _ _ hchg hy₂).1 hz₂
  have hM : ∀ τ, (letM Dw K₁ τ).map ψ' = b τ * (letM Dw K₁ τ).map φ' := fun τ => by
    ext i k
    exact hX τ i k
  have hζ : ψ' (cst Dw ζ) = 1 * φ' (cst Dw ζ) := by
    rw [one_mul]
    exact (RingHom.congr_fun hι _).symm
  rw [funext hM, hζ] at c₂
  have c₃ : FrChg b 1 z₁ z₂ := (cT.1 _ b _ 1 _ _ _ c₁).2 c₂
  have hbu : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
    have hu := ((GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c T b 1 z₁).2.2.1 z₂ c₃).1 τ
    have htri : (b τ).IsLowerTriangular := fun i j hij => hb τ i j hij
    exact (htri.det_ne_zero_iff.mp hu.ne_zero) i
  let t : Ix Dw → Tˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (b x.1 x.2 x.2) (hbu x.1 x.2)
  have hbor : FrBor t z₁ z₂ := (cT.2.2.2 t z₁ z₂).2 ⟨b, fun _ _ => rfl, hb, c₃⟩
  have eS := (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hF (ArcS Dw K₁)).1
  have eT := ((GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hF T).2 inferInstance).1 t z₁ z₂ hbor
  rw [eS T φ' yF z₁ hz₁, eS T ψ' yF z₂ hz₂] at eT
  have hw : wchar (ex Dw a n) t = ∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ)) := by
    rw [wchar, Fintype.prod_option, Fintype.prod_sigma]
    simp [t, ex]
  rw [hw] at eT
  exact eT

theorem ArcDatum.exists_normal_tangent (h1 : Out.Laws) (h2 : Out.Laws2)
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) :
    ∃ (ζ : K₁) (e₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt (d.a.restrict (c.V d.Wp).subtype).D₀ (epsR K₁))
      (y₀ : FrPt Xo c (ArcS Dw K₁)), IsArcFr d.W e₀ d.th (arcι Dw K₁) y₀ ∧
        FrChg (letM Dw K₁) (cst Dw ζ) y₀ d.yF := by
  obtain ⟨ζ, -, -, -, -, e₀, y₀, -, hy₀, hc⟩ := GlobalTheory.ArcQ.exists_normalForm h1 h2 E H Dw l Xo c K₁ d
  exact ⟨ζ, e₀, y₀, hy₀, hc⟩

theorem evR_arc_isHomogeneous : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁), algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  intro h1 h2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d a n F hF
  obtain ⟨ζ, e₀, y₀, hy₀, hc⟩ := d.exists_normal_tangent h1 h2
  have hth : ThNZ d.th := by
    obtain ⟨_, _, _, _, hne, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.nonzero_generates h1 h2 K₁ _ d.th).1.1 hne
  exact GlobalTheory.BorelAlg.exists_isHomogeneous_of_equivariant E H Dw K₁ a _ fun T _ φ ψ b hφψ hb hX =>
    evR_letters_equivariant h1 h2 hev (GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)) d.W e₀ d.th hth ζ y₀ d.yF hy₀ hc
      a n F hF T φ ψ b hφψ hb hX

end GlobalTheory.ArcQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLettersStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁), algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  first | exact @GlobalTheory.ArcQ.evR_arc_isHomogeneous | exact GlobalTheory.ArcQ.evR_arc_isHomogeneous | (intros; apply GlobalTheory.ArcQ.evR_arc_isHomogeneous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockType
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockType
noncomputable section

namespace GlobalTheory.ArcType

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding Unf GoodEmb relab perFr gxFst gxSnd
open scoped LaurentSeries MonObj

theorem ext_dual {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} {p q : Sp (DualNumber R) ⟶ X}
    (h₀ : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ p = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ q)
    (h₁ : ∀ (V : X.Opens) (f : Γ(X, V)), ⊤ ≤ p ⁻¹ᵁ V → ⊤ ≤ q ⁻¹ᵁ V →
      TrivSqZeroExt.snd (valR p V f) = TrivSqZeroExt.snd (valR q V f)) : p = q := by
  have := ConstTan.isLocalRing_dual R
  have : IsLocalHom (TrivSqZeroExt.fstHom R R R).toRingHom :=
    ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩
  have hc : spMap (TrivSqZeroExt.fstHom R R R).toRingHom (IsLocalRing.closedPoint R) =
      IsLocalRing.closedPoint (DualNumber R) := IsLocalRing.comap_closedPoint _
  have hpq : p (IsLocalRing.closedPoint (DualNumber R)) = q (IsLocalRing.closedPoint (DualNumber R)) := by
    rw [← hc]
    exact congrArg (fun r : Sp R ⟶ X => r (IsLocalRing.closedPoint R)) h₀
  obtain ⟨_, ⟨V, hV, rfl⟩, hm, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint (DualNumber R)))) isOpen_univ
  have hp : ⊤ ≤ p ⁻¹ᵁ V := (Points.le_preimage_iff p V).2 hm
  have hq : ⊤ ≤ q ⁻¹ᵁ V := (Points.le_preimage_iff q V).2 (hpq ▸ hm)
  refine Points.ext_of_valR hV hp hq fun f => TrivSqZeroExt.ext ?_ (h₁ V f hp hq)
  exact (Points.valR_spMap_comp _ p V hp f).symm.trans
    ((congrArg (fun r => valR r V f) h₀).trans (Points.valR_spMap_comp _ q V hq f))

theorem ext_of_injective {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] {k : R →+* S}
    (hi : Function.Injective k) {X : Scheme.{0}} {p q : Sp (DualNumber R) ⟶ X}
    (h₀ : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ p = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ q)
    (h₁ : spMap (dualMap k) ≫ p = spMap (dualMap k) ≫ q) : p = q := by
  refine ext_dual h₀ fun V f hp hq => hi ?_
  have := (Points.valR_spMap_comp _ p V hp f).symm.trans
    ((congrArg (fun r => valR r V f) h₁).trans (Points.valR_spMap_comp _ q V hq f))
  simpa [dualMap] using congrArg TrivSqZeroExt.snd this

theorem eq_of_sumsAt {s s' : PowerSeries ℂ} {T : ℝ} (h : ∀ w : ℂ, T < w.im → ∃ x, SumsAt s w x ∧ SumsAt s' w x) :
    s = s' := by
  have h0 : ∀ w : ℂ, T < w.im → SumsAt (s - s') w 0 := fun w hw => by
    obtain ⟨x, h₁, h₂⟩ := h w hw
    simpa [SumsAt, sub_mul] using h₁.sub h₂
  have hm := Conv.coe_mem_halfRing.2 fun w hw => ⟨0, h0 w hw⟩
  have := Conv.halfRing_spec.2.2.2.1 T T ⟨_, hm⟩ fun w hw _ =>
    HasSum.unique (Conv.sumsAt_ev hw hm) (h0 w hw)
  have h2 : ((s - s' : PowerSeries ℂ) : ℂ⸨X⸩) = 0 := congrArg Subtype.val this
  exact sub_eq_zero.1 (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (h2.trans (map_zero _).symm))

theorem fderiv_diag {g : ℕ} (a : Fin g → ℂ) (ha : ∀ k, a k ≠ 0) (F : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    fderiv ℂ (fun z => F (fun k => a k * z k)) 0 z = fderiv ℂ F 0 (fun k => a k * z k) := by
  let L : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
    (LinearEquiv.piCongrRight fun k => LinearEquiv.smulOfNeZero ℂ ℂ (a k) (ha k)).toContinuousLinearEquiv
  have := L.comp_right_fderiv (f := F) (x := 0)
  rw [map_zero] at this
  exact congrArg (fun D => D z) this

section Hol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} [Algebra (FractionRing ℂ) ℂ]
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {a : ArcIn Dw l β ℂ (σ.comp β)} {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty} (Ha : HolArc Y σ a χ W Fu)

theorem diff_of {ν : Out.GtPt a.D₀ (epsR ℂ)} {z₀ : Fin g → ℂ} {v : epsR (PowerSeries ℂ) ⟶ W.t.G}
    (h : AnVec Ha ν z₀) (hv : LieImg W ν v) (V : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, V))
    (hV : ⊤ ≤ (v.left ≫ W.m.φ) ⁻¹ᵁ V) : ∃ T' : ℝ, ∀ w : ℂ, T' < w.im →
      ∀ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left), (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left ∧
        xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ) →
        SumsAt (TrivSqZeroExt.snd (valR (A := DualNumber (PowerSeries ℂ)) (v.left ≫ W.m.φ) V f)) w
          (fderiv ℂ (fun z => valAt' (xF z ≫ Y.m.φ) V f) 0 z₀) := by
  refine Ha.diff z₀ ν v V f h.1 h.2 (fun n ρ κ vn h₁ h₂ h₃ h₄ h₆ => hv n ρ κ vn h₁ h₂ h₃ h₄ ?_ h₆) hV
  rw [← cancel_mono (Out.thick (PowerSeries ℂ) (Ideal.span {PowerSeries.X}) n)]
  have e₁ := Over.w (Out.fstG (Ideal.span {(PowerSeries.X : PowerSeries ℂ)}) n W.t.G)
  refine (Category.assoc _ _ _).trans ((congrArg (vn ≫ ·) e₁.symm).trans ((Category.assoc _ _ _).symm.trans ?_))
  rw [h₆, Category.assoc, Over.w v]
  refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
  exact RingHom.ext fun r => h₁ r

theorem exists_lift (w : ℂ) (hw : Ha.T < w.im) : ∃ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left),
    (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left ∧
      xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ) ∧
    ∀ (x : 𝓞 E) z, xF (fun k => ty k (x : E) * z k) ≫ Y.m.φ = (xF z ≫ Y.m.φ) ≫ (Y.t.act.act x).left := by
  have hP := Ha.period w hw
  let yF : Sp ℂ ⟶ Xo.XF c := pullback.lift (Fu.u Ha.i (Ha.Pw w)) (spMap σ)
    ((Fu.over_σ _ _ hP).trans (spMap_comp _ _))
  have C := Y.m0.toSABMap.cart.1
  have hw' : ∀ z, (Fu.ex Ha.i (Ha.Pw w) z).left ≫ Xo.univ.t.G.hom = yF ≫ pullback.fst _ _ := fun z =>
    (Over.w _).trans (pullback.lift_fst _ _ _).symm
  refine ⟨fun z => C.lift _ yF (hw' z), fun z => ⟨C.lift_fst _ _ _, ?_⟩, fun x z => ?_⟩
  · rw [← Category.assoc, C.lift_snd]
    exact pullback.lift_snd _ _ _
  · rw [Category.assoc, ← Y.m.act x, ← Category.assoc]
    congr 1
    refine C.hom_ext ?_ ?_
    · rw [Category.assoc, Y.m0.toSABMap.act x, C.lift_fst, ← Category.assoc, C.lift_fst, Fu.ex_lin _ _ hP]
      rfl
    · rw [Category.assoc, Over.w, C.lift_snd, C.lift_snd]

theorem act_eq {ν ν₁ : Out.GtPt a.D₀ (epsR ℂ)} {z₀ : Fin g → ℂ} {v v₁ : epsR (PowerSeries ℂ) ⟶ W.t.G}
    {x : 𝓞 E} (hx : x ≠ 0) (h : AnVec Ha ν z₀) (hv : LieImg W ν v) (ht : IsTangent v)
    (h₁ : AnVec Ha ν₁ (fun k => ty k (x : E) * z₀ k)) (hv₁ : LieImg W ν₁ v₁) (ht₁ : IsTangent v₁) :
    v₁ = v ≫ W.t.act.act x := by
  have := W.t.act.hom x
  have ht₂ : IsTangent (v ≫ W.t.act.act x) :=
    (Chart.isTan_iff _).1 (Chart.isTan_comp ((Chart.isTan_iff _).2 ht) _)
  refine Over.OverMorphism.ext (W.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  refine ext_dual (R := PowerSeries ℂ) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ W.m.φ) (Eq.trans ht₁ (Eq.symm ht₂))).trans (Category.assoc _ _ _))) ?_
  have e : (v ≫ W.t.act.act x).left ≫ W.m.cm.F = (v.left ≫ W.m.φ) ≫ (Y.t.act.act x).left := by
    rw [Over.comp_left, Category.assoc, W.m.act x, Category.assoc]
  rw [e]
  intro V f hp hq
  obtain ⟨T₁, H₁⟩ := diff_of Ha h₁ hv₁ V f hp
  obtain ⟨T₂, H₂⟩ := diff_of Ha h hv ((Y.t.act.act x).left ⁻¹ᵁ V) (((Y.t.act.act x).left.app V).hom f) hq
  refine eq_of_sumsAt (T := max Ha.T (max T₁ T₂)) fun w hw => ?_
  simp only [max_lt_iff] at hw
  obtain ⟨xF, hF, hl⟩ := exists_lift Ha w hw.1
  refine ⟨_, H₁ w hw.2.1 xF hF, ?_⟩
  have k := H₂ w hw.2.2 xF hF
  rw [← fderiv_diag _ (fun k => (map_ne_zero _).2 (by simpa using hx))]
  simp only [hl, Points.valAt'_eq_valR] at k ⊢
  simp only [Points.valR_comp _ (Y.t.act.act x).left]
  exact k

end Hol

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {R S : Type} [CommRing R] [CommRing S] [Algebra c.F S] {k : R →+* S} {G : Over (Sp R)} [GrpObj G]
  (y : FrPt Xo c S) {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t y.x) {φ : t'.G.left ⟶ G.left}
  (hφ : IsGrpPullback t'.G G (spMap k) φ) (τ : E →+* ℂ) {v : Fin (Dw.mult τ) → (epsR R ⟶ G)}
  {u : Fin (Dw.mult τ) → (epsR S ⟶ t'.G)} (h₁ : ∀ i, (u i).left ≫ m.φ = y.u τ i)
  (h₂ : ∀ i, (u i).left ≫ φ = spMap (dualMap k) ≫ (v i).left)


include hφ h₁ h₂ in
theorem isCombAt_one {cf : Fin (Dw.mult τ) → R} (h : IsLieComb cf v 1) :
    IsCombAt y.x (y.u τ) (fun i => k (cf i)) (1 : tEps y.x ⟶ Xo.univ.t.G).left := by
  have h0 := LieCombBaseChange.prod_left_comp hφ (T := epsR R) (T' := epsR S) _ (LieCombBaseChange.dualMap_over k)
    (n := 0) Fin.elim0 Fin.elim0 (fun i => i.elim0)
  simp only [List.ofFn_zero, List.prod_nil] at h0
  obtain ⟨p, hp, e⟩ := (lieComb_baseChange R S k G t'.G φ hφ _ v 1 cf u 1 h₂ h).1 h0
  refine ⟨fun i => pushHom m.cart (epsR S) (p i), fun i => ?_, ?_⟩
  · exact (congrArg (· ≫ m.φ) (hp i)).trans ((Category.assoc _ _ _).trans (congrArg _ (h₁ i)))
  · have e₁ := map_list_prod (pushHom m.cart (epsR S)) (List.ofFn p)
    rw [← e, map_one, List.map_ofFn] at e₁
    exact congrArg (fun q => q.left) e₁.symm


include hφ h₁ h₂ in
theorem coeff_eq {cf cf' : Fin (Dw.mult τ) → R} (h : IsLieComb cf v 1) (h' : IsLieComb cf' v 1) (i) :
    k (cf i) = k (cf' i) := by
  refine congrFun ((y.basis τ _ ⟨Over.w _, ?_⟩ fun x => ?_).unique (isCombAt_one y m hφ τ h₁ h₂ h)
    (isCombAt_one y m hφ τ h₁ h₂ h')) i
  · let r : Over.mk y.x ⟶ tEps y.x := Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      refine (Category.assoc _ _ _).symm.trans (Eq.trans (congrArg (· ≫ y.x) ?_) (Category.id_comp _))
      exact (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap (RingHom.ext fun _ => rfl)) (Spec.map_id _)))
    exact congrArg (fun q => q.left) (MonObj.comp_one (M := Xo.univ.t.G) r)
  · have := Xo.univ.t.act.hom x
    let r : tEps y.x ⟶ tEps y.x := Over.homMk (spMap (epsMul (algebraMap c.F S (embK c τ x)))) (by
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ y.x) (LieCombBaseChange.epsScale_over _)))
    exact congrArg (fun q => q.left)
      ((MonObj.one_comp (Xo.univ.t.act.act x)).trans (MonObj.comp_one (M := Xo.univ.t.G) r).symm)

end Frame

theorem left_eq_of_comb {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {s : R} {v w : epsR R ⟶ G}
    (h : IsLieComb (fun _ : Fin 1 => s) (fun _ => v) w) : w.left = spMap (epsScaleR s) ≫ v.left := by
  obtain ⟨u, hu, rfl⟩ := h
  simpa using hu 0

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), GoodEmb c σ → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Mono Y.j → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) := by
  intro hL _ E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha _ y e th z hσ halg _ hF hz τ
  have hG := hL.globalFns
  have ex := GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y ℂ _ a χ W
  have lin := GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y ℂ _ a χ W
  obtain ⟨an₁, an₂, an₃, an₄⟩ := GlobalTheory.T.torusExt_exponential_derivative_bijective_tangent hG E H Dw l Xo c σ O β Y a χ W _ _ _ Ha
  obtain ⟨_, t', m1, m2, _, -, -, -, -, -, hu, -⟩ := hF
  choose v u' hv h₁ h₂ hover using hu τ
  have hi : Function.Injective (HahnSeries.ofPowerSeries ℤ ℂ) := HahnSeries.ofPowerSeries_injective
  let u : Fin (Dw.mult τ) → (epsR ℂ⸨X⸩ ⟶ t'.G) := fun i => Over.homMk (u' i) (hover i)
  refine ⟨Fintype.linearIndependent_iff.2 fun cf hcf i => ?_, fun i jj hjj => ?_⟩
  · obtain ⟨o, ho, -⟩ := an₂ 0
    have c₀ := (an₄ 0 Fin.elim0 Fin.elim0 Fin.elim0 o (fun j => j.elim0)).2 (by simpa using ho)
    have h₀ := (lin 0 _ _ o Fin.elim0 1 (fun j => j.elim0) c₀).2 ⟨Fin.elim0, fun j => j.elim0, by simp⟩
    have c₁ := (lin _ cf _ o v 1 hv ((an₄ _ cf _ _ o (hz τ)).2 (hcf ▸ ho))).1 h₀
    have c₂ := (lin _ 0 _ o v 1 hv ((an₄ _ 0 _ _ o (hz τ)).2 (by simpa using ho))).1 h₀
    exact PowerSeries.C_injective (hi (coeff_eq y m1 m2.cart τ (u := u) h₁ h₂ c₁ c₂ i))
  · refine (GlobalTheory.Relab.relab_good E H l c σ hσ).1.1 ?_
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => ?_)
    by_cases hx : x = 0
    · simp [hx]
    have ht := ((ex _).2 _ (hv i)).1 (an₃ _ _ (hz τ i))
    obtain ⟨ν₁, hν₁, -⟩ := an₂ (fun k => relab c σ (Uw.e k).1 (x : E) * z τ i k)
    obtain ⟨v₁, hv₁, -⟩ := (ex ν₁).1
    have e₁ := act_eq Ha hx (hz τ i) (hv i) ht hν₁ hv₁ (((ex _).2 _ hv₁).1 (an₃ _ _ hν₁))
    obtain ⟨ν₂, hν₂, -⟩ := an₂ (σ (embK c τ x) • z τ i)
    obtain ⟨v₂, hv₂, -⟩ := (ex ν₂).1
    have e₂ := left_eq_of_comb ((lin 1 (fun _ => σ (embK c τ x)) (fun _ => e τ i) ν₂ (fun _ => v i) v₂
      (fun _ => hv i) ((an₄ 1 _ _ (fun _ => z τ i) ν₂ fun _ => hz τ i).2 (by simpa using hν₂))).1 hv₂)
    have e₃ : v₁.left = v₂.left := by
      refine ext_of_injective hi (Eq.trans (((ex _).2 _ hv₁).1 (an₃ _ _ hν₁))
        (Eq.symm (((ex _).2 _ hv₂).1 (an₃ _ _ hν₂)))) ?_
      have e₄ : u' i ≫ (t'.act.act x).left = spMap (epsMul (algebraMap c.F ℂ⸨X⸩ (embK c τ x))) ≫ u' i := by
        refine m1.cart.1.hom_ext ?_ ?_
        · rw [Category.assoc, m1.act x, ← Category.assoc, h₁, Category.assoc, h₁]
          exact y.eig τ i x
        · rw [Category.assoc, Over.w, Category.assoc, hover]
          exact (LieCombBaseChange.epsScale_over _).symm
      have e₅ := congrArg (· ≫ m2.φ) e₄
      simp only [Category.assoc] at e₅
      rw [m2.act x, ← Category.assoc, h₂, halg] at e₅
      rw [e₁, e₂, Over.comp_left]
      refine (Category.assoc _ _ _).symm.trans (e₅.trans ?_)
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (v i).left)
        (LieCombBaseChange.dualMap_epsScale _ _).symm).trans (Category.assoc _ _ _))
    obtain rfl : ν₁ = ν₂ := ConstLie.eq_of_red W hG hv₁ hv₂ (congrArg _ e₃)
    exact mul_right_cancel₀ hjj (congrFun ((an₁ _ (an₃ _ _ hν₁)).unique hν₁ hν₂) jj)

end GlobalTheory.ArcType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockTypeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding Unf GoodEmb relab perFr gxFst gxSnd
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_letter_analyticVectors_independent_blockType : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), GoodEmb c σ → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Mono Y.j → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) := by
  first | exact @GlobalTheory.ArcType.main | exact GlobalTheory.ArcType.main | (intros; apply GlobalTheory.ArcType.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumArcLieBasis
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ.DatumBasis

open MonoidalCategory CartesianMonoidalCategory MonObj Matrix

section Coord

open GlobalTheory.Serre

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (a : OAct O G)
  {g : ℕ} {B : Fin g → (epsR R ⟶ G)} (hB : IsLieBasis B)
include hB

theorem comb_iff_symm (z : Fin g → R) (w : epsR R ⟶ G) :
    IsLieComb z B w ↔ w = ((Lie.basis a hB).equivFun.symm z).hom := by
  have e : B = fun i => (Lie.basis a hB i).hom := funext fun i => (Lie.hom_basis hB i).symm
  rw [Module.Basis.equivFun_symm_apply, ← Lie.isLieComb_iff, ← e]


include a in
theorem exists_comb (z : Fin g → R) : ∃ w, IsTangent w ∧ IsLieComb z B w :=
  ⟨_, Lie.isTangent _, (comb_iff_symm a hB z _).2 rfl⟩


include a in
theorem comb_coord {m : ℕ} {U : Fin m → Fin g → R} {u : Fin m → (epsR R ⟶ G)} (hU : ∀ k, IsLieComb (U k) B (u k))
    {z : Fin g → R} {w : epsR R ⟶ G} (hz : IsLieComb z B w) (cf : Fin m → R) :
    IsLieComb cf u w ↔ z = ∑ k, cf k • U k := by
  obtain rfl : u = fun k => ((Lie.basis a hB).equivFun.symm (U k)).hom :=
    funext fun k => (comb_iff_symm a hB _ _).1 (hU k)
  obtain rfl := (comb_iff_symm a hB _ _).1 hz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Lie.isLieComb_iff, ← (Lie.basis a hB).equivFun.symm.injective.eq_iff, map_sum]
  simp only [map_smul]
  exact ⟨fun h => Lie.ext h, fun h => congrArg Lie.hom h⟩

theorem eig_coord {x : O} {M : Matrix (Fin g) (Fin g) R} (hM : ∀ i, IsLieComb (M i) B (B i ≫ a.act x))
    {z : Fin g → R} {w : epsR R ⟶ G} (hz : IsLieComb z B w) (s : R) :
    (w ≫ a.act x).left = spMap (epsScaleR s) ≫ w.left ↔ z ᵥ* M = s • z := by
  obtain rfl := (comb_iff_symm a hB _ _).1 hz
  have h1 : ∀ i, x • Lie.basis a hB i = (Lie.basis a hB).equivFun.symm (M i) := fun i => Lie.ext (by
    rw [Lie.hom_act_smul, Lie.hom_basis]; exact (comb_iff_symm a hB _ _).1 (hM i))
  have h2 : x • (Lie.basis a hB).equivFun.symm z = (Lie.basis a hB).equivFun.symm (z ᵥ* M) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.vecMul_eq_sum, map_sum, Module.Basis.equivFun_symm_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm x, h1, map_smul]
  rw [← Lie.hom_act_smul, ← Lie.hom_smul_left, h2, ← map_smul,
    ← (Lie.basis a hB).equivFun.symm.injective.eq_iff]
  exact ⟨fun h => Lie.ext (Over.OverMorphism.ext h), fun h => by rw [h]⟩

theorem eigBasis_coord {M : O → Matrix (Fin g) (Fin g) R} (hM : ∀ x i, IsLieComb (M x i) B (B i ≫ a.act x))
    {m : ℕ} {U : Fin m → Fin g → R} {u : Fin m → (epsR R ⟶ G)} (hU : ∀ k, IsLieComb (U k) B (u k)) (ρ : O → R) :
    (∀ w : epsR R ⟶ G, IsTangent w → (∀ x, (w ≫ a.act x).left = spMap (epsScaleR (ρ x)) ≫ w.left) →
      ∃! cf : Fin m → R, IsLieComb cf u w) ↔
    ∀ z : Fin g → R, (∀ x, z ᵥ* M x = ρ x • z) → ∃! cf : Fin m → R, z = ∑ k, cf k • U k := by
  constructor
  · intro h z hz
    obtain ⟨w, hw, hc⟩ := exists_comb a hB z
    exact (existsUnique_congr (comb_coord a hB hU hc)).1
      (h w hw fun x => (eig_coord a hB (hM x) hc _).2 (hz x))
  · intro h w hw he
    obtain ⟨z, hc, -⟩ := hB.2 w hw
    exact (existsUnique_congr (comb_coord a hB hU hc)).2
      (h z fun x => (eig_coord a hB (hM x) hc _).1 (he x))

end Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem dual_over {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

section Descent

variable {R S : Type} [CommRing R] [CommRing S] {io : R →+* S} {t : SAB H (Sp R)} {t' : SAB H (Sp S)}
  (m : SABMap t' t (spMap io))

theorem exists_bc (v : epsR R ⟶ t.G) : ∃ q : epsR S ⟶ t'.G, q.left ≫ m.φ = spMap (dualMap io) ≫ v.left := by
  have hv : v.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w v
  have cond : (spMap (dualMap io) ≫ v.left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ spMap io := by
    rw [Category.assoc, hv, dual_over]
  exact ⟨Over.homMk (m.cart.1.lift _ _ cond) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

theorem tangent_of_bc [IsDomain R] (hio : Function.Injective io) {v : epsR R ⟶ t.G} {q : epsR S ⟶ t'.G}
    (h : q.left ≫ m.φ = spMap (dualMap io) ≫ v.left) (hq : IsTangent q) : IsTangent v := by
  have hv : v.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w v
  have := t.semi.separated
  have : IsDominant (spMap io) := ⟨by
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical io).2 ?_
    rw [(RingHom.injective_iff_ker_eq_bot io).1 hio]; exact bot_le⟩
  refine ext_of_isDominant_of_isSeparated t.G.hom ?_ (spMap io) ?_
  · have a : η[t.G].left ≫ t.G.hom = 𝟙 _ := Over.w η[t.G]
    rw [Category.assoc, hv, a, ← spMap_comp]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp
    rw [this]
    exact Spec.map_id _
  · have e := m.cm.e_comm
    rw [m.base] at e
    have sq : spMap io ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom =
        spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap io) := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext fun a => by simp [dualMap]
    rw [← Category.assoc, sq, Category.assoc, ← h, ← Category.assoc]
    exact (congrArg (· ≫ m.φ) hq).trans e

end Descent

theorem eigBasis_descent {K S : Type} [Field K] [CommRing S] [Nontrivial S] {io : PowerSeries K →+* S}
    {t : SAB H (Sp (PowerSeries K))} {t' : SAB H (Sp S)} (m : SABMap t' t (spMap io))
    {g : ℕ} {B : Fin g → (epsR (PowerSeries K) ⟶ t.G)} (hB : IsLieBasis B) {M : 𝓞 E → Matrix (Fin g) (Fin g) K}
    (hM : ∀ x i, IsLieComb (fun k => PowerSeries.C (R := K) (M x i k)) B (B i ≫ t.act.act x))
    {n : ℕ} {U : Fin n → Fin g → K} {v : Fin n → (epsR (PowerSeries K) ⟶ t.G)}
    (hU : ∀ k, IsLieComb (fun i => PowerSeries.C (R := K) (U k i)) B (v k)) {q : Fin n → (epsR S ⟶ t'.G)}
    (hq : ∀ k, (q k).left ≫ m.φ = spMap (dualMap io) ≫ (v k).left) (ρ : 𝓞 E → K)
    (he : ∀ k x, (q k ≫ t'.act.act x).left = spMap (epsScaleR (io (PowerSeries.C (R := K) (ρ x)))) ≫ (q k).left)
    (hb : ∀ w : epsR S ⟶ t'.G, IsTangent w →
      (∀ x, (w ≫ t'.act.act x).left = spMap (epsScaleR (io (PowerSeries.C (R := K) (ρ x)))) ≫ w.left) →
      ∃! cf : Fin n → S, IsLieComb cf q w) :
    (∀ k x, (v k ≫ t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := K) (ρ x))) ≫ (v k).left) ∧
    ∀ w : epsR (PowerSeries K) ⟶ t.G, IsTangent w →
      (∀ x, (w ≫ t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := K) (ρ x))) ≫ w.left) →
      ∃! cf : Fin n → PowerSeries K, IsLieComb cf v w := by
  let _ : Algebra K S := (io.comp (PowerSeries.C (R := K))).toAlgebra
  have := t.semi.smooth
  choose B' hB' using fun i => exists_bc m (B i)
  have hBS : IsLieBasis B' := Chart.isLieBasis_baseChange io m.cart hB hB'
  have hMS : ∀ x i, IsLieComb (((M x).map (algebraMap K S)) i) B' (B' i ≫ t'.act.act x) := fun x i =>
    Chart.comb_baseChange io m.cart (hM x i) hB' (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hB', Category.assoc]; rfl)
  have hUS : ∀ k, IsLieComb (fun j => algebraMap K S (U k j)) B' (q k) := fun k =>
    Chart.comb_baseChange io m.cart (hU k) hB' (hq k)
  have hMR : ∀ x i, IsLieComb (((M x).map (algebraMap K (PowerSeries K))) i) B (B i ≫ t.act.act x) := hM
  have hUR : ∀ k, IsLieComb (fun j => algebraMap K (PowerSeries K) (U k j)) B (v k) := hU
  have key : ∀ (T : Type) [CommRing T] (f : K →+* T) (k : Fin n) (x : 𝓞 E) (j : Fin g),
      f ((U k ᵥ* M x) j) = ((fun j => f (U k j)) ᵥ* (M x).map f) j := fun T _ f k x j =>
    RingHom.map_vecMul f (M x) (U k) j
  have hK : ∀ k x, U k ᵥ* M x = ρ x • U k := fun k x => funext fun j => (algebraMap K S).injective (by
    rw [key, (eig_coord t'.act hBS (hMS x) (hUS k) (algebraMap K S (ρ x))).1 (he k x)]
    simp)
  refine ⟨fun k x => (eig_coord t.act hB (hMR x) (hUR k) (algebraMap K _ (ρ x))).2 (funext fun j => ?_),
    (eigBasis_coord t.act hB hMR hUR fun x => algebraMap K _ (ρ x)).2 ?_⟩
  · rw [← key, hK]; simp
  · exact (GlobalTheory.commonEigenvectors_flat_baseChange K (𝓞 E) g n M ρ).1 S U hK
      ((eigBasis_coord t'.act hBS hMS hUS fun x => algebraMap K S (ρ x)).1 hb) (PowerSeries K)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Push

variable {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)

theorem tan_iff (w : epsR S ⟶ t'.G) : IsTanAt x (w.left ≫ m.φ) ↔ IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  exact ⟨fun h => (Chart.tan_push m.cart w).2 h.2,
    fun h => ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], (Chart.tan_push m.cart w).1 h⟩⟩

theorem eig_iff (w : epsR S ⟶ t'.G) (a : 𝓞 E) (s : S) :
    (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ w.left ≫ m.φ ↔
      (w ≫ t'.act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc, m.act]
  have sc : spMap (epsScaleR s) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
    rw [← spMap_comp]
    congr 1
    ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h
    · rw [Over.w, Category.assoc, hw, sc]; rfl
  · intro h
    rw [h, Category.assoc]; rfl

theorem comb_iff {n : ℕ} (v : Fin n → (epsR S ⟶ t'.G)) (cf : Fin n → S) (w : epsR S ⟶ t'.G) :
    IsCombAt x (fun i => (v i).left ≫ m.φ) cf (w.left ≫ m.φ) ↔ IsLieComb cf v w :=
  (Chart.comb_push m.cart cf v w).symm

end Push

end GlobalTheory.ArcQ.DatumBasis


open GlobalTheory.ArcQ.DatumBasis in
theorem GlobalTheory.ArcQ.arcDatum_arcLieBasis : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁), (∀ τ k, GtTanR (d.e τ k)) → ArcLieBasis d.W d.e := by
  intro hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ d htan
  have hNormal := @GlobalTheory.T.exists_normalForm_arcDatum_framedPoint_rootOfUnity
    hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ _ d
  obtain ⟨ζ, -, -, -, hN, -⟩ := hNormal
  obtain ⟨y, hy, -⟩ := hN htan
  obtain ⟨-, G, m1, m2, -, -, -, -, -, -, h, -⟩ := hy
  choose v p hv hp1 hp2 hp3 using h
  let q : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (ArcS Dw K₁) ⟶ G.G) := fun τ k => Over.homMk (p τ k) (hp3 τ k)
  have hq1 : ∀ τ k, (q τ k).left ≫ m1.φ = y.u τ k := hp1
  have hq2 : ∀ τ k, (q τ k).left ≫ m2.φ = spMap (dualMap (arcι Dw K₁)) ≫ (v τ k).left := hp2
  have hι : Function.Injective (arcι Dw K₁) := (GlobalTheory.ArcConst.algebraMap_injective Dw K₁).comp
    ((MvPolynomial.C_injective _ _).comp HahnSeries.ofPowerSeries_injective)
  have := GlobalTheory.ArcConst.isDomain Dw K₁
  have tq : ∀ τ k, IsTangent (q τ k) := fun τ k => (tan_iff m1 _).1 (hq1 τ k ▸ y.tan τ k)
  have tv : ∀ τ k, IsTangent (v τ k) := fun τ k => tangent_of_bc m2 hι (hq2 τ k) (tq τ k)
  obtain ⟨g, e₀, B, M, h₀, hB, hc, hM⟩ := GlobalTheory.ConstLie.exists_const_basis hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W
  have hU : ∀ τ k, ∃ U : Fin g → K₁, IsLieComb (fun i => PowerSeries.C (R := K₁) (U i)) B (v τ k) := fun τ k => by
    obtain ⟨U, hU, -⟩ := hc (d.e τ k)
      (((GlobalTheory.ConstLie.main hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W (d.e τ k)).2 _ (hv τ k)).2 (tv τ k))
    exact ⟨U, (GlobalTheory.ConstLin.lieImg_iff_isLieComb hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W g U e₀ (d.e τ k) B (v τ k)
      (fun i => (h₀ i).2) hU).1 (hv τ k)⟩
  choose U hU using hU
  have eig : ∀ (τ : E →+* ℂ) (w : epsR (ArcS Dw K₁) ⟶ G.G), IsEigAt c τ (w.left ≫ m1.φ) ↔
      ∀ x : 𝓞 E, (w ≫ G.act.act x).left = spMap (epsScaleR (arcι Dw K₁
        (PowerSeries.C (R := K₁) (algebraMap c.F K₁ (embK c τ x))))) ≫ w.left :=
    fun τ w => forall_congr' fun x => by rw [← arcS_pin]; exact eig_iff m1 w x _
  refine ⟨v, hv, fun τ => ?_⟩
  have hu : y.u τ = fun k => (q τ k).left ≫ m1.φ := funext fun k => (hq1 τ k).symm
  obtain ⟨a₁, a₂⟩ := eigBasis_descent m2 hB hM (hU τ) (hq2 τ) (fun x => algebraMap c.F K₁ (embK c τ x))
    (fun k => (eig τ _).1 (hq1 τ k ▸ y.eig τ k)) fun w hw he =>
      (existsUnique_congr fun cf => by rw [hu]; exact comb_iff m1 (q τ) cf w).1
        (y.basis τ _ ((tan_iff m1 w).2 hw) ((eig τ w).2 he))
  exact ⟨fun k => ⟨tv τ k, a₁ k⟩, a₂⟩
end
end
