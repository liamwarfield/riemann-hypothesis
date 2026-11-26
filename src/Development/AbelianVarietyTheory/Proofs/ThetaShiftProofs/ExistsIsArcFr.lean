module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericFrameIntegralOffFinitelyManyFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ.ExFr

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)

theorem one_eq : η[t'.G].left ≫ m.φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.one_left']
  have := m.cm.e_comm
  rw [m.base] at this
  exact this

theorem tan_iff (w : epsR S ⟶ t'.G) : IsTanAt x (w.left ≫ m.φ) ↔ IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (one_eq m).symm
    · have a : η[t'.G].left ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, hw, a, ← spMap_comp]
      have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
        ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      exact Spec.map_id _
  · intro h
    refine ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) h).trans (one_eq m)

theorem scale_over (s : S) : spMap (epsScaleR s) ≫ spMap (algebraMap S (DualNumber S)) =
    spMap (algebraMap S (DualNumber S)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem eig_iff (w : epsR S ⟶ t'.G) (a : 𝓞 E) (s : S) :
    (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ w.left ≫ m.φ ↔
      (w ≫ t'.act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc, m.act]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h
    · rw [Over.w, Category.assoc, hw, scale_over]; rfl
  · intro h
    rw [h, Category.assoc]; rfl

theorem exists_lift {T : Over (Sp S)} (v : T.left ⟶ Xo.univ.t.G.left) (hv : v ≫ Xo.univ.t.G.hom = T.hom ≫ x) :
    ∃ w : T ⟶ t'.G, w.left ≫ m.φ = v :=
  ⟨Over.homMk (m.cart.1.lift v T.hom hv) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

theorem push_prod {n : ℕ} (u : Fin n → (epsR S ⟶ t'.G)) :
    ((List.ofFn u).prod).left ≫ m.φ = ((List.ofFn fun i => pushHom m.cart (epsR S) (u i)).prod).left := by
  have := map_list_prod (pushHom m.cart (epsR S)) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact congrArg (fun q => q.left) this

theorem comb_iff {n : ℕ} (v : Fin n → (epsR S ⟶ t'.G)) (cf : Fin n → S) (w : epsR S ⟶ t'.G) :
    IsCombAt x (fun i => (v i).left ≫ m.φ) cf (w.left ≫ m.φ) ↔ IsLieComb cf v w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    choose u' hu' using fun i => exists_lift m (T := epsR S) (u i).left (Over.w (u i))
    have e : u = fun i => pushHom m.cart (epsR S) (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
    refine ⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩
    · apply m.cart.1.hom_ext
      · rw [Category.assoc]; exact (hu' i).trans (hu i)
      · have hv : (v i).left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w (v i)
        rw [Over.w, Category.assoc, hv, scale_over]; rfl
    · apply m.cart.1.hom_ext
      · rw [e] at hw
        exact hw.symm.trans (push_prod m u').symm
      · rw [Over.w, Over.w]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushHom m.cart (epsR S) (u i), fun i => ?_, (push_prod m u).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu, Category.assoc]; rfl

end GlobalTheory.ArcQ.ExFr


open GlobalTheory.ArcQ.ExFr in
theorem GlobalTheory.ArcQ.exists_isArcFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (z : Sp S ⟶ Xo.XF c), (ι.comp (PowerSeries.C (R := A))).Flat → z ≫ Y.j = spMap ι ≫ χ → z ≫ pullback.fst _ _ ≫ Xo.s = sOf c S → (∀ τ x, algebraMap c.F S (embK c τ x) = ι (PowerSeries.C (R := A) (ρ τ x))) → ∃ y : FrPt Xo c S, y.x = z ≫ pullback.fst _ _ ∧ IsArcFr W e th ι y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e th hB hth hA S _ _ ι z hfl hz hs hρ
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp S), Nonempty (SABMap t' Y.oF.t z) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull z Y.oF.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m1, hm1⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m m
  have cancel : ∀ (p : Sp S ⟶ Y.X) (_ : p = spMap ι ≫ χ) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' W.t (spMap ι), n.φ = m'.φ ≫ W.m.φ := by
    intro p hp n; subst hp; exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ W.m n
  obtain ⟨m2, hm2⟩ := cancel _ hz n
  open Matrix GlobalTheory.BasisUniv in
  have arcBasis_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
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
  obtain ⟨u, hu1, hu2⟩ := arcBasis_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e hB S ι hfl t' m2
  obtain ⟨⟨θ, hθ, -⟩, -⟩ := GlobalTheory.existsUnique_thetaOf hL hL2 E H Dw l Xo c O β Y A b a χ W th hth
  have hnz := fun g => (GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres hL hL2 E H Dw l Xo c O β Y A b a χ W th θ hth hθ hA g).2
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w2).1 g2) W.t.PP.isLB t'.PP.isLB θ
  have hI2 : IsoMaps w2 σ' (thfPull W.t.PP.L m2.φ θ) := fun (i : PUnit → W.t.PP.L.ι) k => fn_ext fun y hy =>
    (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans
      ((hσ' _ (𝟙 _) y (i PUnit.unit) k (mem_pull.1 hy.1) hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))))))
  have nz := GlobalTheory.SectionBaseChange.fibre_nonzero_of_pull t'.PP.isLB hσ' m2.cart.1 hnz
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have hLB : LBIso t'.PP.L (Xo.univ.t.PP.L.pull m1.cm.F) := by
    obtain ⟨w, hw, -⟩ := m1.lin
    exact ⟨w, hw⟩
  have hgen := GlobalTheory.SectionBaseChange.generates hL.secBaseChange (GlobalTheory.Obj.toPolAV Xo.univ) m1.cart.1 t'.PP.isLB hLB σ' nz
  obtain ⟨s, w1, s1, r1, hI1, hg, hsgen⟩ := frame_of_gen Xo _ t' m1 σ' hgen
  have eig : ∀ (τ : E →+* ℂ) (w : epsR S ⟶ t'.G), IsEigAt c τ (w.left ≫ m1.φ) ↔
      ∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left :=
    fun τ w => forall_congr' fun x => by rw [← hρ]; exact eig_iff m1 w x _
  refine ⟨⟨z ≫ pullback.fst _ _, (Category.assoc _ _ _).trans hs, fun τ k => (u τ k).left ≫ m1.φ,
    fun τ k => (tan_iff m1 _).2 ((hu2 τ).1 k).1, fun τ k => (eig τ _).2 ((hu2 τ).1 k).2, fun τ w hw hw' => ?_,
    s, hsgen⟩, rfl, z, t', m1, m2, m.φ, hz, rfl, m.cart.1.w, hm1.symm, hn.symm.trans hm2, fun τ k => ?_,
    θ, w1, w2, σ', s1, _, hθ, r1, ⟨g2, r2⟩, hI1, hI2, fun _ _ => rfl, hg⟩
  · obtain ⟨w', rfl⟩ := exists_lift m1 (T := epsR S) w hw.1
    exact (existsUnique_congr fun cf => comb_iff m1 (u τ) cf w').2
      ((hu2 τ).2 w' ((tan_iff m1 w').1 hw) ((eig τ w').1 hw'))
  · obtain ⟨v, hv, hv'⟩ := hu1 τ k
    exact ⟨v, (u τ k).left, hv, rfl, hv', Over.w (u τ k)⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDisc
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.DiscInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem sp_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (dualMap (φ.comp io)) = spMap (dualMap φ) ≫ spMap (dualMap io) := by
  rw [← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap]

theorem flat_of_injective {A V : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing V] [IsDomain V]
    (f : A →+* V) (hf : Function.Injective f) : f.Flat := by
  algebraize [f]
  have : FaithfulSMul A V := (faithfulSMul_iff_algebraMap_injective A V).2 hf
  show Module.Flat A V
  infer_instance

theorem isTan_iff {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sec_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {G : SAB H S'} {t' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (m : SABMap G t f) (n : SABMap t' G g) (k : SABMap t' t h) (hb : h = g ≫ f)
    (hφ : k.φ = n.φ ≫ m.φ) (θ : LB.Sec t.PP.L) (w : LB.Iso t'.PP.L (t.PP.L.pull k.φ)) (σ : LB.Sec t'.PP.L)
    (θ2 : LB.Sec (t.PP.L.pull k.φ)) (r : RigIso k w) (hi : IsoMaps w σ θ2) (hp : PullSec k.φ θ θ2) :
    ∃ (θ' : LB.Sec G.PP.L) (w' : LB.Iso t'.PP.L (G.PP.L.pull n.φ)),
      (∀ s : S', (∃ x : t.G.left, t.G.hom x = f s ∧ x ∈ Out.nonzeroLocus θ) →
        ∃ x : G.G.left, G.G.hom x = s ∧ x ∈ Out.nonzeroLocus θ') ∧
      RigIso n w' ∧ IsoMaps w' σ (thfPull G.PP.L n.φ θ') := by
  obtain ⟨w0, g0, r0, -⟩ := m.lin
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) t.PP.isLB G.PP.isLB θ
  have he : k.cm.e = n.cm.e ≫ m.cm.e := by rw [k.base, n.base, m.base, hb]
  obtain ⟨w', r', tri⟩ := GlobalTheory.Reg.TieIntegral.exists_rigIso_cancel m.cm n.cm k.cm hφ he t'.PP G.PP t.PP w0 w ⟨g0, r0⟩ r
  refine ⟨θ', w', ?_, r', fun (i : PUnit → G.PP.L.ι) k' => fn_ext fun y hy => ?_⟩
  · rintro s ⟨z, hz, hz'⟩
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 z s hz
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨i, hi⟩ := exists_chart G.PP.isLB y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨i, hi, ?_⟩⟩
    have u₁ : IsUnit (gs m.φ y _ (θ.f j)) := by rw [gs_stalkMap m.φ y _ hj]; exact u.map _
    have e := hθ' _ (𝟙 _) y j i hj hi
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · have hi' : n.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
    obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (n.φ y))
    have pt : k.φ y = m.φ (n.φ y) := congrArg (fun q => q y) hφ
    have hj' : k.φ y ∈ t.PP.L.U j := pt ▸ hj
    have e1 := hθ' _ (𝟙 _ ≫ n.φ) y j (i PUnit.unit) hj hi'
    have e2 : gs (𝟙 _ ≫ k.φ) y _ (θ.f j) = (gw w (𝟙 _) y j k').val * gs (𝟙 _) y _ (σ.f k') := by
      have hz : y ∈ (t.PP.L.pull k.φ).U (fun _ => j) ⊓ t'.PP.L.U k' := ⟨mem_pull.2 hj', hy.2⟩
      have le : (t.PP.L.pull k.φ).U (fun _ => j) ≤ k.φ ⁻¹ᵁ t.PP.L.U j := fun q hq => mem_pull.1 hq
      have a := congrArg (gs (𝟙 _) y _) (hi (fun _ => j) k')
      refine (gs_appLE k.φ _ _ le (𝟙 _) y hz.1 _).symm.trans ?_
      rw [← hp (fun _ => j) le]
      exact (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
    have e3 := tri _ (𝟙 _) y j (i PUnit.unit) k' hj hi' hy.2
    have e4 : (𝟙 _ ≫ n.φ) ≫ m.φ = 𝟙 _ ≫ k.φ := by rw [Category.assoc, hφ]
    rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
    refine (gs_res _ y _ hy _).trans ((gs_appLE n.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

end GlobalTheory.ArcQ.DiscInt

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames


open DiscInt in
theorem integral_of_isArcFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) [IsPrincipalIdealRing A] (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (ev : PowerSeries A →+* T.V), Function.Injective (ev.comp (PowerSeries.C (R := A))) → (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ev (PowerSeries.C (R := A) (ρ τ x)))) → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y → Integral T io y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W _ ρ e th hB hth hPI T io ev hinj hρ
  letI := io.toAlgebra
  intro y hy
  obtain ⟨z, t', m1, k, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hθ, r1, r2, i1, i2, p2, hg⟩ := hy
  obtain ⟨G, ⟨m⟩⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G W.t (spMap ev)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ev) W.t
    exact ⟨_, ⟨m⟩⟩
  have hb := sp_comp ev (algebraMap T.V T.Fr)
  obtain ⟨n, hn⟩ : ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ := by
    have key : ∀ (g : Sp T.Fr ⟶ _) (k : SABMap t' W.t g), g = spMap (algebraMap T.V T.Fr) ≫ spMap ev →
        ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ := by
      intro g k hg
      subst hg
      exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m k
    exact key _ k hb
  obtain ⟨u, hu1, hu2⟩ :=
    GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e hB
      T.V ev (flat_of_injective _ hinj) G m
  have eig : ∀ (τ : E →+* ℂ) (w : epsR T.V ⟶ G.G), IsEigV c io G τ w ↔ ∀ x : 𝓞 E, (w ≫ G.act.act x).left =
      spMap (epsScaleR (ev (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left := fun τ w =>
    ⟨fun h x => h x _ (hρ τ x).symm, fun h x s hs => by
      obtain rfl : s = ev (PowerSeries.C (R := A) (ρ τ x)) := IsFractionRing.injective T.V T.Fr (hs.trans (hρ τ x))
      exact h x⟩
  obtain ⟨θ', w', hnz, r', i'⟩ := sec_cancel m n k hb hn θ w2 σ θ2 r2 i2 p2
  refine ⟨G, t', m1, n, ⟨u, fun τ i => (isTan_iff _).2 ((hu2 τ).1 i).1, fun τ i => (eig τ _).2 ((hu2 τ).1 i).2,
    fun τ w h1 h2 => (hu2 τ).2 w ((isTan_iff _).1 h1) ((eig τ w).1 h2), fun τ i => ?_⟩, θ',
    GlobalTheory.T.polarisation_section_generates_of_special_fibre hL hL2 E H Dw l Xo c T G t' y.x m1 n θ'
      (hnz _ (GlobalTheory.T.thetaSection_of_arc_nonzero_on_fibres hL hL2 E H Dw l Xo c O β Y A b a χ W th θ hth hθ (Or.inr hPI) _).2),
    w1, w', σ, s1, thfPull G.PP.L n.φ θ', r1, r', i1, i', fun _ _ => rfl, hg⟩
  obtain ⟨v, p, h1, h2, h3, pb⟩ := hu τ i
  obtain ⟨v', h1', h3'⟩ := hu1 τ i
  obtain rfl : v = v' := (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c O β Y A b a χ W (e τ i)).1.unique h1 h1'
  refine ⟨p, h2, ?_⟩
  apply m.cart.1.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact (congrArg _ hn.symm).trans (h3.trans (by rw [dual_comp, Category.assoc]; exact congrArg _ h3'.symm))
  · have ub : (u τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (u τ i)
    rw [Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, pb]
    exact ((congrArg _ ub).trans (dual_alg _)).symm

end GlobalTheory.ArcQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDiscStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_framedPoint_integral_open_disc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) [IsPrincipalIdealRing A] (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (ev : PowerSeries A →+* T.V), Function.Injective (ev.comp (PowerSeries.C (R := A))) → (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ev (PowerSeries.C (R := A) (ρ τ x)))) → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y → Integral T io y := by
  exact @GlobalTheory.ArcQ.integral_of_isArcFr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegralOfFrChg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ.IntChg

section Sec

variable {X Y : Scheme.{0}}

def mulSec {L : LB X} (r : Γ(X, ⊤)) (s : LB.Sec L) : LB.Sec L where
  f i := resG X le_top r * s.f i
  compat i j := by
    have e : ∀ (U : X.Opens) (h : L.U i ⊓ L.U j ≤ U),
        (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := fun U h => by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_mul, map_mul, s.compat i j, e, e, mul_left_comm]

theorem res_res {U V : X.Opens} (h : V ≤ U) (r : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem appLE_res (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (r : Γ(X, ⊤)) :
    (f.appLE U V h).hom (resG X le_top r) = resG Y le_top (f.appTop.hom r) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

theorem isoMaps_mul {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s')
    (r : Γ(X, ⊤)) : IsoMaps w (mulSec r s) (mulSec r s') := by
  intro i k
  have := h i k
  simp only [mulSec, map_mul, res_res]
  rw [this, mul_left_comm]

theorem pullSec_mul {L : LB X} {f : Y ⟶ X} {s : LB.Sec L} {s' : LB.Sec (L.pull f)} (h : PullSec f s s')
    (r : Γ(X, ⊤)) : PullSec f (mulSec r s) (mulSec (f.appTop.hom r) s') := by
  intro j hj
  simp only [mulSec, map_mul, appLE_res]
  rw [h j hj]

theorem appTop_toΓ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) :
    (spMap φ).appTop.hom (toΓ A a) = toΓ B (φ a) := by
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

end Sec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem integral_scal (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr) (a : T.Vˣ) (s' : LB.Sec (PPx y.x))
      (hg : ∀ s'' : LB.Sec (PPx y.x), ∃! b : T.Fr, ∀ i, s''.f i = scal y.x b i * s'.f i),
      (∀ i, s'.f i = scal y.x (algebraMap T.V T.Fr a) i * y.s.f i) → Integral T io y →
      Integral T io { y with s := s', gen := hg } := _root_.GlobalTheory.Reg.GenInt.integral_scal T io

theorem integral_chg (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y y' : FrPt Xo c T.Fr) (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (a : T.Vˣ),
      (∀ τ, IsUnit (k τ).det) → FrChg (fun τ => (k τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr a) y y' →
      Integral T io y → Integral T io y' := by
  let _ := io.toAlgebra
  intro y y' k a hk ⟨hx, hu, pm, h1, h2, h3⟩ hy
  have hk' : ∀ τ, IsUnit (k τ).transpose.det := fun τ => by rw [Matrix.det_transpose]; exact hk τ
  have hK : ∀ τ, IsUnit ((k τ).transpose.map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((k τ).transpose.map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (k τ).transpose.det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk' τ).map _
  have hr := GlobalTheory.IntRebase.integral_reb T io y hy (fun τ => (k τ).transpose) hk' hK
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := y'
  simp only at hx
  subst hx
  have eu : zu = (GlobalTheory.IntRebase.rebase₂ y _ hK).u := by
    funext τ i
    exact Formalism.L2.PjFree.isCombAt_unique (hu τ i)
      ((GlobalTheory.IntRebase.isCombAtG_iff Xo.univ.t y.x (fun j => GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (y.tan τ j)) _ _).2 rfl)
  subst eu
  have ep : pm = 𝟙 _ := by
    apply pullback.hom_ext
    · refine h2.trans ?_
      simp only [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]
      rfl
    · exact h1.trans (Category.id_comp _).symm
  subst ep
  refine integral_scal T io (GlobalTheory.IntRebase.rebase₂ y _ hK) a zs zg (fun i => ?_) hr
  exact (h3 i le_rfl).symm.trans (GlobalTheory.IntRebase.id_appLE_apply _ _ _ _)

theorem integral_of_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (s : T.V), (∀ τ, IsUnit (g τ).det) → IsUnit s → letI := io.toAlgebra; ∀ y y' : FrPt Xo c T.Fr, FrChg (fun τ => (g τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr s) y y' → Integral T io y → Integral T io y' := by
  intro E _ _ _ H Dw l Xo c T io g s hg hs y y' h hy
  obtain ⟨a, rfl⟩ := hs
  exact integral_chg T io y y' g a hg h hy

end GlobalTheory.ArcQ.IntChg
end
end
