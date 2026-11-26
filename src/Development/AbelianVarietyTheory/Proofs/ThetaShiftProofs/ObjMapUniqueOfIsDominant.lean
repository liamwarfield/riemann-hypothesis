module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

namespace ObjRigid

theorem weil_eq_of_iso {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (θ : A ≅ A) [IsMonHom θ.hom] (w : LB.Iso L (L.pull θ.hom.left)) (hw : w.IsGen) {T : Over S}
    [Subsingleton T.left] (k : ℤ) (x y : T ⟶ A) (c c₀ : Γ(T.left, ⊤)ˣ) (h : Out.WeilIs A L k x y c)
    (h₀ : Out.WeilIs A L k (x ≫ θ.hom) (y ≫ θ.hom) c₀) : c = c₀ := by
  refine unit_ext fun p _ => ?_
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hx₀, hy₀⟩, hall₀⟩ := h₀ p
  obtain ⟨V', hpV', -, hall⟩ := h p
  obtain rfl : V = V' := by
    ext q
    rw [Subsingleton.elim q p]
    exact ⟨fun _ => hpV', fun _ => hpV⟩
  have hp := isGrpPullback_of_iso θ
  have hτ : 𝟙 _ ≫ (Out.overRes (T := T) V).hom = (Out.overRes (T := T) V).hom ≫ 𝟙 S := by
    rw [Category.id_comp, Category.comp_id]
  have mvx : 𝟙 _ ≫ θx₀.pt.left = (Out.overResι V ≫ x).left ≫ θ.hom.left := by
    rw [hx₀, Category.id_comp, ← Over.comp_left, Category.assoc]
  have mvy : 𝟙 _ ≫ θy₀.pt.left = (Out.overResι V ≫ y).left ≫ θ.hom.left := by
    rw [hy₀, Category.id_comp, ← Over.comp_left, Category.assoc]
  obtain ⟨θx, hθx, mx⟩ := exists_theta_move hp (𝟙 _) hτ hL hL w hw k _ θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := exists_theta_move hp (𝟙 _) hτ hL hL w hw k _ θy₀ mvy
  have hm := commIsOf_move hp (𝟙 _) hτ hL hL w k θx₀ θy₀ θx θy (by rw [hθx]; exact mvx) (by rw [hθy]; exact mvy)
    mx my (Out.unitRes V c₀) (Out.unitRes V c₀) (fun Z r z => by rw [Category.comp_id]) (hall₀ θx₀ θy₀ hx₀ hy₀)
  exact WeilCube.germ_eq_of_unitRes hpV (commIsOf_unique hL θx θy _ _ (hall θx θy hθx hθy) hm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_eq_nsmul (D : Datum H) (n : ℕ) (v : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF v b) : ∃ z, v = n • z := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
    simpa using h b
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let f : D.La →+ ℤ := AddMonoidHom.mk' (fun b => D.EF v b / n) fun b b' => by
    rw [map_add (f := _), Int.add_ediv_of_dvd_left (h b)]
  obtain ⟨z, hz⟩ := D.unimod.2 f.toIntLinearMap
  refine ⟨z, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, hz]
  exact (Int.mul_ediv_cancel' (h b)).symm

theorem fix_torsion {D : Datum H} (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) (θ : Q →* Q)
    (θ_act : ∀ a x, θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y c c', e l.M x y c → e l.M (θ x) (θ y) c' → c = c')
    (θ_fix : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), θ (I.ev l.M a) = I.ev l.M a)
    (x : Q) (hx : x ^ l.M = 1) : θ x = x := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨a, rfl⟩ := (I.onto _ hM x).1 hx
  obtain ⟨a', ha'⟩ := (I.onto _ hM (θ (I.ev l.M a))).1 (by rw [← map_pow, hx, map_one])
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp l.coprime)
  have hj' : I.ev l.M (j • a') = I.ev l.M (j • a) := by
    rw [← θ_fix (j • a) (Submodule.smul_mem_smul hj trivial), I.lin, I.lin, θ_act, ha']
  obtain ⟨z, hz⟩ := exists_eq_nsmul D l.M (i • (a' - a)) fun b => by
    have hb : H.bar i • b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
      Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) trivial
    have h := θ_iso _ _ _ _ (I.isom _ hM a (H.bar i • b)) (by
      rw [θ_fix _ hb, ← ha']; exact I.isom _ hM a' (H.bar i • b))
    rw [D.adj, map_sub, LinearMap.sub_apply, ← (I.ζ_prim _ hM).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]
  have hi' : I.ev l.M (i • a') = I.ev l.M (i • a) := by
    have h : i • a' = i • (a' - a) + i • a := by rw [← smul_add, sub_add_cancel]
    rw [h, I.add, (I.ker _ hM _).2 ⟨z, hz⟩, _root_.one_mul]
  have split : ∀ v, I.ev l.M v = I.ev l.M (i • v) * I.ev l.M (j • v) := fun v => by
    rw [← I.add, ← add_smul, hij, one_smul]
  rw [← ha', split a', split a, hi', hj']

variable {D : Datum H} {l : Level H}

theorem aut_eq_id (hS : Out.SerreSt) {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} [IsLocallyNoetherian S]
    {s : S ⟶ Sp B} (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) [IsDominant x]
    (θ : o.t.G ≅ o.t.G) [IsMonHom θ.hom] (hact : ∀ a, o.t.act.act a ≫ θ.hom = θ.hom ≫ o.t.act.act a)
    (hL : LBIso o.t.PP.L (o.t.PP.L.pull θ.hom.left)) (heta : ∀ a, o.eta a ≫ θ.hom = o.eta a) :
    θ.hom = 𝟙 _ := by
  obtain ⟨w, hw⟩ := hL
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have := o.t.semi.smooth
  have := o.t.semi.geomConnected
  have := o.proper
  have hsub : Subsingleton (Sp k) := inferInstance
  let p : Sp k := IsLocalRing.closedPoint k
  have : ConnectedSpace S := by
    have : Nonempty S := ⟨x p⟩
    have : PreconnectedSpace S := x.denseRange.preconnectedSpace x.continuous
    exact ⟨inferInstance⟩
  have : ConnectedSpace o.t.G.left := GeometricallyConnected.connectedSpace o.t.G.hom o.t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected o.t.G.hom (eSec o.t.G (x p))
  obtain ⟨-, ws, gs', -⟩ := o.t.sym
  let P : Out.PolAV S :=
    { A := o.t.G, g := d, smoothDim := hd, L := o.t.PP.L, isLB := o.t.PP.isLB, ample := o.ample, ktriv := o.ktriv
      isAb := ⟨inferInstance, inferInstance, inferInstance, ‹_›⟩
      rigid := ⟨o.t.PP.rig, o.t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage _).symm
  have hMu : IsUnit (l.M : Γ(S, ⊤)) := by
    simpa using (b.unit _ hM).map ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ s.appTop).hom
  have : Etale (Out.mulA o.t.G l.M).left := GrpTangent.etale_id_pow o.t.G hMu
  have : IsSeparated (Out.mulA o.t.G l.M).left := by
    have : IsSeparated ((Out.mulA o.t.G l.M).left ≫ o.t.G.hom) := by rw [Over.w]; infer_instance
    exact IsSeparated.of_comp _ o.t.G.hom
  refine hS S P l.M l.three_le θ ‹_› (fun _ => ⟨⊤, trivial, ?_⟩)
    (fix_torsion_of_fix_geometric_of_etale o.t.G l.M x θ.hom fun y hy => ?_)
  · obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (o.t.G.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut o.t.PP.L _ _ _ _ fun n => ?_) t ht
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  · refine fix_torsion l I (IsMonHom.monoidHom θ.hom (Over.mk x)) (fun a z => ?_) (fun z z' c c' h h' => ?_)
      (fun a ha => ?_) y hy
    · show (z ≫ _) ≫ θ.hom = (z ≫ θ.hom) ≫ _
      rw [Category.assoc, hact, Category.assoc]
    · have : Subsingleton (Over.mk x).left := hsub
      exact unitOn_injective (weil_eq_of_iso (T := Over.mk x) o.t.PP.isLB θ w hw _ z z' _ _ h h')
    · show _ ≫ θ.hom = _
      rw [← hI a ha, Category.assoc, heta]

end ObjRigid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem objMap_unique_of_isDominant (hS : Out.SerreSt) {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S S' : Scheme.{0}} [IsLocallyNoetherian S'] {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') [IsDominant x]
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y : S' ⟶ S} (m m' : ObjMap o₁ o y) :
    m.toSABMap.φ = m'.toSABMap.φ := by
  obtain ⟨θ, hθ, hφ, hact, -, w, hw, -⟩ := sabMap_iso m.toSABMap m'.toSABMap rfl rfl
  have h := ObjRigid.aut_eq_id hS o₁ x θ hact ⟨w, hw⟩ fun a => by
    apply Over.OverMorphism.ext
    apply m'.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ).trans ((m.eta a).trans (m'.eta a).symm)
    · rw [Over.w, Over.w]
  rw [← hφ, h, Over.id_left, Category.id_comp]

theorem objMap_unique_of_isDomain (hS : Out.SerreSt) {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {s : S ⟶ Sp B}
    {s' : Sp R ⟶ Sp B'} {o : Obj D l b s} {o₁ : Obj D l b' s'} {y : Sp R ⟶ S} (m m' : ObjMap o₁ o y) :
    m.toSABMap.φ = m'.toSABMap.φ := by
  let φ : R →+* AlgebraicClosure (FractionRing R) := (algebraMap (FractionRing R) _).comp (algebraMap R _)
  have hφ : Function.Injective φ := (algebraMap (FractionRing R) _).injective.comp (IsFractionRing.injective R _)
  have : IsDominant (spMap φ) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)⟩
  exact objMap_unique_of_isDominant hS (spMap φ) m m'

theorem objMap_unique_of_field (hS : Out.SerreSt) {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {F : Type} [Field F] {s : S ⟶ Sp B} {s' : Sp F ⟶ Sp B'}
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y : Sp F ⟶ S} (m m' : ObjMap o₁ o y) :
    m.toSABMap.φ = m'.toSABMap.φ :=
  objMap_unique_of_isDomain hS m m'

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frChg_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s s' : S) (y y' y'' : FrPt Xo c S), FrChg g s y y' → (FrChg g' s' y' y'' ↔ FrChg (fun τ => g' τ * g τ) (s' * s) y y'')) ∧ (∀ y : FrPt Xo c S, FrChg (fun _ => 1) 1 y y) ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), FrChg g s y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ s) z z')) ∧ ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' ↔ ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ (∀ τ i j, i < j → g τ i j = 0) ∧ FrChg g (t none : S) y y' := by
  intro E _ _ _ H Dw l Xo c S _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g g' s s' y y' y'' h
    refine ⟨fun h' => (frChg_refl_and_comp E H Dw l Xo c S y y' y'').2 g g' s s' h h', fun h' => ?_⟩
    have hx : y'.x = y.x := h.1
    have hx' : y''.x = y.x := h'.1
    obtain ⟨g₀, a₀, hg₀, h₀⟩ := (frChg_exists_unique E H Dw l Xo c S y y').1 hx
    obtain ⟨rfl, rfl⟩ := (frChg_exists_unique E H Dw l Xo c S y y').2 _ _ _ _ h h₀
    obtain ⟨k, b, -, hk⟩ := (frChg_exists_unique E H Dw l Xo c S y' y'').1 (hx'.trans hx.symm)
    have hc := (frChg_refl_and_comp E H Dw l Xo c S y y' y'').2 _ _ _ _ h hk
    obtain ⟨e₁, e₂⟩ := (frChg_exists_unique E H Dw l Xo c S y y'').2 _ _ _ _ h' hc
    have e₃ : g' = k := by
      funext τ
      exact ((Matrix.isUnit_iff_isUnit_det _).2 (hg₀ τ)).mul_right_cancel (congrFun e₁ τ)
    have e₄ : s' = (b : S) := a₀.isUnit.mul_right_cancel e₂
    rw [e₃, e₄]
    exact hk
  · intro y
    exact (frChg_refl_and_comp E H Dw l Xo c S y y y).1
  · intro T _ _ φ g s y y' z z' h hm
    exact ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g s h hm
  · intro t y y'
    rw [(frBor_calculus E H Dw l Xo c S y y' y').1 t]
    exact ⟨fun ⟨g, a, b, c⟩ => ⟨g, b, a, c⟩, fun ⟨g, a, b, c⟩ => ⟨g, b, a, c⟩⟩

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangularStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameChange_compose_invert_baseChange_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s s' : S) (y y' y'' : FrPt Xo c S), FrChg g s y y' → (FrChg g' s' y' y'' ↔ FrChg (fun τ => g' τ * g τ) (s' * s) y y'')) ∧ (∀ y : FrPt Xo c S, FrChg (fun _ => 1) 1 y y) ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), FrChg g s y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ s) z z')) ∧ ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' ↔ ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ (∀ τ i j, i < j → g τ i j = 0) ∧ FrChg g (t none : S) y y' := by
  first | exact @GlobalTheory.Frames.frChg_calculus | exact GlobalTheory.Frames.frChg_calculus | (intros; apply GlobalTheory.Frames.frChg_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
noncomputable section

namespace GlobalTheory.ArcQBC

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Bundles

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
  {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}

theorem pmaps_unique (hL : L.IsLB) {a a' : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (H' : PMaps w φ' φ ε a' t h) : a = a' := by
  obtain ⟨s⟩ := a
  obtain ⟨s'⟩ := a'
  refine congrArg _ (funext fun q => unit_ext fun y hy => ?_)
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  exact mul_left_cancel ((H _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)).symm.trans
    (H' _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)))

theorem pmaps_of_val (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (ht : t.IsGen)
    (H : ∀ (y : Y') J J', Good L y J → Good L' y J' → val t (𝟙 _ ≫ h) y J =
      (∏ k, ConstFam.wVal w y J J' (𝟙 _ ≫ φ' k) ^ ε k) * val a (𝟙 _) y J') : PMaps w φ' φ ε a t h := by
  obtain ⟨a', ha', H'⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) hL hL' h hψ t ht
  obtain rfl : a = a' := by
    obtain ⟨s⟩ := a
    obtain ⟨s'⟩ := a'
    refine congrArg _ (funext fun q => unit_ext fun y hy => ?_)
    obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' hL' y
    have e := mul_left_cancel ((H y J J' hJ hJ').symm.trans (ConstFam.pmaps_val hψ H' (𝟙 _) hJ hJ'))
    exact (gen_trans ha (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).trans ((congrArg _ e).trans
      (gen_trans ha' (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).symm)
  exact H'

theorem exists_pullSec (F : X' ⟶ X) (s : LB.Sec L) : ∃ θ : LB.Sec (L.pull F), PullSec F s θ := by
  have le : ∀ j, (L.pull F).U j ≤ F ⁻¹ᵁ L.U (j PUnit.unit) := fun j y hy => mem_pull.1 hy
  refine ⟨⟨fun j => (F.appLE _ _ (le j)).hom (s.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => ?_⟩, fun j h => rfl⟩
  refine ((gs_res _ y _ hy _).trans ((gs_appLE F _ _ (le j) (𝟙 _) y hy.1 _).trans
    (gs_compat s (𝟙 _ ≫ F) y (le j hy.1) (le j' hy.2)))).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 _) y j j' hy.1 hy.2)))
        ((gs_res _ y _ hy _).trans (gs_appLE F _ _ (le j') (𝟙 _) y hy.2 _)))))

theorem through_iff (s : LB.Sec L) (s' : LB.Sec L') :
    (∃ θ : LB.Sec (L.pull F), PullSec F s θ ∧ IsoMaps w s' θ) ↔
      ∀ (y : X') j k, F y ∈ L.U j → y ∈ L'.U k →
        gs (𝟙 _ ≫ F) y _ (s.f j) = (gw w (𝟙 _) y j k).val * gs (𝟙 _) y _ (s'.f k) := by
  have le : ∀ j, (L.pull F).U j ≤ F ⁻¹ᵁ L.U (j PUnit.unit) := fun j y hy => mem_pull.1 hy
  have key : ∀ θ : LB.Sec (L.pull F), PullSec F s θ → ∀ (y : X') (j : PUnit → L.ι), y ∈ (L.pull F).U j →
      gs (𝟙 _) y _ (θ.f j) = gs (𝟙 _ ≫ F) y _ (s.f (j PUnit.unit)) := fun θ hθ y j hy => by
    rw [hθ j (le j)]
    exact gs_appLE F _ _ (le j) (𝟙 _) y hy _
  constructor
  · rintro ⟨θ, hθ, hm⟩ y j k hj hk
    have hy : (𝟙 X' : X' ⟶ X') y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    refine (key θ hθ y (fun _ => j) hy.1).symm.trans ((gs_res _ y _ hy _).symm.trans
      ((congrArg (gs (𝟙 _) y _) (hm (fun _ => j) k)).trans ((gs_mul _ y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)))))
  · intro H
    obtain ⟨θ, hθ⟩ := exists_pullSec F s
    refine ⟨θ, hθ, fun (j : PUnit → L.ι) k => fn_ext fun y hy => ?_⟩
    exact (gs_res _ y _ hy _).trans ((key θ hθ y j hy.1).trans ((H y _ k (le j hy.1) hy.2).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))))))

end Bundles

section Data

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {f : A →+* A'} {D₀ : DegPre A}
  {D₁ : DegPre A'} (p : IsPullDeg f D₀ D₁)

theorem letBC_iff (ν : GtPt D₀ (epsR A)) (ν₁ : GtPt D₁ (epsR A')) :
    LetBC p ν ν₁ ↔ ν₁.b.left ≫ prj p = spMap (dualMap f) ≫ ν.b.left ∧ ∀ χ,
      (∀ i, DegPre.gtφT D₁ (epsR A') ν₁.b χ i ≫ prj p = spMap (dualMap f) ≫ DegPre.gtφT D₀ (epsR A) ν.b (p.xe χ) i) ∧
      PMaps p.w _ _ DegPre.gtε (ν₁.s χ) (ν.s (p.xe χ)) (spMap (dualMap f)) :=
  and_congr Iff.rfl (forall_congr' fun χ =>
    ⟨fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff p.w _ _ _ (ν₁.s χ) (ν.s (p.xe χ)) _ _
      (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩,
    fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff p.w _ _ _ (ν₁.s χ) (ν.s (p.xe χ)) _ _
      (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2 hm⟩⟩)

omit [IsDomain A] [IsDomain A'] in
theorem dual_base (f : A →+* A') : spMap (dualMap f) ≫ (epsR A).hom = (epsR A').hom ≫ spMap f := by
  refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

omit [IsDomain A] [IsDomain A'] in
theorem dual_fst (f : A →+* A') : spMap (TrivSqZeroExt.fstHom A' A' A').toRingHom ≫ spMap (dualMap f) =
    spMap f ≫ spMap (TrivSqZeroExt.fstHom A A A).toRingHom := by
  refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
  refine RingHom.ext fun x => ?_
  simp [dualMap]

theorem existsUnique_letBC (hG : GlobalFnsSt) (ν : GtPt D₀ (epsR A)) : ∃! ν', LetBC p ν ν' := by
  have gp := pull_grp p
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp p.w_gen p.xe.toAddMonoidHom p.c_pr
    (T := epsR A) (T' := epsR A') (spMap (dualMap f)) (dual_base f) ν
  refine existsUnique_of_exists_of_unique ⟨g, (letBC_iff p _ _).2 ⟨(hg 0).1 2, fun χ => ⟨(hg χ).1,
    pmaps_of_val p.w_gen D₀.P.isLB D₁.P.isLB (hg χ).1 (g.isGen χ) (ν.isGen _) fun y J J' hJ hJ' =>
      (hg χ).2 _ (𝟙 _) y J J' hJ hJ'⟩⟩⟩ fun g₁ g₂ h₁ h₂ => ?_
  rw [letBC_iff] at h₁ h₂
  obtain ⟨b₁, s₁, _, _, _⟩ := g₁
  obtain ⟨b₂, s₂, _, _, _⟩ := g₂
  obtain rfl : b₁ = b₂ :=
    Over.OverMorphism.ext (gp.1.hom_ext (h₁.1.trans h₂.1.symm) ((Over.w b₁).trans (Over.w b₂).symm))
  obtain rfl : s₁ = s₂ := funext fun χ => pmaps_unique D₀.P.isLB (h₁.2 χ).2 (h₂.2 χ).2
  rfl

theorem gtTanR_of_letBC (hG : GlobalFnsSt) {ν : GtPt D₀ (epsR A)} {ν' : GtPt D₁ (epsR A')} (h : LetBC p ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  have gp := pull_grp p
  rw [letBC_iff] at h
  obtain ⟨g₀, ⟨z₁, z₂⟩, q₁, q₂⟩ := ht
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp p.w_gen p.xe.toAddMonoidHom p.c_pr
    (T := Over.mk (𝟙 (Sp A))) (T' := Over.mk (𝟙 (Sp A'))) (spMap f)
    ((Category.comp_id _).trans (Category.id_comp _).symm) g₀
  let ρ : Over.mk (𝟙 (Sp A')) ⟶ epsR A' := Over.homMk (spMap (TrivSqZeroExt.fstHom A' A' A').toRingHom) (by
    refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (Spec.map_id _))
    exact RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  have hb : g.b.left ≫ prj p = spMap f ≫ g₀.b.left := (hg 0).1 2
  have b₀ : g.b = 1 := Over.OverMorphism.ext (gp.1.hom_ext (hb.trans (by
    rw [z₁]; exact ((hg 0).1 3).symm)) ((Over.w _).trans (Over.w _).symm))
  have b₁ : g.b = ρ ≫ ν'.b := Over.OverMorphism.ext (gp.1.hom_ext (hb.trans (by
    rw [q₁, ← Category.assoc, ← dual_fst, Category.assoc, ← h.1]
    exact (Category.assoc _ _ _).symm)) ((Over.w _).trans (Over.w _).symm))
  have v : ∀ χ (y : (Over.mk (𝟙 (Sp A'))).left) J J', Good D₀.P.L y J → Good D₁.P.L y J' → val (g₀.s (p.xe χ)) (𝟙 _ ≫ spMap f) y J =
      (ConstFam.wVal p.w y J J' (cP D₁ (Over.mk (𝟙 (Sp A'))) χ * (𝟙 _ ≫ g.b)).left)⁻¹ *
        ConstFam.wVal p.w y J J' (cP D₁ (Over.mk (𝟙 (Sp A'))) χ).left * ConstFam.wVal p.w y J J' (𝟙 _ ≫ g.b).left *
        (ConstFam.wVal p.w y J J' (1 : Over.mk (𝟙 (Sp A')) ⟶ D₁.P.A).left)⁻¹ * val (g.s χ) (𝟙 _) y J' :=
    fun χ y J J' hJ hJ' => ((hg χ).2 _ (𝟙 _) y J J' hJ hJ').trans (congrArg (· * _)
      (FormalPoint.prod_gtφT (𝟙 (Over.mk (𝟙 (Sp A')))) g.b χ (ConstFam.wVal p.w y J J')))
  refine ⟨g, ⟨b₀, fun χ => corr_of_val D₁.P.isLB fun y J' hJ' => ?_⟩, congrArg (fun q => q.left) b₁,
    fun χ => corr_of_val D₁.P.isLB fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D₀.P.isLB y
    have e := ((val_corr hJ (z₂ _) _).trans (val_one _)).symm.trans (v χ y J J' hJ hJ')
    have b₂ : 𝟙 _ ≫ g.b = 1 := (Category.id_comp _).trans b₀
    rw [b₂, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at e
    exact e.symm.trans (val_one _).symm
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D₀.P.isLB y
    have e := ((val_corr hJ (q₂ _) _).trans (val_pull hJ _ _ _)).symm.trans (v χ y J J' hJ hJ')
    have b₂ : 𝟙 _ ≫ g.b = ρ ≫ ν'.b := (Category.id_comp _).trans b₁
    have e' := (ConstFam.pmaps_val (h.2 χ).1 (h.2 χ).2 ρ.left hJ hJ').trans (congrArg (· * _)
      (FormalPoint.prod_gtφT ρ ν'.b χ (ConstFam.wVal p.w y J J')))
    rw [b₂] at e
    have m : ρ.left ≫ spMap (dualMap f) = (𝟙 _ ≫ spMap f) ≫ spMap (TrivSqZeroExt.fstHom A A A).toRingHom :=
      (dual_fst f).trans (by rw [Category.id_comp])
    have e'' := mul_left_cancel (e.symm.trans ((congrArg (fun r => val (ν.s (p.xe χ)) r y J) m).symm.trans e'))
    exact e''.trans ((congrArg (fun r => val (ν'.s χ) r y J') (Category.id_comp _).symm).trans
      (val_pull hJ' _ _ _).symm)

theorem existsUnique_thBC (th : D₀.P.L.Sec) : ∃! th', ThBC p th th' := by
  obtain ⟨s, hs⟩ := sec_pull_down ((isGen_iff p.w).1 p.w_gen) D₀.P.isLB D₁.P.isLB th
  refine existsUnique_of_exists_of_unique ⟨s, (through_iff _ _).2 fun y j k hj hk => hs _ (𝟙 _) y j k hj hk⟩
    fun s₁ s₂ h₁ h₂ => ?_
  have k₁ := (through_iff _ _).1 h₁
  have k₂ := (through_iff _ _).1 h₂
  obtain ⟨f₁, _⟩ := s₁
  obtain ⟨f₂, _⟩ := s₂
  obtain rfl : f₁ = f₂ := funext fun k => fn_ext fun y hy => by
    obtain ⟨j, hj⟩ := exists_chart D₀.P.isLB (prj p y)
    exact (Units.mul_right_inj _).1 ((k₁ y j k hj hy).symm.trans (k₂ y j k hj hy))
  rfl

theorem thNZ_of_thBC {th : D₀.P.L.Sec} {th' : D₁.P.L.Sec} (h : ThBC p th th') (hn : ThNZ th) : ThNZ th' := by
  intro y
  obtain ⟨x₀, hx₀, hm⟩ := hn (spMap f y)
  obtain ⟨x, hx₁, hx₂⟩ := Scheme.exists_preimage_of_isPullback (pull_grp p).1 x₀ y hx₀
  obtain rfl : prj p x = x₀ := hx₁
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have hj' : prj p x ∈ D₀.P.L.U j := D₀.P.A.left.basicOpen_le _ hj
  obtain ⟨k, hk⟩ := exists_chart D₁.P.isLB x
  have u₀ : IsUnit (gs (𝟙 _) (prj p x) _ (th.f j)) := by
    rw [gs_eq (𝟙 _) (prj p x) _ hj']; exact (D₀.P.A.left.mem_basicOpen _ _ hj').1 hj
  have u₁ : IsUnit (gs (prj p) x _ (th.f j)) := by rw [gs_stalkMap (prj p) x _ hj']; exact u₀.map _
  have e := (through_iff _ _).1 h x j k hj' hk
  rw [Category.id_comp] at e
  have u₂ := isUnit_of_mul_isUnit_right (e ▸ u₁)
  refine ⟨x, hx₂, TopologicalSpace.Opens.mem_iSup.2 ⟨k, (D₁.P.A.left.mem_basicOpen _ _ hk).2 ?_⟩⟩
  rwa [gs_eq _ _ _ hk] at u₂

end Data

theorem baseChanges : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A A' : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing A'] [IsDomain A'] [IsPrincipalIdealRing A'] (b : O →+* A) (a : ArcIn Dw l β A b) (f : A →+* A'), Function.Injective f → ∀ b' : O →+* A', b' = f.comp b → (∃ (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀), InBC f a a' p) ∧ ∀ (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀), InBC f a a' p → (∀ (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ), ∃ W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ), WitBC f p W W') ∧ (∀ ν, ∃! ν', LetBC p ν ν') ∧ (∀ ν ν', LetBC p ν ν' → GtTanR ν → GtTanR ν') ∧ (∀ th, ∃! th', ThBC p th th') ∧ ∀ th th', ThBC p th th' → ThNZ th → ThNZ th' := by
  intro hL _ hU h5 E _ _ _ H Dw l Xo c O _ β Y A A' _ _ _ _ _ _ b a f hf b' hb'
  subst hb'
  refine ⟨?_, fun a' p h => ⟨fun χ W => ?_, existsUnique_letBC p hL.globalFns,
    fun ν ν' => gtTanR_of_letBC p hL.globalFns, existsUnique_thBC p, fun th th' => thNZ_of_thBC p⟩⟩
  · obtain ⟨a', p, h, -⟩ := ArcPull.exists_isBC hL.polBaseChange hL.globalFns a f hf
    exact ⟨a', p, rfl, h.xe_smul, h.be_eq, h.act, h.eta, h.etaA⟩
  · obtain ⟨-, h₁, h₂, h₃, h₄, h₅⟩ := h
    exact ArcPull.exists_witness_powerSeries hL.globalFns hL.polBaseChange hU h5 ⟨h₁, h₂, h₃, h₄, h₅⟩ W

end GlobalTheory.ArcQBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPidStatement
alias GlobalTheory.T.degenerationData_baseChanges_exist_pid := GlobalTheory.ArcQBC.baseChanges
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem GlobalTheory.ArcQ.frChg_exists_unique_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y : FrPt Xo c S), ((∀ τ, IsUnit (g τ).det) → IsUnit s → ∃ y', FrChg g s y y') ∧ (∀ y' y'', FrChg g s y y' → FrChg g s y y'' → y' = y'') ∧ (∀ y', FrChg g s y y' → (∀ τ, IsUnit (g τ).det) ∧ IsUnit s) ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃ (g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s' : S), FrChg g' s' y y' := by
  intro E _ _ _ H Dw l Xo c S _ _ g s y
  have hunit : ∀ y', FrChg g s y y' → (∀ τ, IsUnit (g τ).det) ∧ IsUnit s := by
    intro y' h
    obtain ⟨h1, h2⟩ := GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y'
    obtain ⟨g', a, hg', h'⟩ := h1 h.1
    obtain ⟨e1, e2⟩ := h2 g g' s a h h'
    subst e1 e2
    exact ⟨hg', a.isUnit⟩
  refine ⟨fun hg hs => ?_, fun y' y'' h' h'' => ?_, hunit, fun y' hx => ?_⟩
  · obtain ⟨a, rfl⟩ := hs
    exact (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y g a hg).exists
  · obtain ⟨hg, a, rfl⟩ := hunit y' h'
    exact (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y g a hg).unique h' h''
  · obtain ⟨g', a, -, h⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y').1 hx
    exact ⟨g', a, h⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertibleStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameChange_exists_unique_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y : FrPt Xo c S), ((∀ τ, IsUnit (g τ).det) → IsUnit s → ∃ y', FrChg g s y y') ∧ (∀ y' y'', FrChg g s y y' → FrChg g s y y'' → y' = y'') ∧ (∀ y', FrChg g s y y' → (∀ τ, IsUnit (g τ).det) ∧ IsUnit s) ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃ (g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s' : S), FrChg g' s' y y' := by
  first | exact @GlobalTheory.ArcQ.frChg_exists_unique_units | exact GlobalTheory.ArcQ.frChg_exists_unique_units | (intros; apply GlobalTheory.ArcQ.frChg_exists_unique_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLetterRingBaseChange
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.LetterMap

def coeffMap {K L : Type} [Field K] [Field L] (f : K →+* L) : LaurentSeries K →+* LaurentSeries L where
  toFun g := HahnSeries.map g f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

theorem _root_.GlobalTheory.LetterMap.coeffMap_ofPowerSeries {K L : Type} [Field K] [Field L] (f : K →+* L)
    (g : PowerSeries K) :
    _root_.GlobalTheory.LetterMap.coeffMap f (HahnSeries.ofPowerSeries ℤ K g) =
      HahnSeries.ofPowerSeries ℤ L (PowerSeries.map f g) := by
  ext n
  change f ((HahnSeries.ofPowerSeries ℤ K g).coeff n) = _
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem _root_.GlobalTheory.LetterMap.det_ne_zero (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (K₁ : Type) [Field K₁] :
    _root_.Formalism.L2.Pj.arcDet Dw K₁ ≠ 0 := by
  unfold _root_.Formalism.L2.Pj.arcDet
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have h : (Matrix.of fun i k ↦
      (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁))) =
      (MvPolynomial.rename (Sigma.mk τ)).mapMatrix
        (Matrix.mvPolynomialX (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (LaurentSeries K₁)) := by
    ext i k; simp
  rw [h, ← AlgHom.map_det]
  intro h0
  rw [map_eq_zero_iff _ (MvPolynomial.rename_injective _ sigma_mk_injective)] at h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ h0

theorem _root_.GlobalTheory.LetterMap.num_algebraMap {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {K₁ : Type} [Field K₁]
    (P : MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) :
    _root_.Formalism.L2.Pj.QAt.arcNum (algebraMap _ (_root_.Formalism.L2.Pj.ArcS Dw K₁) P) = P := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁)) := by
    unfold _root_.Formalism.L2.Pj.ArcS
    exact IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (_root_.GlobalTheory.LetterMap.det_ne_zero Dw K₁))
  have hex : ∃ Q, algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁) Q =
      algebraMap _ (_root_.Formalism.L2.Pj.ArcS Dw K₁) P := ⟨P, rfl⟩
  unfold _root_.Formalism.L2.Pj.QAt.arcNum
  rw [dite_eq_left hex]
  exact hinj hex.choose_spec

end GlobalTheory.LetterMap

namespace GlobalTheory

end GlobalTheory
end
end
